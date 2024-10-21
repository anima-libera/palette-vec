//! `OutPalVec` is like `PalVec` but with an optimization that reduces pressure on keys size
//! in exchange for worse performances in some cases.

use std::{fmt::Debug, num::NonZeroUsize, ops::Index};

use crate::{
    index_map::{IndexMap, IndexMapAccessOptimizer, IndexMapLocalAccessOptimizer},
    key::{keys_size_for_this_many_keys, Key, KeyAllocator, Opsk, OpskAllocator, PaletteKeyType},
    key_vec::KeyVec,
    palette::{CountAndKey, CountAndKeySorting, Palette, PaletteEntry},
    utils::view_to_owned::ViewToOwned,
    BorrowedOrOwned,
};

// TODO: Better doc!
#[derive(Clone)]
pub struct OutPalVec<T, M = AutoMemoryOptimizationPolicyNever>
where
    T: Clone + Eq + Debug,
    M: AutoMemoryOptimizationPolicy,
{
    /// Instances of `outlier_key` are handled by the `index_to_opsk_map` and the `outlier_palette`
    /// and other keys are handled by `palette`.
    key_vec: KeyVec,
    common_palette: Palette<T, Key>,
    /// Is `None` iff the `outlier_palette` is empty.
    outlier_key: Option<Key>,
    outlier_palette: Palette<T, Opsk>,
    /// Exactly every instance of `outlier_key` in the `key_vec` has an entry here.
    index_to_opsk_map: IndexMap,
    /// Memory management operations are potentially expensive.
    /// This policy will decide if such operations are performed at each occasion.
    memory_management_policy: M,
}

/// Mutable cached information that provides hints to internal components of an `OutPalVec`
/// to make some accesses faster when acessing the `OutPalVec` with locality in mind
/// (for example when iterating over it in order (both dorections work) or potentially
/// accessing the same index multiple times).
pub struct OutAccessOptimizer {
    index_map_access: IndexMapLocalAccessOptimizer,
}

impl OutAccessOptimizer {
    pub fn new() -> OutAccessOptimizer {
        OutAccessOptimizer {
            index_map_access: IndexMapLocalAccessOptimizer::new(),
        }
    }
}

impl Default for OutAccessOptimizer {
    fn default() -> Self {
        Self::new()
    }
}

fn as_index_map_access<'a>(
    access: &'a mut Option<&mut OutAccessOptimizer>,
) -> IndexMapAccessOptimizer<'a> {
    match access {
        None => IndexMapAccessOptimizer::None,
        Some(access) => IndexMapAccessOptimizer::Local(&mut access.index_map_access),
    }
}

/// Trait that a automatic memory optimization policy type
/// passed to the corresponding `OutPalVec` type parameter must have.
///
/// It describes how often the `OutPalVec` will perform
/// potentially expensive memory optimization operations on its own.
pub trait AutoMemoryOptimizationPolicy
where
    Self: Clone,
{
    fn new() -> Self;

    const NEW_ELEMENT_BE_COMMON: bool;

    /// Whenever the `OutPalVec` has an occasion to perform memory optimization operations,
    /// this method is asked if that should be done.
    fn perform_memory_optimization_on_this_occasion(&mut self) -> bool;

    fn check_all_invariants(&self) -> bool {
        true
    }
}

/// The `OutPalVec` will never perform memory optimization operations on its own.
///
/// With such policy, it is important to manually trigger the memory optimization method of
/// the `OutPalVec` or else it will remain in a state no better than a `PalVec`.
/// Use this policy when you know what you are doing
/// and that the times you manually trigger memory optimization are sufficient.
#[derive(Clone)]
pub struct AutoMemoryOptimizationPolicyNever;
impl AutoMemoryOptimizationPolicy for AutoMemoryOptimizationPolicyNever {
    fn new() -> Self {
        AutoMemoryOptimizationPolicyNever
    }

    const NEW_ELEMENT_BE_COMMON: bool = true;

    fn perform_memory_optimization_on_this_occasion(&mut self) -> bool {
        false
    }
}

/// The `OutPalVec` will perform memory optimization operations every time it gets the chance.
///
/// This is probably bad, [`AutoMemoryOptimizationPolicyEveryNOccasions`] is probably better.
#[derive(Clone)]
pub struct AutoMemoryOptimizationPolicyAlways;
impl AutoMemoryOptimizationPolicy for AutoMemoryOptimizationPolicyAlways {
    fn new() -> Self {
        AutoMemoryOptimizationPolicyAlways
    }

    const NEW_ELEMENT_BE_COMMON: bool = false;

    fn perform_memory_optimization_on_this_occasion(&mut self) -> bool {
        true
    }
}

/// The `OutPalVec` will perform memory optimization operations once every N occasions.
///
/// The value of `N` might be something to be tweaked.
#[derive(Clone)]
pub struct AutoMemoryOptimizationPolicyEveryNOccasions<const N: usize = 100> {
    counter: usize,
}
impl<const N: usize> AutoMemoryOptimizationPolicy
    for AutoMemoryOptimizationPolicyEveryNOccasions<N>
{
    fn new() -> Self {
        AutoMemoryOptimizationPolicyEveryNOccasions { counter: 0 }
    }

    const NEW_ELEMENT_BE_COMMON: bool = false;

    fn perform_memory_optimization_on_this_occasion(&mut self) -> bool {
        self.counter += 1;
        if N <= self.counter {
            self.counter = 0;
            true
        } else {
            false
        }
    }

    fn check_all_invariants(&self) -> bool {
        if N <= self.counter {
            // The counter is not supposed to get past `N`.
            return false;
        }

        true
    }
}

impl<T, M> OutPalVec<T, M>
where
    T: Clone + Eq + Debug,
    M: AutoMemoryOptimizationPolicy,
{
    /// Returns `false` if it is detected that an invariant is not respected,
    /// meaning that this `Self` is not in a valid state, it is corrupted.
    ///
    /// Safe methods used on a valid `Self`s (if input is needed)
    /// and that terminate without panicking
    /// shall leave `Self` in a valid state,
    /// if that does not happen then the method has a bug.
    pub(crate) fn check_all_invariants(&self) -> bool {
        if !self.common_palette.check_all_invariants() {
            return false;
        }
        if !self.common_palette.check_all_invariants() {
            return false;
        }
        if !self.key_vec.check_all_invariants() {
            return false;
        }
        if !self.index_to_opsk_map.check_all_invariants() {
            return false;
        }
        if !self.memory_management_policy.check_all_invariants() {
            return false;
        }

        {
            // Two ways to get the OutPalVec length.
            let according_to_key_vec = self.key_vec.len();
            let according_to_palettes = self.common_palette.total_instance_count()
                + self.outlier_palette.total_instance_count();
            if according_to_key_vec != according_to_palettes {
                return false;
            }
        }
        {
            // Three ways to get the total number of outlier instances.
            let according_to_index_map = self.index_to_opsk_map.len();
            let according_to_outlier_palette = self.outlier_palette.total_instance_count();
            let according_to_key_vec = (0..self.key_vec.len())
                .map(|index| self.key_vec.get(index).unwrap())
                .filter(|&key| Some(key) == self.outlier_key)
                .count();
            if according_to_index_map != according_to_outlier_palette
                || according_to_index_map != according_to_key_vec
            {
                return false;
            }
        }
        {
            // There is an outlier key iff there are outliers.
            let there_is_an_outlier_key = self.outlier_key.is_some();
            let there_are_outliers = 1 <= self.outlier_palette.len();
            if there_is_an_outlier_key != there_are_outliers {
                return false;
            }
        }

        for common_element in self.common_palette.iter_elements() {
            if self.outlier_palette.contains(common_element) {
                // An element is either common or outlier, not both.
                return false;
            }
        }

        if let Some(outlier_key) = self.outlier_key {
            if !self.key_vec.does_this_key_fit(outlier_key) {
                // It does not make sense to have an outlier key
                // that cannot fit in the key vec.
                return false;
            }
        }

        if let Some(highest_common_palette_key) = self.common_palette.highest_used_key() {
            if !self.key_vec.does_this_key_fit(highest_common_palette_key) {
                // It does not make sense to have used common palette keys
                // that cannot fit in the key vec.
                return false;
            }
        }

        // Prepare the expected count of all the common keys and OPSKs.
        // common_count_by_key[common_key] == expected remaining count of that key.
        // outlier_count_by_key[opsk] == expected remaining count of that opsk.
        let mut common_count_by_key = {
            let common_counts_and_keys = self
                .common_palette
                .counts_and_keys(CountAndKeySorting::KeySmallestFirst);
            let common_table_length = common_counts_and_keys
                .iter()
                .map(|count_and_key| count_and_key.key.value)
                .max()
                .map_or(0, |max_key_value| max_key_value + 1);
            let mut common_count_by_key = vec![0; common_table_length];
            for common_count_and_key in common_counts_and_keys {
                common_count_by_key[common_count_and_key.key.value] = common_count_and_key.count;
            }
            common_count_by_key
        };
        let mut outlier_count_by_key = {
            let outlier_counts_and_keys = self
                .outlier_palette
                .counts_and_keys(CountAndKeySorting::KeySmallestFirst);
            let outlier_table_length = outlier_counts_and_keys
                .iter()
                .map(|count_and_key| count_and_key.key.value)
                .max()
                .map_or(0, |max_key_value| max_key_value + 1);
            let mut outlier_count_by_key = vec![0; outlier_table_length];
            for outlier_count_and_key in outlier_counts_and_keys {
                outlier_count_by_key[outlier_count_and_key.key.value] = outlier_count_and_key.count;
            }
            outlier_count_by_key
        };

        for index in 0..self.key_vec.len() {
            let key = self.key_vec.get(index).unwrap();

            if Some(key) == self.outlier_key {
                // Every element that is represented by the outlier key in the key vec
                // must have a corresponding entry in the index map.
                let Some(opsk) = self
                    .index_to_opsk_map
                    .get(index, &mut IndexMapAccessOptimizer::None)
                else {
                    return false;
                };

                // Count down its expected remaining count.
                let Some(count) = outlier_count_by_key.get_mut(opsk.value) else {
                    return false;
                };
                if *count == 0 {
                    return false;
                }
                *count -= 1;
            } else {
                // Every element that is NOT represented by the outlier key in the key vec
                // must NOT have a corresponding entry in the index map.
                if self
                    .index_to_opsk_map
                    .get(index, &mut IndexMapAccessOptimizer::None)
                    .is_some()
                {
                    return false;
                };

                // Count down its expected remaining count.
                let Some(count) = common_count_by_key.get_mut(key.value) else {
                    return false;
                };
                if *count == 0 {
                    return false;
                }
                *count -= 1;
            }
        }

        // Check the expected remaining counts,
        // after having counted all the keys, there should not be any remaining expected count.
        if common_count_by_key.iter().any(|&count| count != 0) {
            return false;
        }
        if outlier_count_by_key.iter().any(|&count| count != 0) {
            return false;
        }

        true
    }

    pub fn new() -> Self {
        Self {
            key_vec: KeyVec::new(),
            common_palette: Palette::new(),
            outlier_key: None,
            outlier_palette: Palette::new(),
            index_to_opsk_map: IndexMap::new(),
            memory_management_policy: M::new(),
        }
    }

    pub fn with_len(element: T, len: usize) -> Self {
        if len == 0 {
            Self::new()
        } else {
            // `KeyVec::with_len` is filled with `0`s, and
            // `Palette::with_one_entry` associates the given entry to the key `0`,
            // so it matches.
            Self {
                key_vec: KeyVec::with_len(len),
                common_palette: Palette::with_one_entry(element, len),
                outlier_key: None,
                outlier_palette: Palette::new(),
                index_to_opsk_map: IndexMap::new(),
                memory_management_policy: M::new(),
            }
        }
    }

    pub fn len(&self) -> usize {
        self.key_vec.len()
    }

    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
    }

    pub fn outlier_instance_count(&self) -> usize {
        self.index_to_opsk_map.len()
    }

    pub fn common_palette_len(&self) -> usize {
        self.common_palette.len()
    }

    pub fn outlier_palette_len(&self) -> usize {
        self.outlier_palette.len()
    }

    /// Returns the number of instances of the given element.
    ///
    /// This operation is *O*(*common_palette_len + outlier_palette_len*).
    /// The common palette is searched first.
    pub fn number_of_instances(&self, element: &impl ViewToOwned<T>) -> usize {
        let count_if_common = self.common_palette.number_of_instances(element);
        if count_if_common == 0 {
            self.outlier_palette.number_of_instances(element)
        } else {
            count_if_common
        }
    }

    /// Returns `true` if the given element is present in the `PalVec`.
    ///
    /// This operation is *O*(*common_palette_len + outlier_palette_len*).
    /// The common palette is searched first.
    pub fn contains(&self, element: &impl ViewToOwned<T>) -> bool {
        self.number_of_instances(element) != 0
    }

    pub fn get(&self, index: usize, mut access: Option<&mut OutAccessOptimizer>) -> Option<&T> {
        let key = self.key_vec.get(index)?;
        Some(if Some(key) == self.outlier_key {
            let opsk = self
                .index_to_opsk_map
                .get(index, &mut as_index_map_access(&mut access))
                .expect("Bug: Outlier key in `key_vec` but index not in index map");
            self.outlier_palette
                .get(opsk)
                .expect("Bug: Opsk in index map is not used by the palette")
        } else {
            self.common_palette
                .get(key)
                .expect("Bug: Key used in `key_vec` is not used by the palette")
        })
    }

    pub fn set(
        &mut self,
        index: usize,
        element: impl ViewToOwned<T>,
        mut access: Option<&mut OutAccessOptimizer>,
    ) {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            panic!("set index (is {index}) should be < len (is {})", self.len());
        }

        // Remove previous element.
        let key_of_elemement_to_remove = {
            // SAFETY: We checked the bounds, we have `index < self.len()`.
            unsafe { self.key_vec.get_unchecked(index) }
        };
        if Some(key_of_elemement_to_remove) == self.outlier_key {
            let opsk_of_elemement_to_remove = self
                .index_to_opsk_map
                .remove(index, &mut as_index_map_access(&mut access))
                .expect("Bug: Outlier key in `key_vec` but index not in index map");
            self.outlier_palette
                .remove_element_instances(opsk_of_elemement_to_remove, {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                });
        } else {
            self.common_palette
                .remove_element_instances(key_of_elemement_to_remove, {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                });
        }

        // Add new element.
        let key_of_element_to_add = if self.common_palette.contains(&element)
            || (M::NEW_ELEMENT_BE_COMMON && !self.outlier_palette.contains(&element))
        {
            // Already a common element, or a new element if we decided new elements were common.
            self.common_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                },
            )
        } else {
            // Already an outlier, or a new element if we decided new elements were outliers.
            let opsk_of_element_to_add = self.outlier_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut OpskAllocator,
            );
            let previous_entry = self.index_to_opsk_map.set(
                index,
                opsk_of_element_to_add,
                &mut as_index_map_access(&mut access),
            );
            if previous_entry.is_some() {
                panic!("Bug: Index map entry was supposed to be unoccupied");
            }
            if self.outlier_key.is_none() {
                let outlier_key = self.common_palette.smallest_available_key(&KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                });
                self.key_vec.make_sure_a_key_fits(outlier_key);
                self.outlier_key = Some(outlier_key);
            }
            self.outlier_key.unwrap()
        };

        // SAFETY: We checked the bounds so we have `index < self.len()`,
        // and `KeyAllocator` made sure that the key fits.
        unsafe { self.key_vec.set_unchecked(index, key_of_element_to_add) }

        self.consider_this_occasion_to_maybe_perform_memory_optimization();
    }

    pub fn push(&mut self, element: impl ViewToOwned<T>, how_many: usize) {
        // TODO: Factorize the duplicated code with `set`, there is a lot of it.

        if how_many == 0 {
            return;
        }

        let key_of_element_to_add = if self.common_palette.contains(&element)
            || (M::NEW_ELEMENT_BE_COMMON && !self.outlier_palette.contains(&element))
        {
            // Already a common element, or a new element if we decided new elements were common.
            self.common_palette.add_element_instances(
                element,
                {
                    // SAFETY: If `how_many` were zero then we would have returned earlier.
                    unsafe { NonZeroUsize::new_unchecked(how_many) }
                },
                &mut KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                },
            )
        } else {
            // Already an outlier, or a new element if we decided new elements were outliers.
            let opsk_of_element_to_add = self.outlier_palette.add_element_instances(
                element,
                {
                    // SAFETY: If `how_many` were zero then we would have returned earlier.
                    unsafe { NonZeroUsize::new_unchecked(how_many) }
                },
                &mut OpskAllocator,
            );
            for i in 0..how_many {
                let previous_entry = self.index_to_opsk_map.set(
                    self.key_vec.len() + i,
                    opsk_of_element_to_add,
                    &mut IndexMapAccessOptimizer::Push,
                );
                if previous_entry.is_some() {
                    panic!("Bug: Index map entry was supposed to be unoccupied");
                }
            }
            if self.outlier_key.is_none() {
                let outlier_key = self.common_palette.smallest_available_key(&KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                });
                self.key_vec.make_sure_a_key_fits(outlier_key);
                self.outlier_key = Some(outlier_key);
            }
            self.outlier_key.unwrap()
        };

        // SAFETY: `KeyAllocator` made sure that the key fits.
        unsafe { self.key_vec.push_unchecked(key_of_element_to_add, how_many) }

        self.consider_this_occasion_to_maybe_perform_memory_optimization();
    }

    pub fn pop(&mut self) -> Option<BorrowedOrOwned<'_, T>> {
        // TODO: Is there too much duplicated code with `set`?

        self.key_vec.pop().map(|key_of_elemement_to_remove| {
            if Some(key_of_elemement_to_remove) == self.outlier_key {
                let opsk_of_elemement_to_remove = self
                    .index_to_opsk_map
                    .remove(self.key_vec.len(), &mut IndexMapAccessOptimizer::Pop)
                    .expect("Bug: Outlier key in `key_vec` but index not in index map");
                self.outlier_palette
                    .remove_element_instances(opsk_of_elemement_to_remove, {
                        // SAFETY: 1 is not 0.
                        unsafe { NonZeroUsize::new_unchecked(1) }
                    })
            } else {
                self.common_palette
                    .remove_element_instances(key_of_elemement_to_remove, {
                        // SAFETY: 1 is not 0.
                        unsafe { NonZeroUsize::new_unchecked(1) }
                    })
            }
        })
    }

    /// Return the amount of used memory (in bytes), excluding `self` and the palettes.
    ///
    /// May be smaller than the amount of actually allocated memory.
    pub fn used_memory(&self) -> usize {
        let key_vec_memory_in_bits = self.key_vec.len() * self.key_vec.keys_size();
        let key_vec_memory_in_bytes = key_vec_memory_in_bits.div_ceil(8);
        let index_map_memory_in_bytes =
            self.index_to_opsk_map.len() * self.index_to_opsk_map.entry_size();
        key_vec_memory_in_bytes + index_map_memory_in_bytes
    }

    pub fn used_memory_by_the_key_vec(&self) -> usize {
        let key_vec_memory_in_bits = self.key_vec.len() * self.key_vec.keys_size();
        let key_vec_memory_in_bytes = key_vec_memory_in_bits.div_ceil(8);
        #[allow(clippy::let_and_return)]
        key_vec_memory_in_bytes
    }

    pub fn used_memory_by_the_index_map(&self) -> usize {
        let index_map_memory_in_bytes =
            self.index_to_opsk_map.len() * self.index_to_opsk_map.entry_size();
        #[allow(clippy::let_and_return)]
        index_map_memory_in_bytes
    }

    fn consider_this_occasion_to_maybe_perform_memory_optimization(&mut self) {
        if self
            .memory_management_policy
            .perform_memory_optimization_on_this_occasion()
        {
            self.perform_memory_opimization();
        }
    }

    fn compute_memory_optimization_plan(&self) -> MemoryOptimizationPlan {
        let commons = self.common_palette.len();
        let outliers = self.outlier_palette.len();

        let counts_and_keys_common = self
            .common_palette
            .counts_and_keys(CountAndKeySorting::CountSmallestFirst);
        let counts_and_keys_outlier = self
            .outlier_palette
            .counts_and_keys(CountAndKeySorting::CountBiggestFirst);

        // Let us now consider how many elements to move from one palette to the other,
        // for both ways at the same time.
        // For each possibility, we compute the amount of memory it would use,
        // so that we can find the possibility that uses the least amount of memory.
        //
        // The entry size of the index map is hard to predict exactly in some cases,
        // so we assume the biggets possible entry size given the circumstances
        // and if it happens to end up smaller then we will have a good surprise
        // (but at least it never happens to end up bigger than planed).

        let mut best_max_memory_in_bits = None;
        let mut best_c2o_and_o2c = None;
        let mut best_new_keys_size_in_bits = None;
        for how_many_common_to_outlier in 0..=commons {
            for how_many_outlier_to_common in 0..=outliers {
                let new_common_entry_count =
                    (commons - how_many_common_to_outlier) + how_many_outlier_to_common;
                let new_outlier_entry_count =
                    (outliers - how_many_outlier_to_common) + how_many_common_to_outlier;
                let new_common_key_count =
                    new_common_entry_count + if 1 <= new_outlier_entry_count { 1 } else { 0 };
                let new_keys_size_in_bits = keys_size_for_this_many_keys(new_common_key_count);
                let new_key_vec_memory_in_bits = self.key_vec.len() * new_keys_size_in_bits;

                let new_index_map_entry_count = (self.index_to_opsk_map.len()
                    - counts_and_keys_outlier
                        .iter()
                        .map(|count_and_key| count_and_key.count)
                        .take(how_many_outlier_to_common)
                        .sum::<usize>())
                    + counts_and_keys_common
                        .iter()
                        .map(|count_and_key| count_and_key.count)
                        .take(how_many_common_to_outlier)
                        .sum::<usize>();
                let max_index_map_entry_size_in_bytes = IndexMap::max_entry_size(self.len());
                let new_max_index_map_memory_in_bytes =
                    new_index_map_entry_count * max_index_map_entry_size_in_bytes;

                let new_max_memory_in_bits =
                    new_key_vec_memory_in_bits + new_max_index_map_memory_in_bytes * 8;

                if best_max_memory_in_bits.is_some_and(|best_max_memory_in_bits| {
                    new_max_memory_in_bits < best_max_memory_in_bits
                }) || best_max_memory_in_bits.is_none()
                {
                    best_max_memory_in_bits = Some(new_max_memory_in_bits);
                    best_c2o_and_o2c =
                        Some((how_many_common_to_outlier, how_many_outlier_to_common));
                    best_new_keys_size_in_bits = Some(new_keys_size_in_bits);
                }
            }
        }

        let (how_many_common_to_outlier, how_many_outlier_to_common) = best_c2o_and_o2c.unwrap();
        let new_keys_size_in_bits = best_new_keys_size_in_bits.unwrap();

        MemoryOptimizationPlan {
            counts_and_keys_common,
            counts_and_keys_outlier,
            new_keys_size_in_bits,
            how_many_common_to_outlier,
            how_many_outlier_to_common,
        }
    }

    fn apply_memory_optimization_plan(&mut self, plan: MemoryOptimizationPlan) {
        let old_common_highest_used_key = self.common_palette.highest_used_key();
        let old_outlier_highest_used_key = self.outlier_palette.highest_used_key();

        let new_outlier_palette_len = (self.outlier_palette.len()
            + plan.how_many_common_to_outlier)
            - plan.how_many_outlier_to_common;

        // PHASE 1
        //
        // First we extract palette entries that will move to the other palette.

        struct EntryAndOldKey<T, K>
        where
            K: PaletteKeyType,
        {
            entry: PaletteEntry<T>,
            old_key: K,
        }

        let mut common_to_outlier_entries = Vec::with_capacity(plan.how_many_common_to_outlier);
        for i in 0..plan.how_many_common_to_outlier {
            let key = plan.counts_and_keys_common[i].key;
            let entry = self.common_palette.remove_entry(key).unwrap();
            common_to_outlier_entries.push(EntryAndOldKey {
                entry,
                old_key: key,
            });
        }

        let mut outlier_to_common_entries = Vec::with_capacity(plan.how_many_outlier_to_common);
        for i in 0..plan.how_many_outlier_to_common {
            let opsk = plan.counts_and_keys_outlier[i].key;
            let entry = self.outlier_palette.remove_entry(opsk).unwrap();
            outlier_to_common_entries.push(EntryAndOldKey {
                entry,
                old_key: opsk,
            });
        }

        // PHASE 2
        //
        // Now we establish key rewrite tables as we recompose the palettes.
        // Each palette is packed (so that there is no "hole" in the key values it uses)
        // and is added the palette entries that move to this palette according to the plan.
        // While the entries move and their associated keys and OPSKs change,
        // the key changes (and the common/outlier status changes) are recorded in
        // key rewrite tables that will be used to then rewrite the key vec and the the index map.

        #[derive(Clone, Copy, Debug)]
        enum KeyRewrite {
            NoRewrite,
            ToCommonKey(Key),
            ToOutlierKeyWithOPSK(Opsk),
            /// It doesn't make sense to acces this key rewrite,
            /// for example because the old key it corresponds to was not used.
            Unreachable,
        }

        let common_key_rewrite_table_len = match (old_common_highest_used_key, self.outlier_key) {
            (None, None) => 0,
            (None, Some(outlier_key)) => outlier_key.value + 1,
            (Some(higest_used_key), None) => higest_used_key.value + 1,
            (Some(higest_used_key), Some(outlier_key)) => {
                higest_used_key.value.max(outlier_key.value) + 1
            }
        };
        let outlier_key_rewrite_table_len =
            old_outlier_highest_used_key.map_or(0, |highest_used_key| highest_used_key.value + 1);

        let mut common_key_rewrite_table =
            vec![KeyRewrite::Unreachable; common_key_rewrite_table_len];
        let mut outlier_key_rewrite_table =
            vec![KeyRewrite::Unreachable; outlier_key_rewrite_table_len];

        let old_outlier_key = self.outlier_key;
        let new_outlier_key = (1 <= new_outlier_palette_len).then_some(
            self.common_palette.smallest_available_key(&KeyAllocator {
                key_vec: &mut self.key_vec,
                reserved_key: None,
            }),
        );

        // Common to common rewrites.
        for key_value_to_rewrite_if_used in 0..common_key_rewrite_table_len {
            if let Some(entry) = self
                .common_palette
                .remove_entry(Key::with_value(key_value_to_rewrite_if_used))
            {
                let new_key = self.common_palette.add_entry(
                    entry,
                    &mut KeyAllocator {
                        key_vec: &mut self.key_vec,
                        reserved_key: new_outlier_key,
                    },
                );
                let old_key_value = key_value_to_rewrite_if_used;
                common_key_rewrite_table[old_key_value] =
                    if Key::with_value(old_key_value) == new_key {
                        KeyRewrite::NoRewrite
                    } else {
                        KeyRewrite::ToCommonKey(new_key)
                    };
            }
        }

        // Outlier to outlier rewrites.
        for key_value_to_rewrite_if_used in 0..outlier_key_rewrite_table_len {
            if let Some(entry) = self
                .outlier_palette
                .remove_entry(Opsk::with_value(key_value_to_rewrite_if_used))
            {
                let new_opsk = self.outlier_palette.add_entry(entry, &mut OpskAllocator);
                let old_opsk_value = key_value_to_rewrite_if_used;
                outlier_key_rewrite_table[old_opsk_value] =
                    if Opsk::with_value(old_opsk_value) == new_opsk {
                        KeyRewrite::NoRewrite
                    } else {
                        KeyRewrite::ToOutlierKeyWithOPSK(new_opsk)
                    };
            }
        }

        // Outlier to common rewrites.
        for entry_and_old_key in outlier_to_common_entries {
            let new_key = self.common_palette.add_entry(
                entry_and_old_key.entry,
                &mut KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: new_outlier_key,
                },
            );
            outlier_key_rewrite_table[entry_and_old_key.old_key.value] =
                KeyRewrite::ToCommonKey(new_key);
        }

        // Common to outlier rewrites.
        for entry_and_old_key in common_to_outlier_entries {
            let new_opsk = self
                .outlier_palette
                .add_entry(entry_and_old_key.entry, &mut OpskAllocator);
            common_key_rewrite_table[entry_and_old_key.old_key.value] =
                KeyRewrite::ToOutlierKeyWithOPSK(new_opsk);
        }

        // PHASE 3
        //
        // Now we use the key rewrite tables to rewrite the key vec and the the index map.

        self.outlier_key = new_outlier_key;

        let mut index_map_local_access = IndexMapLocalAccessOptimizer::new();
        let mut index_map_access = IndexMapAccessOptimizer::Local(&mut index_map_local_access);
        for index_in_key_vec in 0..self.key_vec.len() {
            let old_key = self.key_vec.get(index_in_key_vec).unwrap();
            if Some(old_key) == old_outlier_key {
                // The old key was the outlier key.
                let old_opsk = self
                    .index_to_opsk_map
                    .get(index_in_key_vec, &mut index_map_access)
                    .expect("Bug: Outlier key in key vec but no entry in index map");
                let key_rewrite = outlier_key_rewrite_table[old_opsk.value];
                match key_rewrite {
                    KeyRewrite::NoRewrite => {
                        if new_outlier_key != old_outlier_key {
                            self.key_vec.set(index_in_key_vec, new_outlier_key.unwrap());
                        }
                    }
                    KeyRewrite::ToCommonKey(new_key) => {
                        self.key_vec.set(index_in_key_vec, new_key);
                        self.index_to_opsk_map
                            .remove(index_in_key_vec, &mut index_map_access);
                    }
                    KeyRewrite::ToOutlierKeyWithOPSK(new_opsk) => {
                        if new_outlier_key != old_outlier_key {
                            self.key_vec.set(index_in_key_vec, new_outlier_key.unwrap());
                        }
                        self.index_to_opsk_map.set(
                            index_in_key_vec,
                            new_opsk,
                            &mut index_map_access,
                        );
                    }
                    KeyRewrite::Unreachable => unreachable!(),
                }
            } else {
                // The old key was not the outlier key.
                let key_rewrite = common_key_rewrite_table[old_key.value];
                match key_rewrite {
                    KeyRewrite::NoRewrite => {}
                    KeyRewrite::ToCommonKey(new_key) => {
                        self.key_vec.set(index_in_key_vec, new_key);
                    }
                    KeyRewrite::ToOutlierKeyWithOPSK(new_opsk) => {
                        self.key_vec.set(index_in_key_vec, new_outlier_key.unwrap());
                        self.index_to_opsk_map.set(
                            index_in_key_vec,
                            new_opsk,
                            &mut index_map_access,
                        );
                    }
                    KeyRewrite::Unreachable => unreachable!(),
                }
            }
        }

        self.key_vec.change_keys_size(plan.new_keys_size_in_bits);
    }

    pub fn perform_memory_opimization(&mut self) {
        let plan = self.compute_memory_optimization_plan();
        self.apply_memory_optimization_plan(plan);
    }
}

struct MemoryOptimizationPlan {
    counts_and_keys_common: Vec<CountAndKey<Key>>,
    counts_and_keys_outlier: Vec<CountAndKey<Opsk>>,
    new_keys_size_in_bits: usize,
    how_many_common_to_outlier: usize,
    how_many_outlier_to_common: usize,
}

impl<T> Default for OutPalVec<T>
where
    T: Clone + Eq + Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Index<usize> for OutPalVec<T>
where
    T: Clone + Eq + Debug,
{
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index, None) {
            Some(element) => element,
            None => {
                panic!("index (is {index}) should be < len (is {})", self.len());
            }
        }
    }
}

impl<T> Index<(usize, Option<&mut OutAccessOptimizer>)> for OutPalVec<T>
where
    T: Clone + Eq + Debug,
{
    type Output = T;
    fn index(&self, (index, access): (usize, Option<&mut OutAccessOptimizer>)) -> &Self::Output {
        match self.get(index, access) {
            Some(element) => element,
            None => {
                panic!("index (is {index}) should be < len (is {})", self.len());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{OptionBorrowedOrOwnedAsRef, OptionBorrowedOrOwnedCopied};

    use super::*;

    #[test]
    fn new_is_empty() {
        let palvec: OutPalVec<()> = OutPalVec::new();
        assert!(palvec.is_empty());
        assert_eq!(palvec.len(), 0);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn push_and_len() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert_eq!(palvec.len(), 0);
        palvec.push((), 1);
        assert_eq!(palvec.len(), 1);
        palvec.push((), 1);
        assert_eq!(palvec.len(), 2);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn push_and_get() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(42, 1);
        assert_eq!(palvec.get(0, None), Some(&42));
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn get_out_of_bounds_is_none() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert!(palvec.get(0, None).is_none());
        palvec.push((), 1);
        palvec.push((), 1);
        assert!(palvec.get(0, None).is_some());
        assert!(palvec.get(1, None).is_some());
        assert!(palvec.get(2, None).is_none());
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn pop_empty() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert_eq!(palvec.pop().map_as_ref(), None);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn push_and_pop_strings() {
        let mut palvec: OutPalVec<String> = OutPalVec::new();
        palvec.push("uwu", 1);
        palvec.push(String::from("owo"), 1);
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("uwu"));
        assert_eq!(palvec.pop().map_as_ref(), None);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn push_and_pop_numbers() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8, 1);
        palvec.push(5, 1);
        assert_eq!(palvec.pop().map_copied(), Some(5));
        assert_eq!(palvec.pop().map_copied(), Some(8));
        assert_eq!(palvec.pop().map_as_ref(), None);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    #[should_panic]
    fn set_out_of_bounds_panic() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        palvec.push((), 1);
        palvec.push((), 1);
        palvec.set(2, (), None);
    }

    #[test]
    fn with_len() {
        let palvec: OutPalVec<()> = OutPalVec::with_len((), 18);
        assert!(!palvec.is_empty());
        assert_eq!(palvec.len(), 18);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn set_and_get() {
        let mut palvec: OutPalVec<i32> = OutPalVec::with_len(0, 20);
        palvec.set(10, 0, None);
        palvec.set(11, 1, None);
        palvec.set(12, 1, None);
        palvec.set(13, 2, None);
        assert_eq!(palvec.get(0, None), Some(&0));
        assert_eq!(palvec.get(19, None), Some(&0));
        assert_eq!(palvec.get(10, None), Some(&0));
        assert_eq!(palvec.get(11, None), Some(&1));
        assert_eq!(palvec.get(12, None), Some(&1));
        assert_eq!(palvec.get(13, None), Some(&2));
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn single_index() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8, 1);
        palvec.push(5, 1);
        assert_eq!(palvec[0], 8);
        assert_eq!(palvec[1], 5);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn clone() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8, 1);
        palvec.push(5, 1);
        let palvec = palvec.clone();
        assert_eq!(palvec[0], 8);
        assert_eq!(palvec[1], 5);
        assert_eq!(palvec.len(), 2);
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn access_hint() {
        let mut palvec: OutPalVec<i32> = OutPalVec::with_len(0, 20);
        let mut access = Some(OutAccessOptimizer::new());
        palvec.set(10, 0, access.as_mut());
        palvec.set(11, 1, access.as_mut());
        palvec.set(12, 1, access.as_mut());
        palvec.set(13, 2, access.as_mut());
        assert_eq!(palvec.get(0, access.as_mut()), Some(&0));
        assert_eq!(palvec.get(19, access.as_mut()), Some(&0));
        assert_eq!(palvec.get(10, access.as_mut()), Some(&0));
        assert_eq!(palvec.get(11, access.as_mut()), Some(&1));
        assert_eq!(palvec.get(12, access.as_mut()), Some(&1));
        assert_eq!(palvec.get(13, access.as_mut()), Some(&2));
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn memory_management() {
        let mut palvec: OutPalVec<isize, AutoMemoryOptimizationPolicyEveryNOccasions<20>> =
            OutPalVec::new();
        let mut vec_to_compare = vec![];
        for i in 0..100 {
            for _j in 0..i {
                palvec.push(-i, 1);
                vec_to_compare.push(-i);
            }
        }
        #[allow(clippy::needless_range_loop)]
        for i in 0..vec_to_compare.len() {
            assert_eq!(palvec.get(i, None), Some(&vec_to_compare[i]));
        }
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn memory_optimization_plan() {
        let mut palvec: OutPalVec<isize, AutoMemoryOptimizationPolicyNever> = OutPalVec::new();
        let mut vec_to_compare = vec![];
        for i in 0..3 {
            for _j in 0..1000 {
                palvec.push(-i, 1);
                vec_to_compare.push(-i);
            }
        }
        // 6 palette entries of very small instance count.
        // They default to be common (due to the policy) but they should be planed to
        // be moved to the outliers.
        for value in [-10, -10, -10, -11, -11, -12, -13, -14, -15] {
            palvec.push(value, 1);
            vec_to_compare.push(value);
        }
        let plan = palvec.compute_memory_optimization_plan();
        assert_eq!(plan.how_many_common_to_outlier, 6);
        assert_eq!(plan.how_many_outlier_to_common, 0);
        for count_and_key in plan.counts_and_keys_common.iter().take(6) {
            // Check that they are sorted correctly so that the 6 commons that are flagged to move
            // are the 6 we think about.
            assert!(count_and_key.count <= 3);
        }
        #[allow(clippy::needless_range_loop)]
        for i in 0..vec_to_compare.len() {
            assert_eq!(palvec.get(i, None), Some(&vec_to_compare[i]));
        }
        assert!(palvec.check_all_invariants());
    }

    #[test]
    fn memory_management_2() {
        let mut palvec: OutPalVec<isize, AutoMemoryOptimizationPolicyNever> = OutPalVec::new();
        let mut vec_to_compare = vec![];
        for i in 0..3 {
            for _j in 0..1000 {
                palvec.push(-i, 1);
                vec_to_compare.push(-i);
            }
        }
        // 6 palette entries of very small instance count.
        // They default to be common (due to the policy) but they should be planed to
        // be moved to the outliers.
        for value in [-10, -10, -10, -11, -11, -12, -13, -14, -15] {
            palvec.push(value, 1);
            vec_to_compare.push(value);
        }
        palvec.perform_memory_opimization();
        assert_eq!(palvec.outlier_palette.len(), 6);
        #[allow(clippy::needless_range_loop)]
        for i in 0..vec_to_compare.len() {
            assert_eq!(palvec.get(i, None), Some(&vec_to_compare[i]));
        }
        assert!(palvec.check_all_invariants());
    }
}
