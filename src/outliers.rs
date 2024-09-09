//! `OutPalVec` is like `PalVec` but with an optimization that reduces pressure on keys size
//! in exchange for worse performances in some cases.

use std::{marker::PhantomData, num::NonZeroUsize, ops::Index};

use crate::{
    index_map::{IndexMap, IndexMapAccessOptimizer, IndexMapLocalAccessOptimizer},
    key::{Key, KeyAllocator, Opsk, OpskAllocator, PaletteKeyType},
    key_vec::KeyVec,
    palette::Palette,
    utils::view_to_owned::ViewToOwned,
    BorrowedOrOwned,
};

// TODO: Better doc!
#[derive(Clone)]
pub struct OutPalVec<T, I = OutlierMemoryRatioIntervalDefault>
where
    T: Clone + Eq,
    I: OutlierMemoryRatioInterval,
{
    /// Instances of `outlier_key` are handled by the `index_to_opsk_map` and the `outlier_palette`
    /// and other keys are handled by `palette`.
    key_vec: KeyVec,
    common_palette: Palette<T, Key>,
    /// Is `None` iff the `outlier_palette` is empty.
    outlier_key: Option<Key>,
    outlier_palette: Palette<T, Opsk>,
    /// Exactly every instance of `outlier_key` in the `key_vec` has an entry here.
    ///
    /// TODO: Maybe provide an alternative to the hash map, like a sorted vec. This would
    /// allow to really get its memory usage smaller, and also to know its memory usage
    /// with precision, which enables the best possible memory usage optimization for this whole
    /// thing as we could think in terms of smaller memory usage to decide when to move elements
    /// between the outlier and common palettes.
    index_to_opsk_map: IndexMap,
    /// The palette holds owned `T`s, also `T` has to be used in a field.
    _phantom: PhantomData<T>,
    /// `I` has to be used in a field.
    _phantom_interval: PhantomData<I>,
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

pub trait OutlierMemoryRatioInterval
where
    Self: Clone,
{
    const LOWER_LIMIT_WEAK: f32;
    const UPPER_LIMIT: f32;
}

#[derive(Clone)]
pub struct OutlierMemoryRatioIntervalDefault;
impl OutlierMemoryRatioInterval for OutlierMemoryRatioIntervalDefault {
    const LOWER_LIMIT_WEAK: f32 = 0.013;
    const UPPER_LIMIT: f32 = 0.025;
}

impl<T, I> OutPalVec<T, I>
where
    T: Clone + Eq,
    I: OutlierMemoryRatioInterval,
{
    pub fn new() -> Self {
        Self {
            key_vec: KeyVec::new(),
            common_palette: Palette::new(),
            outlier_key: None,
            outlier_palette: Palette::new(),
            index_to_opsk_map: IndexMap::new(),
            _phantom: PhantomData,
            _phantom_interval: PhantomData,
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
                _phantom: PhantomData,
                _phantom_interval: PhantomData,
            }
        }
    }

    pub fn len(&self) -> usize {
        self.key_vec.len()
    }

    pub fn outlier_instance_count(&self) -> usize {
        self.index_to_opsk_map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
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
        let key_of_element_to_add = if self.common_palette.contains(&element) {
            // Already a common element.
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
            // Either a new element or an already outlier element.
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

        self.enforce_upper_limit_on_outlier_ratio();
    }

    pub fn push(&mut self, element: impl ViewToOwned<T>) {
        // TODO: Factorize the duplicated code with `set`, there is a lot of it.

        let key_of_element_to_add = if self.common_palette.contains(&element) {
            // Already a common element.
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
            // Either a new element or an already outlier element.
            let opsk_of_element_to_add = self.outlier_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut OpskAllocator,
            );
            let previous_entry = self.index_to_opsk_map.set(
                self.key_vec.len(),
                opsk_of_element_to_add,
                &mut IndexMapAccessOptimizer::Push,
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

        // SAFETY: `KeyAllocator` made sure that the key fits.
        unsafe { self.key_vec.push_unchecked(key_of_element_to_add) }

        self.enforce_upper_limit_on_outlier_ratio();
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

    fn move_most_numerous_outlier_to_common(&mut self) {
        let Some(opsk_to_move) = self.outlier_palette.key_of_most_instanced_element() else {
            return;
        };
        let palette_entry = self
            .outlier_palette
            .remove_entry(opsk_to_move)
            .expect("Bug: We just got this opsk from the outlier palette");
        if self.outlier_palette.len() == 0 {
            // There are no outliers anymore, we can make the outlier key available.
            self.outlier_key = None;
        }
        let new_key = self.common_palette.add_entry(
            palette_entry,
            &mut KeyAllocator {
                key_vec: &mut self.key_vec,
                reserved_key: self.outlier_key,
            },
        );
        self.index_to_opsk_map
            .remove_all_with_opsk(opsk_to_move, |index| {
                self.key_vec.set(index, new_key);
            });
    }

    fn move_least_numerous_common_to_outlier(&mut self) {
        let Some(key_to_move) = self.common_palette.key_of_least_instanced_element() else {
            return;
        };
        let highest_key_value = if let Some(outlier_key) = self.outlier_key {
            self.common_palette.len().max(outlier_key.value)
        } else {
            self.common_palette.len()
        };
        let mut key_rewriting_map: Vec<Option<Key>> = vec![None; highest_key_value];
        let palette_entry = self
            .common_palette
            .remove_entry(key_to_move)
            .expect("Bug: We just got this key from the common palette");
        let how_many_entries_to_add_to_index_map = palette_entry.count();
        if self.outlier_key.is_none() {
            let outlier_key = self.common_palette.smallest_available_key(&KeyAllocator {
                key_vec: &mut self.key_vec,
                reserved_key: self.outlier_key,
            });
            self.key_vec.make_sure_a_key_fits(outlier_key);
            self.outlier_key = Some(outlier_key);
        }
        let new_opsk = self
            .outlier_palette
            .add_entry(palette_entry, &mut OpskAllocator);
        key_rewriting_map[key_to_move.value] = Some(self.outlier_key.unwrap());
        loop {
            let highest_key_value = if let Some(outlier_key) = self.outlier_key {
                self.common_palette.len().max(outlier_key.value)
            } else {
                self.common_palette.len()
            };
            let available_key = self.common_palette.smallest_available_key(&KeyAllocator {
                key_vec: &mut self.key_vec,
                reserved_key: self.outlier_key,
            });
            if highest_key_value <= available_key.value {
                break;
            } else if self
                .outlier_key
                .is_some_and(|outlier_key| outlier_key.value == highest_key_value)
            {
                key_rewriting_map[self.outlier_key.unwrap().value] = Some(available_key);
                key_rewriting_map[key_to_move.value] = Some(available_key);
            } else {
                let palette_entry = self
                    .common_palette
                    .remove_entry(Key::with_value(highest_key_value))
                    .expect("Bug: We just got this key from the common palette");
                let new_key_for_this_entry = self.common_palette.add_entry(
                    palette_entry,
                    &mut KeyAllocator {
                        key_vec: &mut self.key_vec,
                        reserved_key: self.outlier_key,
                    },
                );
                key_rewriting_map[highest_key_value] = Some(new_key_for_this_entry);
            }
        }
        let mut add_many_entries_to_index_map = self
            .index_to_opsk_map
            .add_many_entries(how_many_entries_to_add_to_index_map);
        for index in (0..self.key_vec.len()).rev() {
            let key = self.key_vec.get(index).unwrap();
            if let Some(new_key) = key_rewriting_map[key.value] {
                self.key_vec.set(index, new_key);
                if Some(new_key) == self.outlier_key {
                    add_many_entries_to_index_map.add_entry(index, new_opsk);
                }
            }
        }
        add_many_entries_to_index_map.finish();
    }

    fn outlier_ratio(&self) -> Option<f32> {
        let len = self.len();
        (len != 0).then(|| {
            let outlier_instance_count = self.outlier_instance_count();
            outlier_instance_count as f32 / len as f32
        })
    }

    fn enforce_upper_limit_on_outlier_ratio(&mut self) {
        loop {
            let Some(outlier_ratio) = self.outlier_ratio() else {
                return;
            };
            if outlier_ratio <= I::UPPER_LIMIT {
                // All is good.
                break;
            }
            self.move_most_numerous_outlier_to_common();
        }
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
}

impl<T> Default for OutPalVec<T>
where
    T: Clone + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Index<usize> for OutPalVec<T>
where
    T: Clone + Eq,
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
    T: Clone + Eq,
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
    }

    #[test]
    fn push_and_len() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert_eq!(palvec.len(), 0);
        palvec.push(());
        assert_eq!(palvec.len(), 1);
        palvec.push(());
        assert_eq!(palvec.len(), 2);
    }

    #[test]
    fn push_and_get() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(42);
        assert_eq!(palvec.get(0, None), Some(&42));
    }

    #[test]
    fn get_out_of_bounds_is_none() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert!(palvec.get(0, None).is_none());
        palvec.push(());
        palvec.push(());
        assert!(palvec.get(0, None).is_some());
        assert!(palvec.get(1, None).is_some());
        assert!(palvec.get(2, None).is_none());
    }

    #[test]
    fn pop_empty() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn push_and_pop_strings() {
        let mut palvec: OutPalVec<String> = OutPalVec::new();
        palvec.push("uwu");
        palvec.push(String::from("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("uwu"));
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn push_and_pop_numbers() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert_eq!(palvec.pop().map_copied(), Some(5));
        assert_eq!(palvec.pop().map_copied(), Some(8));
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    #[should_panic]
    fn set_out_of_bounds_panic() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        palvec.push(());
        palvec.push(());
        palvec.set(2, (), None);
    }

    #[test]
    fn with_len() {
        let palvec: OutPalVec<()> = OutPalVec::with_len((), 18);
        assert!(!palvec.is_empty());
        assert_eq!(palvec.len(), 18);
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
    }

    #[test]
    fn outlier_ratio_upper_limit() {
        #[derive(Clone)]
        pub struct OutlierMemoryRatioIntervalTest;
        impl OutlierMemoryRatioInterval for OutlierMemoryRatioIntervalTest {
            const LOWER_LIMIT_WEAK: f32 = 0.010;
            const UPPER_LIMIT: f32 = 0.030;
        }
        let mut palvec: OutPalVec<String, OutlierMemoryRatioIntervalTest> =
            OutPalVec::with_len("common".to_string(), 1000);
        for i in 0..100 {
            palvec.set(i, format!("{}", i), None);
        }
        for i in 100..200 {
            palvec.set(i, "uwu", None);
        }
        // 100 all different outliers, and 100 other identical outliers, so 200 outliers
        // but the `OutlierMemoryRatioInterval::SUP` upper ratio limit is enforced
        assert_eq!(palvec.outlier_instance_count(), 30);
        for i in 0..100 {
            assert_eq!(palvec.get(i, None), Some(&format!("{}", i)));
        }
        for i in 100..200 {
            assert_eq!(
                palvec.get(i, None).as_ref().map(|s| s.as_str()),
                Some("uwu")
            );
        }
        for i in 200..1000 {
            assert_eq!(
                palvec.get(i, None).as_ref().map(|s| s.as_str()),
                Some("common")
            );
        }
    }

    #[test]
    fn single_index() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert_eq!(palvec[0], 8);
        assert_eq!(palvec[1], 5);
    }

    #[test]
    fn clone() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        let palvec = palvec.clone();
        assert_eq!(palvec[0], 8);
        assert_eq!(palvec[1], 5);
        assert_eq!(palvec.len(), 2);
    }

    #[test]
    fn move_least_numerous_common_to_outlier() {
        let mut palvec: OutPalVec<i32> = OutPalVec::with_len(0, 20);
        palvec.set(10, 0, None);
        palvec.set(11, 1, None);
        palvec.set(12, 1, None);
        palvec.set(13, 2, None);
        palvec.move_least_numerous_common_to_outlier();
        assert_eq!(palvec.get(0, None), Some(&0));
        assert_eq!(palvec.get(19, None), Some(&0));
        assert_eq!(palvec.get(10, None), Some(&0));
        assert_eq!(palvec.get(11, None), Some(&1));
        assert_eq!(palvec.get(12, None), Some(&1));
        assert_eq!(palvec.get(13, None), Some(&2));
    }

    #[test]
    fn move_least_numerous_common_to_outlier_2() {
        let mut palvec: OutPalVec<usize> = OutPalVec::with_len(42, 100 * 100);
        for i in 0..100 {
            for j in 0..100 {
                palvec.set(i * 100 + j, i * 100, None);
            }
        }
        for _k in 0..50 {
            for i in 0..100 {
                for j in 0..100 {
                    assert_eq!(palvec.get(i * 100 + j, None), Some(&(i * 100)));
                }
            }
            palvec.move_least_numerous_common_to_outlier();
        }
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
    }
}
