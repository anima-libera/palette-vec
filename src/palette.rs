use std::{fmt::Debug, marker::PhantomData, mem::MaybeUninit, num::NonZeroUsize};

use crate::{
    key::{PaletteKeyAllocator, PaletteKeyType},
    utils::view_to_owned::ViewToOwned,
    BorrowedOrOwned,
};

pub(crate) struct PaletteEntry<T> {
    count: usize,
    /// Initialized iff `count` is non-zero.
    element: MaybeUninit<T>,
}

impl<T> Default for PaletteEntry<T> {
    fn default() -> Self {
        Self {
            count: 0,
            element: MaybeUninit::uninit(),
        }
    }
}

impl<T> Clone for PaletteEntry<T>
where
    T: Clone,
{
    fn clone(&self) -> Self {
        Self {
            count: self.count,
            element: if self.count == 0 {
                MaybeUninit::uninit()
            } else {
                MaybeUninit::new({
                    // SAFETY: The entry's `count` is non zero so the element is initialized.
                    unsafe { self.element.assume_init_ref().clone() }
                })
            },
        }
    }
}

#[derive(Clone)]
pub(crate) struct Palette<T, K>
where
    T: Clone + Eq,
    K: PaletteKeyType,
{
    vec: Vec<PaletteEntry<T>>,
    _phantom: PhantomData<K>,
}

pub(crate) enum BrokenInvariantInPalette<K>
where
    K: PaletteKeyType,
{
    /// There are two different keys that are associated to the same element value.
    ///
    /// There must be one and only one key value associated to each element in the palette.
    TwoKeysHaveSameElement { keys: (K, K) },
}

impl<T, K> Palette<T, K>
where
    T: Clone + Eq,
    K: PaletteKeyType,
{
    /// Returns `Err` if it is detected that an invariant is not respected,
    /// meaning that this `Self` is not in a valid state, it is corrupted.
    ///
    /// Safe methods used on a valid `Self`s (if input is needed)
    /// and that terminate without panicking
    /// shall leave `Self` in a valid state,
    /// if that does not happen then the method has a bug.
    pub(crate) fn check_all_invariants(&self) -> Result<(), BrokenInvariantInPalette<K>> {
        for index_a in 0..self.vec.len() {
            for index_b in (index_a + 1)..self.vec.len() {
                let entry_a = &self.vec[index_a];
                let entry_b = &self.vec[index_b];
                if 0 < entry_a.count && 0 < entry_b.count {
                    // SAFETY: The entries' `count` are non zero so the elements are initialized.
                    let (element_a, element_b) = unsafe {
                        (
                            entry_a.element.assume_init_ref(),
                            entry_b.element.assume_init_ref(),
                        )
                    };
                    if element_a == element_b {
                        return Err(BrokenInvariantInPalette::TwoKeysHaveSameElement {
                            keys: (K::with_value(index_a), K::with_value(index_b)),
                        });
                    }
                }
            }
        }

        Ok(())
    }

    /// Creates an empty palette.
    ///
    /// Does not allocate now,
    /// allocations are done when keys are added to it or it is told to reserve memory.
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            vec: vec![],
            _phantom: PhantomData,
        }
    }

    /// Creates a palette that initially contains one entry.
    pub(crate) fn with_one_entry(element: T, count: usize) -> Self {
        Self {
            vec: vec![PaletteEntry {
                count,
                element: MaybeUninit::new(element),
            }],
            _phantom: PhantomData,
        }
    }

    /// Returns the number of entries in the palette (and not the total number of instances).
    pub(crate) fn len(&self) -> usize {
        self.vec
            .iter()
            .filter(|palette_entry| 0 < palette_entry.count)
            .count()
    }

    pub(crate) fn total_instance_count(&self) -> usize {
        self.vec
            .iter()
            .map(|palette_entry| palette_entry.count)
            .sum()
    }

    pub(crate) fn smallest_available_key(&self, key_allocator: &impl PaletteKeyAllocator<K>) -> K {
        for key_value in 0.. {
            let key = K::with_value(key_value);
            if let Some(palette_entry) = self.vec.get(key_value) {
                if palette_entry.count == 0 && key_allocator.can_allocate(key) {
                    return key;
                }
            } else if key_allocator.can_allocate(key) {
                return key;
            }
        }
        unreachable!()
    }

    fn allocate_smallest_available_key(
        &self,
        key_allocator: &mut impl PaletteKeyAllocator<K>,
    ) -> K {
        let allocated_key = self.smallest_available_key(key_allocator);
        key_allocator.palette_allocate(allocated_key);
        allocated_key
    }

    fn get_palette_entry_and_key_value(
        &self,
        element: &impl ViewToOwned<T>,
    ) -> Option<(usize, &PaletteEntry<T>)> {
        self.vec
            .iter()
            .enumerate()
            .find(|(_key_value, palette_entry)| {
                if 0 < palette_entry.count {
                    let entry_element = {
                        // SAFETY: The entry's `count` is non zero
                        // so the element is initialized.
                        unsafe { palette_entry.element.assume_init_ref() }
                    };
                    element.eq(entry_element)
                } else {
                    false
                }
            })
    }

    fn get_mut_palette_entry_and_key_value(
        &mut self,
        element: &impl ViewToOwned<T>,
    ) -> Option<(usize, &mut PaletteEntry<T>)> {
        self.vec
            .iter_mut()
            .enumerate()
            .find(|(_key_value, palette_entry)| {
                if 0 < palette_entry.count {
                    let entry_element = {
                        // SAFETY: The entry's `count` is non zero
                        // so the element is initialized.
                        unsafe { palette_entry.element.assume_init_ref() }
                    };
                    element.eq(entry_element)
                } else {
                    false
                }
            })
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and return the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub(crate) fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut impl PaletteKeyAllocator<K>,
    ) -> K {
        let already_in_palette = self.get_mut_palette_entry_and_key_value(&element);
        if let Some((key_value, palette_entry)) = already_in_palette {
            palette_entry.count = palette_entry
                .count
                .checked_add(that_many.get())
                .expect("Palette entry count overflow (max is usize::MAX)");
            K::with_value(key_value)
        } else {
            let key = self.allocate_smallest_available_key(key_allocator);
            // Making sure that `vec.len()` is at least `key + 1`.
            if self.vec.len() <= key.value() {
                self.vec.resize_with(key.value() + 1, PaletteEntry::default);
            }
            let palette_entry = {
                // SAFETY: We just made sure that `vec.len()` is at least `key + 1`,
                // so we cannot be out-of-bounds here.
                unsafe { self.vec.get_mut(key.value()).unwrap_unchecked() }
            };
            *palette_entry = PaletteEntry {
                count: that_many.get(),
                element: MaybeUninit::new(element.into_owned()),
            };
            key
        }
    }

    /// Tells the palette that `that_many` instances of the element corresponding to the given key
    /// will be removed from the `PalVec`'s array,
    /// and it must update its map and counts and all,
    /// possiby deallocating the key if the element has no more instances.
    ///
    /// Only touches the palette and key allocator.
    /// The caller must make sure that indeed `that_many` instances of the given key
    /// are indeed removed from `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not used by the palette.
    ///
    /// Panics if `that_many` is more than the number of instances of the `element`.
    pub(crate) fn remove_element_instances(
        &mut self,
        key: K,
        that_many: NonZeroUsize,
    ) -> BorrowedOrOwned<'_, T> {
        let palette_entry = self
            .vec
            .get_mut(key.value())
            .expect("Bug: Removing element instances by a key that is unused");
        palette_entry.count = palette_entry
            .count
            .checked_sub(that_many.get())
            .expect("Bug: Removing more element instances from palette than its count");
        let count = palette_entry.count;
        if count == 0 {
            let removed_element =
                std::mem::replace(&mut palette_entry.element, MaybeUninit::uninit());
            let removed_element = {
                // SAFETY: We cound subtract (without overflow) `count` by NonZero `that_many`,
                // so we know that `count` was non-zero before the subtraction,
                // which means that the `element` was initialized.
                unsafe { removed_element.assume_init() }
            };
            BorrowedOrOwned::Owned(removed_element)
        } else {
            let element = {
                // SAFETY: We cound subtract (without overflow) `count` by NonZero `that_many`,
                // so we know that `count` was non-zero before the subtraction,
                // which means that the `element` was initialized.
                unsafe { palette_entry.element.assume_init_ref() }
            };
            BorrowedOrOwned::Borrowed(element)
        }
    }

    /// Returns a reference to the element associated to the given `key`,
    /// or `None` if the key is unused.
    pub(crate) fn get(&self, key: K) -> Option<&T> {
        self.vec
            .get(key.value())
            .filter(|palette_entry| 0 < palette_entry.count)
            .map(|palette_entry| {
                // SAFETY: The entry's `count` is non zero so the element is initialized.
                unsafe { palette_entry.element.assume_init_ref() }
            })
    }

    /// Returns the number of instances of the given element.
    ///
    /// This operation is *O*(*len*).
    pub(crate) fn number_of_instances(&self, element: &impl ViewToOwned<T>) -> usize {
        self.get_palette_entry_and_key_value(element)
            .map(|(_key_value, palette_entry)| {
                debug_assert!(0 < palette_entry.count);
                palette_entry.count
            })
            .unwrap_or(0)
    }

    /// Returns the key associated with the given element.
    ///
    /// This operation is *O*(*len*).
    pub(crate) fn key_of_element(&self, element: &impl ViewToOwned<T>) -> Option<K> {
        self.get_palette_entry_and_key_value(element)
            .map(|(key_value, palette_entry)| {
                debug_assert!(0 < palette_entry.count);
                K::with_value(key_value)
            })
    }

    /// Returns `true` if the palette contains the given element.
    ///
    /// This operation is *O*(*len*).
    pub(crate) fn contains(&self, element: &impl ViewToOwned<T>) -> bool {
        self.get_palette_entry_and_key_value(element).is_some()
    }

    /// Returns an iterator over the keys currently used by the palette.
    fn _used_keys(&self) -> impl Iterator<Item = K> + '_ {
        self.vec
            .iter()
            .enumerate()
            .filter_map(|(key_value, palette_entry)| {
                (0 < palette_entry.count).then_some(K::with_value(key_value))
            })
    }

    pub(crate) fn iter_elements(&self) -> impl Iterator<Item = &T> {
        self.vec.iter().filter_map(|palette_entry| {
            (0 < palette_entry.count).then_some({
                // SAFETY: The entry's `count` is non zero so the element is initialized.
                unsafe { palette_entry.element.assume_init_ref() }
            })
        })
    }

    pub(crate) fn iter_elements_and_keys(&self) -> impl Iterator<Item = (K, &T)> {
        self.vec
            .iter()
            .enumerate()
            .filter_map(|(key_value, palette_entry)| {
                (0 < palette_entry.count).then_some({
                    // SAFETY: The entry's `count` is non zero so the element is initialized.
                    let element = unsafe { palette_entry.element.assume_init_ref() };
                    let key = K::with_value(key_value);
                    (key, element)
                })
            })
    }

    pub(crate) fn counts_and_keys(&self, sorting: CountAndKeySorting) -> Vec<CountAndKey<K>> {
        let mut counts_and_keys: Vec<_> = self
            .vec
            .iter()
            .enumerate()
            .filter_map(|(key_value, palette_entry)| {
                (0 < palette_entry.count).then_some(CountAndKey {
                    count: palette_entry.count,
                    key: K::with_value(key_value),
                })
            })
            .collect();
        match sorting {
            CountAndKeySorting::KeySmallestFirst => {
                // It is already sorted that way.
            }
            CountAndKeySorting::CountSmallestFirst => {
                counts_and_keys.sort_by(|left, right| left.count.cmp(&right.count));
            }
            CountAndKeySorting::CountBiggestFirst => {
                counts_and_keys.sort_by(|left, right| right.count.cmp(&left.count));
            }
        }
        counts_and_keys
    }

    pub(crate) fn highest_used_key(&self) -> Option<K> {
        self.vec
            .iter()
            .enumerate()
            .rev()
            .find_map(|(key_value, palette_entry)| {
                (0 < palette_entry.count).then_some(K::with_value(key_value))
            })
    }

    pub(crate) fn remove_entry(&mut self, key: K) -> Option<PaletteEntry<T>> {
        Some(std::mem::take(self.vec.get_mut(key.value())?))
    }

    pub(crate) fn add_entry(
        &mut self,
        palette_entry: PaletteEntry<T>,
        key_allocator: &mut impl PaletteKeyAllocator<K>,
    ) -> K {
        let key = self.allocate_smallest_available_key(key_allocator);
        // Making sure that `vec.len()` is at least `key + 1`.
        if self.vec.len() <= key.value() {
            self.vec.resize_with(key.value() + 1, PaletteEntry::default);
        }
        let palette_entry_to_overwrite = {
            // SAFETY: We just made sure that `vec.len()` is at least `key + 1`,
            // so we cannot be out-of-bounds here.
            unsafe { self.vec.get_mut(key.value()).unwrap_unchecked() }
        };
        *palette_entry_to_overwrite = palette_entry;
        key
    }
}

pub(crate) struct CountAndKey<K>
where
    K: PaletteKeyType,
{
    pub(crate) count: usize,
    pub(crate) key: K,
}

#[allow(clippy::enum_variant_names)]
pub(crate) enum CountAndKeySorting {
    KeySmallestFirst,
    CountSmallestFirst,
    CountBiggestFirst,
}

impl<T, K> Debug for Palette<T, K>
where
    T: Clone + Eq + Debug,
    K: PaletteKeyType,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_map = f.debug_map();
        for (key_value, palette_entry) in self.vec.iter().enumerate() {
            if 0 < palette_entry.count {
                // SAFETY: The entry's `count` is non zero so the element is initialized.
                let element = unsafe { palette_entry.element.assume_init_ref() };
                debug_map.entry(&key_value, element);
            }
        }
        debug_map.finish()
    }
}
