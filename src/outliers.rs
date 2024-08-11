use std::collections::HashMap;
use std::marker::PhantomData;
use std::num::NonZeroUsize;

use fxhash::FxHashMap;

use crate::key::Key;
use crate::key_alloc::{KeyAllocator, KeyAllocatorZst};
use crate::key_vec::KeyVec;
use crate::palette::{Palette, PaletteAsKeyAllocator, PaletteVecOrMap};
use crate::utils::{borrowed_or_owned::BorrowedOrOwned, view_to_owned::ViewToOwned};

// TODO: Better doc!
pub struct OutPalVec<T, P = PaletteVecOrMap<T>, A: KeyAllocator = KeyAllocatorZst>
where
    T: Clone + Eq,
    P: Palette<T> + PaletteAsKeyAllocator,
    A: KeyAllocator,
{
    key_vec: KeyVec,
    common_palette: P,
    outlier_palette: P,
    outlier_key: Option<Key>,
    index_to_outlier_side_key: FxHashMap<usize, Key>,
    common_key_allocator: A,
    outlier_key_allocator: A,
    /// The palettes hold owned `T`s, also `T` has to be used in a field.
    _phantom: PhantomData<T>,
}

impl<T, P, A> OutPalVec<T, P, A>
where
    T: Clone + Eq,
    P: Palette<T> + PaletteAsKeyAllocator,
    A: KeyAllocator,
{
    pub fn new() -> Self {
        Self {
            key_vec: KeyVec::new(),
            common_palette: P::new(),
            outlier_palette: P::new(),
            outlier_key: None,
            index_to_outlier_side_key: HashMap::default(),
            common_key_allocator: A::new(),
            outlier_key_allocator: A::new(),
            _phantom: PhantomData,
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
                common_palette: P::with_one_entry(element, len),
                outlier_palette: P::new(),
                outlier_key: None,
                index_to_outlier_side_key: HashMap::default(),
                common_key_allocator: A::with_zero_already_allocated(),
                outlier_key_allocator: A::new(),
                _phantom: PhantomData,
            }
        }
    }

    /// Returns the number of elements in the `OutPalVec`'s array.
    pub fn len(&self) -> usize {
        self.key_vec.len()
    }

    /// Returns `true` if the `OutPalVec` array contains no elements.
    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
    }

    /// Returns a reference to the `OutPalVec`'s array element at the given `index`.
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&self, index: usize) -> Option<&T> {
        let key = self.key_vec.get(index)?;
        Some(if self.outlier_key == Some(key) {
            let key_for_outlier_palette = *self
                .index_to_outlier_side_key
                .get(&index)
                .expect("Bug: Outlier key in `key_vec` but the index is not in index map");
            self.outlier_palette
                .get(key_for_outlier_palette)
                .expect("Bug: Key used in index map is not used by the outlier palette")
        } else {
            self.common_palette
                .get(key)
                .expect("Bug: Key used in `key_vec` is not used by the common palette")
        })
    }

    /// Sets the `PalVec`'s array element at the given `index` to the given `element`.
    /// Subsequent calls to `get` with that `index` will return `element`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub fn set(&mut self, index: usize, element: impl ViewToOwned<T>) {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            panic!("set index (is {index}) should be < len (is {})", self.len());
        }

        // TODO: Optimize case where an outlier is replaced by an outlier,
        // the `index_to_outlier_side_key` is currently accessed twice at the same index
        // but should be accessed once.

        // Removing the replaced element.
        let key_of_elemement_to_remove = {
            if self.key_vec.keys_size() == 0 {
                0
            } else {
                // SAFETY: We checked the bounds, we have `index < self.len()`.
                unsafe { self.key_vec.get_unchecked(index) }
            }
        };
        if self.outlier_key == Some(key_of_elemement_to_remove) {
            let key_for_outlier_palette = self
                .index_to_outlier_side_key
                .remove(&index)
                .expect("Bug: Outlier key in `key_vec` but the index is not in index map");
            self.outlier_palette.remove_element_instances(
                key_for_outlier_palette,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut self.outlier_key_allocator,
            );
            // TODO: Maybe there are no more outlier.
        } else {
            self.common_palette.remove_element_instances(
                key_of_elemement_to_remove,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut self.common_key_allocator,
            );
        }

        // Adding the new element.
        let key_of_element_to_add = if self.common_palette.contains(&element) {
            // Already a common element.
            self.common_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut self.common_key_allocator,
                Some(&mut self.key_vec),
                self.outlier_key,
            )
        } else {
            // Either already an outlier or a new outlier.

            // TODO: Keep outlier proportion regulated.

            let outlier_side_key = self.outlier_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut self.outlier_key_allocator,
                None,
                None,
            );
            let previous = self
                .index_to_outlier_side_key
                .insert(index, outlier_side_key);
            debug_assert!(previous.is_none(), "Bug: Index map slot is occupied");
            if self.outlier_key.is_none() {
                let outlier_key = self
                    .common_key_allocator
                    .allocate(&self.common_palette, None);
                self.key_vec.make_sure_a_key_fits(outlier_key);
                self.outlier_key = Some(outlier_key);
            }
            self.outlier_key.unwrap()
        };
        if self.key_vec.keys_size() == 0 {
            // Nothing to do here, all the keys have the same value of zero.
            debug_assert_eq!(key_of_element_to_add, 0);
        } else {
            // SAFETY: We checked the bounds, we have `index < self.len()`,
            // and `add_element_instances` made sure that the key fits.
            unsafe { self.key_vec.set_unchecked(index, key_of_element_to_add) }
        }
    }

    /// Appends the given `element` to the back of the `PalVec`'s array.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub fn push(&mut self, element: impl ViewToOwned<T>) {
        todo!()
    }

    /// Removes the last element from the `PalVec`'s array and returns it,
    /// or `None` if it is empty.
    ///
    /// If the popped element was the last of its instances,
    /// then it is removed from the palette and returned in a [`BorrowedOrOwned::Owned`].
    /// Else, it is borrowed from the palette and returned in a [`BorrowedOrOwned::Borrowed`].
    pub fn pop(&mut self) -> Option<BorrowedOrOwned<'_, T>> {
        todo!()
    }

    /// Returns the number of elements in the palette,
    /// which is the number of *different* elements in the `PalVec`'s array.
    pub fn palette_len(&self) -> usize {
        todo!()
    }

    /// Returns `true` if the palette contains the given element.
    pub fn palette_contains(&self, element: impl ViewToOwned<T>) -> bool {
        todo!()
    }
}

impl<T, P> Default for OutPalVec<T, P>
where
    T: Clone + Eq,
    P: Palette<T> + PaletteAsKeyAllocator,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::{
        key::{key_min_size, Key},
        utils::borrowed_or_owned::{OptionBorrowedOrOwnedAsRef, OptionBorrowedOrOwnedCopied},
    };

    use super::*;

    #[test]
    fn new_is_empty() {
        let outpalvec: OutPalVec<()> = OutPalVec::new();
        assert!(outpalvec.is_empty());
        assert_eq!(outpalvec.len(), 0);
    }

    #[test]
    fn key_min_size_values() {
        assert_eq!(key_min_size(0), 0);
        assert_eq!(key_min_size(1), 1);
        assert_eq!(key_min_size(2), 2);
        assert_eq!(key_min_size(3), 2);
        assert_eq!(key_min_size(4), 3);
    }

    #[test]
    fn with_len() {
        let outpalvec: OutPalVec<()> = OutPalVec::with_len((), 30);
        assert_eq!(outpalvec.len(), 30);
    }

    #[test]
    fn set_and_get() {
        let mut outpalvec: OutPalVec<i32> = OutPalVec::with_len(42, 30);
        for i in 0..30 {
            assert_eq!(outpalvec.get(i), Some(&42));
        }
        outpalvec.set(6, 69);
        outpalvec.set(9, 69);
        assert_eq!(outpalvec.get(0), Some(&42));
        assert_eq!(outpalvec.get(6), Some(&69));
        assert_eq!(outpalvec.get(7), Some(&42));
        assert_eq!(outpalvec.get(9), Some(&69));
        assert_eq!(outpalvec.get(29), Some(&42));
    }

    /*
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
        assert_eq!(palvec.get(0), Some(&42));
    }

    #[test]
    fn get_out_of_bounds_is_none() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert!(palvec.get(0).is_none());
        palvec.push(());
        palvec.push(());
        assert!(palvec.get(0).is_some());
        assert!(palvec.get(1).is_some());
        assert!(palvec.get(2).is_none());
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
    fn set_and_get() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        palvec.set(0, 0);
        palvec.set(1, 1);
        assert_eq!(palvec.get(0), Some(&0));
        assert_eq!(palvec.get(1), Some(&1));
    }

    #[test]
    #[should_panic]
    fn set_out_of_bounds_panic() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        palvec.push(());
        palvec.push(());
        palvec.set(2, ());
    }

    #[test]
    fn with_len() {
        // Vector length of epic proportions,
        // remains cheap as long as there is only one entry in the palette.
        let epic_len = Key::MAX;
        let funi = "nyaa :3 mrrrrp mreow";
        let mut palvec: OutPalVec<String> = OutPalVec::with_len(String::from(funi), epic_len);
        assert_eq!(palvec.len(), epic_len);
        assert_eq!(palvec.get(0).map(|s| s.as_str()), Some(funi));
        assert_eq!(palvec.get(epic_len - 1).map(|s| s.as_str()), Some(funi));
        assert_eq!(palvec.get(epic_len / 2).map(|s| s.as_str()), Some(funi));
        assert_eq!(palvec.pop().map_as_ref().map(|s| s.as_str()), Some(funi));
        assert_eq!(palvec.len(), epic_len - 1);
        palvec.set(epic_len / 2, funi);
        assert_eq!(palvec.get(epic_len / 2).map(|s| s.as_str()), Some(funi));
        palvec.push(funi);
        assert_eq!(palvec.len(), epic_len);
    }

    #[test]
    #[should_panic]
    fn entry_count_too_big() {
        let mut palvec: OutPalVec<()> = OutPalVec::with_len((), Key::MAX);
        palvec.push(());
    }

    #[test]
    fn push_adds_to_palette() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert!(palvec.palette.contains(8));
        assert!(palvec.palette.contains(5));
    }

    #[test]
    fn pop_removes_from_palette() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        palvec.pop();
        palvec.pop();
        assert!(!palvec.palette.contains(8));
        assert!(!palvec.palette.contains(5));
    }

    #[test]
    fn many_palette_entries() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        for i in 0..50 {
            palvec.push(i);
        }
        for i in (0..50).rev() {
            dbg!(i);
            assert!(palvec.palette.contains(i));
            assert_eq!(palvec.pop().map_copied(), Some(i));
            assert!(!palvec.palette.contains(i));
        }
    }

    #[test]
    fn entry_count_up_and_down_many_times() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        for i in 2..50 {
            for j in 0..i {
                palvec.push(j);
            }
            for j in (0..i).rev() {
                dbg!(palvec.len());
                assert!(palvec.palette.contains(j));
                assert_eq!(palvec.pop().map_copied(), Some(j));
                assert!(!palvec.palette.contains(j));
            }
        }
    }
    */
}
