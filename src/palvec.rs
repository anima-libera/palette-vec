use std::marker::PhantomData;
use std::num::NonZeroUsize;

use crate::key_alloc::{KeyAllocator, KeyAllocatorZst};
use crate::key_vec::KeyVec;
use crate::palette::{Palette, PaletteVecOrMap};
use crate::utils::{borrowed_or_owned::BorrowedOrOwned, view_to_owned::ViewToOwned};

// TODO: Better doc!
pub struct PalVec<T, P = PaletteVecOrMap<T>, A: KeyAllocator = KeyAllocatorZst>
where
    T: Clone + Eq,
    P: Palette<T>,
    A: KeyAllocator,
{
    /// Each element in the `PalVec`'s array is represented by a key here,
    /// that maps to the element's value via the palette.
    /// All the keys contained here are valid `palette` keys, thus not unused (see `unused_keys`).
    key_vec: KeyVec,
    /// Each key in `key_vec` is a key into this table to refer to the element it represents.
    /// Accessing index `i` of the `PalVec` array will really access `palette[key_vec[i]]`.
    ///
    /// A key that is not present in the palette is considered unused and tracked by `unused_keys`.
    palette: P,
    /// The palette holds owned `T`s,
    /// also `T` has to be used in a field.
    _phantom: PhantomData<T>,
    /// This is used to keep track of all the unused keys so that when we want to allocate a new
    /// key to use then we can just get its smallest member, and when we no longer use a key we
    /// can deallocate it and return it to the set it represents.
    key_allocator: A,
}

impl<T, P, A> PalVec<T, P, A>
where
    T: Clone + Eq,
    P: Palette<T>,
    A: KeyAllocator,
{
    /// Creates an empty `PalVec`.
    ///
    /// Does not allocate now,
    /// allocations are done when content is added to it or it is told to reserve memory.
    pub fn new() -> Self {
        Self {
            key_vec: KeyVec::new(),
            palette: P::new(),
            _phantom: PhantomData,
            key_allocator: A::new(),
        }
    }

    /// Creates a `PalVec` filled with the given `element` and that has length `len`.
    ///
    /// Leveraging a memory usage optimization available when there is only one
    /// element in the palette, this call is cheap no matter how big `len` is.
    pub fn with_len(element: T, len: usize) -> Self {
        if len == 0 {
            Self::new()
        } else {
            // `KeyVec::with_len` is filled with `0`s, and
            // `Palette::with_one_entry` associates the given entry to the key `0`,
            // so it matches.
            Self {
                key_vec: KeyVec::with_len(len),
                palette: P::with_one_entry(element, len),
                _phantom: PhantomData,
                key_allocator: A::with_zero_already_allocated(),
            }
        }
    }

    /// Returns the number of elements in the `PalVec`'s array.
    pub fn len(&self) -> usize {
        self.key_vec.len()
    }

    /// Returns `true` if the `PalVec` array contains no elements.
    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
    }

    /// Returns a reference to the `PalVec`'s array element at the given `index`.
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&self, index: usize) -> Option<&T> {
        let key = self.key_vec.get(index)?;
        let element = self
            .palette
            .get(key)
            .expect("Bug: Key used in `key_vec` is not used by the palette");
        Some(element)
    }

    /// Sets the `PalVec`'s array element at the given `index` to the given `element`.
    /// Subsequent calls to `get` with that `index` will return `element`.
    ///
    /// This operation is *O*(1) if the `keys_size` doesn't increase,
    /// but if it does increase (which happens rarely) then it is *O*(*len*).
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub fn set(&mut self, index: usize, element: impl ViewToOwned<T>) {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            // Style of panic message inspired form the one in
            // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
            panic!("set index (is {index}) should be < len (is {})", self.len());
        }

        // TODO: Optimize the case where the new element is the same as the one it replaces, maybe?

        // We just replace the element at `index` by the given element.
        //
        // The removed element is removed from the palette before the new element is added to it.
        // This may allow the key allocator to spare using bigger keys that may require a resizing
        // of `keys_size` to fit in the case where the removed element was the last instance of it
        // and the new element had no instance yet (which allows the key allocator to reuse the key
        // of the removed element for the new one).
        let key_of_elemement_to_remove = {
            if self.key_vec.keys_size() == 0 {
                0
            } else {
                // SAFETY: We checked the bounds, we have `index < self.len()`.
                unsafe { self.key_vec.get_unchecked(index) }
            }
        };
        self.palette.remove_element_instances(
            key_of_elemement_to_remove,
            {
                // SAFETY: 1 is not 0.
                unsafe { NonZeroUsize::new_unchecked(1) }
            },
            &mut self.key_allocator,
        );
        let key_of_element_to_add = self.palette.add_element_instances(
            element,
            {
                // SAFETY: 1 is not 0.
                unsafe { NonZeroUsize::new_unchecked(1) }
            },
            &mut self.key_allocator,
            &mut self.key_vec,
        );
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
        let key = self.palette.add_element_instances(
            element,
            {
                // SAFETY: 1 is not 0.
                unsafe { NonZeroUsize::new_unchecked(1) }
            },
            &mut self.key_allocator,
            &mut self.key_vec,
        );
        self.key_vec.push(key);
    }

    /// Removes the last element from the `PalVec`'s array and returns it,
    /// or `None` if it is empty.
    ///
    /// If the popped element was the last of its instances,
    /// then it is removed from the palette and returned in a [`BorrowedOrOwned::Owned`].
    /// Else, it is borrowed from the palette and returned in a [`BorrowedOrOwned::Borrowed`].
    pub fn pop(&mut self) -> Option<BorrowedOrOwned<'_, T>> {
        self.key_vec.pop().map(|key| {
            self.palette.remove_element_instances(
                key,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut self.key_allocator,
            )
        })
    }

    /// Returns the number of elements in the palette,
    /// which is the number of *different* elements in the `PalVec`'s array.
    pub fn palette_len(&self) -> usize {
        self.palette.len()
    }

    /// Returns `true` if the palette contains the given element.
    ///
    /// This operation is *O*(*palette_len*).
    pub fn palette_contains(&self, element: impl ViewToOwned<T>) -> bool {
        self.palette.contains(element)
    }
}

impl<T, P> Default for PalVec<T, P>
where
    T: Clone + Eq,
    P: Palette<T>,
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
        let palvec: PalVec<()> = PalVec::new();
        assert!(palvec.is_empty());
        assert_eq!(palvec.len(), 0);
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
    fn push_and_len() {
        let mut palvec: PalVec<()> = PalVec::new();
        assert_eq!(palvec.len(), 0);
        palvec.push(());
        assert_eq!(palvec.len(), 1);
        palvec.push(());
        assert_eq!(palvec.len(), 2);
    }

    #[test]
    fn push_and_get() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(42);
        assert_eq!(palvec.get(0), Some(&42));
    }

    #[test]
    fn get_out_of_bounds_is_none() {
        let mut palvec: PalVec<()> = PalVec::new();
        assert!(palvec.get(0).is_none());
        palvec.push(());
        palvec.push(());
        assert!(palvec.get(0).is_some());
        assert!(palvec.get(1).is_some());
        assert!(palvec.get(2).is_none());
    }

    #[test]
    fn pop_empty() {
        let mut palvec: PalVec<()> = PalVec::new();
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn push_and_pop_strings() {
        let mut palvec: PalVec<String> = PalVec::new();
        palvec.push("uwu");
        palvec.push(String::from("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("uwu"));
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn push_and_pop_numbers() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert_eq!(palvec.pop().map_copied(), Some(5));
        assert_eq!(palvec.pop().map_copied(), Some(8));
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn set_and_get() {
        let mut palvec: PalVec<i32> = PalVec::new();
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
        let mut palvec: PalVec<()> = PalVec::new();
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
        let mut palvec: PalVec<String> = PalVec::with_len(String::from(funi), epic_len);
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
        let mut palvec: PalVec<()> = PalVec::with_len((), Key::MAX);
        palvec.push(());
    }

    #[test]
    fn push_adds_to_palette() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert!(palvec.palette.contains(8));
        assert!(palvec.palette.contains(5));
    }

    #[test]
    fn pop_removes_from_palette() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(8);
        palvec.push(5);
        palvec.pop();
        palvec.pop();
        assert!(!palvec.palette.contains(8));
        assert!(!palvec.palette.contains(5));
    }

    #[test]
    fn many_palette_entries() {
        let mut palvec: PalVec<i32> = PalVec::new();
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
        let mut palvec: PalVec<i32> = PalVec::new();
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
}
