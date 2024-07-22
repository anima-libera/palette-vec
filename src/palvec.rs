use std::collections::{hash_map::Entry, HashMap};

use crate::key::{key_min_size, Key};
use crate::key_alloc::KeyAllocator;
use crate::key_vec::KeyVec;
use crate::utils::{borrowed_or_owned::BorrowedOrOwned, view_to_owned::ViewToOwned};
use fxhash::FxHashMap;

// TODO: Better doc!
pub struct PalVec<E>
where
    E: Clone + Eq,
{
    /// Each element in the `PalVec`'s array is represented by a key here,
    /// that maps to the element's value via the palette.
    /// All the keys contained here are valid `palette` keys, thus not unused (see `unused_keys`).
    key_vec: KeyVec,
    /// Each key in `key_vec` is a key into this table to refer to the element it represents.
    /// Accessing index `i` of the `PalVec` array will really access `palette[key_vec[i]]`.
    ///
    /// A key that is not present in the palette is considered unused and tracked by `unused_keys`.
    // TODO: Better optimize the palette type thing!
    palette: FxHashMap<Key, PaletteEntry<E>>,
    /// This is used to keep track of all the unused keys so that when we want to allocate a new
    /// key to use then we can just get its smallest member, and when we no longer use a key we
    /// can deallocate it and return it to the set it represents.
    key_allocator: KeyAllocator,
}

struct PaletteEntry<E> {
    count: usize,
    element: E,
}

impl<E> PalVec<E>
where
    E: Clone + Eq,
{
    /// Creates an empty `PalVec`.
    ///
    /// Does not allocate now,
    /// allocations are done when content is added to it or it is told to reserve memory.
    pub fn new() -> Self {
        Self {
            key_vec: KeyVec::new(),
            palette: HashMap::default(),
            key_allocator: KeyAllocator::new(),
        }
    }

    /// Creates a `PalVec` filled with the given `element` and that has length `len`.
    ///
    /// Leveraging a memory usage optimization available when there is only one
    /// element in the palette, this call is cheap no matter how big `len` is.
    pub fn with_len(element: E, len: usize) -> Self {
        if len == 0 {
            Self::new()
        } else {
            Self {
                key_vec: KeyVec::with_len(len),
                palette: {
                    let mut palette = HashMap::default();
                    palette.insert(
                        0,
                        PaletteEntry {
                            count: len,
                            element,
                        },
                    );
                    palette
                },
                key_allocator: KeyAllocator::with_zero_already_allocated(),
            }
        }
    }

    /// Returns the number of elements in the `PalVec`'s array.
    pub fn len(&self) -> usize {
        self.key_vec.len()
    }

    /// Returns the number of elements in the palette,
    /// which is the number of *different* elements in the `PalVec`'s array.
    pub fn palette_len(&self) -> usize {
        self.palette.len()
    }

    /// Returns `true` if the `PalVec` array contains no elements.
    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
    }

    /// Allocates the smallest unused key value.
    ///
    /// It is quarenteed that it will fit in `keys_size` bits,
    /// by properly increasing `keys_size` if necessary.
    fn allocate_new_key_and_make_it_fit(&mut self) -> Key {
        let new_key = self.key_allocator.allocate();
        let min_size = key_min_size(new_key);
        let does_it_already_fit = min_size <= self.key_vec.keys_size();
        if does_it_already_fit {
            // It already fits, nothing to do.
        } else {
            // Properly making `keys_size` bigger so that the new key fits.
            self.key_vec.change_keys_size(min_size);
        }
        new_key
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and returns the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette and key allocator.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    fn add_element_instances_to_palette(
        &mut self,
        element: impl ViewToOwned<E>,
        that_many: usize,
    ) -> Key {
        let already_in_palette = self
            .palette
            .iter_mut()
            .find(|(_key, palette_entry)| element.eq(&palette_entry.element));
        if let Some((&key, entry)) = already_in_palette {
            entry.count = entry
                .count
                .checked_add(that_many)
                .expect("Palette entry count overflow (max is usize::MAX)");
            key
        } else {
            let key = self.allocate_new_key_and_make_it_fit();
            self.palette.insert(
                key,
                PaletteEntry {
                    count: that_many,
                    element: element.into_owned(),
                },
            );
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
    fn remove_element_instances_from_palette(
        &mut self,
        key: Key,
        that_many: usize,
    ) -> BorrowedOrOwned<'_, E> {
        let map_entry = self.palette.entry(key);
        let Entry::Occupied(mut occupied_entry) = map_entry else {
            panic!("Bug: Removing element instances by a key that is unused");
        };
        let palette_entry = occupied_entry.get_mut();
        palette_entry.count = palette_entry
            .count
            .checked_sub(that_many)
            .expect("Bug: Removing more element instances from palette than its count");
        let count = palette_entry.count;
        if count == 0 {
            let entry_removed = occupied_entry.remove();
            self.key_allocator.deallocate(key);
            BorrowedOrOwned::Owned(entry_removed.element)
        } else {
            BorrowedOrOwned::Borrowed(&occupied_entry.into_mut().element)
        }
    }

    fn get_element_from_used_key(&self, key: Key) -> Option<&E> {
        self.palette.get(&key).map(|entry| &entry.element)
    }

    /// Returns a reference to the `PalVec`'s array element at the given `index`.
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&self, index: usize) -> Option<&E> {
        let key = self.key_vec.get(index)?;
        let element = self
            .get_element_from_used_key(key)
            .expect("Bug: Key used in `key_vec` is not used by the palette");
        Some(element)
    }

    /// Sets the `PalVec`'s array element at the given `index` to the given `element`.
    ///
    /// Subsequent calls to `get` with that `index` will return `element`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub fn set(&mut self, index: usize, element: impl ViewToOwned<E>) {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            // Style of panic message inspired form the one in
            // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
            panic!("set index (is {index}) should be < len (is {})", self.len());
        }

        let key_of_elemement_to_remove = {
            if self.key_vec.keys_size() == 0 {
                0
            } else {
                // SAFETY: We checked the bounds, we have `index < self.len()`.
                unsafe { self.key_vec.get_unchecked(index) }
            }
        };
        self.remove_element_instances_from_palette(key_of_elemement_to_remove, 1);
        let key_of_element_to_add = self.add_element_instances_to_palette(element, 1);
        if self.key_vec.keys_size() == 0 {
            // Nothing to do here, all the keys have the same value of zero.
            debug_assert_eq!(key_of_element_to_add, 0);
        } else {
            // SAFETY: We checked the bounds, we have `index < self.len()`.
            unsafe { self.key_vec.set_unchecked(index, key_of_element_to_add) }
        }
    }

    /// Appends the given `element` to the back of the `PalVec`'s array.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub fn push(&mut self, element: impl ViewToOwned<E>) {
        let key = self.add_element_instances_to_palette(element, 1);
        self.key_vec.push(key);
    }

    /// Removes the last element from the `PalVec`'s array and returns it,
    /// or `None` if it is empty.
    ///
    /// If the popped element was the last of its instances,
    /// then it is removed from the palette and returned in a [`BorrowedOrOwned::Owned`].
    /// Else, it is borrowed from the palette and returned in a [`BorrowedOrOwned::Borrowed`].
    pub fn pop(&mut self) -> Option<BorrowedOrOwned<'_, E>> {
        self.key_vec
            .pop()
            .map(|key| self.remove_element_instances_from_palette(key, 1))
    }
}

impl<E> Default for PalVec<E>
where
    E: Clone + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::borrowed_or_owned::{
        OptionBorrowedOrOwnedAsRef, OptionBorrowedOrOwnedCopied,
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
        let mut palvec = PalVec::with_len(String::from(funi), epic_len);
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
        let mut palvec = PalVec::with_len((), Key::MAX);
        palvec.push(());
    }

    #[test]
    fn push_adds_to_palette() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert!(palvec.palette.values().any(|v| v.element == 8));
        assert!(palvec.palette.values().any(|v| v.element == 5));
    }

    #[test]
    fn pop_removes_from_palette() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(8);
        palvec.push(5);
        palvec.pop();
        palvec.pop();
        assert!(!palvec.palette.values().any(|v| v.element == 8));
        assert!(!palvec.palette.values().any(|v| v.element == 5));
    }
}
