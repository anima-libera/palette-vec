use std::{
    collections::{hash_map::Entry, HashMap},
    num::NonZeroUsize,
};

use fxhash::FxHashMap;
use key_allocator::KeyAllocator;
use key_vec::KeyVec;

type Key = u32;

mod key_vec {
    use std::{cmp::Ordering, num::NonZeroUsize, ops::Range};

    use bitvec::{field::BitField, order::Lsb0, slice::BitSlice, vec::BitVec, view::BitViewSized};

    use crate::Key;

    /// An array of keys, each being represented with [`Self::keys_size()`] bits exactly,
    /// without padding between keys (so they are probably not byte-aligned).
    pub(crate) struct KeyVec {
        /// The array of keys, keys are alligned on `keys_size` bits.
        /// The key at index `i` occupies the bit range `Self::key_bit_range(self.keys_size, i)`.
        ///
        /// The number of live bits in the `BitVec` is always a multiple of `keys_size`.
        vec: BitVec<usize, Lsb0>,
        /// The size in bits of the memory representation of each key in `vec`.
        keys_size: NonZeroUsize,
    }

    impl KeyVec {
        /// Creates an empty `KeyVec`.
        ///
        /// Does not allocate now,
        /// allocations are done when keys are added to it or it is told to reserve memory.
        pub(crate) fn new() -> Self {
            Self {
                vec: BitVec::new(),
                keys_size: {
                    // SAFETY: 1 is not 0
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
            }
        }

        /// The size in bits of the representation of each key in the `KeyVec`.
        #[inline]
        pub(crate) fn keys_size(&self) -> NonZeroUsize {
            self.keys_size
        }

        /// Returns the number of keys in the `KeyVec`.
        #[inline]
        pub(crate) fn len(&self) -> usize {
            self.vec.len() / self.keys_size
        }

        /// Returns `true` if the `KeyVec` contains no key.
        #[inline]
        pub(crate) fn is_empty(&self) -> bool {
            self.vec.is_empty()
        }

        /// Returns the range of bits in the `KeyVec`'s `BitVec`
        /// that holds the representation of its `index`-th key.
        ///
        /// Assumes a large enough `KeyVec`.
        fn key_bit_range(keys_size: NonZeroUsize, index: usize) -> Range<usize> {
            let index_inf = index * keys_size.get();
            let index_sup_excluded = index_inf + keys_size.get();
            index_inf..index_sup_excluded
        }

        /// Returns the key at the given `index`, or None if out of bounds.
        pub(crate) fn get(&self, index: usize) -> Option<Key> {
            if index < self.len() {
                Some({
                    // SAFETY: We just checked the bounds, `index < self.len()`.
                    unsafe { self.get_unchecked(index) }
                })
            } else {
                None
            }
        }

        /// Overwrites the key at the given `index` with the given `key`.
        ///
        /// # Panics
        ///
        /// Panics if `index` is out of bounds.
        pub(crate) fn _set(&mut self, index: usize, key: Key) {
            if index < self.len() {
                // SAFETY: We just checked the bounds, `index < self.len()`.
                unsafe {
                    self.set_unchecked(index, key);
                }
            } else {
                // Style of panic message inspired form the one in
                // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
                panic!(
                    "set index (is {index}) should be < len (len is {})",
                    self.len()
                );
            }
        }

        /// Returns the key at the given index in the array of keys.
        ///
        /// # Safety
        ///
        /// The `index` must be `< self.len()`.
        pub(crate) unsafe fn get_unchecked(&self, index: usize) -> Key {
            let bit_range = Self::key_bit_range(self.keys_size, index);
            debug_assert!(bit_range.end <= self.vec.len());
            self.vec[bit_range].load()
        }

        /// Sets the key at the given index to the given `key`.
        ///
        /// # Safety
        ///
        /// The `index` must be `< self.len()`.
        pub(crate) unsafe fn set_unchecked(&mut self, index: usize, key: Key) {
            let bit_range = Self::key_bit_range(self.keys_size, index);
            debug_assert!(bit_range.end <= self.vec.len());
            self.vec[bit_range].store(key);
        }

        pub(crate) fn push(&mut self, key: Key) {
            let key_le = (key as usize).to_le();
            let key_bits = key_le.as_raw_slice();
            let key_bits: &BitSlice<usize, Lsb0> = BitSlice::from_slice(key_bits);
            let key_bits = &key_bits[0..self.keys_size.get()];
            self.vec.extend_from_bitslice(key_bits);
        }

        pub(crate) fn pop(&mut self) -> Option<Key> {
            if self.is_empty() {
                None
            } else {
                let len = self.len();
                let last_key = {
                    // SAFETY: `len-1 < len`, and `0 < len` (we are not empty) so `0 <= len-1`.
                    unsafe { self.get_unchecked(len - 1) }
                };
                self.vec.truncate(len - self.keys_size.get());
                Some(last_key)
            }
        }

        /// Reserves capacity for at least `additional` more keys,
        /// with an effort to allocate the minimum sufficient amount of memory.
        #[inline]
        fn _reserve_exact(&mut self, additional: usize) {
            self.vec.reserve_exact(additional * self.keys_size.get());
        }

        /// Reserves capacity for at least `additional` more keys.
        #[inline]
        fn _reserve(&mut self, additional: usize) {
            self.vec.reserve(additional * self.keys_size.get());
        }

        /// Adapts the representation of the contained keys so that now
        /// every key is represented on `new_keys_size` bits.
        /// The value of the keys doesn't change, the content is still the same,
        /// except it will now work with a bigger `keys_size` to accomodate for
        /// more possible key values.
        pub(crate) fn change_keys_size(&mut self, new_keys_size: NonZeroUsize) {
            match self.keys_size.get().cmp(&new_keys_size.get()) {
                Ordering::Equal => {}
                Ordering::Less => {
                    // The `keys_size` has to increase.
                    let old_keys_size = self.keys_size;
                    let len = self.len();
                    // Here we break some `KeyVec` invariants.
                    // We first resize the `vec` to get enough room to make all its keys bigger.
                    self.vec.resize(len * new_keys_size.get(), false);
                    // Now we have free space at the end of `vec`,
                    // and all the keys with their old size packed at the beginning
                    // (each key being at its old position).
                    // We move from the last key to the first, taking a key from its
                    // old position and putting it at its new position (the position it would
                    // have if `keys_size` was `new_keys_size`) and extending it so that its
                    // representation takes `new_keys_size` bits.
                    // The growing reigion of `≈i` newly resized keys at the end
                    // and the shrinking reigion of `≈len-i` yet-to-be-resized keys at the start
                    // never overlap because we resized the vec to accomodate for the
                    // biggest size of the reigion with bigger keys.
                    for i in (0..len).rev() {
                        // Get the last not-yet moved key from its old position.
                        let key: Key = {
                            let bit_range = Self::key_bit_range(old_keys_size, i);
                            self.vec[bit_range].load()
                        };
                        // Move the key to its new position, and represent it with the new key size.
                        {
                            let bit_range = Self::key_bit_range(new_keys_size, i);
                            self.vec[bit_range].store(key);
                        }
                    }
                    self.keys_size = new_keys_size;
                }
                Ordering::Greater => todo!("`keys_size` has to decrease"),
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn key_bit_range() {
            assert_eq!(KeyVec::key_bit_range(3.try_into().unwrap(), 0), 0..3);
            assert_eq!(KeyVec::key_bit_range(3.try_into().unwrap(), 1), 3..6);
            assert_eq!(KeyVec::key_bit_range(10.try_into().unwrap(), 10), 100..110);
        }
    }
}

mod key_allocator {
    use std::cmp::Ordering;

    use crate::Key;

    /// Manages the attribution of keys to new palette entries.
    ///
    /// When asked for a new key, it allocates it in the space of all possible key values,
    /// and when a key no longer used is returned, it deallocates it to make it available again.
    ///
    /// It actually keeps track of all the unused key values, in the form of a set that
    /// distinguishes the two regions:
    /// - a sparse interval of values where most of the keys are used,
    /// this interval is `0..range_start`; the unused keys that are in this interval
    /// are in `sparse_vec` (which is sorted in reverse for a fast pop of its min value).
    /// - an interval where all the key values are unused, `range_start..`.
    pub(crate) struct KeyAllocator {
        /// Always sorted in reverse (higest member first, lowest member last).
        sparse_vec: Vec<Key>,
        range_start: Key,
    }

    impl KeyAllocator {
        /// Creates an empty `KeyAllocator`.
        ///
        /// Does not allocate now,
        /// allocations are done at some point if necessary after at least one key deallocation.
        pub(crate) fn new() -> Self {
            Self {
                sparse_vec: Vec::new(),
                range_start: 0,
            }
        }

        /// Allocates the smallest available key value from the `range_start..` range.
        fn allocate_from_range(&mut self) -> Key {
            self.range_start += 1;
            self.range_start - 1
        }

        /// Allocates the smallest available key value.
        /// May return a key value that was deallocated before.
        pub(crate) fn allocate(&mut self) -> Key {
            // Smallest member is last in `sparse_vec`.
            self.sparse_vec
                .pop()
                .unwrap_or_else(|| self.allocate_from_range())
        }

        /// Deallocates a key value, making it available for some future allocation.
        ///
        /// # Panics
        ///
        /// Panics if the `key` was already not allocated.
        pub(crate) fn deallocate(&mut self, key: Key) {
            match (key + 1).cmp(&self.range_start) {
                Ordering::Greater => {
                    // The key is already in the range `range_start..`.
                    panic!("`deallocate` called on an already unused key");
                }
                Ordering::Equal => {
                    if self.sparse_vec.first() == Some(&key) {
                        // The first element of `sparse_vec` is its higest member,
                        // so if the key (which is just below the lowest value of `range_start..`)
                        // is in `sparse_vec` then it can only be its first member.
                        panic!("`deallocate` called on an already unused key");
                    }
                    // The key touches the edge of the range `range_start..`,
                    // we can just expand the range to include the key.
                    self.range_start -= 1;
                }
                Ordering::Less => {
                    // Potentially expensive (O(n)) reduction of `sparse_vec`'s length
                    // is only performed when it could spare us a reallocation.
                    if self.sparse_vec.capacity() == self.sparse_vec.len() {
                        self.reduce_sparse_vec_len_if_possible();
                    }

                    // Insert key in `sparse_vec` in a way that keeps it sorted in reverse.
                    let where_to_insert = self
                        .sparse_vec
                        .binary_search_by(|probe| {
                            // Compare but reversed, because the list is sorted in reverse.
                            key.cmp(probe)
                        })
                        .expect_err("`deallocate` called on an already unused key");
                    self.sparse_vec.insert(where_to_insert, key);
                }
            }
        }

        /// Attempt to reduce the size of `sparse_vec`'s content.
        /// If successful it can prevent a reallocation of `sparse_vec` when adding a key to it.
        ///
        /// Runs in O(n) time if attempt if successful.
        fn reduce_sparse_vec_len_if_possible(&mut self) {
            // If the higest values of `sparse_vec` (which are all at the beginning of the vec)
            // touch `range_start..` then we can consider them to be in the range `range_start..`
            // by extending it (the range) to swallow them, which allows to remove them
            // from `sparse_vec` to gain some space withou changing the set of deallocated keys
            // that these represent.
            if self
                .sparse_vec
                .first()
                .is_some_and(|value| value + 1 == self.range_start)
            {
                let redundant_values_at_the_start_of_sparse_vec = self
                    .sparse_vec
                    .iter()
                    .enumerate()
                    .take_while(|(i, &value)| value + 1 + *i as Key == self.range_start)
                    .count();
                self.sparse_vec
                    .drain(0..redundant_values_at_the_start_of_sparse_vec);
                self.range_start -= redundant_values_at_the_start_of_sparse_vec as Key;
            }
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn key_allocation_simple() {
            let mut al = KeyAllocator::new();
            assert_eq!(al.allocate(), 0);
            assert_eq!(al.allocate(), 1);
            assert_eq!(al.allocate(), 2);
            assert_eq!(al.sparse_vec, &[]);
            assert_eq!(al.range_start, 3);
        }

        #[test]
        fn key_allocation_and_deallocation() {
            let mut al = KeyAllocator::new();
            assert_eq!(al.allocate(), 0);
            let some_key = al.allocate();
            assert_eq!(some_key, 1);
            assert_eq!(al.allocate(), 2);
            al.deallocate(some_key);
            assert_eq!(al.sparse_vec, &[some_key]);
            assert_eq!(al.range_start, 3);
            assert_eq!(al.allocate(), some_key);
        }

        #[test]
        fn key_deallocation_unused_keys_clearing_manually() {
            let mut al = KeyAllocator::new();
            let mut keys = vec![];
            for _ in 0..20 {
                keys.push(al.allocate());
            }
            for key in keys.into_iter() {
                al.deallocate(key);
            }
            // Manually trigger redudant information cleaning.
            al.reduce_sparse_vec_len_if_possible();
            // We are back to the initial state where all the possible key values are unused
            // (because we deallocated all of those that we allocated).
            assert_eq!(al.sparse_vec, &[]);
            assert_eq!(al.range_start, 0);
        }

        #[test]
        fn key_deallocation_unused_keys_clearing_convenient_order() {
            let mut al = KeyAllocator::new();
            let mut keys = vec![];
            for _ in 0..20 {
                keys.push(al.allocate());
            }
            for key in keys.into_iter().rev() {
                al.deallocate(key);
            }
            // Here we deallocated the keys in reverse order of their allocation,
            // so higest key first deallocated etc.
            // This happens to be the convenient order of key deallocation
            // for the `deallocate` method to be able to keep `sparse_vec`
            // from growing past its capacity of 4 (its first allocation)
            // without manual calls to `reduce_sparse_vec_len_if_possible`
            // (because automatic calls to this function all worked).
            assert!(al.sparse_vec.len() <= 4);
        }
    }
}

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

    /// Returns the minimal size (in bits) that any representation of the given key can fit in.
    fn key_min_size(key: Key) -> NonZeroUsize {
        // SAFETY: The expression has the form `unsigned_term + 1`, so it is at least 1.
        unsafe { NonZeroUsize::new_unchecked((key.checked_ilog2().unwrap_or(0) + 1) as usize) }
    }

    /// Allocates the smallest unused key value.
    ///
    /// It is quarenteed that it will fit in `keys_size` bits,
    /// by properly increasing `keys_size` if necessary.
    fn allocate_new_key_and_make_it_fit(&mut self) -> Key {
        let new_key = self.key_allocator.allocate();
        let min_size = Self::key_min_size(new_key);
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
            entry.count += that_many;
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
    fn remove_element_instances_from_palette(&mut self, key: Key, that_many: usize) {
        let map_entry = self.palette.entry(key);
        let Entry::Occupied(mut occupied_entry) = map_entry else {
            panic!("Bug: Removing element instances by a key that is unused");
        };
        let palette_entry = occupied_entry.get_mut();
        palette_entry.count = palette_entry
            .count
            .checked_sub(that_many)
            .expect("Bug: Removing more element instances from palette than its count");
        if palette_entry.count == 0 {
            occupied_entry.remove();
            self.key_allocator.deallocate(key);
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
    pub fn set(&mut self, index: usize, element: impl ViewToOwned<E>) {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            // Style of panic message inspired form the one in
            // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
            panic!(
                "set index (is {index}) should be < len (len is {})",
                self.len()
            );
        }

        let key_of_elemement_to_remove = {
            // SAFETY: We checked the bounds, we have `index < self.len()`.
            unsafe { self.key_vec.get_unchecked(index) }
        };
        self.remove_element_instances_from_palette(key_of_elemement_to_remove, 1);
        let key_of_element_to_add = self.add_element_instances_to_palette(element, 1);
        // SAFETY: We checked the bounds, we have `index < self.len()`.
        unsafe {
            self.key_vec.set_unchecked(index, key_of_element_to_add);
        }
    }

    /// Appends the given `element` to the back of the `PalVec`'s array.
    pub fn push(&mut self, element: impl ViewToOwned<E>) {
        let key = self.add_element_instances_to_palette(element, 1);
        self.key_vec.push(key);
    }

    /// Removes the last element from the `PalVec`'s array and returns it,
    /// or `None` if it is empty.
    pub fn pop(&mut self) -> Option<&E> {
        self.key_vec.pop().map(|key| {
            self.get_element_from_used_key(key)
                .expect("Bug: Key used in `key_vec` is not used by the palette")
        })
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

pub trait ViewToOwned<T>
where
    T: Eq,
{
    fn into_owned(self) -> T;
    fn eq(&self, other: &T) -> bool;
}

impl<T> ViewToOwned<T> for &T
where
    T: Clone + Eq,
{
    fn into_owned(self) -> T {
        self.clone()
    }

    fn eq(&self, other: &T) -> bool {
        self == &other
    }
}

impl<T> ViewToOwned<T> for T
where
    T: Clone + Eq,
{
    fn into_owned(self) -> T {
        self
    }

    fn eq(&self, other: &T) -> bool {
        self == other
    }
}

impl ViewToOwned<String> for &str {
    fn into_owned(self) -> String {
        self.to_string()
    }

    fn eq(&self, other: &String) -> bool {
        self == other
    }
}

impl ViewToOwned<Box<str>> for &str {
    fn into_owned(self) -> Box<str> {
        self.to_string().into_boxed_str()
    }

    fn eq(&self, other: &Box<str>) -> bool {
        *self == other.as_ref()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn new_is_empty() {
        let palvec: PalVec<()> = PalVec::new();
        assert!(palvec.is_empty());
        assert_eq!(palvec.len(), 0);
    }

    #[test]
    fn key_min_size() {
        assert_eq!(PalVec::<()>::key_min_size(0).get(), 1);
        assert_eq!(PalVec::<()>::key_min_size(1).get(), 1);
        assert_eq!(PalVec::<()>::key_min_size(2).get(), 2);
        assert_eq!(PalVec::<()>::key_min_size(3).get(), 2);
        assert_eq!(PalVec::<()>::key_min_size(4).get(), 3);
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
        assert_eq!(palvec.pop(), None);
    }

    #[test]
    fn push_and_pop_strings() {
        let mut palvec: PalVec<String> = PalVec::new();
        palvec.push("uwu");
        palvec.push(String::from("owo"));
        assert_eq!(palvec.pop().map(AsRef::as_ref), Some("owo"));
        assert_eq!(palvec.pop().map(AsRef::as_ref), Some("uwu"));
        assert_eq!(palvec.pop(), None);
    }

    #[test]
    fn push_and_pop_numbers() {
        let mut palvec: PalVec<i32> = PalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert_eq!(palvec.pop(), Some(&5));
        assert_eq!(palvec.pop(), Some(&8));
        assert_eq!(palvec.pop(), None);
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
}
