use std::{
    cmp::Ordering,
    collections::{hash_map::Entry, HashMap},
    num::NonZero,
    ops::Range,
};

use bitvec::{field::BitField, order::Lsb0, slice::BitSlice, vec::BitVec, view::BitViewSized};
use fxhash::FxHashMap;

type Key = u32;

// TODO: Better doc!
pub struct PalVec<E> {
    /// An array of keys, each being represented with `keys_size` bits exactly,
    /// without padding between keys (so they are probably not byte-aligned).
    /// All the keys contained here are valid `palette` keys, thus not unused (see `unused_keys`).
    ///
    /// Should be accessed via
    /// [`PalVec::get_key_in_vec_unchecked`] and [`PalVec::set_key_in_vec_unchecked`]
    /// when seen as an array of keys instead of just an array of bits.
    key_vec: BitVec<usize, Lsb0>,
    /// All keys in `key_vec` are represented with exactly this size *in bits*.
    /// Cannot be zero, even if the array or palette or both are empty.
    keys_size: NonZero<usize>,
    /// Each key in `key_vec` is a key into this table to refer to the element it represents.
    /// Accessing index `i` of the `PalVec` array will really access `palette[key_vec[i]]`.
    ///
    /// A key that is not present in the palette is considered unused and tracked by `unused_keys`.
    // TODO: Better optimize the palette type thing!
    palette: FxHashMap<Key, PaletteEntry<E>>,
    /// Always sorted in reverse (higest first, lowest last) (so that popping its min is O(1)).
    /// All the possible keys above the higest member are also available.
    /// If empty, then it is treated as if it were `vec![0]` (so every possible key is available).
    ///
    /// This is used to keep track of all the unused keys so that when we want to allocate a new
    /// key to use then we can just get its smallest member, and when we no longer use a key we
    /// can deallocate it and return it to the set it represents.
    // TODO: Change this into Vec AND max (as a separate field) representing vec content plus max..
    unused_keys: Vec<Key>,
}

struct PaletteEntry<E> {
    count: usize,
    element: E,
}

impl<E> PalVec<E> {
    /// Creates an empty `PalVec`.
    ///
    /// Does not allocate now,
    /// allocations are done when content is added to it or is is told to reserve memory.
    pub fn new() -> Self {
        Self {
            key_vec: BitVec::new(),
            keys_size: {
                // SAFETY: 1 is not 0
                unsafe { NonZero::new_unchecked(1) }
            },
            palette: HashMap::default(),
            unused_keys: vec![],
        }
    }

    /// Returns the number of elements in the `PalVec` array.
    pub fn len(&self) -> usize {
        self.key_vec.len() / self.keys_size
    }

    /// Returns `true` if the `PalVec` array contains no elements.
    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
    }

    /// Returns the minimal size (in bits) that any representation of the given key can fit in.
    fn key_min_size(key: Key) -> usize {
        (key.checked_ilog2().unwrap_or(0) + 1) as usize
    }

    /// Returns the range of bits in the `keys_size` of a `PalVec`
    /// that has the given `keys_size`.
    ///
    /// No bound check, assumes large enough `key_vec`.
    fn key_bit_range(index: usize, keys_size: usize) -> Range<usize> {
        let index_inf = index * keys_size;
        let index_sup_excluded = index_inf + keys_size;
        index_inf..index_sup_excluded
    }

    /// Returns the key at the given index in the array of keys.
    ///
    /// # Safety
    ///
    /// The `index` must be `< self.len()`.
    unsafe fn get_key_in_vec_unchecked(&self, index: usize) -> Key {
        let bit_range = Self::key_bit_range(index, self.keys_size.get());
        debug_assert!(self.key_vec.len() <= bit_range.end);
        self.key_vec[bit_range].load()
    }

    /// Sets the key at the given index to the given key.
    ///
    /// # Safety
    ///
    /// The `index` must be `< self.len()`.
    unsafe fn set_key_in_vec_unchecked(&mut self, index: usize, key: Key) {
        let bit_range = Self::key_bit_range(index, self.keys_size.get());
        debug_assert!(self.key_vec.len() < bit_range.end);
        self.key_vec[bit_range].store(key);
    }

    fn push_key_in_vec(&mut self, key: Key) {
        let key_le = (key as usize).to_le();
        let key_bits = key_le.as_raw_slice();
        let key_bits: &BitSlice<usize, Lsb0> = BitSlice::from_slice(key_bits);
        let key_bits = &key_bits[0..self.keys_size.get()];
        self.key_vec.extend_from_bitslice(key_bits);
    }

    /// Reserves capacity for at least `additional` more elements
    /// to be inserted in the `PalVec`'s array,
    /// with an effort to allocate the minimum sufficient amount of memory.
    ///
    /// If `keys_size` grows, then this reservation will not suffice anymore.
    fn _reserve_exact_array(&mut self, additional: usize) {
        self.key_vec
            .reserve_exact(additional * self.keys_size.get());
    }

    /// Reserves capacity for at least `additional` more elements
    /// to be inserted in the `PalVec`'s array.
    ///
    /// If `keys_size` grows, then this reservation might not suffice anymore.
    fn _reserve_array(&mut self, additional: usize) {
        self.key_vec.reserve(additional * self.keys_size.get());
    }

    /// Sets `keys_size` to the given value,
    /// adapting `key_vec` so that every key is now represented on `new_keys_size` bits
    /// (without changing the value of the keys).
    fn set_keys_size(&mut self, new_keys_size: usize) {
        match self.keys_size.get().cmp(&new_keys_size) {
            Ordering::Equal => {}
            Ordering::Less => {
                // The `keys_size` has to increase.
                let old_keys_size = self.keys_size.get();
                let len = self.len();
                // We first resize the `key_vec` to get enough room to make all its keys bigger.
                self.key_vec.resize(len * new_keys_size, false);
                // Now we have free space at the end of `key_vec`,
                // and all the keys with their old size packed at the beginning
                // (each key being at its old position).
                // We move from the last key to the first, taking a key from its
                // old position and putting it at its new position (the position it would
                // have if `keys_size` was `new_keys_size`) and extending it so that its
                // representation takes `new_keys_size` bits.
                for i in (0..len).rev() {
                    // Get the last not-yet moved key from its old position.
                    let key: Key = {
                        let bit_range = Self::key_bit_range(i, old_keys_size);
                        self.key_vec[bit_range].load()
                    };
                    // Move it to its new position, and represent it with its new size.
                    {
                        let bit_range = Self::key_bit_range(i, new_keys_size);
                        self.key_vec[bit_range].store(key);
                    }
                }
                self.keys_size = {
                    // SAFETY: `keys_size` is NonZero unigned, so `0 < keys_size`,
                    // and `keys_size < new_keys_size`, so `0 < new_keys_size`.
                    unsafe { NonZero::new_unchecked(new_keys_size) }
                };
            }
            Ordering::Greater => todo!("`keys_size` has to decrease"),
        }
    }

    /// Allocates the smallest unused key value.
    ///
    /// No work is done to make sure its smallest representation is small enough
    /// to fit in `keys_size` bits. See [`PalVec::allocate_new_key_and_make_it_fit`] for that.
    fn allocate_new_key_that_may_not_fit(&mut self) -> Key {
        let new_key = self.unused_keys.pop().unwrap_or(0);
        if self.unused_keys.is_empty() {
            // `unused_keys` is a sorted list of unused keys,
            // sorted in reverse so that we can pop the lowest unused key in O(1).
            // The unused keys are all the keys in `unused_keys` and all the
            // possible key values above the higest member of `unused_keys`.
            // It is empty now, which means that it only contained 0 or 1 key before the pop,
            // so the actual set of unused keys was the range `new_key..`.
            // `new_key` is being allocated now, meaning to be used, so it is excluded from
            // the range that now becomes `(new_key+1)..`.
            self.unused_keys.push(new_key + 1);
        }
        new_key
    }

    /// Allocates the smallest unused key value.
    ///
    /// It is quarenteed that it will fit in `keys_size` bits,
    /// by properly increasing `keys_size` if necessary.
    fn allocate_new_key_and_make_it_fit(&mut self) -> Key {
        let new_key = self.allocate_new_key_that_may_not_fit();
        let min_size = Self::key_min_size(new_key);
        let does_it_already_fit = min_size <= self.keys_size.get();
        if does_it_already_fit {
            // It already fits, nothing to do.
        } else {
            // Properly making `keys_size` bigger so that the new key fits.
            self.set_keys_size(min_size);
        }
        new_key
    }

    /// Deallocates a previously allocated key,
    /// making it "unused" again and available for future key allocation.
    ///
    /// `keys_size` is left untouched.
    fn deallocate_key(&mut self, key: Key) {
        // Potentially expensive (O(n)) reduction of `unused_keys`'s length
        // is only performed when it could spare us reallocation.
        if self.unused_keys.capacity() == self.unused_keys.len() {
            self.reduce_unused_keys_len_if_possible();
        }

        // Insert key in `unused_keys` in a way that keeps it sorted in reverse.
        let where_to_insert = self
            .unused_keys
            .binary_search_by(|probe| {
                // Compare but reversed, because the list is sorted in reverse.
                key.cmp(probe)
            })
            .expect_err("`deallocate_key` called on an already unused key");
        self.unused_keys.insert(where_to_insert, key);
    }

    /// Doesn't change the set of unused keys,
    /// but attempt to reduce the length of its representation by removing redundant information.
    ///
    /// Runs in O(n) time if triggered.
    fn reduce_unused_keys_len_if_possible(&mut self) {
        // `unused_keys` represents a set of values.
        // The represented set contains all the members of `unused_keys`
        // and all the possible values that are greater than its higest member.
        // So if `unused_keys` contains, say, {2, 3, 7, 8}, then we could remove the 8
        // from its representation without changing its meaning.
        // This can be generalized: if its representation contains a sequence A,B,..,Z
        // of consecutive values and if Z is its higest value, then we can remove B,..,Z
        // (but keep A) without changing the represented set.
        // This is what we do here, using the fact that `unused_keys` is sorted (in reverse).
        let redundant_values_at_the_end = self
            .unused_keys
            .windows(2)
            .take_while(|&window| window[0] == window[1] + 1)
            .count();
        self.unused_keys.drain(0..redundant_values_at_the_end);

        // See if we can use the empty vec representation (that represents all possible values).
        if self.unused_keys.first().copied() == Some(0) {
            // `unused_keys` is sorted in reverse, so its first element is the higest.
            // If the higest element of the unused set representation is zero,
            // then it means all the possible key values are in fact unused
            // and we can go back to the initial representation of the full set by an empty vec.
            self.unused_keys.clear();
            // TODO: Deallocate `unused_keys`?
            // TODO: Why even do this?
        }
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
        element: impl Into<E> + PartialEq<E>,
        that_many: usize,
    ) -> Key {
        let already_in_palette = self
            .palette
            .iter_mut()
            .find(|(_key, palette_entry)| element == palette_entry.element);
        if let Some((&key, entry)) = already_in_palette {
            entry.count += that_many;
            key
        } else {
            let key = self.allocate_new_key_and_make_it_fit();
            self.palette.insert(
                key,
                PaletteEntry {
                    count: that_many,
                    element: element.into(),
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
            self.deallocate_key(key);
        }
    }

    /// Returns a reference to the `PalVec`'s array element at the given `index`.
    ///
    /// Returns `None` if `index` is out of bounds.
    pub fn get(&self, index: usize) -> Option<&E> {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            return None;
        }

        let key = {
            // SAFETY: We checked the bounds, we have `index < self.len()`.
            unsafe { self.get_key_in_vec_unchecked(index) }
        };
        let element = &self
            .palette
            .get(&key)
            .expect("Bug: Key used in `key_vec` is not used by the palette")
            .element;
        Some(element)
    }

    /// Sets the `PalVec`'s array element at the given `index` to the given `element`.
    ///
    /// Subsequent calls to `get` with that `index` will return `element`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    pub fn set(&mut self, index: usize, element: impl Into<E> + PartialEq<E>) {
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
            unsafe { self.get_key_in_vec_unchecked(index) }
        };
        self.remove_element_instances_from_palette(key_of_elemement_to_remove, 1);
        let key_of_element_to_add = self.add_element_instances_to_palette(element, 1);
        // SAFETY: We checked the bounds, we have `index < self.len()`.
        unsafe {
            self.set_key_in_vec_unchecked(index, key_of_element_to_add);
        }
    }

    pub fn push(&mut self, element: impl Into<E> + PartialEq<E>) {
        let key_of_element_to_add = self.add_element_instances_to_palette(element, 1);
        self.push_key_in_vec(key_of_element_to_add);
    }
}

impl<E> Default for PalVec<E> {
    fn default() -> Self {
        Self::new()
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
        assert_eq!(PalVec::<()>::key_min_size(0), 1);
        assert_eq!(PalVec::<()>::key_min_size(1), 1);
        assert_eq!(PalVec::<()>::key_min_size(2), 2);
        assert_eq!(PalVec::<()>::key_min_size(3), 2);
        assert_eq!(PalVec::<()>::key_min_size(4), 3);
    }

    #[test]
    fn key_bit_range() {
        assert_eq!(PalVec::<()>::key_bit_range(0, 3), 0..3);
        assert_eq!(PalVec::<()>::key_bit_range(1, 3), 3..6);
        assert_eq!(PalVec::<()>::key_bit_range(10, 10), 100..110);
    }

    #[test]
    fn key_allocation_simple() {
        let mut palvec: PalVec<()> = PalVec::new();
        // Should always allocate the smallest available key,
        // and a new empty PalVec uses no key so all the unsigned numbers are available.
        // Each allocated key that is not deallocated should not be returned again
        // so it must count up.
        assert_eq!(palvec.allocate_new_key_that_may_not_fit(), 0);
        assert_eq!(palvec.allocate_new_key_that_may_not_fit(), 1);
        assert_eq!(palvec.allocate_new_key_that_may_not_fit(), 2);
        // Implementation detail about the set of unused keys representation.
        assert_eq!(palvec.unused_keys, &[3]);
    }

    #[test]
    fn key_allocation_and_deallocation() {
        let mut palvec: PalVec<()> = PalVec::new();
        assert_eq!(palvec.allocate_new_key_that_may_not_fit(), 0);
        let some_key = palvec.allocate_new_key_that_may_not_fit();
        assert_eq!(some_key, 1);
        assert_eq!(palvec.allocate_new_key_that_may_not_fit(), 2);
        palvec.deallocate_key(some_key);
        assert_eq!(palvec.unused_keys, &[3, some_key]);
        assert_eq!(palvec.allocate_new_key_that_may_not_fit(), some_key);
    }

    #[test]
    fn key_deallocation_unused_keys_clearing_manually() {
        let mut palvec: PalVec<()> = PalVec::new();
        let mut keys = vec![];
        for _ in 0..20 {
            keys.push(palvec.allocate_new_key_that_may_not_fit());
        }
        for key in keys.into_iter() {
            palvec.deallocate_key(key);
        }
        // Manually trigger redudant information cleaning.
        palvec.reduce_unused_keys_len_if_possible();
        // We are back to the initial state where all the possible key values are unused
        // (because we deallocated all of those that we allocated)
        // so `unused_keys` should be represented by the smallest representation of its
        // initial state, that happens to be the empty vec.
        assert_eq!(palvec.unused_keys, &[]);
    }

    #[test]
    fn key_deallocation_unused_keys_clearing_convenient_order() {
        let mut palvec: PalVec<()> = PalVec::new();
        let mut keys = vec![];
        for _ in 0..20 {
            keys.push(palvec.allocate_new_key_that_may_not_fit());
        }
        for key in keys.into_iter().rev() {
            palvec.deallocate_key(key);
        }
        // Here we deallocated the keys in reverse order of their allocation,
        // so higest key first deallocated etc.
        // This happens to be the convenient order of key deallocation
        // for the `deallocate_key` method that must keep `unused_keys`
        // from growing past its capacity of 4 (its first allocation)
        // without manual calls to `reduce_unused_keys_len_if_possible`
        // (because automatic calls to this function all worked).
        assert!(palvec.unused_keys.len() <= 4);
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
        let mut palvec: PalVec<String> = PalVec::new();
        palvec.push("hello");
        assert_eq!(palvec.get(0), Some(&"hello".to_string()));
    }

    #[test]
    #[should_panic]
    fn get_out_of_bounds_is_none() {
        let mut palvec: PalVec<()> = PalVec::new();
        assert!(palvec.get(0).is_none());
        palvec.push(());
        palvec.push(());
        assert!(palvec.get(0).is_some());
        assert!(palvec.get(1).is_some());
        assert!(palvec.get(2).is_none());
    }
}
