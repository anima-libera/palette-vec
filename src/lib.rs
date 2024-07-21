use std::collections::{hash_map::Entry, HashMap};

use fxhash::FxHashMap;
use key_allocator::KeyAllocator;
use key_vec::KeyVec;
use view_to_owned::ViewToOwned;

type Key = usize;

/// Returns the minimal size (in bits) that any representation of the given key can fit in.
fn key_min_size(key: Key) -> usize {
    key.checked_ilog2().map(|size| size + 1).unwrap_or(0) as usize
}

mod key_vec {
    use std::{
        cmp::Ordering,
        mem::ManuallyDrop,
        ops::{DerefMut, Range},
    };

    use bitvec::{field::BitField, order::Lsb0, slice::BitSlice, vec::BitVec, view::BitViewSized};

    use crate::{key_min_size, Key};

    /// An array of keys, each being represented with [`Self::keys_size()`] bits exactly,
    /// without padding between keys (so they are probably not byte-aligned).
    ///
    /// Supports a `keys_size` of zero, which doesn't allocate and only support the key value `0`.
    pub(crate) struct KeyVec {
        /// The size in bits of the memory representation of each key in `vec_or_len.vec`.
        ///
        /// It is always less-than-or-equal-to `Key`'s size in bits.
        keys_size: usize,
        vec_or_len: BitVecOrLen,
    }

    union BitVecOrLen {
        /// The array of keys, keys are alligned on `keys_size` bits.
        /// The key at index `i` occupies the bit range `Self::key_bit_range(self.keys_size, i)`.
        ///
        /// The number of live bits in the `BitVec` is always a multiple of `keys_size`.
        ///
        /// When `keys_size` is non-zero, then this field is active.
        /// When `keys_size` is zero, then `len` is active.
        vec: ManuallyDrop<BitVec<usize, Lsb0>>,
        /// When `keys_size` is zero (0), there is no allocation to be done,
        /// there is only the length of an imaginary vec of zero-sized elements,
        /// which are all the key value `0` represented with 0 bits.
        len: usize,
    }

    impl Drop for KeyVec {
        fn drop(&mut self) {
            if 0 < self.keys_size {
                // SAFETY: `vec` is the active field iff `keys_size` is zero.
                unsafe { ManuallyDrop::drop(&mut self.vec_or_len.vec) }
            }
        }
    }

    impl KeyVec {
        /// Creates an empty `KeyVec` (with `keys_size` initially set to zero).
        ///
        /// Does not allocate now,
        /// allocations are done when keys are added to it or it is told to reserve memory.
        /// While `keys_size` remains zero, no allocation is performed either.
        #[inline]
        pub(crate) fn new() -> Self {
            Self {
                vec_or_len: BitVecOrLen { len: 0 },
                keys_size: 0,
            }
        }

        /// Creates a `KeyVec` (with `keys_size` initially set to zero)
        /// that is filled with `0`s and that has a length of the given `len`.
        /// This is as cheap as [`Self::new()`], no matter how big is the given `len`.
        ///
        /// Does not allocate now,
        /// allocations are done when keys are added to it or it is told to reserve memory.
        /// While `keys_size` remains zero, no allocation is performed either.
        #[inline]
        pub(crate) fn with_len(len: usize) -> Self {
            Self {
                vec_or_len: BitVecOrLen { len },
                keys_size: 0,
            }
        }

        /// The size in bits of the representation of each key in the `KeyVec`.
        #[inline]
        pub(crate) fn keys_size(&self) -> usize {
            self.keys_size
        }

        /// Safely run code on the active field of `vec_or_len`.
        #[inline]
        fn visit_vec_or_len<R>(
            &self,
            on_vec: impl FnOnce(&BitVec<usize, Lsb0>) -> R,
            on_len: impl FnOnce(usize) -> R,
        ) -> R {
            if self.keys_size == 0 {
                on_len({
                    // SAFETY: `keys_size` is zero so `len` is active.
                    unsafe { self.vec_or_len.len }
                })
            } else {
                on_vec({
                    // SAFETY: `keys_size` is not zero so `vec` is active.
                    unsafe { &self.vec_or_len.vec }
                })
            }
        }

        /// Safely run code on the active field of `vec_or_len` provided as an `&mut _`.
        #[inline]
        fn _visit_vec_or_len_mut<R>(
            &mut self,
            on_vec: impl FnOnce(&mut BitVec<usize, Lsb0>) -> R,
            on_len: impl FnOnce(&mut usize) -> R,
        ) -> R {
            if self.keys_size == 0 {
                on_len({
                    // SAFETY: `keys_size` is zero so `len` is active.
                    unsafe { &mut self.vec_or_len.len }
                })
            } else {
                on_vec({
                    // SAFETY: `keys_size` is not zero so `vec` is active.
                    unsafe { &mut self.vec_or_len.vec }
                })
            }
        }

        /// Returns the number of keys in the `KeyVec`.
        #[inline]
        pub(crate) fn len(&self) -> usize {
            self.visit_vec_or_len(|vec| vec.len() / self.keys_size, |len| len)
        }

        /// Returns `true` if the `KeyVec` contains no key.
        #[inline]
        pub(crate) fn is_empty(&self) -> bool {
            self.visit_vec_or_len(|vec| vec.is_empty(), |len| len == 0)
        }

        /// Returns the range of bits in the `KeyVec`'s `BitVec`
        /// that holds the representation of its `index`-th key.
        ///
        /// Assumes a large enough `KeyVec`.
        ///
        /// Also works if `keys_size` is zero, even though such range is never required.
        #[inline]
        fn key_bit_range(keys_size: usize, index: usize) -> Range<usize> {
            let index_inf = index * keys_size;
            let index_sup_excluded = index_inf + keys_size;
            index_inf..index_sup_excluded
        }

        /// Returns the key at the given `index`, or None if out of bounds.
        pub(crate) fn get(&self, index: usize) -> Option<Key> {
            if index < self.len() {
                Some(if self.keys_size == 0 {
                    // Only possible key value when `keys_size` is zero.
                    0
                } else {
                    // SAFETY: `keys_size` is non-zero, and `index < self.len()`.
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
        /// Panics if `key_min_size(key)` is not `<= self.keys_size()`.
        pub(crate) fn _set(&mut self, index: usize, key: Key) {
            if index < self.len() {
                if key_min_size(key) <= self.keys_size {
                    if self.keys_size == 0 {
                        // Nothing to do, `key` is zero since `key_min_size(key) == 0`.
                        debug_assert_eq!(key, 0);
                    } else {
                        // SAFETY: We just checked all the conditions.
                        unsafe { self.set_unchecked(index, key) }
                    }
                } else {
                    // The key doesn't fit, `keys_size` is too small.
                    panic!(
                        "key min size (is {} bits) should be <= keys_size (is {})",
                        key_min_size(key),
                        self.keys_size,
                    );
                }
            } else {
                // Style of panic message inspired form the one in
                // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
                panic!("set index (is {index}) should be < len (is {})", self.len());
            }
        }

        /// Appends the given `key` to the end of the `KeyVec`.
        ///
        /// # Panics
        ///
        /// Panics if `key_min_size(key)` is not `<= self.keys_size()`.
        pub(crate) fn push(&mut self, key: Key) {
            if key_min_size(key) <= self.keys_size {
                if self.keys_size == 0 {
                    debug_assert_eq!(key, 0);
                    // SAFETY: `keys_size` is zero so `len` is the active field.
                    unsafe { self.vec_or_len.len += 1 }
                } else {
                    // SAFETY: We are in a `if SAFETY_CONDITION` block.
                    unsafe { self.push_unchecked(key) }
                }
            } else {
                // The key doesn't fit, `keys_size` is too small.
                panic!(
                    "key min size (is {} bits) should be <= keys_size (is {})",
                    key_min_size(key),
                    self.keys_size,
                );
            }
        }

        /// Removes the last key of the `KeyVec` and returns it, or `None` if it is empty.
        pub(crate) fn pop(&mut self) -> Option<Key> {
            if self.keys_size == 0 {
                // SAFETY: `keys_size` is zero so `len` is the active field.
                unsafe {
                    if self.vec_or_len.len == 0 {
                        None
                    } else {
                        self.vec_or_len.len -= 1;
                        Some(0)
                    }
                }
            } else {
                // SAFETY: `keys_size` is non-zero so `vec` is the active field.
                unsafe {
                    if self.vec_or_len.vec.is_empty() {
                        None
                    } else {
                        let len = self.len();
                        let last_key = {
                            // SAFETY: `len-1 < len`, and `0 < len` (we are not empty)
                            // so `0 <= len-1`.
                            self.get_unchecked(len - 1)
                        };
                        self.vec_or_len
                            .vec
                            .deref_mut()
                            .truncate(len - self.keys_size);
                        Some(last_key)
                    }
                }
            }
        }

        /// Returns the key at the given index in the `KeyVec`.
        ///
        /// # Safety
        ///
        /// `self.keys_size()` must be non-zero, and
        /// `index` must be `< self.len()`.
        pub(crate) unsafe fn get_unchecked(&self, index: usize) -> Key {
            debug_assert!(0 < self.keys_size);
            let bit_range = Self::key_bit_range(self.keys_size, index);
            debug_assert!(bit_range.end <= self.vec_or_len.vec.len());
            self.vec_or_len.vec[bit_range].load()
        }

        /// Sets the key at the given index to the given `key`.
        ///
        /// # Safety
        ///
        /// `self.keys_size()` must be non-zero, and
        /// `index` must be `< self.len()`, and
        /// `key_min_size(key)` must be `<= self.keys_size()`.
        pub(crate) unsafe fn set_unchecked(&mut self, index: usize, key: Key) {
            debug_assert!(0 < self.keys_size);
            debug_assert!(key_min_size(key) <= self.keys_size);
            let bit_range = Self::key_bit_range(self.keys_size, index);
            debug_assert!(bit_range.end <= self.vec_or_len.vec.len());
            self.vec_or_len.vec.deref_mut()[bit_range].store(key);
        }

        /// Appends the given `key` to the end of the `KeyVec`.
        ///
        /// # Safety
        ///
        /// `self.keys_size()` must be non-zero, and
        /// `key_min_size(key)` must be `<= self.keys_size()`.
        pub(crate) unsafe fn push_unchecked(&mut self, key: Key) {
            debug_assert!(0 < self.keys_size);
            debug_assert!(key_min_size(key) <= self.keys_size);
            let key_le = key.to_le();
            let key_bits = key_le.as_raw_slice();
            let key_bits: &BitSlice<Key, Lsb0> = BitSlice::from_slice(key_bits);
            // `keys_size` is <= `Key`'s size in bits, this won't go out-of-bounds.
            let key_bits = &key_bits[0..self.keys_size];
            self.vec_or_len
                .vec
                .deref_mut()
                .extend_from_bitslice(key_bits);
        }

        /// Reserves capacity for at least `additional` more keys,
        /// with an effort to allocate the minimum sufficient amount of memory.
        #[inline]
        fn _reserve_exact(&mut self, additional: usize) {
            let keys_size = self.keys_size;
            self._visit_vec_or_len_mut(|vec| vec.reserve_exact(additional * keys_size), |_len| {});
        }

        /// Reserves capacity for at least `additional` more keys.
        #[inline]
        fn _reserve(&mut self, additional: usize) {
            let keys_size = self.keys_size;
            self._visit_vec_or_len_mut(|vec| vec.reserve(additional * keys_size), |_len| {});
        }

        /// Adapts the representation of the contained keys so that now
        /// every key is represented on `new_keys_size` bits.
        /// The value of the keys doesn't change, the content is still the same,
        /// except it will now work with a bigger `keys_size` to accomodate for
        /// more possible key values.
        ///
        /// # Panics
        ///
        /// Panics if `new_keys_size` is not `<= Key::BITS`.
        pub(crate) fn change_keys_size(&mut self, new_keys_size: usize) {
            let max_key_size = Key::BITS as usize;
            if max_key_size < new_keys_size {
                panic!(
                    "new key size (is {} bits) should be <= `Key::BITS` (is {})",
                    new_keys_size, max_key_size
                );
            }
            if self.keys_size == 0 {
                if 0 < new_keys_size {
                    let len = {
                        // SAFETY: `keys_size` is still zero at this point.
                        unsafe { self.vec_or_len.len }
                    };
                    // All the key values are `0`, so all the bits shall be zeros.
                    self.vec_or_len = BitVecOrLen {
                        vec: ManuallyDrop::new(BitVec::repeat(false, len * new_keys_size)),
                    };
                }
            } else {
                match self.keys_size.cmp(&new_keys_size) {
                    Ordering::Equal => {}
                    Ordering::Less => {
                        // SAFETY: `keys_size` is non-zero so `vec` is the active field.
                        unsafe {
                            // The `keys_size` has to increase.
                            let old_keys_size = self.keys_size;
                            let len = self.len();
                            // Here we break some `KeyVec` invariants.
                            // We first resize the `vec` to get enough room to make all its keys bigger.
                            self.vec_or_len
                                .vec
                                .deref_mut()
                                .resize(len * new_keys_size, false);
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
                                    self.vec_or_len.vec.deref_mut()[bit_range].load()
                                };
                                // Move the key to its new position, and represent it with the new key size.
                                {
                                    let bit_range = Self::key_bit_range(new_keys_size, i);
                                    self.vec_or_len.vec.deref_mut()[bit_range].store(key);
                                }
                            }
                        }
                    }
                    Ordering::Greater => todo!("`keys_size` has to decrease"),
                }
            }
            self.keys_size = new_keys_size;
        }
    }

    #[cfg(test)]
    mod tests {
        use super::*;

        #[test]
        fn key_bit_range() {
            assert_eq!(KeyVec::key_bit_range(3, 0), 0..3);
            assert_eq!(KeyVec::key_bit_range(3, 1), 3..6);
            assert_eq!(KeyVec::key_bit_range(10, 10), 100..110);
            assert_eq!(KeyVec::key_bit_range(0, 0), 0..0);
            assert_eq!(KeyVec::key_bit_range(0, 100), 0..0);
        }

        fn assert_is_len(key_vec: &KeyVec, expected_len: usize) {
            assert_eq!(key_vec.keys_size, 0);
            let key_vec_len = {
                // SAFETY: `keys_size` is zero so `len` is the active field.
                unsafe { key_vec.vec_or_len.len }
            };
            assert_eq!(key_vec_len, expected_len);
        }

        fn assert_is_vec(key_vec: &KeyVec, expected_len: usize) {
            assert_ne!(key_vec.keys_size, 0);
            let key_vec_len = {
                // SAFETY: `keys_size` is not zero so `vec` is the active field.
                unsafe { &key_vec.vec_or_len.vec }.len() * key_vec.keys_size
            };
            assert_eq!(key_vec_len, expected_len);
        }

        #[test]
        fn key_size_zero_remains_len() {
            let mut key_vec = KeyVec::new();
            assert_is_len(&key_vec, 0);
            key_vec.push(0);
            assert_is_len(&key_vec, 1);
            key_vec.push(0);
            assert_is_len(&key_vec, 2);
            key_vec.push(0);
            assert_is_len(&key_vec, 3);
            key_vec.push(0);
            assert_is_len(&key_vec, 4);
        }

        #[test]
        fn key_size_nonzero_switches_to_vec() {
            let mut key_vec = KeyVec::new();
            assert_is_len(&key_vec, 0);
            key_vec.push(0);
            assert_is_len(&key_vec, 1);
            key_vec.push(0);
            assert_is_len(&key_vec, 2);
            key_vec.change_keys_size(1);
            assert_is_vec(&key_vec, 2);
            key_vec.push(0);
            assert_is_vec(&key_vec, 3);
            key_vec.push(0);
            assert_is_vec(&key_vec, 4);
        }

        #[test]
        fn can_push_max_key_for_any_size() {
            let mut key_vec = KeyVec::new();
            key_vec.push(0);
            for key_size in 1..=Key::BITS as usize {
                let mak_key_for_given_size = {
                    let mut value = 0;
                    for _i in 0..key_size {
                        value = (value << 1) | 1;
                    }
                    value
                };
                key_vec.change_keys_size(key_size);
                key_vec.push(mak_key_for_given_size);
            }
        }

        #[test]
        #[should_panic]
        fn cannot_set_key_size_too_big() {
            let mut key_vec = KeyVec::new();
            key_vec.change_keys_size(Key::BITS as usize + 1);
        }

        #[test]
        fn can_set_key_size_to_max() {
            let mut key_vec = KeyVec::new();
            key_vec.change_keys_size(Key::BITS as usize);
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

        /// Creates a `KeyAllocator` that considers the key value `0` as allocated already.
        ///
        /// Does not allocate now,
        /// allocations are done at some point if necessary after at least one key deallocation.
        pub(crate) fn with_zero_already_allocated() -> Self {
            Self {
                sparse_vec: Vec::new(),
                range_start: 1,
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

mod view_to_owned {
    /// Trait that can be implemented for both types of a type pair (R, O)
    /// where R is a reference-like or view-like type
    /// that refers to the content of the type O, whereas O owns its data.
    ///
    /// A method that takes an `impl ViewToOwned<O>` can thus take either
    /// an owned O or an R.
    /// The method can always compare the argument's data for equality with other `&O`s
    /// via [`ViewToOwned::eq`] (a bit specific, this is needed by this crate).
    /// If the method happens to need to take ownership of the argument as an O,
    /// it can via [`ViewToOwned::into_owned`] and it will only do work to construct
    /// an O(wned) version if it was not already owned.
    ///
    /// This allows to get the best of both worlds in the ref vs owned argument tradeoff
    /// and this crate happens to need to be able to do this.
    pub trait ViewToOwned<T>
    where
        T: Eq,
    {
        /// Make sure we own the result, doing some work only if needed.
        fn into_owned(self) -> T;

        /// Compare just like `PartialEq::eq` with `Eq`'s guarentees.
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

pub enum BorrowedOrOwned<'a, T> {
    Borrowed(&'a T),
    Owned(T),
}

impl<'a, T> BorrowedOrOwned<'a, T> {
    /// Get a reference even if `Owned`.
    #[allow(clippy::should_implement_trait)] // `Option` has its own `as_ref`, it's ok!
    pub fn as_ref(&'a self) -> &'a T {
        match self {
            BorrowedOrOwned::Borrowed(borrowed) => borrowed,
            BorrowedOrOwned::Owned(owned) => owned,
        }
    }
}

/// Shortens the use of [`BorrowedOrOwned::as_ref`] on `Option<BorrowedOrOwned<T>>`.
///
/// `palvec.pop().as_ref().map(BorrowedOrOwned::as_ref)` can be shortened to
/// `palvec.pop().map_as_ref()`.
pub trait OptionBorrowedOrOwned<'a, T> {
    /// Is the same as `self.as_ref().map(BorrowedOrOwned::as_ref)`.
    fn map_as_ref(&'a self) -> Option<&'a T>;
}

impl<'a, T> OptionBorrowedOrOwned<'a, T> for Option<BorrowedOrOwned<'a, T>> {
    fn map_as_ref(&'a self) -> Option<&'a T> {
        self.as_ref().map(BorrowedOrOwned::as_ref)
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
        assert_eq!(palvec.pop().map_as_ref(), Some(&5));
        assert_eq!(palvec.pop().map_as_ref(), Some(&8));
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
