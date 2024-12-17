//! `KeyVec` type! It is a bit-packed array of `Key`s.

use std::{
    cmp::Ordering,
    fmt::Debug,
    mem::ManuallyDrop,
    ops::{DerefMut, Range},
};

use bitvec::{field::BitField, order::Lsb0, slice::BitSlice, vec::BitVec, view::BitViewSized};

use crate::key::{Key, PaletteKeyType};

/// An array of `Key`s, each being represented with [`Self::keys_size()`] bits exactly,
/// without padding between keys (so they are probably not byte-aligned).
///
/// Supports a `keys_size` of zero,
/// which doesn't allocate any array and only support the key value `0`.
pub(crate) struct KeyVec {
    /// The size in bits of the memory representation of each key in `vec_or_len.vec`.
    ///
    /// It is always less-than-or-equal-to `Key`'s size in bits.
    keys_size: usize,
    vec_or_len: BitVecOrLen,
}

/// - When `keys_size` is non-zero, then `vec` is the active field.
/// - When `keys_size` is zero, then `len` is the active field.
union BitVecOrLen {
    /// The array of keys, keys are alligned on `keys_size` bits.
    /// The key at index `i` occupies the bit range `KeyVec::key_bit_range(self.keys_size, i)`.
    ///
    /// The number of live bits in the `BitVec` is always a multiple of `keys_size`.
    vec: ManuallyDrop<BitVec<usize, Lsb0>>,
    /// When `keys_size` is zero (0), then there is no allocation to be done,
    /// there is only the length of an imaginary vec of zero-sized elements,
    /// which are all the key value `0` represented with 0 bits.
    len: usize,
}

pub enum BrokenInvariantInKeyVec {
    /// The KeyVec's `keys_size` is bigger than `Key::MAX_SIZE`.
    ///
    /// Key values passed around and manipulated outside of the KeyVec's bit-packed array of keys
    /// are all represented with the `Key` type. It does not make sense for the KeyVec to pretend
    /// to be able to hold key values that can't even fit in a `Key`.
    KeysSizeBiggerThanMaxPossibleSize { keys_size: usize },
    /// The KeyVec's length (in bits) of its bit array is not a multiple of `keys_size`.
    ///
    /// The KeyVec's bit array is just a way to represent an array of bit-packed values that all
    /// have a size of `keys_size` in bits. Let `N` be the number of keys in the KeyVec,
    /// then there are `N * keys_size` bits in the bit array to represent these `N` keys.
    /// It does not make sense to have a number of bits that is not a multiple of `keys_size`.
    BitArrayLengthNotAMultipleOfKeysSize {
        length_in_bits: usize,
        keys_size: usize,
    },
}

impl KeyVec {
    /// Returns `Err` if it is detected that an invariant is not respected,
    /// meaning that this `Self` is not in a valid state, it is corrupted.
    ///
    /// Safe methods used on a valid `Self`s (if input is needed)
    /// and that terminate without panicking
    /// shall leave `Self` in a valid state,
    /// if that does not happen then the method has a bug.
    pub(crate) fn check_invariants(&self) -> Result<(), BrokenInvariantInKeyVec> {
        if Key::MAX_SIZE < self.keys_size {
            return Err(BrokenInvariantInKeyVec::KeysSizeBiggerThanMaxPossibleSize {
                keys_size: self.keys_size,
            });
        }

        if 0 < self.keys_size {
            // SAFETY: `keys_size` is not zero so `vec` is active.
            let length_in_bits = unsafe { self.vec_or_len.vec.len() };
            if length_in_bits % self.keys_size != 0 {
                return Err(
                    BrokenInvariantInKeyVec::BitArrayLengthNotAMultipleOfKeysSize {
                        length_in_bits,
                        keys_size: self.keys_size,
                    },
                );
            }
        }

        Ok(())
    }
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
            Some({
                // SAFETY: `index < self.len()`.
                unsafe { self.get_unchecked(index) }
            })
        } else {
            None
        }
    }

    /// Returns the key at the given index in the `KeyVec`.
    ///
    /// # Safety
    ///
    /// `index` must be `< self.len()`.
    pub(crate) unsafe fn get_unchecked(&self, index: usize) -> Key {
        debug_assert!(index <= self.len());
        if self.keys_size == 0 {
            // Only possible key value when `keys_size` is zero.
            Key::with_value(0)
        } else {
            let bit_range = Self::key_bit_range(self.keys_size, index);
            debug_assert!(bit_range.end <= self.vec_or_len.vec.len());
            Key::with_value(self.vec_or_len.vec[bit_range].load())
        }
    }

    /// Overwrites the key at the given `index` with the given `key`.
    ///
    /// # Panics
    ///
    /// Panics if `index` is out of bounds.
    ///
    /// Panics if `key_min_size(key)` is not `<= self.keys_size()`.
    pub(crate) fn set(&mut self, index: usize, key: Key) {
        if index < self.len() {
            let key_min_size = key.min_size();
            if key_min_size <= self.keys_size {
                // SAFETY: The index is in bounds and the key fits.
                unsafe { self.set_unchecked(index, key) }
            } else {
                // The key doesn't fit, `keys_size` is too small.
                panic!(
                    "key min size (is {} bits) should be <= keys_size (is {})",
                    key_min_size, self.keys_size,
                );
            }
        } else {
            // Style of panic message inspired form the one in
            // https://doc.rust-lang.org/std/vec/struct.Vec.html#method.swap_remove
            panic!("set index (is {index}) should be < len (is {})", self.len());
        }
    }

    /// Sets the key at the given index to the given `key`.
    ///
    /// # Safety
    ///
    /// `index` must be `< self.len()`, and
    /// `key_min_size(key)` must be `<= self.keys_size()`.
    pub(crate) unsafe fn set_unchecked(&mut self, index: usize, key: Key) {
        debug_assert!(index <= self.len());
        if self.keys_size == 0 {
            // Nothing to do, `key` is zero since `key_min_size(key) == 0`.
            debug_assert_eq!(key, Key::with_value(0));
        } else {
            debug_assert!(key.min_size() <= self.keys_size);
            let bit_range = Self::key_bit_range(self.keys_size, index);
            debug_assert!(bit_range.end <= self.vec_or_len.vec.len());
            self.vec_or_len.vec.deref_mut()[bit_range].store(key.value);
        }
    }

    /// Appends the given `key` to the end of the `KeyVec`, `how_many` times.
    ///
    /// # Panics
    ///
    /// Panics if `key_min_size(key)` is not `<= self.keys_size()`.
    pub(crate) fn _push(&mut self, key: Key, how_many: usize) {
        let key_min_size = key.min_size();
        if key_min_size <= self.keys_size {
            // SAFETY: The key fits.
            unsafe { self.push_unchecked(key, how_many) }
        } else {
            // The key doesn't fit, `keys_size` is too small.
            panic!(
                "key min size (is {} bits) should be <= keys_size (is {})",
                key_min_size, self.keys_size,
            );
        }
    }

    /// Appends the given `key` to the end of the `KeyVec`, `how_many` times.
    ///
    /// # Safety
    ///
    /// `key_min_size(key)` must be `<= self.keys_size()`.
    pub(crate) unsafe fn push_unchecked(&mut self, key: Key, how_many: usize) {
        if self.keys_size == 0 {
            debug_assert_eq!(key, Key::with_value(0));
            // SAFETY: `keys_size` is zero so `len` is the active field.
            unsafe { self.vec_or_len.len += how_many }
        } else {
            debug_assert!(key.min_size() <= self.keys_size);
            self.vec_or_len
                .vec
                .deref_mut()
                .reserve(how_many * self.keys_size);
            for _ in 0..how_many {
                let key_le = key.value.to_le();
                let key_bits = key_le.as_raw_slice();
                let key_bits: &BitSlice<usize, Lsb0> = BitSlice::from_slice(key_bits);
                // `keys_size` is <= `Key`'s size in bits, this won't go out-of-bounds.
                let key_bits = &key_bits[0..self.keys_size];
                self.vec_or_len
                    .vec
                    .deref_mut()
                    .extend_from_bitslice(key_bits);
            }
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
                    Some(Key::with_value(0))
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
                    let new_len = self.len() - 1;
                    let new_len_in_bits = new_len * self.keys_size;
                    self.vec_or_len.vec.deref_mut().truncate(new_len_in_bits);
                    Some(last_key)
                }
            }
        }
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
    /// except it will now work with a different `keys_size`
    /// - either to accomodate for bigger key values,
    /// - or to save memory when the keys can all be represented on less bits.
    ///
    /// # Panics
    ///
    /// Panics if any contained key does not fit the given `new_keys_size`.
    ///
    /// Panics if `new_keys_size` is not `<= Key::MAX_SIZE`.
    pub(crate) fn change_keys_size(&mut self, new_keys_size: usize) {
        self.change_keys_size_internal::<false>(new_keys_size, |_index, _old_key| unreachable!());
    }

    /// Same as `change_keys_size`
    /// but also maps all the keys through the given `key_mapping` function
    /// as they are iterated over.
    pub(crate) fn change_keys_size_and_map_keys(
        &mut self,
        new_keys_size: usize,
        key_mapping: impl FnMut(usize, Key) -> Key,
    ) {
        self.change_keys_size_internal::<true>(new_keys_size, key_mapping);
    }

    /// See [`Self::change_keys_size`] and [`Self::change_keys_size_and_map_keys`].
    ///
    /// # Panics
    ///
    /// Panics if any key (after mapping if any) does not fit the given `new_keys_size`.
    ///
    /// Panics if `new_keys_size` is not `<= Key::MAX_SIZE`.
    fn change_keys_size_internal<const KEY_MAPPING_IS_USED: bool>(
        &mut self,
        new_keys_size: usize,
        mut key_mapping: impl FnMut(usize, Key) -> Key,
    ) {
        if Key::MAX_SIZE < new_keys_size {
            panic!(
                "new key size (is {} bits) should be <= `Key::MAX_SIZE` (is {})",
                new_keys_size,
                Key::MAX_SIZE
            );
        }
        if self.keys_size == 0 {
            if 0 < new_keys_size {
                // From `keys_size == 0` to `keys_size != 0`.
                // We have to switch the active field from `len` to `vec`.

                if KEY_MAPPING_IS_USED {
                    // TODO: Implement!
                    unimplemented!("change_keys_size from 0 to non-0 with a mapper");
                } else {
                    let len = {
                        // SAFETY: `keys_size` is still zero at this point.
                        unsafe { self.vec_or_len.len }
                    };
                    // All the key values are `0`, so all the bits shall be zeros.
                    self.vec_or_len = BitVecOrLen {
                        vec: ManuallyDrop::new(BitVec::repeat(false, len * new_keys_size)),
                    };
                    // `keys_size` is updated at the end of the function.
                }
            } else {
                // When `keys_size == 0` and `keys_size` does not change.

                if KEY_MAPPING_IS_USED {
                    // TODO: Maybe implement this?
                    // This is a bit of a stupid case, where we would do nothing
                    // but still have to check that for all the indices calls to
                    // `key_mapping.map_key(index, 0)` always return 0.
                    // This is not something that has any use, maybe paniking is good.
                    unimplemented!("change_keys_size from 0 to non-0 with a mapper");
                } else {
                    // Nothing to do.
                }
            }
        } else {
            match self.keys_size.cmp(&new_keys_size) {
                Ordering::Equal => {
                    // When `keys_size != 0` and `keys_size` does not change.

                    if KEY_MAPPING_IS_USED {
                        // TODO: Implement!
                        unimplemented!("change_keys_size when the non-0");
                    } else {
                        // Nothing to do.
                    }
                }
                Ordering::Less => {
                    // When `keys_size != 0` and the `keys_size` has to increase.

                    let old_keys_size = self.keys_size;
                    let len = self.len();
                    // SAFETY: `keys_size` is non-zero so `vec` is the active field.
                    unsafe {
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
                        // The growing reigion of `≈index` newly resized keys at the end
                        // and the shrinking reigion of `≈len-index` yet-to-be-resized keys
                        // at the start never overlap because we resized the vec
                        // to accomodate for the biggest size of the reigion with bigger keys.
                        for index in (0..len).rev() {
                            // Get the last not-yet moved key from its old position.
                            let old_key: Key = {
                                let bit_range = Self::key_bit_range(old_keys_size, index);
                                Key::with_value(self.vec_or_len.vec.deref_mut()[bit_range].load())
                            };
                            let new_key = if KEY_MAPPING_IS_USED {
                                key_mapping(index, old_key)
                            } else {
                                old_key
                            };
                            // Move the key to its new position and
                            // represent it with the new key size
                            // (which is bigger than the old key size so we know the key fits).
                            {
                                let bit_range = Self::key_bit_range(new_keys_size, index);
                                self.vec_or_len.vec.deref_mut()[bit_range].store(new_key.value);
                            }
                        }
                    }
                }
                Ordering::Greater => {
                    // When `keys_size != 0` and the `keys_size` has to decrease.

                    let old_keys_size = self.keys_size;
                    let len = self.len();
                    // SAFETY: `keys_size` is non-zero so `vec` is the active field.
                    unsafe {
                        for index in 0..len {
                            // Get the last not-yet moved key from its old position.
                            let old_key: Key = {
                                let bit_range = Self::key_bit_range(old_keys_size, index);
                                Key::with_value(self.vec_or_len.vec.deref_mut()[bit_range].load())
                            };
                            let new_key = if KEY_MAPPING_IS_USED {
                                key_mapping(index, old_key)
                            } else {
                                old_key
                            };
                            assert!(new_key.min_size() <= new_keys_size);
                            // Move the key to its new position and
                            // represent it with the new key size.
                            {
                                let bit_range = Self::key_bit_range(new_keys_size, index);
                                self.vec_or_len.vec.deref_mut()[bit_range].store(new_key.value);
                            }
                        }
                        self.vec_or_len
                            .vec
                            .deref_mut()
                            .resize(len * new_keys_size, false);
                    }
                }
            }
        }
        self.keys_size = new_keys_size;
    }

    /// Calls `change_keys_size` if required to make sure
    /// that the given key can be used in the `KeyVec`.
    pub(crate) fn make_sure_a_key_fits(&mut self, key: Key) {
        let min_size = key.min_size();
        let does_it_already_fit = min_size <= self.keys_size();
        if does_it_already_fit {
            // It already fits, nothing to do.
        } else {
            // Properly making `keys_size` bigger so that the new key fits.
            self.change_keys_size(min_size);
        }
    }

    /// Can the `KeyVec` hold a representation of the given key value
    /// without changing the `keys_size`?
    pub(crate) fn does_this_key_fit(&self, key: Key) -> bool {
        key.min_size() <= self.keys_size()
    }
}

impl Clone for KeyVec {
    fn clone(&self) -> Self {
        KeyVec {
            keys_size: self.keys_size,
            vec_or_len: if 0 == self.keys_size {
                BitVecOrLen {
                    len: {
                        // SAFETY: `keys_size` is zero so `len` is active.
                        unsafe { self.vec_or_len.len }
                    },
                }
            } else {
                BitVecOrLen {
                    vec: {
                        // SAFETY: `keys_size` is not zero so `vec` is active.
                        unsafe { self.vec_or_len.vec.clone() }
                    },
                }
            },
        }
    }
}

impl Debug for KeyVec {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let mut debug_list = f.debug_list();
        for index in 0..self.len() {
            debug_list.entry(&self.get(index).unwrap().value);
        }
        debug_list.finish()
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
        key_vec._push(Key::with_value(0), 1);
        assert_is_len(&key_vec, 1);
        key_vec._push(Key::with_value(0), 1);
        assert_is_len(&key_vec, 2);
        key_vec._push(Key::with_value(0), 1);
        assert_is_len(&key_vec, 3);
        key_vec._push(Key::with_value(0), 1);
        assert_is_len(&key_vec, 4);
        assert!(key_vec.check_invariants().is_ok());
    }

    #[test]
    fn key_size_nonzero_switches_to_vec() {
        let mut key_vec = KeyVec::new();
        assert_is_len(&key_vec, 0);
        key_vec._push(Key::with_value(0), 1);
        assert_is_len(&key_vec, 1);
        key_vec._push(Key::with_value(0), 1);
        assert_is_len(&key_vec, 2);
        key_vec.change_keys_size(1);
        assert_is_vec(&key_vec, 2);
        key_vec._push(Key::with_value(0), 1);
        assert_is_vec(&key_vec, 3);
        key_vec._push(Key::with_value(0), 1);
        assert_is_vec(&key_vec, 4);
        assert!(key_vec.check_invariants().is_ok());
    }

    #[test]
    fn can_push_max_key_for_any_size() {
        let mut key_vec = KeyVec::new();
        key_vec._push(Key::with_value(0), 1);
        for key_size in 1..=Key::MAX_SIZE {
            let mak_key_for_given_size = Key::with_value({
                let mut value = 0;
                for _i in 0..key_size {
                    value = (value << 1) | 1;
                }
                value
            });
            key_vec.change_keys_size(key_size);
            key_vec._push(mak_key_for_given_size, 1);
        }
        assert!(key_vec.check_invariants().is_ok());
    }

    #[test]
    #[should_panic]
    fn cannot_set_key_size_too_big() {
        let mut key_vec = KeyVec::new();
        key_vec.change_keys_size(Key::MAX_SIZE + 1);
    }

    #[test]
    fn can_set_key_size_to_max() {
        let mut key_vec = KeyVec::new();
        key_vec.change_keys_size(Key::MAX_SIZE);
        assert!(key_vec.check_invariants().is_ok());
    }

    #[test]
    fn push_many() {
        let mut key_vec = KeyVec::new();
        key_vec._push(Key::with_value(0), 1000);
        assert_eq!(key_vec.len(), 1000);
        key_vec.change_keys_size(1);
        key_vec._push(Key::with_value(1), 1000);
        assert_eq!(key_vec.len(), 2000);
        for i in 0..1000 {
            assert_eq!(key_vec.get(i), Some(Key::with_value(0)));
        }
        for i in 1000..2000 {
            assert_eq!(key_vec.get(i), Some(Key::with_value(1)));
        }
        assert!(key_vec.check_invariants().is_ok());
    }

    #[test]
    fn push_zero() {
        let mut key_vec = KeyVec::new();
        key_vec._push(Key::with_value(0), 0);
        assert_eq!(key_vec.len(), 0);
        key_vec.change_keys_size(1);
        key_vec._push(Key::with_value(1), 0);
        assert_eq!(key_vec.len(), 0);
        assert_eq!(key_vec.get(0), None);
        assert!(key_vec.check_invariants().is_ok());
    }
}
