use std::{
    cmp::Ordering,
    mem::ManuallyDrop,
    ops::{DerefMut, Range},
};

use bitvec::{field::BitField, order::Lsb0, slice::BitSlice, vec::BitVec, view::BitViewSized};

use crate::key::{key_min_size, Key};

/// An array of keys, each being represented with [`Self::keys_size()`] bits exactly,
/// without padding between keys (so they are probably not byte-aligned).
///
/// Supports a `keys_size` of zero, which doesn't allocate and only support the key value `0`.
pub struct KeyVec {
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
                    let vec_len_in_bits = self.vec_or_len.vec.len();
                    self.vec_or_len
                        .vec
                        .deref_mut()
                        .truncate(vec_len_in_bits - self.keys_size);
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
                            // Move the key to its new position and
                            // represent it with the new key size
                            // (which is bigger than the old key size so we know the key fits).
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

    /// Calls `change_keys_size` if required to make sure
    /// that the given key can be used in the `KeyVec`.
    pub(crate) fn make_sure_a_key_fits(&mut self, key: Key) {
        let min_size = key_min_size(key);
        let does_it_already_fit = min_size <= self.keys_size();
        if does_it_already_fit {
            // It already fits, nothing to do.
        } else {
            // Properly making `keys_size` bigger so that the new key fits.
            self.change_keys_size(min_size);
        }
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
