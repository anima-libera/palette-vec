//! Key types. A key is an index in a palette (most of the time).
//!
//! The use of keys by `PalVec` is a lot simpler than by `OutPalVec`.
//!
//! Here is an overview of what uses which kind of keys:
//! - `PalVec` only deal with `Key`s.
//! - `OutPalVec` deals with both `Key`s and `Opsk`s because it has two different palettes
//!   which have very different roles and their keys shall not be mixed or confused together.
//! - `KeyVec` is a bit-packed array of `Key`s, not quite a `Vec<Key>` but it acts like it
//!   (as far as needed by the scope of this crate) and its API takes and returns `Key`s.
//! - `IndexMap` is a memory-tight map of indices to `Opsk`s, not quite a `HashMap<usize, Opsk>`
//!   but it acts like it (as far as needed by the scope of this crate)
//!   and its API takes and returns `Opsk`s.
//! - `Palette<K>` is generic over its key type, `K` can be `Key` or `Opsk`, but then it
//!   only deals with `K` and never with the other key type, its API takes and returns `K`s.
//!   It is as such to allow `OutPalVec` to have its two palettes that do not mix their key types.

use std::{fmt::Debug, ops::Not};

use crate::key_vec::KeyVec;

/// Types that a palette can use as keys implement this trait.
///
/// Using different types for different kinds of keys instead of just `usize`
/// allows for better type safety and prevents mixed key bugs.
pub trait PaletteKeyType: Debug + Clone + Copy + PartialEq + Eq {
    fn with_value(value: usize) -> Self;
    fn value(self) -> usize;
}

/// Key type that is used for common elements, used by the `KeyVec`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Key {
    pub(crate) value: usize,
}

impl Key {
    /// Maximum number of bits that can ever be required to represent a key value.
    pub(crate) const MAX_SIZE: usize = usize::BITS as usize;

    /// Returns the minimal size (in bits) that any representation of the given key can fit in.
    pub(crate) fn min_size(self) -> usize {
        self.value.checked_ilog2().map(|size| size + 1).unwrap_or(0) as usize
    }

    /// Returns the higest key value that can fit in the given key size (in bits).
    pub(crate) fn max_that_fits_in_size(keys_size: usize) -> Key {
        Key {
            value: (usize::MAX.checked_shl(keys_size as u32).unwrap_or(0)).not(),
        }
    }
}

impl PaletteKeyType for Key {
    #[inline]
    fn with_value(value: usize) -> Key {
        Key { value }
    }

    #[inline]
    fn value(self) -> usize {
        self.value
    }
}

/// Returns the minimal size (in bits) of key representation
/// needed to support this many key values.
pub(crate) fn keys_size_for_this_many_keys(how_many: usize) -> usize {
    if let Some(max_key_value) = how_many.checked_sub(1) {
        Key::with_value(max_key_value).min_size()
    } else {
        0
    }
}

/// OPSK means Outlier Palette Side Key,
/// it represents a key of an outlier element.
///
/// Such keys are not present in the `KeyVec`, but they are present in the index map
/// to access the right outlier element in the outlier palette given the index.
/// Hence the name (these are keys that are only used on the side of the outlier palette,
/// the `KeyVec` and common palette never see such keys).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Opsk {
    pub(crate) value: usize,
}

impl PaletteKeyType for Opsk {
    #[inline]
    fn with_value(value: usize) -> Opsk {
        Opsk { value }
    }

    #[inline]
    fn value(self) -> usize {
        self.value
    }
}

/// When a palette allocates a new key, a part of the allocation work cannot be done by the palette
/// and is done instead by a type that implements this trait.
///
/// This does key-type-specific work.
pub(crate) trait PaletteKeyAllocator<K> {
    fn can_allocate(&self, key: K) -> bool;
    fn palette_allocate(&mut self, key: K);
}

/// Used when allocating a `Key`.
///
/// Makes sure the `KeyVec` can contain the allocated key.
/// Also disallow the allocation of a reserved key, used as the outlier key by the `OutPalVec`.
pub(crate) struct KeyAllocator<'a> {
    pub(crate) key_vec: &'a mut KeyVec,
    pub(crate) reserved_key: Option<Key>,
}

impl<'a> PaletteKeyAllocator<Key> for KeyAllocator<'a> {
    #[inline]
    fn can_allocate(&self, key: Key) -> bool {
        !(Some(key) == self.reserved_key)
    }

    #[inline]
    fn palette_allocate(&mut self, key: Key) {
        self.key_vec.make_sure_a_key_fits(key)
    }
}

/// Used when allocating an `Opsk` (Outlier Palette Side Key)
pub(crate) struct OpskAllocator;

impl PaletteKeyAllocator<Opsk> for OpskAllocator {
    #[inline]
    fn can_allocate(&self, _key: Opsk) -> bool {
        true
    }

    #[inline]
    fn palette_allocate(&mut self, _key: Opsk) {}
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn key_min_size_values() {
        fn min_size(key_value: usize) -> usize {
            Key::with_value(key_value).min_size()
        }

        assert_eq!(min_size(0), 0);
        assert_eq!(min_size(1), 1);

        // for i in range(2, 64+1):
        //  print(f"assert_eq!(min_size({2**(i-1)}), {i}); assert_eq!(min_size({(2**i)-1}), {i});")
        assert_eq!(min_size(2), 2);
        assert_eq!(min_size(3), 2);
        assert_eq!(min_size(4), 3);
        assert_eq!(min_size(7), 3);
        assert_eq!(min_size(8), 4);
        assert_eq!(min_size(15), 4);
        assert_eq!(min_size(16), 5);
        assert_eq!(min_size(31), 5);
        assert_eq!(min_size(32), 6);
        assert_eq!(min_size(63), 6);
        assert_eq!(min_size(64), 7);
        assert_eq!(min_size(127), 7);
        // ...
        assert_eq!(min_size(2305843009213693952), 62);
        assert_eq!(min_size(4611686018427387903), 62);
        assert_eq!(min_size(4611686018427387904), 63);
        assert_eq!(min_size(9223372036854775807), 63);
        assert_eq!(min_size(9223372036854775808), 64);
        assert_eq!(min_size(18446744073709551615), 64);
    }

    #[test]
    fn key_max_values_given_size() {
        assert_eq!(Key::max_that_fits_in_size(0).value, 0);
        assert_eq!(Key::max_that_fits_in_size(1).value, 0b1);
        assert_eq!(Key::max_that_fits_in_size(2).value, 0b11);
        assert_eq!(Key::max_that_fits_in_size(3).value, 0b111);
        assert_eq!(Key::max_that_fits_in_size(4).value, 0b1111);
        assert_eq!(Key::max_that_fits_in_size(5).value, 0b11111);
        assert_eq!(Key::max_that_fits_in_size(6).value, 0b111111);
        assert_eq!(Key::max_that_fits_in_size(7).value, 0b1111111);
        // ...
        assert_eq!(Key::max_that_fits_in_size(61).value, usize::MAX >> 3);
        assert_eq!(Key::max_that_fits_in_size(62).value, usize::MAX >> 2);
        assert_eq!(Key::max_that_fits_in_size(63).value, usize::MAX >> 1);
        assert_eq!(Key::max_that_fits_in_size(64).value, usize::MAX);
    }

    #[test]
    fn keys_size_for_this_many_keys_values() {
        fn size_for(this_many_keys: usize) -> usize {
            keys_size_for_this_many_keys(this_many_keys)
        }

        assert_eq!(size_for(0), 0);
        assert_eq!(size_for(1), 0);
        assert_eq!(size_for(2), 1);

        // for i in range(2, 64+1-1):
        //  print(f"assert_eq!(size_for({2**(i-1)+1}), {i}); assert_eq!(size_for({2**i}), {i});")
        assert_eq!(size_for(3), 2);
        assert_eq!(size_for(4), 2);
        assert_eq!(size_for(5), 3);
        assert_eq!(size_for(8), 3);
        assert_eq!(size_for(9), 4);
        assert_eq!(size_for(16), 4);
        assert_eq!(size_for(17), 5);
        assert_eq!(size_for(32), 5);
        assert_eq!(size_for(33), 6);
        assert_eq!(size_for(64), 6);
        assert_eq!(size_for(65), 7);
        assert_eq!(size_for(128), 7);
        // ...
        assert_eq!(size_for(1152921504606846977), 61);
        assert_eq!(size_for(2305843009213693952), 61);
        assert_eq!(size_for(2305843009213693953), 62);
        assert_eq!(size_for(4611686018427387904), 62);
        assert_eq!(size_for(4611686018427387905), 63);
        assert_eq!(size_for(9223372036854775808), 63);

        // Beware not to use a literal that would equal `usize::MAX + 1` if it could.
        assert_eq!(size_for(9223372036854775809), 64);
        assert_eq!(size_for(18446744073709551615), 64);
    }

    #[test]
    fn key_allocator() {
        let some_key = Key::with_value(9);

        let mut key_vec = KeyVec::new();
        assert!(!key_vec.does_this_key_fit(some_key));

        let mut key_allocator = KeyAllocator {
            key_vec: &mut key_vec,
            reserved_key: Some(Key::with_value(6)),
        };

        assert!(key_allocator.can_allocate(Key::with_value(0)));
        assert!(key_allocator.can_allocate(Key::with_value(1)));
        assert!(key_allocator.can_allocate(Key::with_value(5)));
        assert!(!key_allocator.can_allocate(Key::with_value(6)));
        assert!(key_allocator.can_allocate(Key::with_value(7)));

        key_allocator.palette_allocate(some_key);
        assert!(key_vec.does_this_key_fit(some_key));
    }
}
