use std::{fmt::Debug, ops::Not};

use crate::key_vec::KeyVec;

/// Types that a palette can use as keys implement this trait.
///
/// Using different types for different kinds of keys instead of just `usize`
/// allows for better type safety and prevents mixed key bugs.
pub(crate) trait PaletteKeyType: Debug + Clone + Copy + PartialEq + Eq {
    fn with_value(value: usize) -> Self;
    fn value(self) -> usize;
}

/// Key type that is used for common elements, used by the `KeyVec`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Key {
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
            value: (usize::MAX << keys_size).not(),
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
/// Such keys are not present in the `KeyVec`, but they are present in the index map
/// to access the right outlier element in the outlier palette given the index.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Opsk {
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
pub(crate) trait PaletteKeyAllocator<K> {
    fn can_allocate(&self, key: K) -> bool;
    fn palette_allocate(&mut self, key: K);
}

/// Used when allocating a `Key`.
///
/// Makes sure the `KeyVec` can contain the allocated key.
///
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
        assert_eq!(Key::with_value(0).min_size(), 0);
        assert_eq!(Key::with_value(1).min_size(), 1);
        assert_eq!(Key::with_value(2).min_size(), 2);
        assert_eq!(Key::with_value(3).min_size(), 2);
        assert_eq!(Key::with_value(4).min_size(), 3);
    }

    #[test]
    fn keys_size_for_this_many_keys_values() {
        assert_eq!(keys_size_for_this_many_keys(0), 0);
        assert_eq!(keys_size_for_this_many_keys(1), 0);
        assert_eq!(keys_size_for_this_many_keys(2), 1);
        assert_eq!(keys_size_for_this_many_keys(3), 2);
        assert_eq!(keys_size_for_this_many_keys(4), 2);
        assert_eq!(keys_size_for_this_many_keys(5), 3);
    }

    #[test]
    fn key_max_values_given_size() {
        assert_eq!(Key::max_that_fits_in_size(0).value, 0);
        assert_eq!(Key::max_that_fits_in_size(1).value, 1);
        assert_eq!(Key::max_that_fits_in_size(2).value, 0b11);
        assert_eq!(Key::max_that_fits_in_size(3).value, 0b111);
        assert_eq!(Key::max_that_fits_in_size(4).value, 0b1111);
    }
}
