use std::fmt::Debug;

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
    /// Returns the minimal size (in bits) that any representation of the given key can fit in.
    pub(crate) fn min_size(self) -> usize {
        self.value.checked_ilog2().map(|size| size + 1).unwrap_or(0) as usize
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
    fn palette_allocate(self, key: K);
}

/// Used when allocating a `Key`. Makes sure the `KeyVec` can contain the allocated key.
pub(crate) struct KeyAllocator<'a> {
    pub(crate) key_vec: &'a mut KeyVec,
}

impl<'a> PaletteKeyAllocator<Key> for KeyAllocator<'a> {
    #[inline]
    fn palette_allocate(self, key: Key) {
        self.key_vec.make_sure_a_key_fits(key);
    }
}

/// Used when allocating an `Opsk` (Outlier Palette Side Key)
pub(crate) struct OpskAllocator;

impl PaletteKeyAllocator<Opsk> for OpskAllocator {
    #[inline]
    fn palette_allocate(self, _key: Opsk) {}
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
}
