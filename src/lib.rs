use std::{collections::HashMap, num::NonZero};

use bitvec::vec::BitVec;
use fxhash::FxHashMap;

type Key = u32;

// TODO: Doc!
pub struct PalVec<E> {
    /// An array of keys, each being represented with `key_size_in_bits` bits exactly,
    /// without padding between keys (so they are probably not byte-aligned).
    key_vec: BitVec,
    /// All keys in `key_vec` are represented with exactly this size.
    /// Cannot be zero.
    key_size_in_bits: NonZero<usize>,
    /// Each key in `key_vec` is a key into this table to refer to the element it represents.
    /// Accessing index `i` of a `PalVec` will really access `palette[key_vec[i]]`.
    palette: FxHashMap<Key, E>,
    /// Always sorted (ascending order).
    /// All the possible keys above the higest member are also available.
    /// If empty, then it is treated as if it were `vec![0]`.
    available_palette_keys: Vec<Key>,
}

impl<E> PalVec<E> {
    /// Creates an empty `PalVec`.
    ///
    /// Does not allocate now,
    /// allocations are done when content is added to it or is is told to reserve memory.
    pub fn new() -> Self {
        Self {
            key_vec: BitVec::new(),
            key_size_in_bits: unsafe {
                // SAFETY: 1 is not 0
                NonZero::new_unchecked(1)
            },
            palette: HashMap::default(),
            available_palette_keys: vec![],
        }
    }

    pub fn len(&self) -> usize {
        self.key_vec.len() / self.key_size_in_bits
    }

    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
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
        let palvec: PalVec<i32> = PalVec::new();
        assert!(palvec.is_empty());
        assert_eq!(palvec.len(), 0);
    }
}
