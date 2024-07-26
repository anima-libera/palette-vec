use std::cmp::Ordering;

use crate::{
    key::{key_min_size, Key},
    key_vec::KeyVec,
};

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
pub struct KeyAllocator {
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

    /// Allocates the smallest unused key value.
    ///
    /// It is guarenteed that it will fit in `key_vec.keys_size()` bits,
    /// by properly increasing the `keys_size` of the given `key_vec` if necessary.
    pub(crate) fn allocate_and_make_sure_it_fits(&mut self, key_vec: &mut KeyVec) -> Key {
        let new_key = self.allocate();
        let min_size = key_min_size(new_key);
        let does_it_already_fit = min_size <= key_vec.keys_size();
        if does_it_already_fit {
            // It already fits, nothing to do.
        } else {
            // Properly making `keys_size` bigger so that the new key fits.
            key_vec.change_keys_size(min_size);
        }
        new_key
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
