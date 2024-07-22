pub type Key = usize;

/// Returns the minimal size (in bits) that any representation of the given key can fit in.
pub(crate) fn key_min_size(key: Key) -> usize {
    key.checked_ilog2().map(|size| size + 1).unwrap_or(0) as usize
}
