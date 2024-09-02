//! Map type that maps indices to [`Opsk`]s, but optimized for minimal memory usage.

// Note: There is no `u8` variant, this is because palette vectors of length below 256
// are so small that it probably doesn't make a difference to optimize the index map
// of such OutPalVec more than by using `u16`s.

use crate::key::{Opsk, PaletteKeyType};

pub(crate) struct IndexMap {
    inner: IndexMapEnum,
}
enum IndexMapEnum {
    U16(IndexMapSized<u16>),
    U32(IndexMapSized<u32>),
    U64(IndexMapSized<u64>),
}

impl IndexMap {
    pub(crate) fn new() -> IndexMap {
        IndexMap {
            inner: IndexMapEnum::U16(IndexMapSized::new()),
        }
    }

    pub(crate) fn set(&mut self, index_in_key_vec: usize, opsk: Opsk) {
        match &mut self.inner {
            IndexMapEnum::U16(map_sized_u16) => {
                let max = index_in_key_vec.max(opsk.value);
                if (u16::MAX as usize) < max {
                    self.grow_to_accomodate(max);
                    // Re-run the match, it is no longer u16.
                    // This is a super rare path so it is ok if it is dumb.
                    self.set(index_in_key_vec, opsk);
                    return;
                }
                map_sized_u16.set(index_in_key_vec as u16, opsk.value as u16);
            }
            IndexMapEnum::U32(map_sized_u32) => {
                let max = index_in_key_vec.max(opsk.value);
                if (u32::MAX as usize) < max {
                    self.grow_to_accomodate(max);
                    // Re-run the match, it is no longer u32.
                    // This is a super rare path so it is ok if it is dumb.
                    self.set(index_in_key_vec, opsk);
                    return;
                }
                map_sized_u32.set(index_in_key_vec as u32, opsk.value as u32);
            }
            IndexMapEnum::U64(map_sized_u64) => {
                map_sized_u64.set(index_in_key_vec as u64, opsk.value as u64);
            }
        }
    }

    pub(crate) fn get(&self, index_in_key_vec: usize) -> Option<Opsk> {
        match &self.inner {
            IndexMapEnum::U16(map_sized_u16) => {
                let index_in_key_vec: u16 = index_in_key_vec.try_into().ok()?;
                map_sized_u16
                    .get(index_in_key_vec)
                    .map(|opsk_value| Opsk::with_value(opsk_value as usize))
            }
            IndexMapEnum::U32(map_sized_u32) => {
                let index_in_key_vec: u32 = index_in_key_vec.try_into().ok()?;
                map_sized_u32
                    .get(index_in_key_vec)
                    .map(|opsk_value| Opsk::with_value(opsk_value as usize))
            }
            IndexMapEnum::U64(map_sized_u64) => map_sized_u64
                .get(index_in_key_vec as u64)
                .map(|opsk_value| Opsk::with_value(opsk_value as usize)),
        }
    }

    fn grow_to_accomodate(&mut self, to_what_number: usize) {
        let empty_map = IndexMapEnum::U16(IndexMapSized { vec: vec![] });
        let map = std::mem::replace(&mut self.inner, empty_map);
        match map {
            IndexMapEnum::U16(map_sized_u16) => {
                if to_what_number <= (u16::MAX as usize) {
                    panic!("Bug: grow_to_accomodate called when unnecessary");
                } else if to_what_number <= (u32::MAX as usize) {
                    self.inner = IndexMapEnum::U32(IndexMapSized::from_other_map(map_sized_u16));
                } else {
                    self.inner = IndexMapEnum::U64(IndexMapSized::from_other_map(map_sized_u16));
                }
            }
            IndexMapEnum::U32(map_sized_u32) => {
                if to_what_number <= (u32::MAX as usize) {
                    panic!("Bug: grow_to_accomodate called when unnecessary");
                } else {
                    self.inner = IndexMapEnum::U64(IndexMapSized::from_other_map(map_sized_u32));
                }
            }
            IndexMapEnum::U64(_map_sized_u64) => {
                panic!("Bug: grow_to_accomodate called when unnecessary");
            }
        }
    }
}

trait NumberType
where
    Self: Clone + Copy + Ord + TryFrom<usize>,
{
    const IS_U64: bool;
}
impl NumberType for u16 {
    const IS_U64: bool = false;
}
impl NumberType for u32 {
    const IS_U64: bool = false;
}
impl NumberType for u64 {
    const IS_U64: bool = true;
}

struct IndexMapEntry<N>
where
    N: NumberType,
{
    index_in_key_vec: N,
    opsk_value: N,
}

struct IndexMapSized<N>
where
    N: NumberType,
{
    vec: Vec<IndexMapEntry<N>>,
}

impl<N> IndexMapSized<N>
where
    N: NumberType,
{
    fn new() -> IndexMapSized<N> {
        IndexMapSized { vec: vec![] }
    }

    fn from_other_map<M>(other_map: IndexMapSized<M>) -> IndexMapSized<N>
    where
        M: NumberType,
        N: TryFrom<M>,
        <N as TryFrom<M>>::Error: std::fmt::Debug,
    {
        let mut map: IndexMapSized<N> = IndexMapSized {
            vec: Vec::with_capacity(other_map.vec.capacity()),
        };
        for entry in other_map.vec.into_iter() {
            map.vec.push(IndexMapEntry {
                index_in_key_vec: entry.index_in_key_vec.try_into().unwrap(),
                opsk_value: entry.opsk_value.try_into().unwrap(),
            });
        }
        map
    }

    fn set(&mut self, index_in_key_vec: N, opsk_value: N) {
        let index_in_map = self
            .vec
            .binary_search_by_key(&index_in_key_vec, |entry| entry.index_in_key_vec);
        match index_in_map {
            Ok(index_in_map) => {
                self.vec[index_in_map].opsk_value = opsk_value;
            }
            Err(index_in_map) => {
                self.vec.insert(
                    index_in_map,
                    IndexMapEntry {
                        index_in_key_vec,
                        opsk_value,
                    },
                );
            }
        }
    }

    fn get(&self, index_in_key_vec: N) -> Option<N> {
        let index_in_map = self
            .vec
            .binary_search_by_key(&index_in_key_vec, |entry| entry.index_in_key_vec)
            .ok()?;
        Some(self.vec[index_in_map].opsk_value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn access_empty_returns_none() {
        let index_map = IndexMap::new();
        assert_eq!(index_map.get(0), None);
    }

    #[test]
    fn set_and_get() {
        let mut index_map = IndexMap::new();
        index_map.set(0, Opsk::with_value(0));
        index_map.set(1, Opsk::with_value(1));
        index_map.set(2, Opsk::with_value(50));
        index_map.set(70, Opsk::with_value(50));
        index_map.set(3, Opsk::with_value(50));
        index_map.set(8, Opsk::with_value(100));
        assert_eq!(index_map.get(0), Some(Opsk::with_value(0)));
        assert_eq!(index_map.get(1), Some(Opsk::with_value(1)));
        assert_eq!(index_map.get(2), Some(Opsk::with_value(50)));
        assert_eq!(index_map.get(3), Some(Opsk::with_value(50)));
        assert_eq!(index_map.get(8), Some(Opsk::with_value(100)));
        assert_eq!(index_map.get(70), Some(Opsk::with_value(50)));
        assert_eq!(index_map.get(4), None);
        assert_eq!(index_map.get(69), None);
        assert_eq!(index_map.get(71), None);
    }

    #[test]
    fn doesnt_grow_if_not_needed() {
        let mut index_map = IndexMap::new();
        index_map.set(0, Opsk::with_value(0));
        index_map.set(u16::MAX as usize, Opsk::with_value(u16::MAX as usize));
        assert_eq!(index_map.get(0), Some(Opsk::with_value(0)));
        assert_eq!(
            index_map.get(u16::MAX as usize),
            Some(Opsk::with_value(u16::MAX as usize))
        );
        assert_eq!(index_map.get(1), None);
        assert_eq!(index_map.get(u16::MAX as usize - 1), None);
        assert!(matches!(index_map.inner, IndexMapEnum::U16(_)));
    }

    #[test]
    fn grows_if_needed() {
        let mut index_map = IndexMap::new();
        index_map.set(0, Opsk::with_value(0));
        index_map.set(u16::MAX as usize, Opsk::with_value(u16::MAX as usize));
        assert_eq!(index_map.get(0), Some(Opsk::with_value(0)));
        assert_eq!(
            index_map.get(u16::MAX as usize),
            Some(Opsk::with_value(u16::MAX as usize))
        );
        assert_eq!(index_map.get(1), None);
        assert_eq!(index_map.get(u16::MAX as usize - 1), None);
        assert!(matches!(index_map.inner, IndexMapEnum::U16(_)));

        index_map.set(u16::MAX as usize + 1, Opsk::with_value(42));
        assert!(matches!(index_map.inner, IndexMapEnum::U32(_)));
        assert_eq!(index_map.get(0), Some(Opsk::with_value(0)));
        assert_eq!(
            index_map.get(u16::MAX as usize),
            Some(Opsk::with_value(u16::MAX as usize))
        );
        assert_eq!(index_map.get(1), None);
        assert_eq!(index_map.get(u16::MAX as usize - 1), None);
        assert_eq!(
            index_map.get(u16::MAX as usize + 1),
            Some(Opsk::with_value(42))
        );
        index_map.set(u32::MAX as usize, Opsk::with_value(u32::MAX as usize));
        assert!(matches!(index_map.inner, IndexMapEnum::U32(_)));

        index_map.set(u32::MAX as usize + 1, Opsk::with_value(3));
        assert!(matches!(index_map.inner, IndexMapEnum::U64(_)));
        assert_eq!(index_map.get(0), Some(Opsk::with_value(0)));
        assert_eq!(
            index_map.get(u32::MAX as usize + 1),
            Some(Opsk::with_value(3))
        );
    }
}
