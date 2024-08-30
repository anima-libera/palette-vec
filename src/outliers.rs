use std::{marker::PhantomData, num::NonZeroUsize, ops::Index};

use fxhash::FxHashMap;

use crate::{
    key::{Key, KeyAllocator, Opsk, OpskAllocator, PaletteKeyType},
    key_vec::KeyVec,
    palette::Palette,
    utils::view_to_owned::ViewToOwned,
    BorrowedOrOwned,
};

// TODO: Better doc!
pub struct OutPalVec<T, I = OutlierMemoryRatioIntervalDefault>
where
    T: Clone + Eq,
    I: OutlierMemoryRatioInterval,
{
    /// Instances of `outlier_key` are handled by the `index_to_opsk_map` and the `outlier_palette`
    /// and other keys are handled by `palette`.
    key_vec: KeyVec,
    /// Contains at most one `OutlierPalette`.
    palette: Palette<T, Key>,
    /// Is `None` iff the `outlier_palette` is empty.
    outlier_key: Option<Key>,
    outlier_palette: Palette<T, Opsk>,
    /// Exactly every instance of `outlier_key` in the `key_vec` has an entry here.
    ///
    /// TODO: Maybe provide an alternative to the hash map, like a sorted vec. This would
    /// allow to really get its memory usage smaller, and also to know its memory usage
    /// with precision, which enables the best possible memory usage optimization for this whole
    /// thing as we could think in terms of smaller memory usage to decide when to move elements
    /// between the outlier and common palettes.
    index_to_opsk_map: FxHashMap<usize, Opsk>,
    _phantom: PhantomData<T>,
    _phantom_interval: PhantomData<I>,
}

pub trait OutlierMemoryRatioInterval {
    const LOWER_LIMIT_WEAK: f32;
    const UPPER_LIMIT: f32;
}

pub struct OutlierMemoryRatioIntervalDefault;
impl OutlierMemoryRatioInterval for OutlierMemoryRatioIntervalDefault {
    const LOWER_LIMIT_WEAK: f32 = 0.013;
    const UPPER_LIMIT: f32 = 0.025;
}

impl<T, I> OutPalVec<T, I>
where
    T: Clone + Eq,
    I: OutlierMemoryRatioInterval,
{
    pub fn new() -> Self {
        Self {
            key_vec: KeyVec::new(),
            palette: Palette::new(),
            outlier_key: None,
            outlier_palette: Palette::new(),
            index_to_opsk_map: FxHashMap::default(),
            _phantom: PhantomData,
            _phantom_interval: PhantomData,
        }
    }

    pub fn with_len(element: T, len: usize) -> Self {
        if len == 0 {
            Self::new()
        } else {
            // `KeyVec::with_len` is filled with `0`s, and
            // `Palette::with_one_entry` associates the given entry to the key `0`,
            // so it matches.
            Self {
                key_vec: KeyVec::with_len(len),
                palette: Palette::with_one_entry(element, len),
                outlier_key: None,
                outlier_palette: Palette::new(),
                index_to_opsk_map: FxHashMap::default(),
                _phantom: PhantomData,
                _phantom_interval: PhantomData,
            }
        }
    }

    pub fn len(&self) -> usize {
        self.key_vec.len()
    }

    pub fn outlier_instance_count(&self) -> usize {
        self.index_to_opsk_map.len()
    }

    pub fn is_empty(&self) -> bool {
        self.key_vec.is_empty()
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        let key = self.key_vec.get(index)?;
        Some(if Some(key) == self.outlier_key {
            let opsk = *self
                .index_to_opsk_map
                .get(&index)
                .expect("Bug: Outlier key in `key_vec` but index not in index map");
            self.outlier_palette
                .get(opsk)
                .expect("Bug: Opsk in index map is not used by the palette")
        } else {
            self.palette
                .get(key)
                .expect("Bug: Key used in `key_vec` is not used by the palette")
        })
    }

    pub fn set(&mut self, index: usize, element: impl ViewToOwned<T>) {
        let is_in_bounds = index < self.len();
        if !is_in_bounds {
            panic!("set index (is {index}) should be < len (is {})", self.len());
        }

        // Remove previous element.
        let key_of_elemement_to_remove = {
            if self.key_vec.keys_size() == 0 {
                Key::with_value(0)
            } else {
                // SAFETY: We checked the bounds, we have `index < self.len()`.
                unsafe { self.key_vec.get_unchecked(index) }
            }
        };
        if Some(key_of_elemement_to_remove) == self.outlier_key {
            let opsk_of_elemement_to_remove = self
                .index_to_opsk_map
                .remove(&index)
                .expect("Bug: Outlier key in `key_vec` but index not in index map");
            self.outlier_palette
                .remove_element_instances(opsk_of_elemement_to_remove, {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                });
        } else {
            self.palette
                .remove_element_instances(key_of_elemement_to_remove, {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                });
        }

        // Add new element.
        let key_of_element_to_add = if self.palette.contains(&element) {
            // Already a common element.
            self.palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                },
            )
        } else {
            // Either a new element or an already outlier element.
            let opsk_of_element_to_add = self.outlier_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut OpskAllocator,
            );
            let previous_entry = self.index_to_opsk_map.insert(index, opsk_of_element_to_add);
            if previous_entry.is_some() {
                panic!("Bug: Index map entry was supposed to be unoccupied");
            }
            if self.outlier_key.is_none() {
                let outlier_key = self.palette.smallest_available_key(&KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                });
                self.key_vec.make_sure_a_key_fits(outlier_key);
                self.outlier_key = Some(outlier_key);
            }
            self.outlier_key.unwrap()
        };
        if self.key_vec.keys_size() == 0 {
            // Nothing to do here, all the keys have the same value of zero.
            debug_assert_eq!(key_of_element_to_add, Key::with_value(0));
        } else {
            // SAFETY: We checked the bounds, we have `index < self.len()`,
            // and `add_element_instances` made sure that the key fits.
            unsafe { self.key_vec.set_unchecked(index, key_of_element_to_add) }
        }

        self.enforce_upper_limit_on_outlier_ratio();
    }

    pub fn push(&mut self, element: impl ViewToOwned<T>) {
        // TODO: Factorize the duplicated code with `set`, there is a lot of it.

        let key_of_element_to_add = if self.palette.contains(&element) {
            // Already a common element.
            self.palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                },
            )
        } else {
            // Either a new element or an already outlier element.
            let opsk_of_element_to_add = self.outlier_palette.add_element_instances(
                element,
                {
                    // SAFETY: 1 is not 0.
                    unsafe { NonZeroUsize::new_unchecked(1) }
                },
                &mut OpskAllocator,
            );
            let previous_entry = self
                .index_to_opsk_map
                .insert(self.key_vec.len(), opsk_of_element_to_add);
            if previous_entry.is_some() {
                panic!("Bug: Index map entry was supposed to be unoccupied");
            }
            if self.outlier_key.is_none() {
                let outlier_key = self.palette.smallest_available_key(&KeyAllocator {
                    key_vec: &mut self.key_vec,
                    reserved_key: self.outlier_key,
                });
                self.key_vec.make_sure_a_key_fits(outlier_key);
                self.outlier_key = Some(outlier_key);
            }
            self.outlier_key.unwrap()
        };

        self.key_vec.push(key_of_element_to_add);

        self.enforce_upper_limit_on_outlier_ratio();
    }

    pub fn pop(&mut self) -> Option<BorrowedOrOwned<'_, T>> {
        // TODO: Is there too much duplicated code with `set`?

        self.key_vec.pop().map(|key_of_elemement_to_remove| {
            if Some(key_of_elemement_to_remove) == self.outlier_key {
                let opsk_of_elemement_to_remove = self
                    .index_to_opsk_map
                    .remove(&self.key_vec.len())
                    .expect("Bug: Outlier key in `key_vec` but index not in index map");
                self.outlier_palette
                    .remove_element_instances(opsk_of_elemement_to_remove, {
                        // SAFETY: 1 is not 0.
                        unsafe { NonZeroUsize::new_unchecked(1) }
                    })
            } else {
                self.palette
                    .remove_element_instances(key_of_elemement_to_remove, {
                        // SAFETY: 1 is not 0.
                        unsafe { NonZeroUsize::new_unchecked(1) }
                    })
            }
        })
    }

    fn move_most_numerous_outlier_to_common(&mut self) {
        let Some(opsk_to_move) = self.outlier_palette.key_of_most_instanced_element() else {
            return;
        };
        let palette_entry = self
            .outlier_palette
            .remove_entry(opsk_to_move)
            .expect("Bug: We just got this opsk for the outlier palette");
        if self.outlier_palette.len() == 0 {
            // There are no outliers anymore, we can make the outlier key available.
            self.outlier_key = None;
        }
        let new_key = self.palette.add_entry(
            palette_entry,
            &mut KeyAllocator {
                key_vec: &mut self.key_vec,
                reserved_key: self.outlier_key,
            },
        );
        self.index_to_opsk_map.retain(|index, opsk| {
            let remove = *opsk == opsk_to_move;
            if remove {
                self.key_vec.set(*index, new_key);
            }
            !remove
        });
    }

    fn outlier_ratio(&self) -> Option<f32> {
        let len = self.len();
        (len != 0).then(|| {
            let outlier_instance_count = self.outlier_instance_count();
            outlier_instance_count as f32 / len as f32
        })
    }

    fn enforce_upper_limit_on_outlier_ratio(&mut self) {
        loop {
            let Some(outlier_ratio) = self.outlier_ratio() else {
                return;
            };
            if outlier_ratio <= I::UPPER_LIMIT {
                // All is good.
                break;
            }
            self.move_most_numerous_outlier_to_common();
        }
    }
}

impl<T> Default for OutPalVec<T>
where
    T: Clone + Eq,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Index<usize> for OutPalVec<T>
where
    T: Clone + Eq,
{
    type Output = T;
    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index) {
            Some(element) => element,
            None => {
                panic!("index (is {index}) should be < len (is {})", self.len());
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::{OptionBorrowedOrOwnedAsRef, OptionBorrowedOrOwnedCopied};

    use super::*;

    #[test]
    fn new_is_empty() {
        let palvec: OutPalVec<()> = OutPalVec::new();
        assert!(palvec.is_empty());
        assert_eq!(palvec.len(), 0);
    }

    #[test]
    fn push_and_len() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert_eq!(palvec.len(), 0);
        palvec.push(());
        assert_eq!(palvec.len(), 1);
        palvec.push(());
        assert_eq!(palvec.len(), 2);
    }

    #[test]
    fn push_and_get() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(42);
        assert_eq!(palvec.get(0), Some(&42));
    }

    #[test]
    fn get_out_of_bounds_is_none() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert!(palvec.get(0).is_none());
        palvec.push(());
        palvec.push(());
        assert!(palvec.get(0).is_some());
        assert!(palvec.get(1).is_some());
        assert!(palvec.get(2).is_none());
    }

    #[test]
    fn pop_empty() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn push_and_pop_strings() {
        let mut palvec: OutPalVec<String> = OutPalVec::new();
        palvec.push("uwu");
        palvec.push(String::from("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("owo"));
        assert_eq!(palvec.pop().map_as_ref().map(AsRef::as_ref), Some("uwu"));
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    fn push_and_pop_numbers() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert_eq!(palvec.pop().map_copied(), Some(5));
        assert_eq!(palvec.pop().map_copied(), Some(8));
        assert_eq!(palvec.pop().map_as_ref(), None);
    }

    #[test]
    #[should_panic]
    fn set_out_of_bounds_panic() {
        let mut palvec: OutPalVec<()> = OutPalVec::new();
        palvec.push(());
        palvec.push(());
        palvec.set(2, ());
    }

    #[test]
    fn with_len() {
        let palvec: OutPalVec<()> = OutPalVec::with_len((), 18);
        assert!(!palvec.is_empty());
        assert_eq!(palvec.len(), 18);
    }

    #[test]
    fn set_and_get() {
        let mut palvec: OutPalVec<i32> = OutPalVec::with_len(0, 20);
        palvec.set(10, 0);
        palvec.set(11, 1);
        palvec.set(12, 1);
        palvec.set(13, 2);
        assert_eq!(palvec.get(0), Some(&0));
        assert_eq!(palvec.get(19), Some(&0));
        assert_eq!(palvec.get(10), Some(&0));
        assert_eq!(palvec.get(11), Some(&1));
        assert_eq!(palvec.get(12), Some(&1));
        assert_eq!(palvec.get(13), Some(&2));
    }

    #[test]
    fn outlier_ratio_upper_limit() {
        pub struct OutlierMemoryRatioIntervalTest;
        impl OutlierMemoryRatioInterval for OutlierMemoryRatioIntervalTest {
            const LOWER_LIMIT_WEAK: f32 = 0.010;
            const UPPER_LIMIT: f32 = 0.030;
        }
        let mut palvec: OutPalVec<String, OutlierMemoryRatioIntervalTest> =
            OutPalVec::with_len("common".to_string(), 1000);
        for i in 0..100 {
            palvec.set(i, format!("{}", i));
        }
        for i in 100..200 {
            palvec.set(i, "uwu");
        }
        // 100 all different outliers, and 100 other identical outliers, so 200 outliers
        // but the `OutlierMemoryRatioInterval::SUP` upper ratio limit is enforced
        assert_eq!(palvec.outlier_instance_count(), 30);
        for i in 0..100 {
            assert_eq!(palvec.get(i), Some(&format!("{}", i)));
        }
        for i in 100..200 {
            assert_eq!(palvec.get(i).as_ref().map(|s| s.as_str()), Some("uwu"));
        }
        for i in 200..1000 {
            assert_eq!(palvec.get(i).as_ref().map(|s| s.as_str()), Some("common"));
        }
    }

    #[test]
    fn single_index() {
        let mut palvec: OutPalVec<i32> = OutPalVec::new();
        palvec.push(8);
        palvec.push(5);
        assert_eq!(palvec[0], 8);
        assert_eq!(palvec[1], 5);
    }
}
