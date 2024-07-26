use std::{
    collections::{hash_map::Entry, HashMap},
    mem::MaybeUninit,
    num::NonZeroUsize,
};

use fxhash::FxHashMap;

use crate::{
    key::Key, key_alloc::KeyAllocator, key_vec::KeyVec, utils::view_to_owned::ViewToOwned,
    BorrowedOrOwned,
};

pub(crate) struct PaletteEntry<T> {
    count: usize,
    element: T,
}

pub(crate) struct PaletteVec<T>
where
    T: Clone + Eq,
{
    /// The `element`s of each entry is initialized iff the entry's `count` is non-zero.
    vec: Vec<PaletteEntry<MaybeUninit<T>>>,
}

impl<T> PaletteVec<T>
where
    T: Clone + Eq,
{
    pub(crate) fn new() -> Self {
        Self { vec: vec![] }
    }

    pub(crate) fn with_one_entry(element: T, count: usize) -> Self {
        Self {
            vec: vec![PaletteEntry {
                count,
                element: MaybeUninit::new(element),
            }],
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.vec
            .iter()
            .filter(|palette_entry| 0 < palette_entry.count)
            .count()
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and returns the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub(crate) fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut KeyAllocator,
        key_vec: &mut KeyVec,
    ) -> Key {
        let already_in_palette = self
            .vec
            .iter_mut()
            .enumerate()
            .find(|(_key, palette_entry)| {
                if 0 < palette_entry.count {
                    let entry_element = {
                        // SAFETY: The entry's `count` is non zero so the element is initialized.
                        unsafe { palette_entry.element.assume_init_ref() }
                    };
                    element.eq(entry_element)
                } else {
                    false
                }
            });
        if let Some((key, palette_entry)) = already_in_palette {
            palette_entry.count = palette_entry
                .count
                .checked_add(that_many.get())
                .expect("Palette entry count overflow (max is usize::MAX)");
            key
        } else {
            let key = key_allocator.allocate_and_make_sure_it_fits(key_vec);
            // Making sure that `vec.len()` is at least `key + 1`.
            if self.vec.len() <= key {
                self.vec.resize_with(key + 1, || PaletteEntry {
                    count: 0,
                    element: MaybeUninit::uninit(),
                });
            }
            let palette_entry = {
                // SAFETY: We just made sure that `vec.len()` is at least `key + 1`,
                // so we cannot be out-of-bounds here.
                unsafe { self.vec.get_mut(key).unwrap_unchecked() }
            };
            *palette_entry = PaletteEntry {
                count: that_many.get(),
                element: MaybeUninit::new(element.into_owned()),
            };
            key
        }
    }

    /// Tells the palette that `that_many` instances of the element corresponding to the given key
    /// will be removed from the `PalVec`'s array,
    /// and it must update its map and counts and all,
    /// possiby deallocating the key if the element has no more instances.
    ///
    /// Only touches the palette and key allocator.
    /// The caller must make sure that indeed `that_many` instances of the given key
    /// are indeed removed from `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if `key` is not used by the palette.
    ///
    /// Panics if `that_many` is more than the number of instances of the `element`.
    pub(crate) fn remove_element_instances(
        &mut self,
        key: Key,
        that_many: NonZeroUsize,
        key_allocator: &mut KeyAllocator,
    ) -> BorrowedOrOwned<'_, T> {
        let palette_entry = self
            .vec
            .get_mut(key)
            .expect("Bug: Removing element instances by a key that is unused");
        palette_entry.count = palette_entry
            .count
            .checked_sub(that_many.get())
            .expect("Bug: Removing more element instances from palette than its count");
        let count = palette_entry.count;
        if count == 0 {
            let removed_element =
                std::mem::replace(&mut palette_entry.element, MaybeUninit::uninit());
            let removed_element = {
                // SAFETY: We cound subtract (without overflow) `count` by NonZero `that_many`,
                // so we know that `count` was non-zero before the subtraction,
                // which means that the `element` was initialized.
                unsafe { removed_element.assume_init() }
            };
            key_allocator.deallocate(key);
            BorrowedOrOwned::Owned(removed_element)
        } else {
            let element = {
                // SAFETY: We cound subtract (without overflow) `count` by NonZero `that_many`,
                // so we know that `count` was non-zero before the subtraction,
                // which means that the `element` was initialized.
                unsafe { palette_entry.element.assume_init_ref() }
            };
            BorrowedOrOwned::Borrowed(element)
        }
    }

    /// Returns a reference to the element associated to the given `key`,
    /// or `None` if the key is unused.
    pub(crate) fn get(&self, key: Key) -> Option<&T> {
        self.vec
            .get(key)
            .filter(|palette_entry| 0 < palette_entry.count)
            .map(|palette_entry| {
                // SAFETY: The entry's `count` is non zero so the element is initialized.
                unsafe { palette_entry.element.assume_init_ref() }
            })
    }

    /// Returns `true` if the palette contains the given element.
    ///
    /// This operation is *O*(*len*).
    pub(crate) fn contains(&self, element: impl ViewToOwned<T>) -> bool {
        self.vec.iter().any(|palette_entry| {
            0 < palette_entry.count
                && ({
                    let entry_element = {
                        // SAFETY: The entry's `count` is non zero so the element is initialized.
                        unsafe { palette_entry.element.assume_init_ref() }
                    };
                    element.eq(entry_element)
                })
        })
    }
}

pub(crate) struct PaletteMap<T>
where
    T: Clone + Eq,
{
    map: FxHashMap<Key, PaletteEntry<T>>,
}

impl<T> PaletteMap<T>
where
    T: Clone + Eq,
{
    pub(crate) fn new() -> Self {
        Self {
            map: HashMap::default(),
        }
    }

    pub(crate) fn with_one_entry(element: T, count: usize) -> Self {
        Self {
            map: {
                let mut map = HashMap::default();
                map.insert(0, PaletteEntry { count, element });
                map
            },
        }
    }

    pub(crate) fn len(&self) -> usize {
        self.map.len()
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and returns the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    pub(crate) fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut KeyAllocator,
        key_vec: &mut KeyVec,
    ) -> Key {
        let already_in_palette = self
            .map
            .iter_mut()
            .find(|(_key, palette_entry)| element.eq(&palette_entry.element));
        if let Some((&key, palette_entry)) = already_in_palette {
            palette_entry.count = palette_entry
                .count
                .checked_add(that_many.get())
                .expect("Palette entry count overflow (max is usize::MAX)");
            key
        } else {
            let key = key_allocator.allocate_and_make_sure_it_fits(key_vec);
            self.map.insert(
                key,
                PaletteEntry {
                    count: that_many.get(),
                    element: element.into_owned(),
                },
            );
            key
        }
    }

    /// Tells the palette that `that_many` instances of the element corresponding to the given key
    /// will be removed from the `PalVec`'s array,
    /// and it must update its map and counts and all,
    /// possiby deallocating the key if the element has no more instances.
    ///
    /// Only touches the palette and key allocator.
    /// The caller must make sure that indeed `that_many` instances of the given key
    /// are indeed removed from `key_vec`.
    pub(crate) fn remove_element_instances(
        &mut self,
        key: Key,
        that_many: NonZeroUsize,
        key_allocator: &mut KeyAllocator,
    ) -> BorrowedOrOwned<'_, T> {
        let map_entry = self.map.entry(key);
        let Entry::Occupied(mut occupied_entry) = map_entry else {
            panic!("Bug: Removing element instances by a key that is unused");
        };
        let palette_entry = occupied_entry.get_mut();
        palette_entry.count = palette_entry
            .count
            .checked_sub(that_many.get())
            .expect("Bug: Removing more element instances from palette than its count");
        let count = palette_entry.count;
        if count == 0 {
            let entry_removed = occupied_entry.remove();
            key_allocator.deallocate(key);
            BorrowedOrOwned::Owned(entry_removed.element)
        } else {
            BorrowedOrOwned::Borrowed(&occupied_entry.into_mut().element)
        }
    }

    /// Returns a reference to the element associated to the given `key`,
    /// or `None` if the key is unused.
    pub(crate) fn get(&self, key: Key) -> Option<&T> {
        self.map
            .get(&key)
            .map(|palette_entry| &palette_entry.element)
    }

    /// Returns `true` if the palette contains the given element.
    ///
    /// This operation is *O*(*len*).
    pub(crate) fn contains(&self, element: impl ViewToOwned<T>) -> bool {
        self.map
            .values()
            .any(|palette_entry| element.eq(&palette_entry.element))
    }
}
