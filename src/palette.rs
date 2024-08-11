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

pub trait Palette<T>
where
    T: Clone + Eq,
{
    /// Creates an empty palette.
    fn new() -> Self;

    /// Creates a palette that initially contains one entry.
    fn with_one_entry(element: T, count: usize) -> Self;

    /// Returns the number of entries in the palette (and not the total number of instances).
    fn len(&self) -> usize;

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and return the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
        key_vec: Option<&mut KeyVec>,
        reserved_key: Option<Key>,
    ) -> Key;

    /// Tells the palette that `that_many` instances of the element corresponding to the given key
    /// will be removed from the `PalVec`'s array,
    /// and it must update its map and counts and all,
    /// possiby deallocating the key if the element has no more instances.
    ///
    /// Only touches the palette and key allocator.
    /// The caller must make sure that indeed `that_many` instances of the given key
    /// are indeed removed from `key_vec`.
    fn remove_element_instances(
        &mut self,
        key: Key,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
    ) -> BorrowedOrOwned<'_, T>;

    /// Returns a reference to the element associated to the given `key`,
    /// or `None` if the key is unused.
    fn get(&self, key: Key) -> Option<&T>;

    /// Returns `true` if the palette contains the given element.
    fn contains(&self, element: &impl ViewToOwned<T>) -> bool;

    /// Returns an iterator over the keys currently used by the palette.
    fn used_keys(&self) -> impl Iterator<Item = Key>;
}

pub trait PaletteAsKeyAllocator {
    fn get_smallest_unused_key(&self, outlier_key: Option<Key>) -> Key;
}

pub(crate) struct PaletteEntry<T> {
    count: usize,
    element: T,
}

/// Palette that starts as a [`PaletteVec`]
/// and switches to a [`PaletteMap`] when the number of entries grows past a threshold.
pub enum PaletteVecOrMap<T>
where
    T: Clone + Eq,
{
    Vec(PaletteVec<T>),
    Map(PaletteMap<T>),
}

impl<T> Palette<T> for PaletteVecOrMap<T>
where
    T: Clone + Eq,
{
    /// Creates an empty palette.
    ///
    /// Does not allocate now,
    /// allocations are done when keys are added to it or it is told to reserve memory.
    #[inline]
    fn new() -> Self {
        Self::Vec(PaletteVec::new())
    }

    /// Creates a palette that initially contains one entry.
    #[inline]
    fn with_one_entry(element: T, count: usize) -> Self {
        Self::Vec(PaletteVec::with_one_entry(element, count))
    }

    /// Returns the number of entries in the palette (and not the total number of instances).
    #[inline]
    fn len(&self) -> usize {
        match self {
            Self::Vec(vec) => vec.len(),
            Self::Map(map) => map.len(),
        }
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and return the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
        key_vec: Option<&mut KeyVec>,
        reserved_key: Option<Key>,
    ) -> Key {
        match self {
            Self::Vec(vec) => {
                let key = vec.add_element_instances(
                    element,
                    that_many,
                    key_allocator,
                    key_vec,
                    reserved_key,
                );
                // If the vec gets too long, we switch to a map.
                //
                // TODO: Instead of doing this, we should switch to a map when the
                // vec becomes very sparse because this is the only case where a map is better
                // than a vec.
                // Also, in such case, it also would be intresting for the user to trigger
                // a reassignment of entries to smaller keys to "unsparse" the allocated keys.
                // The palette is not what is important, having a small max allocated key value is.
                if vec.len() > 16 {
                    self.use_map_variant();
                }
                key
            }
            Self::Map(map) => {
                map.add_element_instances(element, that_many, key_allocator, key_vec, reserved_key)
            }
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
    #[inline]
    fn remove_element_instances(
        &mut self,
        key: Key,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
    ) -> BorrowedOrOwned<'_, T> {
        match self {
            Self::Vec(vec) => vec.remove_element_instances(key, that_many, key_allocator),
            Self::Map(map) => map.remove_element_instances(key, that_many, key_allocator),
        }
    }

    /// Returns a reference to the element associated to the given `key`,
    /// or `None` if the key is unused.
    #[inline]
    fn get(&self, key: Key) -> Option<&T> {
        match self {
            Self::Vec(vec) => vec.get(key),
            Self::Map(map) => map.get(key),
        }
    }

    /// Returns `true` if the palette contains the given element.
    ///
    /// This operation is *O*(*len*).
    #[inline]
    fn contains(&self, element: &impl ViewToOwned<T>) -> bool {
        match self {
            Self::Vec(vec) => vec.contains(element),
            Self::Map(map) => map.contains(element),
        }
    }

    /// Returns an iterator over the keys currently used by the palette.
    #[inline] // Inline to help with iterator-related optimizations.
    fn used_keys(&self) -> impl Iterator<Item = Key> {
        // Returning either one or the other of two different opaque type iterators is impossible.
        // Or so I thought before actually trying, but it turns out it is as simple as that.

        enum EitherIterator<A, B>
        where
            A: Iterator<Item = Key>,
            B: Iterator<Item = Key>,
        {
            A(A),
            B(B),
        }

        impl<A, B> Iterator for EitherIterator<A, B>
        where
            A: Iterator<Item = Key>,
            B: Iterator<Item = Key>,
        {
            type Item = Key;

            fn next(&mut self) -> Option<Self::Item> {
                match self {
                    Self::A(a) => a.next(),
                    Self::B(b) => b.next(),
                }
            }
        }

        match self {
            Self::Vec(vec) => EitherIterator::A(vec.used_keys()),
            Self::Map(map) => EitherIterator::B(map.used_keys()),
        }
    }
}

impl<T> PaletteAsKeyAllocator for PaletteVecOrMap<T>
where
    T: Clone + Eq,
{
    fn get_smallest_unused_key(&self, reserved_key: Option<Key>) -> Key {
        match self {
            Self::Vec(vec) => vec.get_smallest_unused_key(reserved_key),
            Self::Map(map) => map.get_smallest_unused_key(reserved_key),
        }
    }
}

impl<T> PaletteVecOrMap<T>
where
    T: Clone + Eq,
{
    fn use_map_variant(&mut self) {
        match self {
            Self::Vec(vec) => {
                let vec = std::mem::take(&mut vec.vec);
                let mut palette_map = PaletteMap::new();
                for (key, palette_entry) in vec.into_iter().enumerate() {
                    if 0 < palette_entry.count {
                        palette_map.map.insert(
                            key,
                            PaletteEntry {
                                count: palette_entry.count,
                                element: {
                                    // SAFETY: `count` is non-zero so `element` is initialized.
                                    unsafe { palette_entry.element.assume_init() }
                                },
                            },
                        );
                    }
                }
                *self = Self::Map(palette_map);
            }
            Self::Map(_map) => {}
        }
    }
}

pub struct PaletteVec<T>
where
    T: Clone + Eq,
{
    /// The `element`s of each entry is initialized iff the entry's `count` is non-zero.
    vec: Vec<PaletteEntry<MaybeUninit<T>>>,
}

impl<T> Palette<T> for PaletteVec<T>
where
    T: Clone + Eq,
{
    /// Creates an empty palette.
    ///
    /// Does not allocate now,
    /// allocations are done when keys are added to it or it is told to reserve memory.
    #[inline]
    fn new() -> Self {
        Self { vec: vec![] }
    }

    /// Creates a palette that initially contains one entry.
    fn with_one_entry(element: T, count: usize) -> Self {
        Self {
            vec: vec![PaletteEntry {
                count,
                element: MaybeUninit::new(element),
            }],
        }
    }

    /// Returns the number of entries in the palette (and not the total number of instances).
    fn len(&self) -> usize {
        self.vec
            .iter()
            .filter(|palette_entry| 0 < palette_entry.count)
            .count()
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and return the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
        key_vec: Option<&mut KeyVec>,
        reserved_key: Option<Key>,
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
            let key = key_allocator.allocate(self, reserved_key);
            if let Some(key_vec) = key_vec {
                key_vec.make_sure_a_key_fits(key);
            }
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
    fn remove_element_instances(
        &mut self,
        key: Key,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
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
    fn get(&self, key: Key) -> Option<&T> {
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
    fn contains(&self, element: &impl ViewToOwned<T>) -> bool {
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

    /// Returns an iterator over the keys currently used by the palette.
    fn used_keys(&self) -> impl Iterator<Item = Key> {
        self.vec
            .iter()
            .enumerate()
            .filter_map(|(key, palette_entry)| (0 < palette_entry.count).then_some(key))
    }
}

impl<T> PaletteAsKeyAllocator for PaletteVec<T>
where
    T: Clone + Eq,
{
    fn get_smallest_unused_key(&self, outlier_key: Option<Key>) -> Key {
        self.vec
            .iter()
            .enumerate()
            .find_map(|(key, palette_entry)| {
                (palette_entry.count == 0 && outlier_key != Some(key)).then_some(key)
            })
            .unwrap_or(self.vec.len())
    }
}

pub struct PaletteMap<T>
where
    T: Clone + Eq,
{
    map: FxHashMap<Key, PaletteEntry<T>>,
}

impl<T> Palette<T> for PaletteMap<T>
where
    T: Clone + Eq,
{
    /// Creates an empty palette.
    ///
    /// Does not allocate now,
    /// allocations are done when keys are added to it or it is told to reserve memory.
    #[inline]
    fn new() -> Self {
        Self {
            map: HashMap::default(),
        }
    }

    /// Creates a palette that initially contains one entry.
    fn with_one_entry(element: T, count: usize) -> Self {
        Self {
            map: {
                let mut map = HashMap::default();
                map.insert(0, PaletteEntry { count, element });
                map
            },
        }
    }

    /// Returns the number of entries in the palette (and not the total number of instances).
    #[inline]
    fn len(&self) -> usize {
        self.map.len()
    }

    /// Tells the palette that `that_many` new `element` instances
    /// will be added to the `PalVec`'s array,
    /// and the palette must update its map and counts and all and return the key to `element`,
    /// allocating this key if `element` is new in the palette.
    ///
    /// Only touches the palette, the key allocator, and the `key_vec`'s `key_size`.
    /// The caller must make sure that indeed `that_many` new instances of the returned key
    /// are indeed added to `key_vec`.
    ///
    /// # Panics
    ///
    /// Panics if the palette entry count for `element` becomes more than `usize::MAX`.
    fn add_element_instances(
        &mut self,
        element: impl ViewToOwned<T>,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
        key_vec: Option<&mut KeyVec>,
        reserved_key: Option<Key>,
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
            let key = key_allocator.allocate(self, reserved_key);
            if let Some(key_vec) = key_vec {
                key_vec.make_sure_a_key_fits(key);
            }
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
    fn remove_element_instances(
        &mut self,
        key: Key,
        that_many: NonZeroUsize,
        key_allocator: &mut impl KeyAllocator,
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
    fn get(&self, key: Key) -> Option<&T> {
        self.map
            .get(&key)
            .map(|palette_entry| &palette_entry.element)
    }

    /// Returns `true` if the palette contains the given element.
    ///
    /// This operation is *O*(*len*).
    fn contains(&self, element: &impl ViewToOwned<T>) -> bool {
        self.map
            .values()
            .any(|palette_entry| element.eq(&palette_entry.element))
    }

    /// Returns an iterator over the keys currently used by the palette.
    fn used_keys(&self) -> impl Iterator<Item = Key> {
        self.map.keys().cloned()
    }
}

impl<T> PaletteAsKeyAllocator for PaletteMap<T>
where
    T: Clone + Eq,
{
    fn get_smallest_unused_key(&self, reserved_key: Option<Key>) -> Key {
        for key in 0.. {
            if !self.map.contains_key(&key) && Some(key) != reserved_key {
                return key;
            }
        }
        unreachable!()
    }
}
