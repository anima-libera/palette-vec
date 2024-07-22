pub(crate) mod view_to_owned {
    /// Trait that can be implemented for both types of a type pair (R, O)
    /// where R is a reference-like or view-like type
    /// that refers to the content of the type O, whereas O owns its data.
    ///
    /// A method that takes an `impl ViewToOwned<O>` can thus take either
    /// an owned O or an R.
    /// The method can always compare the argument's data for equality with other `&O`s
    /// via [`ViewToOwned::eq`] (a bit specific, this is needed by this crate).
    /// If the method happens to need to take ownership of the argument as an O,
    /// it can via [`ViewToOwned::into_owned`] and it will only do work to construct
    /// an O(wned) version if it was not already owned.
    ///
    /// This allows to get the best of both worlds in the ref vs owned argument tradeoff
    /// and this crate happens to need to be able to do this.
    pub trait ViewToOwned<T>
    where
        T: Eq,
    {
        /// Make sure we own the result, doing some work only if needed.
        fn into_owned(self) -> T;

        /// Compare just like `PartialEq::eq` with `Eq`'s guarentees.
        fn eq(&self, other: &T) -> bool;
    }

    impl<T> ViewToOwned<T> for &T
    where
        T: Clone + Eq,
    {
        fn into_owned(self) -> T {
            self.clone()
        }

        fn eq(&self, other: &T) -> bool {
            self == &other
        }
    }

    impl<T> ViewToOwned<T> for T
    where
        T: Clone + Eq,
    {
        fn into_owned(self) -> T {
            self
        }

        fn eq(&self, other: &T) -> bool {
            self == other
        }
    }

    impl ViewToOwned<String> for &str {
        fn into_owned(self) -> String {
            self.to_string()
        }

        fn eq(&self, other: &String) -> bool {
            self == other
        }
    }

    impl ViewToOwned<Box<str>> for &str {
        fn into_owned(self) -> Box<str> {
            self.to_string().into_boxed_str()
        }

        fn eq(&self, other: &Box<str>) -> bool {
            *self == other.as_ref()
        }
    }
}

pub(crate) mod borrowed_or_owned {
    pub enum BorrowedOrOwned<'a, T> {
        Borrowed(&'a T),
        Owned(T),
    }

    impl<'a, T> BorrowedOrOwned<'a, T> {
        /// Get a reference even if `Owned`.
        #[allow(clippy::should_implement_trait)] // `Option` has its own `as_ref`, it's ok!
        pub fn as_ref(&'a self) -> &'a T {
            match self {
                BorrowedOrOwned::Borrowed(borrowed) => borrowed,
                BorrowedOrOwned::Owned(owned) => owned,
            }
        }
    }

    impl<'a, T: Clone> BorrowedOrOwned<'a, T> {
        /// Get an owned even if `Borrowed` by cloning if necessary.
        pub fn cloned(self) -> T {
            match self {
                BorrowedOrOwned::Borrowed(borrowed) => borrowed.clone(),
                BorrowedOrOwned::Owned(owned) => owned,
            }
        }
    }

    impl<'a, T: Copy> BorrowedOrOwned<'a, T> {
        /// Get an owned even if `Borrowed` by copying if necessary.
        pub fn copied(self) -> T {
            match self {
                BorrowedOrOwned::Borrowed(borrowed) => *borrowed,
                BorrowedOrOwned::Owned(owned) => owned,
            }
        }
    }

    /// Shortens the use of [`BorrowedOrOwned::as_ref`] on `Option<BorrowedOrOwned<T>>`.
    ///
    /// `palvec.pop().as_ref().map(BorrowedOrOwned::as_ref)` can be shortened to
    /// `palvec.pop().map_as_ref()`.
    pub trait OptionBorrowedOrOwnedAsRef<'a, T> {
        /// Is the same as `self.as_ref().map(BorrowedOrOwned::as_ref)`.
        fn map_as_ref(&'a self) -> Option<&'a T>;
    }

    impl<'a, T> OptionBorrowedOrOwnedAsRef<'a, T> for Option<BorrowedOrOwned<'a, T>> {
        fn map_as_ref(&'a self) -> Option<&'a T> {
            self.as_ref().map(BorrowedOrOwned::as_ref)
        }
    }

    /// Shortens the use of [`BorrowedOrOwned::cloned`] on `Option<BorrowedOrOwned<T>>`.
    ///
    /// `palvec.pop().map(BorrowedOrOwned::cloned)` can be shortened to
    /// `palvec.pop().map_cloned()`.
    pub trait OptionBorrowedOrOwnedCloned<'a, T: Clone> {
        /// Is the same as `self.map(BorrowedOrOwned::cloned)`.
        ///
        /// See [`BorrowedOrOwned::cloned`].
        fn map_cloned(self) -> Option<T>;
    }

    impl<'a, T: Clone> OptionBorrowedOrOwnedCloned<'a, T> for Option<BorrowedOrOwned<'a, T>> {
        fn map_cloned(self) -> Option<T> {
            self.map(BorrowedOrOwned::cloned)
        }
    }

    /// Shortens the use of [`BorrowedOrOwned::copied`] on `Option<BorrowedOrOwned<T>>`.
    ///
    /// `palvec.pop().map(BorrowedOrOwned::copied)` can be shortened to
    /// `palvec.pop().map_copied()`.
    pub trait OptionBorrowedOrOwnedCopied<'a, T: Clone> {
        /// Is the same as `self.map(BorrowedOrOwned::copied)`.
        ///
        /// See [`BorrowedOrOwned::copied`].
        fn map_copied(self) -> Option<T>;
    }

    impl<'a, T: Copy> OptionBorrowedOrOwnedCopied<'a, T> for Option<BorrowedOrOwned<'a, T>> {
        fn map_copied(self) -> Option<T> {
            self.map(BorrowedOrOwned::copied)
        }
    }
}
