//! Palette-compressed Vec-like collection.

mod key;
mod key_alloc;
mod key_vec;
mod palvec;
mod utils;

pub use palvec::PalVec;

pub use utils::borrowed_or_owned::*;
