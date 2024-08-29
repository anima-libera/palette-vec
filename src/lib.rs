//! Palette-compressed Vec-like collection.

mod key;
mod key_vec;
mod outliers;
mod palette;
mod palvec;
mod utils;

pub use outliers::OutPalVec;
pub use palvec::PalVec;

pub use utils::borrowed_or_owned::*;
