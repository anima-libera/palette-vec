//! Palette-compressed Vec-like collections.
//!
//! - `PalVec<T>` is classic palette compression.
//! - `OutPalVec<T>` is palette compression with a super epic original optimization twist on top
//!   that allows for better compression with some small compromise on performance.

//#![warn(missing_debug_implementations)]

mod index_map;
mod key;
mod key_vec;
mod outliers;
mod palette;
mod palvec;
mod utils;

pub use outliers::{
    AutoMemoryOptimizationPolicy, AutoMemoryOptimizationPolicyAlways,
    AutoMemoryOptimizationPolicyEveryNOccasions, AutoMemoryOptimizationPolicyNever,
    OutAccessOptimizer, OutPalVec,
};
pub use palvec::PalVec;
pub use utils::borrowed_or_owned::*;
pub use utils::view_to_owned::*;
