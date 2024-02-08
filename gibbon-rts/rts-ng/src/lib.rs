//! Next generation runtime system for the Gibbon compiler.

// Erroring on every warning is OK for now, but can be refined in the future:
// https://rust-unofficial.github.io/patterns/anti_patterns/deny-warnings.html
#![deny(warnings)]

pub use ffi::c::*;
pub use ffi::rs::*;
pub use gc::ValueStats;

mod ffi;
mod gc;
pub mod tagged_pointer;
