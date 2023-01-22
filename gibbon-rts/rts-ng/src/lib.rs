//! Next generation runtime system for the Gibbon compiler.

pub use ffi::c::*;
pub use ffi::rs::*;
pub use gc::ValueStats;

mod ffi;
mod gc;
pub mod tagged_pointer;
