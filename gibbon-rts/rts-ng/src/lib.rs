//! Next generation runtime system for the Gibbon compiler.

#![feature(destructuring_assignment)]
#![feature(core_intrinsics)]

pub use ffi::c::*;
pub use ffi::rs::*;

mod ffi;
mod gc;
mod tagged_pointer;
