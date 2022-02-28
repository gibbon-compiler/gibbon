//! The Gibbon runtime system.

// Required to initialize the thread-local nursery in mem.rs.
#![feature(once_cell)]
#![feature(thread_local)]
#![feature(destructuring_assignment)]

pub mod ffi;
mod gc;
mod tagged_pointer;
