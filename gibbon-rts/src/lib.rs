//! The Gibbon runtime system.

// Required to initialize the thread-local nursery in mem.rs.
#![feature(once_cell)]
#![feature(thread_local)]

pub mod ffi;
mod gc;
