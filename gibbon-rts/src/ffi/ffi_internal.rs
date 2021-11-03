use crate::ffi::types::*;
use crate::mem;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

#[no_mangle]
pub extern "C" fn gib_alloc_region2(size: u64) -> *mut C_GibCursorsPair {
    let (start, end) = mem::alloc_region(size);
    let cursors = C_GibCursorsPair { start, end };
    Box::into_raw(Box::new(cursors))
}

#[no_mangle]
/// Only use this while testing the Rust RTS!
pub extern "C" fn gib_reset_nursery() {
    mem::reset_nursery();
}
