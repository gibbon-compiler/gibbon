/*!

Memory Management; regions, chunks, GC etc.

 */

use std::lazy::Lazy;

use crate::ffi::types as ffi;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/**

We have roughly four ways of initializing a heap allocated thread-local storage:


(1) The thread_local! macro:

    This appears to be slow compared to C's thread_locals[1].


(2) Using new but unstable features coming to the Rust compiler:

    Specifically, once_cell[2,3] and thread_local[4].


(3) Initialize a thread_local[3] nursery to be std::ptr::null(), and then
    run get_or_initialize upon every allocation in it. This is what the
    C RTS does for its thread-locals. Presumably, option (2) would also
    do something very similar.


(4) A thread_local variable defined in C and accessed through FFI:

    I don't have any hope of this being efficient without good
    link time optimization.


We should update [1] to include option (2).


[1]: https://matklad.github.io/2020/10/03/fast-thread-locals-in-rust.html
[2]: https://github.com/rust-lang/rfcs/pull/2788
[3]: https://github.com/rust-lang-nursery/lazy-static.rs/issues/111
[4]: https://github.com/rust-lang/rust/issues/29594

 */

#[thread_local]
static NURSERY_START: Lazy<*const libc::c_char> =
    Lazy::new(|| unsafe { libc::malloc(NURSERY_SIZE as usize) as *const libc::c_char });

#[thread_local]
static NURSERY_END: Lazy<*const libc::c_char> =
    Lazy::new(|| unsafe { NURSERY_START.offset(NURSERY_SIZE as isize) });

#[thread_local]
static mut NURSERY_ALLOC: *const libc::c_char = std::ptr::null();

/// The nursery is 4 MB.
const NURSERY_SIZE: u64 = 4 * 1048576;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

pub fn alloc_region(size: u64) -> (ffi::C_GibCursor, ffi::C_GibCursor) {
    unsafe {
        // Initialize the nursery allocation pointer if its NULL.
        if NURSERY_ALLOC.is_null() {
            NURSERY_ALLOC = *NURSERY_START;
        }
        // Allocate in the nursery if there's space, otherwise fall back to
        // malloc. No garbage collection for now.
        let bump = NURSERY_ALLOC.offset(size as isize);
        let heap_start = if bump < *NURSERY_END {
            let old = NURSERY_ALLOC;
            NURSERY_ALLOC = bump;
            old
        } else {
            println!("MALLOC!!!");
            libc::malloc(size as usize) as ffi::C_GibCursor
        };
        // The end is always start+size no matter where the allocation happens.
        let heap_end = heap_start.offset(size as isize);
        (heap_start, heap_end)
    }
}

/// Only use this while testing the Rust RTS!
pub unsafe fn reset_nursery() {
    NURSERY_ALLOC = *NURSERY_START;
}
