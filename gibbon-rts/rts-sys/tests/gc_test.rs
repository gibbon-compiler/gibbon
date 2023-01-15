use std::ptr::null_mut;

use gibbon_rts_sys::*;
mod utils;
use crate::utils::heap::*;

#[test]
pub fn tests() {
    unsafe {
        // Initialize storage.
        gib_init(0, null_mut());

        // Test 0; check if clear_all works.
        let chunk1 = gib_alloc_region(1024);
        clear_all();
        let chunk2 = gib_alloc_region(1024);
        assert!(chunk1.start == chunk2.start);
        assert!(chunk1.end == chunk2.end);

        // Test 1.
        ffi_works();
        clear_all();

        // Test 2.
        globals_access();
        clear_all();

        // Free storage.
        gib_exit();
    }
}

fn ffi_works() {
    let chunk = unsafe { gib_alloc_region(1024) };
    assert!(!chunk.start.is_null());
    assert!(!chunk.end.is_null());
}

fn globals_access() {
    unsafe {
        assert!(!gib_global_read_shadowstacks.is_null());
        assert!(!gib_global_write_shadowstacks.is_null());
        assert!(!gib_global_write_shadowstacks.is_null());
        assert!(!gib_global_nurseries.is_null());
        assert!(!gib_global_oldgen.is_null());
    }
}

/// Reset stuff between tests.
fn clear_all() {
    let nursery: &mut GibNursery = unsafe { &mut *gib_global_nurseries };
    let rstack: &mut GibShadowstack =
        unsafe { &mut *gib_global_read_shadowstacks };
    let wstack: &mut GibShadowstack =
        unsafe { &mut *gib_global_write_shadowstacks };
    nursery.clear();
    rstack.clear();
    wstack.clear();
}
