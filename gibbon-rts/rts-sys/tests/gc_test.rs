use quickcheck::{QuickCheck, TestResult};
use std::panic;
use std::ptr::null_mut;

use gibbon_rts_sys::*;
mod utils;
use crate::utils::heap::{test_redirections_in_inlined_data, test_reverse1, test_split_root};

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

#[test]
pub fn gc_tests() {
    println!("");
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
        test_ffi_works();
        clear_all();

        // Test 2.
        test_globals_access();
        clear_all();

        // Test 3.
        QuickCheck::new().tests(100).quickcheck(qc_test_reverse1 as fn(u8) -> TestResult);

        // Test 4.
        let result = panic::catch_unwind(|| {
            test_split_root();
        });
        clear_all();

        // Test 5.
        test_redirections_in_inlined_data();
        clear_all();

        // Free storage.
        gib_exit();
    }
}

/// Test if some simple functions from the FFI work.
fn test_ffi_works() {
    let chunk = unsafe { gib_alloc_region(1024) };
    assert!(!chunk.start.is_null());
    assert!(!chunk.end.is_null());
}

/// Test if access to C globals is OK.
fn test_globals_access() {
    unsafe {
        assert!(!gib_global_read_shadowstacks.is_null());
        assert!(!gib_global_write_shadowstacks.is_null());
        assert!(!gib_global_write_shadowstacks.is_null());
        assert!(!gib_global_nurseries.is_null());
        assert!(!gib_global_oldgen.is_null());
    }
}

fn qc_test_reverse1(n: u8) -> TestResult {
    let res = test_reverse1(n);
    clear_all();
    TestResult::from_bool(res)
}

/// Reset stuff between tests.
fn clear_all() {
    let nursery: &mut GibNursery = unsafe { &mut *gib_global_nurseries };
    let rstack: &mut GibShadowstack = unsafe { &mut *gib_global_read_shadowstacks };
    let wstack: &mut GibShadowstack = unsafe { &mut *gib_global_write_shadowstacks };
    let oldgen: &mut GibOldgen = unsafe { GibOldgen::from_ffi(gib_global_oldgen) };
    nursery.clear();
    rstack.clear();
    wstack.clear();
    oldgen.clear_zcts();
}
