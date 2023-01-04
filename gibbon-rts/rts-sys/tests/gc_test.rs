use std::ptr::null_mut;

use gibbon_rts_sys::*;
mod utils;

#[test]
fn ffi_works() {
    unsafe {
        // Test functions from C RTS.
        gib_init(0, null_mut());
        let chunk = gib_alloc_region(1024);
        println!("chunk = {:?}", chunk);

        // Test functions from Rust RTS.
        gib_info_table_initialize(4);
    }
}

#[test]
pub fn globals_access() {
    unsafe {
        gib_init(0, null_mut());
        println!("{:?}", *gib_global_read_shadowstacks);
        println!("{:?}", *gib_global_write_shadowstacks);
        println!("{:?}", *gib_global_nurseries);
        println!("{:?}", GibOldgen::from_ffi(gib_global_oldgen));
        gib_exit();
    }
}
