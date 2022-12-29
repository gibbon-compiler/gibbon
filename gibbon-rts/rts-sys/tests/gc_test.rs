use gibbon_rts_sys::*;
use std::ptr::null;

#[test]
fn it_works() {
    unsafe {
        // Test functions from C RTS.
        gib_init(0, null());
        let chunk = gib_alloc_region(1024);
        println!("chunk = {:?}", chunk);

        // Test functions from Rust RTS.
        gib_info_table_initialize(4);
    }
}
