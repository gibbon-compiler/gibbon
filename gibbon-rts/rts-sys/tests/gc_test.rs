use gibbon_rts_sys::*;

#[test]
fn it_works() {
    use std::ptr::null_mut;
    unsafe {
        // Test functions from C RTS.
        gib_init(0, null_mut());
        let chunk = gib_alloc_region(1024);
        println!("chunk = {:?}", chunk);

        // Test functions from Rust RTS.
        gib_info_table_initialize(4);
    }
}
