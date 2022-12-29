#[derive(Debug)]
#[repr(C)]
pub struct C_GibChunk {
    start: *mut i8,
    end: *mut i8,
}

#[link(name = "gibbon_rts")]
extern "C" {
    pub fn gib_alloc_region(size: usize) -> C_GibChunk;
    pub fn gib_init(argc: i32, argv: *const *const i8) -> i32;
    pub fn gib_info_table_initialize(size: usize) -> i32;
}

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
