/*!

The foreign function interface which exposes this RTS to C.
See gibbon-compiler/cbits/gibbon.h.

 */

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Translating Gibbon's types to Rust
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

pub mod types {
    #![allow(non_camel_case_types)]

    //! Everything in this module must match its counterpart in C. See
    //! gibbon-compiler/cbits/gibbon.h and gibbon-compiler/cbits/gibbon_rts.c.

    pub type C_GibPackedTag = u8;
    pub type C_GibBoxedTag = u8;
    pub type C_GibInt = i64;
    pub type C_GibFloat = f32;
    pub type C_GibSym = u64;
    pub type C_GibBool = bool;
    pub type C_GibPtr = *const i8;
    pub type C_GibCursor = *const i8;

    /// An enum in C, which is 4 bytes.
    pub type C_GibDatatype = u32;

    pub const C_REDIRECTION_TAG: C_GibPackedTag = 255;
    pub const C_INDIRECTION_TAG: C_GibPackedTag = 254;
    pub const C_NUM_GENERATIONS: u8 = 1;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibNursery {
        pub collections: u64,
        pub heap_size: u64,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
        pub initialized: bool,
        pub rem_set: *mut std::ffi::c_void,
    }

    pub type C_GibRememberedSetElt = C_GibShadowstackFrame;
    pub type C_GibRememberedSet = C_GibShadowstack;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibGeneration {
        pub no: u8,
        pub dest: *mut C_GibGeneration,
        pub oldest: bool,
        pub mem_allocated: u64,
        pub heap_size: u64,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
        pub rem_set: *mut C_GibRememberedSet,
        pub zct: *mut std::ffi::c_void,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibShadowstack {
        pub initialized: bool,
        pub start: *const i8,
        pub end: *const i8,
        pub alloc: *const i8,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibShadowstackFrame {
        pub ptr: *const i8,
        pub endptr: *const i8,
        pub datatype: C_GibDatatype,
    }

    const MAX_OUTSET_LENGTH: usize = 10;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibRegionInfo {
        pub id: C_GibSym,
        pub refcount: u16,
        pub outset_len: u16,
        pub outset: [C_GibCursor; MAX_OUTSET_LENGTH],
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibChunkFooter {
        pub reg_info: *mut C_GibRegionInfo,
        pub seq_no: u16,
        pub size: u64,
        pub next: *mut C_GibChunkFooter,
        pub prev: *mut C_GibChunkFooter,
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * FFI functions
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

use std::slice;

use crate::ffi::types::*;
use crate::gc;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

#[no_mangle]
/// The user is responsible for initializing the info table before
/// calling the get/set methods on it.
pub extern "C" fn gib_info_table_initialize() -> i32 {
    match gc::info_table_initialize() {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn gib_info_table_insert_packed_dcon(
    datatype: C_GibDatatype,
    datacon: C_GibPackedTag,
    scalar_bytes: u8,
    num_scalars: u8,
    num_packed: u8,
    c_field_tys: *const C_GibDatatype,
    c_field_tys_length: u8,
) -> i32 {
    let field_tys: Vec<C_GibDatatype> = unsafe {
        slice::from_raw_parts(c_field_tys, c_field_tys_length as usize)
            .to_vec()
    };
    match gc::info_table_insert_packed_dcon(
        datatype,
        datacon,
        scalar_bytes,
        num_scalars,
        num_packed,
        field_tys,
    ) {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn gib_info_table_insert_scalar(
    datatype: C_GibDatatype,
    size: u8,
) -> i32 {
    match gc::info_table_insert_scalar(datatype, size) {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn gib_garbage_collect(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
    force_major: bool,
) -> i32 {
    match gc::collect_minor(
        rstack_ptr,
        wstack_ptr,
        nursery_ptr,
        generations_ptr,
        force_major,
    ) {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}
