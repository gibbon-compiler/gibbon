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

    use std::collections::HashSet;

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

    // Tags reserved for the garbage collector.
    pub const C_CAUTERIZED_TAG: C_GibPackedTag = 253;
    pub const C_COPIED_TO_TAG: C_GibPackedTag = 252;
    pub const C_COPIED_TAG: C_GibPackedTag = 251;
    pub const C_SCALAR_TAG: C_GibPackedTag = 250;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibNursery {
        pub num_collections: u64,
        pub heap_size: usize,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
        pub chunk_starts: *const i8,
        pub num_chunk_starts: u64,
    }

    pub type C_GibRememberedSetElt = C_GibShadowstackFrame;
    pub type C_GibRememberedSet = C_GibShadowstack;

    pub type Zct = HashSet<*const C_GibRegionInfo>;
    pub type Outset = HashSet<*const C_GibRegionInfo>;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibGeneration {
        pub no: u8,
        pub dest: *mut C_GibGeneration,
        pub oldest: bool,
        pub mem_allocated: usize,
        pub heap_size: usize,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
        pub rem_set: *mut C_GibRememberedSet,
        pub old_zct: *mut Zct,
        pub new_zct: *mut Zct,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibShadowstack {
        pub start: *const i8,
        pub end: *const i8,
        pub alloc: *const i8,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibShadowstackFrame {
        pub ptr: *mut i8,
        pub endptr: *mut i8,
        pub datatype: C_GibDatatype,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibRegionInfo {
        pub id: C_GibSym,
        pub refcount: u16,
        pub outset: *mut Outset,
        pub first_chunk_footer: *const C_GibChunkFooter,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibChunkFooter {
        pub reg_info: *mut C_GibRegionInfo,
        pub size: usize,
        pub next: *mut C_GibChunkFooter,
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * FFI functions
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

use std::mem::size_of;
use std::ptr::null_mut;
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
    scalar_bytes: usize,
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
    size: usize,
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
    match gc::garbage_collect(
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

#[no_mangle]
pub extern "C" fn gib_handle_old_to_old_indirection(
    from_footer_ptr: *mut i8,
    to_footer_ptr: *mut i8,
) -> i32 {
    match gc::handle_old_to_old_indirection(from_footer_ptr, to_footer_ptr) {
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
pub extern "C" fn gib_init_footer_at(
    chunk_end: *mut i8,
    // Total size of the chunk, *including* space required to store the footer.
    chunk_size: usize,
    refcount: u16,
) -> *mut i8 {
    unsafe { gc::init_footer_at(chunk_end, null_mut(), chunk_size, refcount) }
}

#[no_mangle]
pub extern "C" fn gib_init_zcts(generations_ptr: *mut C_GibGeneration) {
    gc::init_zcts(generations_ptr);
}

#[no_mangle]
pub extern "C" fn gib_add_to_old_zct(
    generations_ptr: *mut C_GibGeneration,
    reg_info: *const C_GibRegionInfo,
) {
    if C_NUM_GENERATIONS == 1 {
        unsafe { (*((*generations_ptr).old_zct)).insert(reg_info) };
    } else {
        todo!("NUM_GENERATIONS > 1");
    }
}

#[no_mangle]
pub extern "C" fn gib_gc_cleanup(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
) -> i32 {
    match gc::cleanup(rstack_ptr, wstack_ptr, nursery_ptr, generations_ptr) {
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
pub extern "C" fn gib_get_rust_struct_sizes(
    stack: *mut usize,
    frame: *mut usize,
    nursery: *mut usize,
    generation: *mut usize,
    reg_info: *mut usize,
    footer: *mut usize,
) {
    unsafe {
        *stack = size_of::<C_GibShadowstack>();
        *frame = size_of::<C_GibShadowstackFrame>();
        *nursery = size_of::<C_GibNursery>();
        *generation = size_of::<C_GibGeneration>();
        *reg_info = size_of::<C_GibRegionInfo>();
        *footer = size_of::<C_GibChunkFooter>();
    }
}
