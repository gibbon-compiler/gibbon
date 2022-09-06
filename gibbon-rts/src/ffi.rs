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

    // Tags reserved for the garbage collector.
    pub const C_CAUTERIZED_TAG: C_GibPackedTag = 253;
    pub const C_COPIED_TO_TAG: C_GibPackedTag = 252;
    pub const C_COPIED_TAG: C_GibPackedTag = 251;
    pub const C_SCALAR_TAG: C_GibPackedTag = 250;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibNursery {
        pub heap_size: usize,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
    }

    pub type C_GibRememberedSetElt = C_GibShadowstackFrame;
    pub type C_GibRememberedSet = C_GibShadowstack;

    pub type Zct = HashSet<*const C_GibRegionInfo>;
    pub type Outset = HashSet<*const C_GibRegionInfo>;

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibOldgen<'a> {
        pub rem_set: &'a mut C_GibRememberedSet,
        pub old_zct: &'a mut Zct,
        pub new_zct: &'a mut Zct,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibGcStats {
        pub minor_collections: u64,
        pub major_collections: u64,
        pub mem_allocated: usize,
        pub mem_copied: usize,
        pub mem_burned: usize,
        pub nursery_regions: u64,
        pub oldgen_regions: u64,
        pub gc_elapsed_time: f64,
        pub gc_cpu_time: f64,
        pub gc_rootset_sort_time: f64,
        pub gc_burn_time: f64,
        pub gc_find_fwdptr_time: f64,
        pub gc_info_tbl_lkp_time: f64,
        pub gc_zct_mgmt_time: f64,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibShadowstack {
        pub start: *mut i8,
        pub end: *mut i8,
        pub alloc: *mut i8,
    }

    #[repr(u32)]
    #[derive(Debug, PartialEq, Eq)]
    pub enum C_GcRootProv {
        Stk,
        RemSet,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibShadowstackFrame {
        pub ptr: *mut i8,
        pub endptr: *mut i8,
        pub gc_root_prov: C_GcRootProv,
        pub datatype: C_GibDatatype,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibRegionInfo {
        pub id: C_GibSym,
        pub refcount: u16,
        pub outset: *mut Outset,
        pub first_chunk_footer: *const C_GibOldgenChunkFooter,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct C_GibOldgenChunkFooter {
        pub reg_info: *mut C_GibRegionInfo,
        pub size: usize,
        pub next: *mut C_GibOldgenChunkFooter,
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
pub extern "C" fn gib_info_table_initialize(size: usize) -> i32 {
    gc::info_table_initialize(size);
    0
}

#[no_mangle]
pub extern "C" fn gib_info_table_finalize() -> i32 {
    gc::info_table_finalize();
    0
}

#[no_mangle]
pub extern "C" fn gib_info_table_insert_packed_dcon(
    datatype: C_GibDatatype,
    datacon: C_GibPackedTag,
    scalar_bytes: usize,
    num_shortcut: usize,
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
        num_shortcut,
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
    gc::info_table_insert_scalar(datatype, size);
    0
}

#[no_mangle]
pub extern "C" fn gib_garbage_collect(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    oldgen_ptr: *mut C_GibOldgen,
    gc_stats: *mut C_GibGcStats,
    force_major: bool,
) -> i32 {
    // let Some() = rstack_ptr.as_mut();
    let rstack: &mut C_GibShadowstack = unsafe { &mut *rstack_ptr };
    let wstack: &mut C_GibShadowstack = unsafe { &mut *wstack_ptr };
    let nursery: &mut C_GibNursery = unsafe { &mut *nursery_ptr };
    let oldgen: &mut C_GibOldgen = unsafe { &mut *oldgen_ptr };
    match gc::garbage_collect(
        rstack,
        wstack,
        nursery,
        oldgen,
        gc_stats,
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
) {
    unsafe {
        gc::handle_old_to_old_indirection(from_footer_ptr, to_footer_ptr);
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
pub extern "C" fn gib_init_zcts(oldgen_ptr: *mut C_GibOldgen) {
    let oldgen: &mut C_GibOldgen = unsafe { &mut *oldgen_ptr };
    gc::init_zcts(oldgen);
}

#[no_mangle]
pub extern "C" fn gib_insert_into_new_zct(
    oldgen_ptr: *mut C_GibOldgen,
    reg_info: *const C_GibRegionInfo,
) {
    unsafe { (*((*oldgen_ptr).new_zct)).insert(reg_info) };
}

#[no_mangle]
pub extern "C" fn gib_clone_zct(zct: *const Zct) -> *const Zct {
    unsafe {
        let zct2: Zct = (*zct).clone();
        Box::into_raw(Box::new(zct2))
    }
}

#[no_mangle]
pub extern "C" fn gib_clone_outset(outset: *const Outset) -> *const Outset {
    unsafe {
        let outset2: Outset = (*outset).clone();
        Box::into_raw(Box::new(outset2))
    }
}

#[no_mangle]
pub extern "C" fn gib_free_zct(zct: *mut Zct) {
    unsafe { drop(Box::from_raw(zct)) }
}

#[no_mangle]
pub extern "C" fn gib_free_outset(outset: *mut Outset) {
    unsafe { drop(Box::from_raw(outset)) }
}

#[no_mangle]
pub extern "C" fn gib_gc_cleanup(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    oldgen_ptr: *mut C_GibOldgen,
) -> i32 {
    let rstack: &mut C_GibShadowstack = unsafe { &mut *rstack_ptr };
    let wstack: &mut C_GibShadowstack = unsafe { &mut *wstack_ptr };
    let nursery: &mut C_GibNursery = unsafe { &mut *nursery_ptr };
    let oldgen: &mut C_GibOldgen = unsafe { &mut *oldgen_ptr };
    match gc::cleanup(rstack, wstack, nursery, oldgen) {
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
    gc_stats: *mut usize,
) {
    unsafe {
        *stack = size_of::<C_GibShadowstack>();
        *frame = size_of::<C_GibShadowstackFrame>();
        *nursery = size_of::<C_GibNursery>();
        *generation = size_of::<C_GibOldgen>();
        *reg_info = size_of::<C_GibRegionInfo>();
        *footer = size_of::<C_GibOldgenChunkFooter>();
        *gc_stats = size_of::<C_GibGcStats>();
    }
}

#[no_mangle]
pub extern "C" fn gib_print_nursery_and_oldgen(
    rstack: *const C_GibShadowstack,
    wstack: *const C_GibShadowstack,
    nursery: *const C_GibNursery,
    oldgen: *const C_GibOldgen,
) {
    unsafe {
        gc::print_nursery_and_oldgen(&*rstack, &*wstack, &*nursery, &*oldgen);
    }
}
