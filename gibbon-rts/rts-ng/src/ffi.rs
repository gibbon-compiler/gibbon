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

    pub type GibPackedTag = u8;
    pub type GibBoxedTag = u8;
    pub type GibInt = i64;
    pub type GibFloat = f32;
    pub type GibSym = u64;
    pub type GibBool = bool;
    pub type GibPtr = *const i8;
    pub type GibCursor = *const i8;

    /// An enum in C, which is 4 bytes.
    pub type GibDatatype = u32;

    pub const REDIRECTION_TAG: GibPackedTag = 255;
    pub const INDIRECTION_TAG: GibPackedTag = 254;

    // Tags reserved for the garbage collector.
    pub const CAUTERIZED_TAG: GibPackedTag = 253;
    pub const COPIED_TO_TAG: GibPackedTag = 252;
    pub const COPIED_TAG: GibPackedTag = 251;
    pub const SCALAR_TAG: GibPackedTag = 250;

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibNursery {
        pub heap_size: usize,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
    }

    pub type GibRememberedSetElt = GibShadowstackFrame;
    pub type GibRememberedSet = GibShadowstack;

    pub type Zct = HashSet<*const GibRegionInfo>;
    pub type Outset = HashSet<*const GibRegionInfo>;

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibOldgen<'a> {
        pub rem_set: &'a mut GibRememberedSet,
        pub old_zct: &'a mut Zct,
        pub new_zct: &'a mut Zct,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibGcStats {
        pub minor_collections: u64,
        pub major_collections: u64,
        pub mem_allocated: usize,
        pub mem_copied: usize,
        pub mem_burned: usize,
        pub forwarded: u64,
        pub not_forwarded: u64,
        pub indirs_inlined: u64,
        pub indirs_not_inlined: u64,
        pub redirs_inlined: u64,
        pub redirs_not_inlined: u64,
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
    pub struct GibShadowstack {
        pub start: *mut i8,
        pub end: *mut i8,
        pub alloc: *mut i8,
    }

    #[repr(u32)]
    #[derive(Debug, PartialEq, Eq)]
    pub enum GcRootProv {
        Stk,
        RemSet,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibShadowstackFrame {
        pub ptr: *mut i8,
        pub endptr: *mut i8,
        pub gc_root_prov: GcRootProv,
        pub datatype: GibDatatype,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibRegionInfo {
        pub id: GibSym,
        pub refcount: u16,
        pub outset: *mut Outset,
        pub first_chunk_footer: *const GibOldgenChunkFooter,
    }

    pub type GibNurseryChunkFooter = u16;

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibOldgenChunkFooter {
        pub reg_info: *mut GibRegionInfo,
        pub size: usize,
        pub next: *mut GibOldgenChunkFooter,
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
    datatype: GibDatatype,
    datacon: GibPackedTag,
    scalar_bytes: usize,
    num_shortcut: usize,
    num_scalars: u8,
    num_packed: u8,
    c_field_tys: *const GibDatatype,
    c_field_tys_length: u8,
) -> i32 {
    let field_tys: Vec<GibDatatype> = unsafe {
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
    datatype: GibDatatype,
    size: usize,
) -> i32 {
    gc::info_table_insert_scalar(datatype, size);
    0
}

#[no_mangle]
pub extern "C" fn gib_garbage_collect(
    rstack_ptr: *mut GibShadowstack,
    wstack_ptr: *mut GibShadowstack,
    nursery_ptr: *mut GibNursery,
    oldgen_ptr: *mut GibOldgen,
    gc_stats: *mut GibGcStats,
    force_major: bool,
) -> i32 {
    // let Some() = rstack_ptr.as_mut();
    let rstack: &mut GibShadowstack = unsafe { &mut *rstack_ptr };
    let wstack: &mut GibShadowstack = unsafe { &mut *wstack_ptr };
    let nursery: &mut GibNursery = unsafe { &mut *nursery_ptr };
    let oldgen: &mut GibOldgen = unsafe { &mut *oldgen_ptr };
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
pub extern "C" fn gib_free_region_(
    footer: *const GibOldgenChunkFooter,
) -> i32 {
    unsafe {
        match gc::free_region(footer, null_mut()) {
            Ok(()) => 0,
            Err(err) => {
                if cfg!(debug_assertions) {
                    println!("{:?}", err);
                }
                -1
            }
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
pub extern "C" fn gib_init_zcts(oldgen_ptr: *mut GibOldgen) {
    let oldgen: &mut GibOldgen = unsafe { &mut *oldgen_ptr };
    gc::init_zcts(oldgen);
}

#[no_mangle]
pub extern "C" fn gib_insert_into_new_zct(
    oldgen_ptr: *mut GibOldgen,
    reg_info: *const GibRegionInfo,
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
    rstack_ptr: *mut GibShadowstack,
    wstack_ptr: *mut GibShadowstack,
    nursery_ptr: *mut GibNursery,
    oldgen_ptr: *mut GibOldgen,
) -> i32 {
    let rstack: &mut GibShadowstack = unsafe { &mut *rstack_ptr };
    let wstack: &mut GibShadowstack = unsafe { &mut *wstack_ptr };
    let nursery: &mut GibNursery = unsafe { &mut *nursery_ptr };
    let oldgen: &mut GibOldgen = unsafe { &mut *oldgen_ptr };
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
        *stack = size_of::<GibShadowstack>();
        *frame = size_of::<GibShadowstackFrame>();
        *nursery = size_of::<GibNursery>();
        *generation = size_of::<GibOldgen>();
        *reg_info = size_of::<GibRegionInfo>();
        *footer = size_of::<GibOldgenChunkFooter>();
        *gc_stats = size_of::<GibGcStats>();
    }
}

#[no_mangle]
pub extern "C" fn gib_print_nursery_and_oldgen(
    rstack: *const GibShadowstack,
    wstack: *const GibShadowstack,
    nursery: *const GibNursery,
    oldgen: *const GibOldgen,
) {
    unsafe {
        gc::print_nursery_and_oldgen(&*rstack, &*wstack, &*nursery, &*oldgen);
    }
}
