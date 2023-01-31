#![allow(non_camel_case_types)]

/*

Everything in this module must match its counterpart in C.
gibbon-compiler/cbits/gibbon.h and gibbon-compiler/cbits/gibbon_rts.c.

 */

pub mod c {
    /** FFI functions implemented in C. */
    use std::collections::HashSet;
    use std::os::raw::*;

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Translating Gibbon's types to Rust
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    pub type GibPackedTag = u8;
    pub type GibBoxedTag = u8;
    pub type GibInt = i64;
    pub type GibFloat = f32;
    pub type GibSym = u64;
    pub type GibChar = i8;
    pub type GibBool = bool;
    pub type GibPtr = *const i8;
    pub type GibCursor = *const i8;
    pub type GibTaggedPtr = usize;
    pub type GibThreadId = u64;

    /// An enum in C, which is 4 bytes.
    pub type GibDatatype = u32;

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Globals and their accessors
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        // Chunk sizes of buffers, see GitHub #79 and #110.
        pub fn gib_get_biginf_init_chunk_size() -> usize;
        pub fn gib_get_inf_init_chunk_size() -> usize;

        // Runtime arguments, values updated by the flags parser.
        pub fn gib_get_size_param() -> GibInt;
        pub fn gib_get_iters_param() -> GibInt;
        pub fn gib_read_bench_prog_param() -> *const c_char;
        pub fn gib_read_benchfile_param() -> *const c_char;
        pub fn gib_read_arrayfile_param() -> *const c_char;
        pub fn gib_read_arrayfile_length_param() -> u64;

        /// Number of regions allocated.
        pub fn gib_read_region_count() -> i64;

        /// Invariant: should always be equal to max(sym_table_keys).
        pub fn gib_read_gensym_counter() -> GibSym;
    }

    // Tags reserved for generated code.
    pub const REDIRECTION_TAG: GibPackedTag = 255;
    pub const INDIRECTION_TAG: GibPackedTag = 254;

    // Tags reserved for the garbage collector.
    pub const CAUTERIZED_TAG: GibPackedTag = 253;
    pub const COPIED_TO_TAG: GibPackedTag = 252;
    pub const COPIED_TAG: GibPackedTag = 251;
    pub const SCALAR_TAG: GibPackedTag = 250;

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Pointer tagging
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /*
    extern "C" {
        // TODO: macro.
        pub fn gib_store_tag();
        pub fn gib_untag();
        pub fn gib_get_tag();
    }
    */

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Allocators
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        pub fn gib_alloc(size: usize) -> *mut c_void;
        pub fn gib_scoped_alloc(size: usize) -> *mut c_void;
        pub fn gib_free(ptr: *mut c_void);
    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Arenas
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibArena {
        pub ind: c_int,
        pub mem: *mut c_char,
        pub reflist: *mut c_void,
    }

    extern "C" {
        /// Arenas.
        pub fn gib_alloc_arena() -> *mut GibArena;
        pub fn gib_free_arena(ar: *mut GibArena);
        pub fn gib_extend_arena(ar: *mut GibArena, size: c_int) -> GibCursor;
    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Arena-based dictionaries
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibSymDict {
        pub next: *mut GibSymDict,
        pub key: GibSym,
        pub ptrval: *mut c_void,
    }

    extern "C" {
        pub fn gib_dict_alloc(ar: *mut GibArena) -> *mut GibSymDict;
        pub fn gib_dict_insert_ptr(
            ar: *mut GibArena,
            ptr: *mut GibSymDict,
            key: GibSym,
            val: GibPtr,
        ) -> *mut GibSymDict;
        pub fn gib_dict_lookup_ptr(
            ptr: *mut GibSymDict,
            key: GibSym,
        ) -> GibPtr;
    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Sets
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /*
    #[repr(C)]
    #[derive(Debug)]
    pub struct GibSymSet {
        pub val: c_int,
        // TODO: uthash.
        pub hh: c_void,
    }

    extern "C" {
        pub fn gib_empty_set() -> *mut GibSymSet;
        pub fn gib_insert_set(set: *mut GibSymSet, sym: c_int) -> *mut GibSymSet;
        pub fn gib_contains_set(set: *mut GibSymSet, sym: c_int) -> GibBool;
    }
    */

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Sym Hash
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /*
    #[repr(C)]
    #[derive(Debug)]
    pub struct GibSymHash {
        pub key: c_int,
        pub val: c_int,
        // TODO: uthash.
        pub hh: c_void,
    }
    pub type GibIntHash = GibSymHash;

    extern "C" {
        pub fn gib_empty_hash() -> *mut GibSymHash;
        pub fn gib_insert_hash(
            hash: *mut GibSymHash,
            k: c_int,
            v: c_int,
        ) -> *mut GibSymHash;
        pub fn gib_lookup_hash(hash: *mut GibSymHash, k: c_int) -> GibSym;
        pub fn gib_contains_hash(hash: *mut GibSymHash, sym: c_int) -> GibBool;
    }

    */

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Symbol table
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /*
    #[repr(C)]
    #[derive(Debug)]
    pub struct GibSymtable {
        pub idx: GibSym,
        pub value: [c_char; 256usize],
        // TODO: uthash.
        pub hh: c_void,
    }

    extern "C" {
        pub fn gib_add_symbol(idx: GibSym, value: *mut c_char);
        pub fn gib_set_newline(idx: GibSym);
        pub fn gib_set_space(idx: GibSym);
        pub fn gib_set_comma(idx: GibSym);
        pub fn gib_set_leftparen(idx: GibSym);
        pub fn gib_set_rightparen(idx: GibSym);
        pub fn gib_print_symbol(idx: GibSym) -> c_int;
        pub fn gib_gensym() -> GibSym;
        pub fn gib_free_symtable();
    }

    */

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Vectors
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibVector {
        pub lower: i64,
        pub upper: i64,
        pub elt_size: usize,
        pub data: *mut c_void,
    }

    extern "C" {
        pub fn gib_vector_alloc(
            num: GibInt,
            elt_size: usize,
        ) -> *mut GibVector;
        pub fn gib_vector_length(vec: *mut GibVector) -> GibInt;
        pub fn gib_vector_is_empty(vec: *mut GibVector) -> GibBool;
        pub fn gib_vector_slice(
            i: GibInt,
            n: GibInt,
            vec: *mut GibVector,
        ) -> *mut GibVector;
        pub fn gib_vector_nth(vec: *mut GibVector, i: GibInt) -> *mut c_void;
        pub fn gib_vector_inplace_update(
            vec: *mut GibVector,
            i: GibInt,
            elt: *mut c_void,
        ) -> *mut GibVector;
        pub fn gib_vector_copy(vec: *mut GibVector) -> *mut GibVector;
        /*
            fn gib_vector_inplace_sort(
                vec: *mut GibVector,
                // TODO: comparison function type.
                cmp: c_void,
            ) -> *mut GibVector;
            fn gib_vector_sort(
                vec: *mut GibVector,
                // TODO: comparison function type.
                cmp: c_void,
            ) -> *mut GibVector;
        */
        pub fn gib_vector_concat(vec: *mut GibVector) -> *mut GibVector;
        pub fn gib_vector_free(vec: *mut GibVector);
        pub fn gib_vector_merge(
            vec1: *mut GibVector,
            vec2: *mut GibVector,
        ) -> *mut GibVector;
        pub fn gib_print_timing_array(times: *mut GibVector);
        pub fn gib_sum_timing_array(times: *mut GibVector) -> f64;
    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Linked lists
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibList {
        pub data_size: usize,
        pub data: *mut c_void,
        pub next: *mut GibList,
    }

    extern "C" {
        pub fn gib_list_bumpalloc_save_state();
        pub fn gib_list_bumpalloc_restore_state();
        pub fn gib_list_alloc(data_size: usize) -> *mut GibList;
        pub fn gib_list_is_empty(ls: *mut GibList) -> GibBool;
        pub fn gib_list_cons(
            elt: *mut c_void,
            ls: *mut GibList,
        ) -> *mut GibList;
        pub fn gib_list_head(ls: *mut GibList) -> *mut c_void;
        pub fn gib_list_tail(ls: *mut GibList) -> *mut GibList;
        pub fn gib_list_free(ls: *mut GibList);
        pub fn gib_list_copy(ls: *mut GibList) -> *mut GibList;
    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Ppm images
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibPixel {
        pub field0: GibInt,
        pub field1: GibInt,
        pub field2: GibInt,
    }

    extern "C" {
        pub fn gib_write_ppm(
            filename: *mut c_char,
            width: GibInt,
            height: GibInt,
            pixels: *mut GibVector,
        );

        /*
        pub fn gib_write_ppm_loop(
            // TODO: FILE.
            fp: *mut c_void,
            idx: GibInt,
            end: GibInt,
            pixels: *mut GibVector,
        );
        */

    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Threads and parallelism
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Memory Management; regions, chunks, GC etc.
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */
    #[repr(C)]
    #[derive(Debug)]
    pub struct GibChunk {
        pub start: *mut i8,
        pub end: *mut i8,
    }

    /// Shadow-stack.
    #[repr(C)]
    #[derive(Debug)]
    pub struct GibShadowstack {
        pub start: *mut i8,
        pub end: *mut i8,
        pub alloc: *mut i8,
    }

    #[repr(u32)]
    #[derive(Debug, PartialEq, Eq)]
    pub enum GibGcRootProv {
        Stk = 0,
        RemSet = 1,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibShadowstackFrame {
        pub ptr: *mut i8,
        pub endptr: *mut i8,
        pub gc_root_prov: GibGcRootProv,
        pub datatype: GibDatatype,
    }

    pub type GibRememberedSetElt = GibShadowstackFrame;
    pub type GibRememberedSet = GibShadowstack;

    /// Nursery.
    #[repr(C)]
    #[derive(Debug)]
    pub struct GibNursery {
        pub heap_size: usize,
        pub heap_start: *const i8,
        pub heap_end: *const i8,
        pub alloc: *const i8,
    }

    pub type Zct = HashSet<*const GibRegionInfo>;
    pub type Outset = HashSet<*const GibRegionInfo>;

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibOldgen {
        pub rem_set: *mut GibRememberedSet,
        pub old_zct: *mut Zct,
        pub new_zct: *mut Zct,
    }

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibOldgen_ {
        pub rem_set_: *mut GibRememberedSet,
        pub old_zct_: *mut c_void,
        pub new_zct_: *mut c_void,
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
    #[derive(Clone)]
    pub struct GibRegionInfo {
        pub id: GibSym,
        pub refcount: u16,
        pub outset: *mut Outset,
        pub first_chunk_footer: *const GibOldgenChunkFooter,
    }

    use std::fmt;
    impl fmt::Debug for GibRegionInfo {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "GibRegionInfo {{id: {}, refcount: {}, outset: {:?}, first_chunk_footer: {:?} }}",
                   self.id,
                   self.refcount,
                   unsafe { (*self.outset).clone() },
                   unsafe { (*self.first_chunk_footer).clone() })
        }
    }

    pub type GibNurseryChunkFooter = u16;

    #[repr(C)]
    #[derive(Debug, Clone)]
    pub struct GibOldgenChunkFooter {
        pub reg_info: *mut GibRegionInfo,
        pub size: usize,
        pub next: *mut GibOldgenChunkFooter,
    }

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Ensure that C and Rust agree on sizes
     * of structs that cross the boundary.
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */
    extern "C" {
        pub fn gib_check_rust_struct_sizes();
    }

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Region allocation and growth
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        // Region allocation.
        pub fn gib_alloc_region(size: usize) -> GibChunk;
        pub fn gib_alloc_region_on_heap(size: usize) -> GibChunk;
        pub fn gib_grow_region(
            writeloc_addr: *mut *mut c_char,
            footer_addr: *mut *mut c_char,
        );
        pub fn gib_free_region(footer_ptr: *mut c_char);

        /// Trigger GC.
        pub fn gib_perform_GC(force_major: bool);

        // Functions related to counting the number of allocated regions.
        pub fn gib_alloc_counted_region(size: usize) -> GibChunk;
        pub fn gib_print_global_region_count();
        pub fn gib_alloc_counted_struct(size: usize) -> *mut c_void;
    }

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Nursery
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        pub static gib_global_nurseries: *mut GibNursery;
        pub static gib_global_oldgen: *mut GibOldgen_;
    }

    impl GibOldgen {
        pub fn from_ffi(
            oldgen_ptr: *mut GibOldgen_,
        ) -> &'static mut GibOldgen {
            unsafe { &mut *(oldgen_ptr as *mut GibOldgen) }
        }
    }

    /*
    extern "C" {
        // TODO: macro.
        fn gib_addr_in_nursery(ptr: *const char) -> bool;
    }
    */

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Shadow-stack
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        pub static gib_global_read_shadowstacks: *mut GibShadowstack;
        pub static gib_global_write_shadowstacks: *mut GibShadowstack;
    }

    extern "C" {
        pub fn gib_shadowstack_push_noinline(
            stack: *const GibShadowstack,
            ptr: *const i8,
            endptr: *const i8,
            gc_root_prov: GibGcRootProv,
            datatype: GibDatatype,
        );
        pub fn gib_shadowstack_pop_noinline(
            stack: *const GibShadowstack,
        ) -> *const GibShadowstackFrame;
        pub fn gib_shadowstack_peek_noinline(
            stack: *const GibShadowstack,
        ) -> *const GibShadowstackFrame;

        /* TODO: macro
                fn gib_shadowstack_length(stack: *const GibShadowstack) -> i32;
                fn gib_shadowstack_print_all(stack: *const GibShadowstack);
        */
    }

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Remembered set
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /*
    extern "C" {
        // TODO: macro.
        fn gib_remset_push(
            stack: *const GibRememberedSet,
            ptr: *const i8,
            endptr: *const i8,
            gc_root_prov: GibGcRootProv,
            datatype: GibDatatype,
        );
        fn gib_remset_pop(
            stack: *const GibRememberedSet,
        ) -> *const GibShadowstackFrame;
        fn gib_remset_length(stack: *const GibRememberedSet) -> i32;
        fn gib_remset_print_all(stack: *const GibRememberedSet);
    }
    */

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Write barrier
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     *
     */

    /*
    // TODO: macro.
    extern "C" {
        pub fn gib_indirection_barrier(
            // Address where the indirection tag is written.
            from: *const i8,
            from_footer: *const i8,
            // Address of the pointed-to data.
            to: *const i8,
            to_footer: *const i8,
            // Data type written at from/to.
            datatype: GibDatatype,
        );
    }
     */

    extern "C" {
        pub fn gib_indirection_barrier_noinline(
            // Address where the indirection tag is written.
            from: GibCursor,
            from_footer: GibCursor,
            // Address of the pointed-to data.
            to: GibCursor,
            to_footer: GibCursor,
            // Data type written at from/to.
            datatype: GibDatatype,
        );
    }

    /*
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Save and restore GC's state
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    /*

    #[repr(C)]
    #[derive(Debug)]
    pub struct GibGcStateSnapshot {
        // nursery
        nursery_alloc: *const i8,
        nursery_heap_start: *const i8,

        // generations
        gen_rem_set_alloc: *const i8,
        gen_old_zct: *const Zct,
        gen_new_zct: *const Zct,

        // shadow-stacks
        ss_read_alloc: *const i8,
        ss_write_alloc: *const i8,

        // region metadata
        num_regions: u64,
        reg_info_addrs: *const *const GibRegionInfo,
        outsets: *const *const i8,
    }

    extern "C" {
        pub fn gib_gc_init_state(num_regions: u64) -> *mut GibGcStateSnapshot;
        /*
        pub fn gib_gc_save_state(
            snapshot: *mut GibGcStateSnapshot,
            num_regions: u64,
            // TODO: variadic arguments.
        );
        */
        pub fn gib_gc_restore_state(snapshot: *mut GibGcStateSnapshot);
        pub fn gib_gc_free_state(snapshot: *mut GibGcStateSnapshot);
    }

    */

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * Helpers
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        pub fn gib_show_usage(argv: *mut *mut c_char);
        pub fn gib_avg(arr: *const f64, n: c_int) -> f64;
        /*
        // TODO: timespec.
        pub fn gib_difftimespecs(t0: *mut c_void, t1: *mut c_void) -> f64;
        */
        pub fn gib_compare_doubles(
            a: *const c_void,
            b: *const c_void,
        ) -> c_int;
        pub fn gib_expll(base: GibInt, pow: GibInt) -> GibInt;
        pub fn gib_get_num_processors() -> GibInt;
    }

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     * RTS initialization and clean up
     * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
     */

    extern "C" {
        pub fn gib_nursery_realloc(
            nursery: *mut GibNursery,
            nsize: usize,
        ) -> usize;
        pub fn gib_init(argc: c_int, argv: *mut *mut c_char) -> c_int;
        pub fn gib_exit() -> c_int;
    }
}

pub mod rs {
    /** FFI functions implemented in Rust. */
    use std::mem::size_of;
    use std::ptr::null_mut;
    use std::slice;

    use crate::ffi::c::*;
    use crate::gc;

    /* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

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

    pub extern "C" fn gib_info_table_clear() -> i32 {
        gc::info_table_clear();
        0
    }

    pub extern "C" fn gib_info_table_print() -> i32 {
        gc::info_table_print();
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
        oldgen_ptr: *mut GibOldgen_,
        gc_stats: *mut GibGcStats,
        force_major: bool,
    ) -> i32 {
        // let Some() = rstack_ptr.as_mut();
        let rstack: &mut GibShadowstack = unsafe { &mut *rstack_ptr };
        let wstack: &mut GibShadowstack = unsafe { &mut *wstack_ptr };
        let nursery: &mut GibNursery = unsafe { &mut *nursery_ptr };
        let oldgen: &mut GibOldgen = GibOldgen::from_ffi(oldgen_ptr);
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
        unsafe {
            gc::init_footer_at(chunk_end, null_mut(), chunk_size, refcount)
        }
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
    pub extern "C" fn gib_clone_outset(
        outset: *const Outset,
    ) -> *const Outset {
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
        oldgen_ptr: *mut GibOldgen_,
    ) -> i32 {
        let rstack: &mut GibShadowstack = unsafe { &mut *rstack_ptr };
        let wstack: &mut GibShadowstack = unsafe { &mut *wstack_ptr };
        let nursery: &mut GibNursery = unsafe { &mut *nursery_ptr };
        let oldgen: &mut GibOldgen = GibOldgen::from_ffi(oldgen_ptr);
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
            gc::print_nursery_and_oldgen(
                &*rstack, &*wstack, &*nursery, &*oldgen,
            );
        }
    }
}
