/*!

Memory Management; regions, chunks, GC etc.

 */

use std::collections::HashMap;
use std::error::Error;
use std::lazy::OnceCell;
use std::mem::size_of;
use std::ptr::copy_nonoverlapping;

use crate::ffi::types as ffi;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Custom error type
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#[derive(Debug)]
pub enum MemError {
    InfoTable(String),
    Gc(String),
}

impl Error for MemError {
    fn description(&self) -> &str {
        match *self {
            MemError::InfoTable(ref err) => err,
            MemError::Gc(ref err) => err,
        }
    }
}

impl std::fmt::Display for MemError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", *self)
    }
}

pub type Result<T> = std::result::Result<T, MemError>;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Info table
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#[derive(Debug)]
struct DataconInfo {
    // Number of bytes before the first packed field.
    scalar_bytes: u8,
    num_scalars: u8,
    num_packed: u8,
    field_tys: Vec<ffi::C_GibDatatype>,
}

#[derive(Debug)]
enum DatatypeInfo {
    Scalar(u8),
    Packed(HashMap<ffi::C_GibPackedTag, DataconInfo>),
}

/// The global info table.
static mut INFO_TABLE: OnceCell<HashMap<ffi::C_GibDatatype, DatatypeInfo>> =
    OnceCell::new();

#[inline]
pub fn info_table_initialize() -> Result<()> {
    unsafe {
        match INFO_TABLE.set(HashMap::new()) {
            Ok(()) => Ok(()),
            Err(_) => Err(MemError::InfoTable(
                "Couldn't initialize info-table.".to_string(),
            )),
        }
    }
}

#[inline]
pub fn info_table_insert_packed_dcon(
    datatype: ffi::C_GibDatatype,
    datacon: ffi::C_GibPackedTag,
    scalar_bytes: u8,
    num_scalars: u8,
    num_packed: u8,
    field_tys: Vec<ffi::C_GibDatatype>,
) -> Result<()> {
    let tbl = unsafe {
        match INFO_TABLE.get_mut() {
            None => {
                return Err(MemError::InfoTable(
                    "INFO_TABLE not initialized.".to_string(),
                ))
            }
            Some(tbl) => tbl,
        }
    };
    match tbl.entry(datatype).or_insert(DatatypeInfo::Packed(HashMap::new())) {
        DatatypeInfo::Packed(packed_info) => {
            if packed_info.contains_key(&datacon) {
                return Err(MemError::InfoTable(format!(
                    "Data constructor {} already present in the info-table.",
                    datacon
                )));
            }
            packed_info.insert(
                datacon,
                DataconInfo {
                    scalar_bytes,
                    num_scalars,
                    num_packed,
                    field_tys,
                },
            );
            Ok(())
        }
        DatatypeInfo::Scalar(_) => Err(MemError::InfoTable(format!(
            "Expected a packed info-table entry for datatype {:?}, got scalar.",
            datatype
        ))),
    }
}

pub fn info_table_insert_scalar(
    datatype: ffi::C_GibDatatype,
    size: u8,
) -> Result<()> {
    let tbl = unsafe {
        match INFO_TABLE.get_mut() {
            None => {
                return Err(MemError::InfoTable(
                    "INFO_TABLE not initialized.".to_string(),
                ))
            }
            Some(tbl) => tbl,
        }
    };
    tbl.insert(datatype, DatatypeInfo::Scalar(size));
    Ok(())
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * GC
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Globals defined in C code.
extern "C" {
    // Nursery.
    static mut gib_global_nursery_from_space_start: *const i8;
    static mut gib_global_nursery_to_space_start: *const i8;
    static mut gib_global_nursery_to_space_end: *const i8;
    static mut gib_global_nursery_alloc_ptr: *const i8;
    static mut gib_global_nursery_alloc_ptr_end: *const i8;
    static mut gib_global_nursery_initialized: bool;

    // Shadow stack for input locations.
    static mut gib_global_read_shadowstack_start: *const i8;
    static mut gib_global_read_shadowstack_end: *const i8;
    static mut gib_global_read_shadowstack_alloc_ptr: *const i8;

    // Shadow stack for output locations.
    static mut gib_global_write_shadowstack_start: *const i8;
    static mut gib_global_write_shadowstack_end: *const i8;
    static mut gib_global_write_shadowstack_alloc_ptr: *const i8;

    // Flag.
    static mut gib_global_shadowstack_initialized: bool;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// Must be consistent with 'GibShadowstackFrame' defined in 'gibbon.h'.
#[repr(C)]
#[derive(Debug)]
struct ShadowstackFrame {
    ptr: *const i8,
    datatype: ffi::C_GibDatatype,
}

enum ShadowstackModality {
    Read,
    Write,
}

struct ShadowstackIter {
    run_ptr: *const i8,
    end_ptr: *const i8,
}

impl ShadowstackIter {
    fn new(rw: ShadowstackModality) -> ShadowstackIter {
        unsafe {
            match rw {
                ShadowstackModality::Read => ShadowstackIter {
                    run_ptr: gib_global_read_shadowstack_start,
                    end_ptr: gib_global_read_shadowstack_alloc_ptr,
                },

                ShadowstackModality::Write => ShadowstackIter {
                    run_ptr: gib_global_write_shadowstack_start,
                    end_ptr: gib_global_write_shadowstack_alloc_ptr,
                },
            }
        }
    }
}

impl Iterator for ShadowstackIter {
    type Item = *mut ShadowstackFrame;

    fn next(&mut self) -> Option<Self::Item> {
        if self.run_ptr < self.end_ptr {
            unsafe {
                let frame = self.run_ptr as *mut ShadowstackFrame;
                self.run_ptr = self.run_ptr.add(size_of::<ShadowstackFrame>());
                Some(frame)
            }
        } else {
            None
        }
    }
}

/// This function is defined here to test if all the globals
/// are set up properly. Its output should match the C version's output.
fn shadowstack_debugprint() {
    println!(
        "length={}, stack of readers:",
        shadowstack_length(ShadowstackModality::Read)
    );
    shadowstack_print(ShadowstackModality::Read);
    println!(
        "length={}, stack of writers:",
        shadowstack_length(ShadowstackModality::Write)
    );
    shadowstack_print(ShadowstackModality::Write);
}

/// Length of the shadow-stack.
fn shadowstack_length(rw: ShadowstackModality) -> isize {
    unsafe {
        let (start_ptr, end_ptr): (
            *const ShadowstackFrame,
            *const ShadowstackFrame,
        ) = match rw {
            ShadowstackModality::Read => (
                gib_global_read_shadowstack_start as *const ShadowstackFrame,
                gib_global_read_shadowstack_alloc_ptr
                    as *const ShadowstackFrame,
            ),
            ShadowstackModality::Write => (
                gib_global_write_shadowstack_start as *const ShadowstackFrame,
                gib_global_write_shadowstack_alloc_ptr
                    as *const ShadowstackFrame,
            ),
        };
        debug_assert!(start_ptr <= end_ptr);
        end_ptr.offset_from(start_ptr)
    }
}

/// Print all frames of the shadow-stack.
#[inline]
fn shadowstack_print(rw: ShadowstackModality) {
    let ss = ShadowstackIter::new(rw);
    for frame in ss {
        unsafe {
            println!("{:?}", *frame);
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Regions, chunks etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Must be same as "gibbon.h".
const REDIRECTION_TAG: ffi::C_GibPackedTag = 255;
const INDIRECTION_TAG: ffi::C_GibPackedTag = 254;

// Used internally in the garbage collector.
const COPIED_TAG: ffi::C_GibPackedTag = 253;
const COPIED_TO_TAG: ffi::C_GibPackedTag = 252;
const CAUTERIZED_TAG: ffi::C_GibPackedTag = 251;

pub fn collect_minor() -> Result<()> {
    if cfg!(debug_assertions) {
        println!("Trigger GC!!!");
        unsafe {
            assert!(gib_global_nursery_initialized);
            assert!(gib_global_shadowstack_initialized);
            assert!(
                gib_global_write_shadowstack_alloc_ptr
                    >= gib_global_write_shadowstack_start
            );
            assert!(
                gib_global_write_shadowstack_alloc_ptr
                    < gib_global_write_shadowstack_end
            );
            shadowstack_debugprint();
        }
    }
    if allocator_in_tospace() {
        promote_to_oldgen()
    } else {
        let current_free_space = unsafe {
            gib_global_nursery_alloc_ptr_end
                .offset_from(gib_global_nursery_alloc_ptr)
        };
        match copy_to_tospace() {
            Err(err) => return Err(err),
            Ok(()) => {
                let new_free_space = unsafe {
                    gib_global_nursery_alloc_ptr_end
                        .offset_from(gib_global_nursery_alloc_ptr)
                };
                // Promote everything to the older generation if we couldn't
                // free up any space after a minor collection.
                if current_free_space == new_free_space {
                    promote_to_oldgen()
                } else {
                    Ok(())
                }
            }
        }
    }
}

fn copy_to_tospace() -> Result<()> {
    unsafe {
        gib_global_nursery_alloc_ptr = gib_global_nursery_to_space_start;
        gib_global_nursery_alloc_ptr_end = gib_global_nursery_to_space_end;
    }
    cauterize_writers().and(copy_readers()).and(uncauterize_writers())
}

fn cauterize_writers() -> Result<()> {
    let ss = ShadowstackIter::new(ShadowstackModality::Write);
    for frame in ss {
        unsafe {
            let ptr = (*frame).ptr as *mut i8;
            write(ptr, CAUTERIZED_TAG);
        }
    }
    Ok(())
}

fn uncauterize_writers() -> Result<()> {
    Ok(())
}

fn copy_readers() -> Result<()> {
    let ss = ShadowstackIter::new(ShadowstackModality::Read);
    for frame in ss {
        unsafe {
            // println!("copy_readers frame: {:?}", *frame);
            let src = (*frame).ptr;
            let datatype = (*frame).datatype;
            // update frame.ptr to dst after copying...
            match INFO_TABLE.get().unwrap().get(&datatype) {
                None => {
                    return Err(MemError::Gc(format!(
                        "Unknown datatype, {:?}",
                        datatype
                    )))
                }
                // A scalar type that can be copied directly.
                Some(DatatypeInfo::Scalar(size)) => {
                    let (dst, _) = nursery_malloc(*size as u64);
                    copy_nonoverlapping(src, dst, *size as usize);
                }
                // A packed type that should copied by referring to the info table.
                Some(DatatypeInfo::Packed(_packed_info)) => {
                    // how big should this allocation be?
                    let (dst, dst_end) = nursery_malloc(1024);
                    let ret = copy_packed(datatype, src, dst, dst_end);
                    match ret {
                        Ok(_) => (),
                        Err(err) => return Err(err),
                    }
                }
            }
        }
    }
    Ok(())
}

fn copy_packed(
    datatype: ffi::C_GibDatatype,
    src: *const i8,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*const i8, *mut i8)> {
    unsafe {
        match INFO_TABLE.get().unwrap().get(&datatype) {
            None => {
                return Err(MemError::Gc(format!(
                    "Unknown datatype, {:?}",
                    datatype
                )));
            }
            Some(DatatypeInfo::Scalar(size)) => {
                copy_nonoverlapping(src, dst, *size as usize);
                Ok((src.add(*size as usize), dst.add(*size as usize)))
            }
            Some(DatatypeInfo::Packed(packed_info)) => {
                let (tag, mut src_next): (ffi::C_GibPackedTag, *const i8) =
                    read(src);
                if tag == INDIRECTION_TAG {
                    todo!()
                } else if tag == REDIRECTION_TAG {
                    todo!()
                } else {
                    let mut dst_next = write(dst, tag);
                    let dcon_info = packed_info.get(&tag).unwrap();
                    let DataconInfo { scalar_bytes, field_tys, .. } =
                        dcon_info;
                    dst_next.copy_from_nonoverlapping(
                        src_next,
                        *scalar_bytes as usize,
                    );
                    src_next = src_next.add(*scalar_bytes as usize);
                    dst_next = dst_next.add(*scalar_bytes as usize);
                    for ty in field_tys.iter() {
                        match copy_packed(
                            datatype, src_next, dst_next, dst_end,
                        ) {
                            Ok((src_next0, dst_next0)) => {
                                src_next = src_next0;
                                dst_next = dst_next0;
                            }
                            Err(err) => return Err(err),
                        }
                    }
                    Ok((src_next, dst_next))
                }
            }
        }
    }
}

fn promote_to_oldgen() -> Result<()> {
    if cfg!(debug_assertions) {
        println!("Promoting to older generation...");
    }
    Ok(())
}

#[inline]
fn nursery_malloc(size: u64) -> (*mut i8, *const i8) {
    unsafe {
        let old = gib_global_nursery_alloc_ptr as *mut i8;
        let bump = gib_global_nursery_alloc_ptr.add(size as usize);
        gib_global_nursery_alloc_ptr = bump;
        (old, bump)
    }
}

#[inline]
fn allocator_in_fromspace() -> bool {
    unsafe { gib_global_nursery_alloc_ptr < gib_global_nursery_to_space_start }
}

#[inline]
fn allocator_in_tospace() -> bool {
    unsafe { gib_global_nursery_alloc_ptr > gib_global_nursery_to_space_start }
}

#[inline]
fn read<A>(cursor: *const i8) -> (A, *const i8) {
    unsafe {
        let cursor2 = cursor as *const A;
        (cursor2.read_unaligned(), cursor2.add(1) as *const i8)
    }
}

#[inline]
fn write<A>(cursor: *mut i8, val: A) -> *mut i8 {
    unsafe {
        let cursor2 = cursor as *mut A;
        cursor2.write_unaligned(val);
        cursor2.add(1) as *mut i8
    }
}
