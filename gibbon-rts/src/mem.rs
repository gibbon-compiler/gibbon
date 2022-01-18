#![allow(dead_code)]

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
pub enum RtsError {
    InfoTable(String),
    Gc(String),
}

impl Error for RtsError {
    fn description(&self) -> &str {
        match *self {
            RtsError::InfoTable(ref err) => err,
            RtsError::Gc(ref err) => err,
        }
    }
}

impl std::fmt::Display for RtsError {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        write!(f, "{:?}", *self)
    }
}

pub type Result<T> = std::result::Result<T, RtsError>;

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
            Err(_) => Err(RtsError::InfoTable(
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
                return Err(RtsError::InfoTable(
                    "INFO_TABLE not initialized.".to_string(),
                ))
            }
            Some(tbl) => tbl,
        }
    };
    match tbl.entry(datatype).or_insert(DatatypeInfo::Packed(HashMap::new())) {
        DatatypeInfo::Packed(packed_info) => {
            if packed_info.contains_key(&datacon) {
                return Err(RtsError::InfoTable(format!(
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
        DatatypeInfo::Scalar(_) => Err(RtsError::InfoTable(format!(
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
                return Err(RtsError::InfoTable(
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
    cbt: ffi::C_GibCursorBindType,
    cbt_baseptr: *const i8,
}

/// There are separate stacks for read and write cursors.
enum ShadowstackModality {
    Read,
    Write,
}

/// An iterator to traverse the shadowstack.
struct ShadowstackIter {
    run_ptr: *const i8,
    end_ptr: *const i8,
}

impl ShadowstackIter {
    fn new(rw: ShadowstackModality) -> ShadowstackIter {
        let (run_ptr, end_ptr) = match rw {
            ShadowstackModality::Read => unsafe {
                (
                    gib_global_read_shadowstack_start,
                    gib_global_read_shadowstack_alloc_ptr,
                )
            },
            ShadowstackModality::Write => unsafe {
                (
                    gib_global_write_shadowstack_start,
                    gib_global_write_shadowstack_alloc_ptr,
                )
            },
        };
        debug_assert!(run_ptr <= end_ptr);
        ShadowstackIter { run_ptr, end_ptr }
    }
}

impl Iterator for ShadowstackIter {
    type Item = *mut ShadowstackFrame;

    fn next(&mut self) -> Option<Self::Item> {
        if self.run_ptr < self.end_ptr {
            let frame = self.run_ptr as *mut ShadowstackFrame;
            unsafe {
                self.run_ptr = self.run_ptr.add(size_of::<ShadowstackFrame>());
            }
            Some(frame)
        } else {
            None
        }
    }
}

/// This function is defined here to test if all the globals are set up
/// properly. Its output should match the C version's output.
fn shadowstack_debugprint() {
    println!(
        "stack of readers, length={}:",
        shadowstack_length(ShadowstackModality::Read)
    );
    shadowstack_print_all(ShadowstackModality::Read);
    println!(
        "stack of writers, length={}:",
        shadowstack_length(ShadowstackModality::Write)
    );
    shadowstack_print_all(ShadowstackModality::Write);
}

/// Length of the shadow-stack.
fn shadowstack_length(rw: ShadowstackModality) -> isize {
    unsafe {
        let (start_ptr, end_ptr) = match rw {
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
fn shadowstack_print_all(rw: ShadowstackModality) {
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
    // Print some debugging information.
    if cfg!(debug_assertions) {
        println!("Triggered GC!!!");
        unsafe {
            assert!(gib_global_nursery_initialized);
            assert!(
                gib_global_nursery_alloc_ptr
                    < gib_global_nursery_alloc_ptr_end
            );
            assert!(gib_global_shadowstack_initialized);
            assert!(
                gib_global_read_shadowstack_alloc_ptr
                    >= gib_global_read_shadowstack_start
            );
            assert!(
                gib_global_read_shadowstack_alloc_ptr
                    < gib_global_read_shadowstack_end
            );
            assert!(
                gib_global_write_shadowstack_alloc_ptr
                    >= gib_global_write_shadowstack_start
            );
            assert!(
                gib_global_write_shadowstack_alloc_ptr
                    < gib_global_write_shadowstack_end
            );
        }
        shadowstack_debugprint();
    }
    if allocator_in_tospace() {
        promote_to_oldgen()
    } else {
        let current_space_avail = allocator_space_available();
        match copy_to_tospace() {
            Ok(()) => {
                let new_space_avail = allocator_space_available();
                // Promote everything to the older generation if we couldn't
                // free up any space after a minor collection.
                if current_space_avail == new_space_avail {
                    promote_to_oldgen()
                } else {
                    Ok(())
                }
            }
            Err(err) => Err(err),
        }
    }
}

fn copy_to_tospace() -> Result<()> {
    allocator_switch_to_tospace();
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
            let src = (*frame).ptr as *mut i8;
            let datatype = (*frame).datatype;
            match INFO_TABLE.get().unwrap().get(&datatype) {
                None => {
                    return Err(RtsError::Gc(format!(
                        "copy_readers: Unknown datatype, {:?}",
                        datatype
                    )))
                }
                // A scalar type that can be copied directly.
                Some(DatatypeInfo::Scalar(size)) => {
                    match nursery_malloc(*size as u64) {
                        Ok((dst, _)) => {
                            copy_nonoverlapping(src, dst, *size as usize);
                            (*frame).ptr = dst
                        }
                        Err(err) => return Err(err),
                    }
                }
                // A packed type that should copied by referring to the info table.
                Some(DatatypeInfo::Packed(_packed_info)) => {
                    // TODO(ckoparkar): How big should this chunk be?
                    //
                    // If we have variable sized initial chunks based on the
                    // region bound analysis, maybe we'll have to store that
                    // info in a chunk footer. Then that size can somehow
                    // influence how big should this new to-space chunk be.
                    // Using 1024 for now.
                    match nursery_malloc(1024) {
                        Ok((dst, dst_end)) => {
                            match copy_packed(&datatype, src, dst, dst_end) {
                                Ok(_) => (*frame).ptr = dst,
                                Err(err) => return Err(err),
                            }
                        }
                        Err(err) => return Err(err),
                    }
                }
            }
        }
    }
    Ok(())
}

fn copy_packed(
    datatype: &ffi::C_GibDatatype,
    src: *mut i8,
    mut dst: *mut i8,
    mut dst_end: *const i8,
) -> Result<(*mut i8, *mut i8)> {
    unsafe {
        match INFO_TABLE.get().unwrap().get(datatype) {
            None => {
                return Err(RtsError::Gc(format!(
                    "copy_packed: Unknown datatype, {:?}",
                    datatype
                )));
            }
            Some(DatatypeInfo::Scalar(size)) => {
                copy_nonoverlapping(src, dst, *size as usize);
                Ok((src.add(*size as usize), dst.add(*size as usize)))
            }
            Some(DatatypeInfo::Packed(packed_info)) => {
                let (tag, src_next_c): (ffi::C_GibPackedTag, *const i8) =
                    read(src);
                // Special tags.
                match tag {
                    INDIRECTION_TAG => todo!(),
                    REDIRECTION_TAG => todo!(),
                    COPIED_TAG => todo!(),
                    COPIED_TO_TAG => todo!(),
                    CAUTERIZED_TAG => todo!(),
                    _ => {
                        let dcon_info = packed_info.get(&tag).unwrap();
                        let DataconInfo {
                            scalar_bytes,
                            field_tys,
                            num_packed,
                            ..
                        } = dcon_info;
                        // If there's enough space, write a COPIED_TO tag and
                        // dst's address at src. Otherwise write a COPIED tag.
                        if (*scalar_bytes) > 8 {
                            write(src, COPIED_TO_TAG);
                            let src_plus_one = src.add(1);
                            write(src_plus_one, dst);
                        } else {
                            write(src, COPIED_TAG);
                        }
                        // Bounds check before copying the fields.
                        let space_avail = dst_end.offset_from(dst);
                        let space_reqd = if *num_packed == 0 {
                            *scalar_bytes as isize
                        } else {
                            // Additional 9 bytes for the redirection node.
                            9 + *scalar_bytes as isize
                        };
                        if space_avail < space_reqd {
                            match nursery_malloc(1024) {
                                Ok((new_dst, new_dst_end)) => {
                                    let next = write(dst, REDIRECTION_TAG);
                                    write(next, new_dst);
                                    dst = new_dst;
                                    dst_end = new_dst_end;
                                }
                                Err(err) => return Err(err),
                            }
                        }
                        // Copy the tag and the fields.
                        let mut src_next = src_next_c as *mut i8;
                        let mut dst_next = write(dst, tag);
                        dst_next.copy_from_nonoverlapping(
                            src_next,
                            *scalar_bytes as usize,
                        );
                        src_next = src_next.add(*scalar_bytes as usize);
                        dst_next = dst_next.add(*scalar_bytes as usize);
                        for ty in field_tys.iter() {
                            match copy_packed(ty, src_next, dst_next, dst_end)
                            {
                                Ok((src_next_next, dst_next_next)) => {
                                    src_next = src_next_next;
                                    dst_next = dst_next_next;
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
}

fn promote_to_oldgen() -> Result<()> {
    if cfg!(debug_assertions) {
        println!("Promoting to older generation...");
    }
    Ok(())
}

#[inline]
fn nursery_malloc(size: u64) -> Result<(*mut i8, *const i8)> {
    unsafe {
        let old = gib_global_nursery_alloc_ptr as *mut i8;
        let bump = gib_global_nursery_alloc_ptr.add(size as usize);
        // Check if there's enough space in the nursery to fulfill the request.
        //
        // CSK: Do we have to check this? Since we're copying things which are
        // already in the from-space, in the worst case we'll copy everything
        // but all of from-space should always fit in the to-space.
        if bump <= gib_global_nursery_alloc_ptr_end {
            gib_global_nursery_alloc_ptr = bump;
            Ok((old, bump))
        } else {
            Err(RtsError::Gc(format!(
                "nursery_malloc: out of space, requested={:?}, available={:?}",
                size,
                gib_global_nursery_alloc_ptr_end
                    .offset_from(gib_global_nursery_alloc_ptr)
            )))
        }
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

fn allocator_space_available() -> isize {
    unsafe {
        gib_global_nursery_alloc_ptr_end
            .offset_from(gib_global_nursery_alloc_ptr)
    }
}

fn allocator_switch_to_tospace() {
    unsafe {
        gib_global_nursery_alloc_ptr = gib_global_nursery_to_space_start;
        gib_global_nursery_alloc_ptr_end = gib_global_nursery_to_space_end;
    }
}

#[inline]
unsafe fn read<A>(cursor: *const i8) -> (A, *const i8) {
    let cursor2 = cursor as *const A;
    (cursor2.read_unaligned(), cursor2.add(1) as *const i8)
}

#[inline]
unsafe fn write<A>(cursor: *mut i8, val: A) -> *mut i8 {
    let cursor2 = cursor as *mut A;
    cursor2.write_unaligned(val);
    cursor2.add(1) as *mut i8
}
