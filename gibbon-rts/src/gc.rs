#![allow(dead_code)]

/*!

Memory Management; regions, chunks, GC etc.

 */

use std::collections::HashMap;
use std::error::Error;
use std::lazy::OnceCell;
use std::mem::size_of;
use std::ptr::{copy_nonoverlapping, null, null_mut, write_bytes};

use crate::ffi::types::*;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Custom error type
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
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

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Info table
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#[derive(Debug)]
struct DataconInfo {
    /// Bytes before the first packed field.
    scalar_bytes: u8,
    /// Number of scalar fields.
    num_scalars: u8,
    /// Number of packed fields.
    num_packed: u8,
    /// Field types.
    field_tys: Vec<C_GibDatatype>,
}

#[derive(Debug)]
enum DatatypeInfo {
    Scalar(u8),
    Packed(HashMap<C_GibPackedTag, DataconInfo>),
}

/// The global info table.
static mut INFO_TABLE: OnceCell<HashMap<C_GibDatatype, DatatypeInfo>> =
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
    datatype: C_GibDatatype,
    datacon: C_GibPackedTag,
    scalar_bytes: u8,
    num_scalars: u8,
    num_packed: u8,
    field_tys: Vec<C_GibDatatype>,
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
    datatype: C_GibDatatype,
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

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * GC
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// An iterator to traverse the shadowstack.
struct ShadowstackIter {
    run_ptr: *const i8,
    end_ptr: *const i8,
}

impl ShadowstackIter {
    fn new(ss: *mut C_GibShadowstack) -> ShadowstackIter {
        unsafe {
            debug_assert!((*ss).start <= (*ss).alloc);
            ShadowstackIter { run_ptr: (*ss).start, end_ptr: (*ss).alloc }
        }
    }
}

impl Iterator for ShadowstackIter {
    type Item = *mut C_GibShadowstackFrame;

    fn next(&mut self) -> Option<Self::Item> {
        if self.run_ptr < self.end_ptr {
            let frame = self.run_ptr as *mut C_GibShadowstackFrame;
            unsafe {
                self.run_ptr =
                    self.run_ptr.add(size_of::<C_GibShadowstackFrame>());
            }
            Some(frame)
        } else {
            None
        }
    }
}

/// This function is defined here to test if all the globals are set up
/// properly. Its output should match the C version's output.
fn shadowstack_debugprint(
    rstack: *mut C_GibShadowstack,
    wstack: *mut C_GibShadowstack,
) {
    println!("stack of readers, length={}:", shadowstack_length(rstack));
    shadowstack_print_all(rstack);
    println!("stack of writers, length={}:", shadowstack_length(wstack));
    shadowstack_print_all(wstack);
}

/// Length of the shadow-stack.
fn shadowstack_length(ss: *mut C_GibShadowstack) -> isize {
    unsafe {
        let (start_ptr, end_ptr) = (
            (*ss).start as *const C_GibShadowstackFrame,
            (*ss).alloc as *const C_GibShadowstackFrame,
        );
        debug_assert!(start_ptr <= end_ptr);
        end_ptr.offset_from(start_ptr)
    }
}

/// Print all frames of the shadow-stack.
#[inline]
fn shadowstack_print_all(ss: *mut C_GibShadowstack) {
    let ss_iter = ShadowstackIter::new(ss);
    for frame in ss_iter {
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
const REDIRECTION_TAG: C_GibPackedTag = 255;
const INDIRECTION_TAG: C_GibPackedTag = 254;

// Used internally in the garbage collector.
const CAUTERIZED_TAG: C_GibPackedTag = 253;
const COPIED_TO_TAG: C_GibPackedTag = 252;
const COPIED_TAG: C_GibPackedTag = 251;

/// Minor collection:
/// If the data is already in to-space, it is promoted to an older generation.
/// Otherwise data in from-space is copied to to-space.
pub fn collect_minor(
    rstack: *mut C_GibShadowstack,
    wstack: *mut C_GibShadowstack,
    nursery: *mut C_GibNursery,
) -> Result<()> {
    // Print some debugging information.
    if cfg!(debug_assertions) {
        println!("Triggered GC!!!");
        unsafe {
            assert!((*nursery).initialized);
            assert!((*nursery).alloc < (*nursery).alloc_end);
        }
        shadowstack_debugprint(rstack, wstack);
    }
    if allocator_in_tospace(nursery) {
        promote_to_oldgen()
    } else {
        let current_space_avail = allocator_space_available(nursery);
        copy_to_tospace(rstack, wstack, nursery)?;
        let new_space_avail = allocator_space_available(nursery);
        // Promote everything to the older generation if we couldn't
        // free up any space after a minor collection.
        if current_space_avail == new_space_avail {
            promote_to_oldgen()
        } else {
            Ok(())
        }
    }
}

/// Copy data in from-space to to-space.
fn copy_to_tospace(
    rstack: *mut C_GibShadowstack,
    wstack: *mut C_GibShadowstack,
    nursery: *mut C_GibNursery,
) -> Result<()> {
    allocator_switch_to_tospace(nursery);
    cauterize_writers(wstack)?;
    // Also uncauterizes writers.
    copy_readers(rstack, nursery)
}

/// Write a CAUTERIZED_TAG at all write cursors so that the collector knows
/// when to stop copying.
fn cauterize_writers(wstack: *mut C_GibShadowstack) -> Result<()> {
    unsafe {
        let ss = ShadowstackIter::new(wstack);
        for frame in ss {
            let ptr = (*frame).ptr as *mut i8;
            let ptr_next = write(ptr, CAUTERIZED_TAG);
            write(ptr_next, frame);
        }
        Ok(())
    }
}

/// Copy values at all read cursors from one place to another. Uses
/// nursery_malloc to allocate memory for the destination.
fn copy_readers(
    rstack: *mut C_GibShadowstack,
    nursery: *mut C_GibNursery,
) -> Result<()> {
    unsafe {
        let ss = ShadowstackIter::new(rstack);
        for frame in ss {
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
                    let (dst, _) = nursery_malloc(nursery, *size as u64)?;
                    let src = (*frame).ptr as *mut i8;
                    copy_nonoverlapping(src, dst, *size as usize);
                    // Update the pointer in shadowstack.
                    (*frame).ptr = dst;
                }
                // A packed type that should copied by referring to the info table.
                Some(DatatypeInfo::Packed(_packed_info)) => {
                    // TODO(ckoparkar): How big should this chunk be?
                    //
                    // If we have variable sized initial chunks based on the
                    // region bound analysis, maybe we'll have to store that
                    // info in a chunk footer. Then that size can somehow
                    // influence how big this new to-space chunk is.
                    // Using 1024 for now.
                    let (dst, dst_end) = nursery_malloc(nursery, 1024)?;
                    let src = (*frame).ptr as *mut i8;
                    let (src_after, dst_after, _dst_after_end, tag) =
                        copy_packed(nursery, &datatype, src, dst, dst_end)?;
                    // Update the pointer in shadowstack.
                    (*frame).ptr = dst;
                    // See (1) below required for supporting a COPIED_TAG;
                    // every value must end with a COPIED_TO_TAG. The exceptions
                    // to this rule are handled in the match expression.
                    //
                    // ASSUMPTION: There are at least 9 bytes available in the
                    // source buffer.
                    match tag {
                        None => {}
                        Some(CAUTERIZED_TAG) => {}
                        Some(COPIED_TO_TAG) => {}
                        Some(COPIED_TAG) => {}
                        _ => {
                            let burn = write(src_after, COPIED_TO_TAG);
                            write(burn, dst_after);
                        }
                    }
                }
            }
        }
        Ok(())
    }
}

/// Copy a packed value by referring to the info table.
///
/// Arguments:
///
/// * nursery - allocation area to copy data into
/// * datatype - an index into the info table
/// * src - a pointer to the value to be copied in source buffer
/// * dst - a pointer to the value's new destination in the destination buffer
/// * dst_end - end of the destination buffer for bounds checking
///
/// Returns: (src_after, dst_after)
///
/// src_after - a pointer in the source buffer that's one past the
///             last cell occupied by the value that was copied
/// dst_after - a pointer in the destination buffer that's one past the
///             last cell occupied by the value in it's new home
/// dst_end   - end of the destination buffer (which can change during copying
///             due to bounds checking)
/// maybe_tag - when copying a packed value, return the tag of the the datacon
///             that this function was called with. copy_readers uses this tag
///             to decide whether it should write a forwarding pointer at
///             the end of the source buffer.
///
fn copy_packed(
    nursery: *mut C_GibNursery,
    datatype: &C_GibDatatype,
    src: *mut i8,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*mut i8, *mut i8, *const i8, Option<C_GibPackedTag>)> {
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
                let size1 = *size as usize;
                Ok((src.add(size1), dst.add(size1), dst_end, None))
            }
            Some(DatatypeInfo::Packed(packed_info)) => {
                let (tag, src_after_tag): (C_GibPackedTag, *mut i8) =
                    read_mut(src);
                match tag {
                    // Nothing to copy. Just update the write cursor's new
                    // address in shadowstack.
                    CAUTERIZED_TAG => {
                        let (wframe_ptr, _): (*const i8, _) =
                            read(src_after_tag);
                        let wframe = wframe_ptr as *mut C_GibShadowstackFrame;
                        if cfg!(debug_assertions) {
                            println!("{:?}", wframe);
                        }
                        (*wframe).ptr = src;
                        Ok((null_mut(), null_mut(), null(), Some(tag)))
                    }
                    // This is a forwarding pointer. Use this to write an
                    // indirection in the destination buffer.
                    COPIED_TO_TAG => {
                        let (fwd_ptr, src_after_fwd_ptr): (*mut i8, _) =
                            read_mut(src_after_tag);
                        let space_reqd = 18;
                        let (dst1, dst_end1) =
                            check_bounds(nursery, space_reqd, dst, dst_end)?;
                        let dst_after_tag = write(dst1, INDIRECTION_TAG);
                        let dst_after_indr = write(dst_after_tag, fwd_ptr);
                        Ok((
                            src_after_fwd_ptr,
                            dst_after_indr,
                            dst_end1,
                            Some(tag),
                        ))
                    }
                    // Algorithm:
                    //
                    // Scan to the right for the next COPIED_TO_TAG, then take
                    // the negative offset of that pointer to find it's position
                    // in the destination buffer. Write an indirection to that
                    // in the spot you would have copied the data to.
                    //
                    // Assumptions:
                    // The correctness of this depends on guaranteeing two
                    // properties:
                    //
                    // (1) We always end a chunk with a CopiedTo tag:
                    //
                    //     this is taken care of by copy_readers.
                    //
                    // (2) There are no indirections inside the interval (before
                    //     or after copying), which would cause it to be a
                    //     different size in the from and to space and thus
                    //     invalidate offsets within it:
                    //
                    //     we are able to guarantee this because indirections
                    //     themselves provide exactly enough room to write a
                    //     COPIED_TO_TAG and forwarding pointer.
                    COPIED_TAG => {
                        let (mut scan_tag, mut scan_ptr): (
                            C_GibPackedTag,
                            *const i8,
                        ) = read(src_after_tag);
                        while scan_tag != COPIED_TO_TAG {
                            (scan_tag, scan_ptr) = read(scan_ptr);
                        }
                        // At this point the scan_ptr is one past the
                        // COPIED_TO_TAG i.e. at the forwarding pointer.
                        let offset = scan_ptr.offset_from(src) - 1;
                        // The forwarding pointer that's available.
                        let (fwd_avail, _): (*const i8, _) = read(scan_ptr);
                        // The position in the destination buffer we wanted.
                        let fwd_want = fwd_avail.sub(offset as usize);
                        let space_reqd = 18;
                        let (dst1, dst_end1) =
                            check_bounds(nursery, space_reqd, dst, dst_end)?;
                        let dst_after_tag = write(dst1, INDIRECTION_TAG);
                        let dst_after_indr = write(dst_after_tag, fwd_want);
                        Ok((null_mut(), dst_after_indr, dst_end1, Some(tag)))
                    }
                    // Indicates end-of-current-chunk in the source buffer i.e.
                    // there's nothing more to copy in the current chunk.
                    // Follow the redirection pointer to the next chunk and
                    // continue copying there.
                    //
                    // POLICY DECISION:
                    // Redirections are always inlined in the current version.
                    REDIRECTION_TAG => {
                        let (next_chunk, _): (*mut i8, _) =
                            read(src_after_tag);
                        // Add a forwarding pointer in the source buffer.
                        write(src, COPIED_TO_TAG);
                        write(src_after_tag, dst);
                        // Continue in the next chunk.
                        copy_packed(
                            nursery, datatype, next_chunk, dst, dst_end,
                        )
                    }
                    // A pointer to a value in another buffer; copy this value
                    // and then switch back to copying rest of the source buffer.
                    //
                    // POLICY DECISION:
                    // Indirections are always inlined in the current version.
                    INDIRECTION_TAG => {
                        let (pointee, _): (*mut i8, _) = read(src_after_tag);
                        let (_, dst_after_pointee, dst_after_pointee_end, _) =
                            copy_packed(
                                nursery, datatype, pointee, dst, dst_end,
                            )?;
                        // Add a forwarding pointer in the source buffer.
                        write(src, COPIED_TO_TAG);
                        let src_after_indr = write(src_after_tag, dst);
                        // Return 1 past the indirection pointer as src_after
                        // and the dst_after that copy_packed returned.
                        Ok((
                            src_after_indr,
                            dst_after_pointee,
                            dst_after_pointee_end,
                            Some(tag),
                        ))
                    }
                    // Regular datatype, copy.
                    _ => {
                        let DataconInfo { scalar_bytes, field_tys, .. } =
                            packed_info.get(&tag).unwrap();
                        // Check bound of the destination buffer before copying.
                        // Reserve additional space for a redirection node or a
                        // forwarding pointer.
                        let space_reqd: isize = (32 + *scalar_bytes).into();
                        {
                            // Scope for mutable variables dst_mut and src_mut.

                            let (mut dst_mut, mut dst_end_mut) = check_bounds(
                                nursery, space_reqd, dst, dst_end,
                            )?;
                            // Copy the tag and the fields.
                            dst_mut = write(dst_mut, tag);
                            dst_mut.copy_from_nonoverlapping(
                                src_after_tag,
                                *scalar_bytes as usize,
                            );
                            let mut src_mut =
                                src_after_tag.add(*scalar_bytes as usize);
                            dst_mut = dst_mut.add(*scalar_bytes as usize);
                            // Add forwarding pointers:
                            // if there's enough space, write a COPIED_TO tag and
                            // dst's address at src. Otherwise write a COPIED tag.
                            // After the forwarding pointer, burn the rest of
                            // space previously occupied by scalars.
                            if *scalar_bytes >= 8 {
                                let mut burn = write(src, COPIED_TO_TAG);
                                burn = write(burn, dst);
                                // TODO: check if src_mut != burn?
                                let i = src_mut.offset_from(burn);
                                write_bytes(burn, COPIED_TAG, i as usize);
                            } else {
                                let burn = write(src, COPIED_TAG);
                                let i = src_mut.offset_from(burn);
                                // TODO: check if src_mut != burn?
                                write_bytes(burn, COPIED_TAG, i as usize);
                            }
                            // TODO(ckoparkar):
                            // (1) instead of recursion, use a worklist
                            // (2) handle redirection nodes properly
                            for ty in field_tys.iter() {
                                let (src1, dst1, dst_end1, field_tag) =
                                    copy_packed(
                                        nursery,
                                        ty,
                                        src_mut,
                                        dst_mut,
                                        dst_end_mut,
                                    )?;
                                // Must immediately stop copying upon reaching
                                // the cauterized tag.
                                if field_tag == CAUTERIZED_TAG {
                                    return Ok((
                                        null_mut(),
                                        null_mut(),
                                        null(),
                                        field_tag,
                                    ));
                                } else {
                                    src_mut = src1;
                                    dst_mut = dst1;
                                    dst_end_mut = dst_end1;
                                }
                            }
                            Ok((src_mut, dst_mut, dst_end_mut, Some(tag)))
                        }
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
fn check_bounds(
    nursery: *mut C_GibNursery,
    space_reqd: isize,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*mut i8, *const i8)> {
    unsafe {
        let space_avail = dst_end.offset_from(dst);
        if space_avail < space_reqd {
            // TODO(ckoparkar): see the TODO in copy_readers.
            let (new_dst, new_dst_end) = nursery_malloc(nursery, 1024)?;
            let dst_after_tag = write(dst, REDIRECTION_TAG);
            write(dst_after_tag, new_dst);
            Ok((new_dst, new_dst_end))
        } else {
            Ok((dst, dst_end))
        }
    }
}

#[inline]
fn nursery_malloc(
    nursery: *mut C_GibNursery,
    size: u64,
) -> Result<(*mut i8, *const i8)> {
    unsafe {
        let old = (*nursery).alloc as *mut i8;
        let bump = old.add(size as usize);
        let end = (*nursery).alloc_end as *mut i8;
        // Check if there's enough space in the nursery to fulfill the request.
        //
        // CSK: Do we have to check this? Since we're copying things which are
        // already in the from-space, in the worst case we'll copy everything
        // but all of from-space should always fit in the to-space.
        if bump <= end {
            (*nursery).alloc = bump;
            Ok((old, bump))
        } else {
            Err(RtsError::Gc(format!(
                "nursery_malloc: out of space, requested={:?}, available={:?}",
                size,
                end.offset_from(old)
            )))
        }
    }
}

#[inline]
fn allocator_in_tospace(nursery: *mut C_GibNursery) -> bool {
    unsafe { (*nursery).alloc > (*nursery).ts_start }
}

fn allocator_space_available(nursery: *mut C_GibNursery) -> isize {
    unsafe { (*nursery).alloc_end.offset_from((*nursery).alloc) }
}

fn allocator_switch_to_tospace(nursery: *mut C_GibNursery) {
    unsafe {
        (*nursery).alloc = (*nursery).ts_start;
        (*nursery).alloc_end = (*nursery).ts_end;
    }
}

#[inline]
unsafe fn read<A>(cursor: *const i8) -> (A, *const i8) {
    let cursor2 = cursor as *const A;
    (cursor2.read_unaligned(), cursor2.add(1) as *const i8)
}

unsafe fn read_mut<A>(cursor: *mut i8) -> (A, *mut i8) {
    let cursor2 = cursor as *const A;
    (cursor2.read_unaligned(), cursor2.add(1) as *mut i8)
}

#[inline]
unsafe fn write<A>(cursor: *mut i8, val: A) -> *mut i8 {
    let cursor2 = cursor as *mut A;
    cursor2.write_unaligned(val);
    cursor2.add(1) as *mut i8
}
