#![allow(dead_code)]

/*!

Implementation of the new generation garbage collector for Gibbon.

 */

use libc;
use std::collections::HashMap;
use std::error::Error;
use std::fmt;
use std::lazy::OnceCell;
use std::mem::size_of;
use std::ptr::{copy_nonoverlapping, null, null_mut, write_bytes};

use crate::ffi::types::*;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Collection; evacuate, promote etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Tags used internally in the garbage collector.
const CAUTERIZED_TAG: C_GibPackedTag = 253;
const COPIED_TO_TAG: C_GibPackedTag = 252;
const COPIED_TAG: C_GibPackedTag = 251;

pub fn garbage_collect(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
    _force_major: bool,
) -> Result<()> {
    if cfg!(debug_assertions) {
        println!("GC!!!");
    }
    collect_minor(rstack_ptr, wstack_ptr, nursery_ptr, generations_ptr)
}

/// Minor collection.
pub fn collect_minor(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
) -> Result<()> {
    let rstack = &Shadowstack(rstack_ptr, GcRootProv::Stk);
    let wstack = &Shadowstack(wstack_ptr, GcRootProv::Stk);
    let nursery = &mut Nursery(nursery_ptr);
    if C_NUM_GENERATIONS == 1 {
        // Start by cauterizing the writers.
        cauterize_writers(wstack)?;
        // Prepare to evacuate the readers.
        let mut oldest_gen = OldestGeneration(generations_ptr);
        let rem_set = unsafe {
            &RememberedSet((*generations_ptr).rem_set, GcRootProv::RemSet)
        };
        // First evacuate the remembered set.
        evacuate_readers(rem_set, &mut oldest_gen)?;
        // Then the shadow stack.
        evacuate_readers(rstack, &mut oldest_gen)?;
        // Reset the allocation area.
        nursery.reset_alloc();
        // Record stats.
        nursery.bump_num_collections();
        // Done.
        Ok(())
    } else {
        todo!("NUM_GENERATIONS > 1")
    }
}

/// Write a CAUTERIZED_TAG at all write cursors so that the collector knows
/// when to stop copying.
fn cauterize_writers(wstack: &Shadowstack) -> Result<()> {
    for frame in wstack.into_iter() {
        unsafe {
            let ptr = (*frame).ptr as *mut i8;
            let ptr_next = write(ptr, CAUTERIZED_TAG);
            write(ptr_next, frame);
        }
    }
    Ok(())
}

/// Copy values at all read cursors from the nursery to the provided
/// destination. Also uncauterize any CAUTERIZED_TAGs that are reached.
fn evacuate_readers(rstack: &Shadowstack, dest: &mut impl Heap) -> Result<()> {
    for frame in rstack.into_iter() {
        unsafe {
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
                    let (dst, dst_end) = Heap::allocate(dest, *size as u64)?;
                    let src = (*frame).ptr as *mut i8;
                    copy_nonoverlapping(src, dst, *size as usize);
                    // Update the pointer in shadowstack.
                    (*frame).ptr = dst;
                    (*frame).endptr = dst_end;
                }
                // A packed type that is copied by referring to the info table.
                Some(DatatypeInfo::Packed(packed_info)) => {
                    // TODO(ckoparkar): How big should this chunk be?
                    //
                    // If we have variable sized initial chunks based on the
                    // region bound analysis, maybe we'll have to store that
                    // info in a chunk footer. Then that size can guide how big
                    // this new to-space chunk should be. Using 1024 for now.
                    let chunk_size = 1024;
                    let (chunk_start, chunk_end) =
                        Heap::allocate(dest, chunk_size)?;
                    // Write a footer if evacuating to the oldest generation.
                    let dst = chunk_start;
                    let dst_end = if !dest.is_oldest() {
                        // Middle generation chunks don't need footers.
                        chunk_end
                    } else {
                        // Oldest generation chunks need a footer.
                        let footer_space = size_of::<C_GibChunkFooter>();
                        let data_end = chunk_end.sub(footer_space) as *mut i8;
                        let usable_size = chunk_size - (footer_space as u64);
                        let refcount = match rstack.1 {
                            GcRootProv::RemSet => 1,
                            GcRootProv::Stk => 0,
                        };
                        init_footer_at(data_end, usable_size, refcount);
                        // TODO(ckoparkar): add data_end to src's outset.
                        data_end
                    };
                    // Evacuate the data.
                    let src = (*frame).ptr as *mut i8;
                    let (src_after, dst_after, dst_after_end, tag) =
                        evacuate_packed(dest, packed_info, src, dst, dst_end)?;
                    // Update the pointers in shadowstack.
                    (*frame).ptr = dst;
                    (*frame).endptr = dst_after_end;
                    /*
                    Each chunk should end with a COPIED_TO_TAG; see (1)
                    regarding the COPIED_TAG. The exceptions to this
                    rule are handled in the match expression below.

                    ASSUMPTION: There are at least 9 bytes available in the
                    source buffer.

                    Is this a reasonable assumption?
                    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

                    Yes, if all values are always evacuated in a left-to-right
                    order. This happens if we process the shadowstack starting
                    with the oldest frame first. Older frames always point to
                    start of regions. Thus, we will evacuate a buffer and reach
                    its *true* end. Due to the way buffers are set up, there's
                    always sufficient space to write a forwarding pointer
                    there. When we get further down the shadowstack and reach
                    frames that point to values in the middle of a buffer,
                    we will encounter COPIED_TO or COPIED tags and not write
                    the forwarding pointers after these values.

                    Can this assumption be invalidated?
                    ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

                    Yes, if values are not evacuated in a left-to-right order.
                    Suppose there's a value (K a b c d) and we first evacuate
                    'a' (e.g. suppose the remembered set points to it). Now
                    the code will reach this point and try to write a forwarding
                    pointer. But this will overwrite other data in the buffer!!
                    Thus, we must only write a forwarding pointer when we've
                    reached the true end of the source buffer. The only time
                    we actually reach the true end is when we're evacuating a
                    value starts at the very beginning of the chunk.
                    Hence, we record this information in the shadowstack.
                     */
                    match tag {
                        None => {}
                        Some(CAUTERIZED_TAG) => {}
                        Some(COPIED_TO_TAG) => {}
                        Some(COPIED_TAG) => {}
                        _ => {
                            if (*frame).start_of_chunk {
                                let burn = write(src_after, COPIED_TO_TAG);
                                write(burn, dst_after);
                            }
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

fn evacuate(
    dest: &mut impl Heap,
    datatype: &C_GibDatatype,
    src: *mut i8,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*mut i8, *mut i8, *const i8, Option<C_GibPackedTag>)> {
    unsafe {
        match INFO_TABLE.get().unwrap().get(datatype) {
            None => {
                return Err(RtsError::Gc(format!(
                    "evacuate: Unknown datatype, {:?}",
                    datatype
                )));
            }
            Some(DatatypeInfo::Scalar(size)) => {
                copy_nonoverlapping(src, dst, *size as usize);
                let size1 = *size as usize;
                Ok((src.add(size1), dst.add(size1), dst_end, None))
            }
            Some(DatatypeInfo::Packed(packed_info)) => {
                evacuate_packed(dest, packed_info, src, dst, dst_end)
            }
        }
    }
}

/**

Evacuate a packed value by referring to the info table.

Arguments:

- dest - allocation area to copy data into
- packed_info - information about the fields of this datatype
- src - a pointer to the value to be copied in source buffer
- dst - a pointer to the value's new destination in the destination buffer
- dst_end - end of the destination buffer for bounds checking

Returns: (src_after, dst_after, dst_end, maybe_tag)

- src_after - a pointer in the source buffer that's one past the
              last cell occupied by the value that was copied
- dst_after - a pointer in the destination buffer that's one past the
              last cell occupied by the value in its new home
- dst_end   - end of the destination buffer (which can change during copying
              due to bounds checking)
- maybe_tag - when copying a packed value, return the tag of the the datacon
              that this function was called with. copy_readers uses this tag
              to decide whether it should write a forwarding pointer at
              the end of the source buffer.

 */
fn evacuate_packed(
    dest: &mut impl Heap,
    packed_info: &HashMap<C_GibPackedTag, DataconInfo>,
    src: *mut i8,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*mut i8, *mut i8, *const i8, Option<C_GibPackedTag>)> {
    unsafe {
        let (tag, src_after_tag): (C_GibPackedTag, *mut i8) = read_mut(src);
        match tag {
            // Nothing to copy. Just update the write cursor's new
            // address in shadowstack.
            CAUTERIZED_TAG => {
                let (wframe_ptr, _): (*const i8, _) = read(src_after_tag);
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
                let (fwd_ptr, _): (*mut i8, _) = read_mut(src_after_tag);
                let space_reqd = 18;
                let (dst1, dst_end1) =
                    Heap::check_bounds(dest, space_reqd, dst, dst_end)?;
                let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
                let dst_after_indr = write(dst_after_tag, fwd_ptr);
                // TODO(ckoparkar):
                // (1) update outsets and refcounts if evacuating to the oldest
                //     generation.
                // (2) return a position *after* this evacuated value in the
                //     source buffer.
                Ok((null_mut(), dst_after_indr, dst_end1, Some(tag)))
            }
            // Algorithm:
            // ~~~~~~~~~~
            // Scan to the right for the next COPIED_TO_TAG, then take
            // the negative offset of that pointer to find its position
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
                let (mut scan_tag, mut scan_ptr): (C_GibPackedTag, *const i8) =
                    read(src_after_tag);
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
                    Heap::check_bounds(dest, space_reqd, dst, dst_end)?;
                let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
                let dst_after_indr = write(dst_after_tag, fwd_want);
                // TODO(ckoparkar):
                // (1) update outsets and refcounts if evacuating to the oldest
                //     generation.
                // (2) return a position *after* this evacuated value in the
                //     source buffer.
                Ok((null_mut(), dst_after_indr, dst_end1, Some(tag)))
            }
            // Indicates end-of-current-chunk in the source buffer i.e.
            // there's nothing more to copy in the current chunk.
            // Follow the redirection pointer to the next chunk and
            // continue copying there.
            //
            // POLICY DECISION:
            // Redirections are always inlined in the current version.
            C_REDIRECTION_TAG => {
                let (next_chunk, _): (*mut i8, _) = read(src_after_tag);
                // Add a forwarding pointer in the source buffer.
                write(src, COPIED_TO_TAG);
                write(src_after_tag, dst);
                // Continue in the next chunk.
                evacuate_packed(dest, packed_info, next_chunk, dst, dst_end)
            }
            // A pointer to a value in another buffer; copy this value
            // and then switch back to copying rest of the source buffer.
            //
            // POLICY DECISION:
            // Indirections are always inlined in the current version.
            C_INDIRECTION_TAG => {
                let (pointee, _): (*mut i8, _) = read(src_after_tag);
                let (_, dst_after_pointee, dst_after_pointee_end, _) =
                    evacuate_packed(dest, packed_info, pointee, dst, dst_end)?;
                // Add a forwarding pointer in the source buffer.
                write(src, COPIED_TO_TAG);
                let src_after_indr = write(src_after_tag, dst);
                // Return 1 past the indirection pointer as src_after
                // and the dst_after that evacuate_packed returned.
                Ok((
                    src_after_indr,
                    dst_after_pointee,
                    dst_after_pointee_end,
                    Some(tag),
                ))
            }
            // Regular datatype, copy.
            _ => {
                let DataconInfo {
                    scalar_bytes, field_tys, num_scalars, ..
                } = packed_info.get(&tag).unwrap();
                // Check bound of the destination buffer before copying.
                // Reserve additional space for a redirection node or a
                // forwarding pointer.
                let space_reqd: usize = (32 + *scalar_bytes).into();
                {
                    // Scope for mutable variables dst_mut and src_mut.

                    let (mut dst_mut, mut dst_end_mut) =
                        Heap::check_bounds(dest, space_reqd, dst, dst_end)?;
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
                        // TODO(ckoparkar): check if src_mut != burn?
                        let i = src_mut.offset_from(burn);
                        write_bytes(burn, COPIED_TAG, i as usize);
                    } else {
                        let burn = write(src, COPIED_TAG);
                        let i = src_mut.offset_from(burn);
                        // TODO(ckoparkar): check if src_mut != burn?
                        write_bytes(burn, COPIED_TAG, i as usize);
                    }
                    // TODO(ckoparkar):
                    // (1) instead of recursion, use a worklist
                    // (2) handle redirection nodes properly
                    for ty in field_tys.iter().skip((*num_scalars) as usize) {
                        let (src1, dst1, dst_end1, field_tag) =
                            evacuate(dest, ty, src_mut, dst_mut, dst_end_mut)?;
                        // Must immediately stop copying upon reaching
                        // the cauterized tag.
                        match field_tag {
                            Some(CAUTERIZED_TAG) => {
                                return Ok((
                                    null_mut(),
                                    null_mut(),
                                    null(),
                                    field_tag,
                                ))
                            }
                            _ => {
                                src_mut = src1;
                                dst_mut = dst1;
                                dst_end_mut = dst_end1;
                            }
                        }
                    }
                    Ok((src_mut, dst_mut, dst_end_mut, Some(tag)))
                }
            }
        }
    }
}

#[inline]
unsafe fn init_footer_at(addr: *mut i8, size: u64, refcount: u16) {
    let region_info = C_GibRegionInfo {
        // TODO(ckoparkar): gensym an identifier.
        id: 0,
        refcount: refcount,
        outset_len: 0,
        outset: [null(); 10],
        outset2: null_mut(),
    };
    let region_info_ptr: *mut C_GibRegionInfo =
        Box::into_raw(Box::new(region_info));
    let footer: *mut C_GibChunkFooter = addr as *mut C_GibChunkFooter;
    (*footer).reg_info = region_info_ptr;
    (*footer).seq_no = 0;
    (*footer).size = size;
    (*footer).next = null_mut();
    (*footer).prev = null_mut();
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
    // TODO(ckoparkar): what's the difference between these?
    // *cursor2 = val;
    cursor2.write_unaligned(val);
    cursor2.add(1) as *mut i8
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Generic memory allocation
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// Typeclass for different allocation areas; nurseries, generations etc.
pub trait Heap {
    fn is_nursery(&self) -> bool;
    fn is_oldest(&self) -> bool;
    fn allocate(&mut self, size: u64) -> Result<(*mut i8, *const i8)>;
    fn space_available(&self) -> usize;

    fn check_bounds(
        &mut self,
        space_reqd: usize,
        dst: *mut i8,
        dst_end: *const i8,
    ) -> Result<(*mut i8, *const i8)> {
        assert!((dst as *const i8) < dst_end);
        unsafe {
            let space_avail = dst_end.offset_from(dst) as usize;
            if space_avail < space_reqd {
                // TODO(ckoparkar): see the TODO in copy_readers.
                let (new_dst, new_dst_end) = Heap::allocate(self, 1024)?;
                let dst_after_tag = write(dst, C_REDIRECTION_TAG);
                write(dst_after_tag, new_dst);
                Ok((new_dst, new_dst_end))
            } else {
                Ok((dst, dst_end))
            }
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Nursery
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// A wrapper over the naked C pointer.
struct Nursery(*mut C_GibNursery);

impl Nursery {
    #[inline]
    fn bump_num_collections(&mut self) {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            (*nursery).num_collections += 1;
        }
    }

    #[inline]
    fn reset_alloc(&mut self) {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            (*nursery).alloc = (*nursery).heap_start;
        }
    }
}

impl fmt::Debug for Nursery {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self.0))
    }
}

impl Heap for Nursery {
    #[inline]
    fn is_nursery(&self) -> bool {
        true
    }

    #[inline]
    fn is_oldest(&self) -> bool {
        false
    }

    #[inline]
    fn space_available(&self) -> usize {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            assert!((*nursery).alloc <= (*nursery).heap_end);
            (*nursery).heap_end.offset_from((*nursery).alloc) as usize
        }
    }

    fn allocate(&mut self, size: u64) -> Result<(*mut i8, *const i8)> {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            assert!((*nursery).alloc < (*nursery).heap_end);
            let old = (*nursery).alloc as *mut i8;
            let bump = old.add(size as usize);
            let end = (*nursery).heap_end as *mut i8;
            // Check if there's enough space in the nursery to fulfill the request.
            if bump <= end {
                (*nursery).alloc = bump;
                Ok((old, bump))
            } else {
                Err(RtsError::Gc(format!(
                    "nursery alloc: out of space, requested={:?}, available={:?}",
                    size,
                    end.offset_from(old)
                )))
            }
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Generation
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// A wrapper over the naked C pointer.
struct Generation(*mut C_GibGeneration);

impl fmt::Debug for Generation {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self.0))
    }
}

impl Heap for Generation {
    #[inline]
    fn is_nursery(&self) -> bool {
        false
    }

    #[inline]
    fn is_oldest(&self) -> bool {
        false
    }

    fn space_available(&self) -> usize {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            assert!((*gen).alloc <= (*gen).heap_end);
            (*gen).heap_end.offset_from((*gen).alloc) as usize
        }
    }

    fn allocate(&mut self, size: u64) -> Result<(*mut i8, *const i8)> {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            assert!((*gen).alloc < (*gen).heap_end);
            let old = (*gen).alloc as *mut i8;
            let bump = old.add(size as usize);
            let end = (*gen).heap_end as *mut i8;
            // Check if there's enough space in the gen to fulfill the request.
            if bump <= end {
                (*gen).mem_allocated += size;
                (*gen).alloc = bump;
                Ok((old, bump))
            } else {
                Err(RtsError::Gc(format!(
                    "gen alloc: out of space, requested={:?}, available={:?}",
                    size,
                    end.offset_from(old)
                )))
            }
        }
    }
}

/// A wrapper over the naked C pointer.
struct OldestGeneration(*mut C_GibGeneration);

impl fmt::Debug for OldestGeneration {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self.0))
    }
}

impl Heap for OldestGeneration {
    #[inline]
    fn is_nursery(&self) -> bool {
        false
    }

    #[inline]
    fn is_oldest(&self) -> bool {
        true
    }

    #[inline]
    fn space_available(&self) -> usize {
        0
    }

    fn allocate(&mut self, size: u64) -> Result<(*mut i8, *const i8)> {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            let start = libc::malloc(size as usize) as *mut i8;
            if start.is_null() {
                Err(RtsError::Gc(format!("oldest gen alloc: malloc failed")))
            } else {
                (*gen).mem_allocated += size;
                let end = start.add(size as usize);
                Ok((start, end))
            }
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// Provenance of a GC root; shadow stack or remembered set.
#[derive(Debug)]
enum GcRootProv {
    Stk,
    RemSet,
}

/// A wrapper over the naked C pointer.
#[derive(Debug)]
struct Shadowstack(*mut C_GibShadowstack, GcRootProv);

impl Shadowstack {
    /// Length of the shadow-stack.
    fn length(&self) -> isize {
        let ss: *mut C_GibShadowstack = self.0;
        unsafe {
            let (start_ptr, end_ptr) = (
                (*ss).start as *const C_GibShadowstackFrame,
                (*ss).alloc as *const C_GibShadowstackFrame,
            );
            assert!(start_ptr <= end_ptr);
            end_ptr.offset_from(start_ptr)
        }
    }
    /// Print all frames of the shadow-stack.
    fn print_all(&self) {
        for frame in ShadowstackIter::new(self) {
            unsafe {
                println!("{:?}", *frame);
            }
        }
    }
}

impl IntoIterator for &Shadowstack {
    type Item = *mut C_GibShadowstackFrame;
    type IntoIter = ShadowstackIter;

    fn into_iter(self) -> Self::IntoIter {
        ShadowstackIter::new(self)
    }
}

/// An iterator to traverse the shadowstack.
struct ShadowstackIter {
    run_ptr: *const i8,
    end_ptr: *const i8,
}

impl ShadowstackIter {
    fn new(stk: &Shadowstack) -> ShadowstackIter {
        unsafe {
            let cstk: *mut C_GibShadowstack = stk.0;
            assert!((*cstk).start <= (*cstk).alloc);
            ShadowstackIter { run_ptr: (*cstk).start, end_ptr: (*cstk).alloc }
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

use Shadowstack as RememberedSet;
use ShadowstackIter as RememberedSetIter;

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
