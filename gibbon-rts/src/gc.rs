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

/*
 * Discuss:
 * ~~~~~~~~

(1)
Only maintain refcounts and outsets for indirections in the old generation.

When evacuating the roots in the remembered set, set refcount of the evacuated
data to 1, or bump it by 1 (how? don't know the meatadata address) if a root
here reaches burnt data. For all roots in the shadow stack, set refcount of the
evacuated data to 0 and add it to ZCT.

(2)
During a major collection, (a) perform a minor collection, and (b) traverse the
ZCT and free all regions which don't have pointers from the shadowstack.

(3)
Evacuate_packed makes an assumption that buffers are always evacuated left-to-right...
But it can encounter burnt data in the middle of the buffer such that there's
more data to be evacuated after it.

New policy:
~~~~~~~~~~~~

If evacuate_packed reaches burnt data while evacuating the fields of a data
constructor, it means that one of the fields was already evacuated before but
there may still be more fields to evacuate. Thus, we must traverse past this
burnt field and evacuate the rest. But this traversal is tricky. The simple
strategy of "go right until you stop seeing burnt things" doesn't work because
the neighboring fields might also be burnt and we wouldn't know where one ends
and the next begins.

If evacuate_packed arrives at burnt data via an indirection, write an indirection
in the destination using the forwarding pointer. In this case we are traversing
past the source field (which was an indirection) to reach any subsequent fields
that might need to be evacuated. See below re: maintaining refcounts.

(4)
Every time we write an indirection while evacuating, we must adjust refcounts
and outsets. In the current implementation, we write an indirection only when
we reach already burnt data, but we don't have access to the metadata of the
region where the data was forwarded. We could do two things here:

  (a) always inline EVERYTHING. but this might be bad..

  (b) in addition to storing a forwarding pointer, we could also store the
      metadata adress with it. but this means that a forwarding node will now
      occupy 17 bytes! this breaks its representational equivalence with
      indirections, which is necessary to support burning data that doesn't
      have room for a forwarding pointer a.k.a. the COPIED tag.
      this means we'll have to make indirections 17 bytes long too? yikes.

(5)
When we write young-to-old indirections in the mutator we run into a similar
problem as above while evacuating them i.e. we must always inline the pointed-to
data. If we wanted to preserve this indirection while evacuating, we would have
to adjust the refcount of the oldgen region, but wouldn't know the address of
its metadata. The presumption here is that data in the oldgen is BIG and we
might not want to inline it. Inlining young-to-young indirections seems okay.

Should we preserve the young-to-old indirections by making the write barrier
store some information in a "deferred increment set"? That is, we store
(from_addr, to_addr, to_metadata) in a set. While evacuating young-to-old
indirections, we lookup this metadata address in the set and update the refcount.
Maintaining a correct outset is easy since regions in nursery don't have any
metadata and we allocate fresh footers and metadata while evacuating them.

(6)
Handle shortcut pointers properly while evacuating.

 */

// Tags used internally in the garbage collector.
const CAUTERIZED_TAG: C_GibPackedTag = 253;
const COPIED_TO_TAG: C_GibPackedTag = 252;
const COPIED_TAG: C_GibPackedTag = 251;

/// Minor collection.
pub fn collect_minor(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
    _force_major: bool,
) -> Result<()> {
    let rstack = &Shadowstack(rstack_ptr);
    let wstack = &Shadowstack(wstack_ptr);
    let nursery = &mut Nursery(nursery_ptr);
    if C_NUM_GENERATIONS == 1 {
        let mut oldest_gen = OldestGeneration(generations_ptr);
        cauterize_writers(wstack)?;
        evacuate_readers(rstack, &mut oldest_gen)?;
        nursery.bump_collections();
        nursery.reset_alloc();
        Ok(())
    } else {
        todo!()
    }
}

/// Write a CAUTERIZED_TAG at all write cursors so that the collector knows
/// when to stop copying.
fn cauterize_writers(wstack: &Shadowstack) -> Result<()> {
    for frame in ShadowstackIter::new(wstack) {
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
    for frame in ShadowstackIter::new(rstack) {
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
                    let (dst, _) = Heap::allocate(dest, *size as u64)?;
                    let src = (*frame).ptr as *mut i8;
                    copy_nonoverlapping(src, dst, *size as usize);
                    // Update the pointer in shadowstack.
                    (*frame).ptr = dst;
                }
                // A packed type that should copied by referring to the info table.
                Some(DatatypeInfo::Packed(packed_info)) => {
                    // TODO(ckoparkar): How big should this chunk be?
                    //
                    // If we have variable sized initial chunks based on the
                    // region bound analysis, maybe we'll have to store that
                    // info in a chunk footer. Then that size can somehow
                    // influence how big this new to-space chunk is.
                    // Using 1024 for now.
                    let (dst, dst_end) = Heap::allocate(dest, 1024)?;
                    let src = (*frame).ptr as *mut i8;
                    let (src_after, dst_after, _dst_after_end, tag) =
                        evacuate_packed(dest, packed_info, src, dst, dst_end)?;
                    // Update the pointer in shadowstack.
                    (*frame).ptr = dst;
                    // See (1) below required for supporting a COPIED_TAG;
                    // every value must end with a COPIED_TO_TAG. The exceptions
                    // to this rule are handled in the match expression.
                    //
                    // ASSUMPTION: There are at least 9 bytes available in the
                    // source buffer.
                    //
                    // Why is this a reasonable assumption?
                    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
                    //
                    // We process the shadowstack starting with the oldest
                    // frame first. Older frames always point to start of
                    // of regions. Thus, we will evacuate a buffer and reach
                    // its true end. Due to the way buffers are set up, there's
                    // always sufficient space to write a forwarding pointer
                    // here. When we get further down the shadowstack and reach
                    // frames that point to values in the middle of a buffer,
                    // we will encounter COPIED_TO or COPIED tags and not write
                    // the forwarding pointers after these values.
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
                Ok((null_mut(), dst_after_indr, dst_end1, Some(tag)))
            }
            // Algorithm:
            //
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

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Generic memory allocation
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// Typeclass for different allocation areas; nurseries, generations etc.
pub trait Heap {
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
    fn bump_collections(&mut self) {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            (*nursery).collections += 1;
        }
    }

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

/// A wrapper over the naked C pointer.
struct Shadowstack(*mut C_GibShadowstack);

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
