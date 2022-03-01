#![allow(dead_code)]

/*!

Implementation of the new generational garbage collector for Gibbon.

 */

use libc;

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::lazy::OnceCell;
use std::mem::size_of;
use std::ptr::{copy_nonoverlapping, null, null_mut, write_bytes};

use crate::ffi::types::*;
use crate::tagged_pointer::*;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Notes
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~


See https://github.com/iu-parfunc/gibbon/issues/122#issuecomment-938311529.


*** Maintaining sharing, Copied and CopiedTo tags:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Maintaining sharing while evacuating packed data is HARD. You can't do the
simple thing of marking all copied data with a forwarding pointer. That depends
on having enough space for the forwarding pointer. But for binary tree data in
the heap, you don't have it:

┌─────────────┐
│  N L 1 L 2  │
└─────────────┘

Specifically, there are 3 heap objects here. The two leaves happen to have
enough room for a forwarding pointer, but the intermediate Node doesn't.
We need some complicated scheme to retain sharing while evacuating this data.
For example:

- "Burn" all data as you copy it by changing all tags to Copied

- Use a CopiedTo tag (that functions identically to existing Indirections),
  when there is room for a forwarding pointer.

- Reason about copies of contiguous intervals. I.e. the GC copies bytes from
  location L0 to L1, without any intervening space for a forwarding pointer.

- A second thread that points into the middle of such an interval, reads a
  Copied tag, but must figure out its destination based on an offset from a
  CopiedTo tag to the left or right of the interval.

  Algorithm: scan to the right for the next COPIED_TO tag, then take the
  negative offset of that pointer to find its position in the destination
  buffer. Write an indirection to that in the spot you would have copied the
  data to.

The correctness of this depends on guaranteeing two properties:

(1) We always end a chunk with a CopiedTo tag:

    this is taken care of by copy_readers.

(2) There are no indirections inside the interval (before or after copying),
    which would cause it to be a different size in the from and to space and
    thus invalidate offsets within it:

    we are able to guarantee this because indirections themselves provide
    exactly enough room to write a CopiedTo and forwarding pointer.



*** Adding a forwarding pointer at the end of every chunk:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

'evacuate_readers' writes this tag and a forwarding pointer unless:


(1) the value being evacuated doesn't end at the *true* end of the buffer,
    see below.

(2) the value being evacuated starts with a CopiedTo or a Copied tag.
    we don't need to write a forwarding pointer since we would have already
    written one during the previous evacuation.


ASSUMPTION: There is sufficient space available (9 bytes) to write a
forwarding pointer in the source buffer.


Is this a reasonable assumption?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Yes, only if all values are always evacuated in a strict left-to-right order.
This happens if we process the shadow-stack starting with the oldest frame first.
Older frames always point to start of regions. Thus, we will evacuate a buffer
and reach its *true* end. Due to the way buffers are set up, there's always
sufficient space to write a forwarding pointer there. When we get further down
the shadow-stack and reach frames that point to values in the middle of a buffer,
we will encounter CopiedTo or Copied tags and not write the forwarding pointers
after these values.

If values are NOT evacuated in a left-to-right order, this assumption is
invalidated. Suppose there's a value (K a b c d) and we first evacuate 'a'
(e.g. maybe because the remembered set points to it). Now the code will reach
this point and try to write a forwarding pointer. But this will overwrite other
data in the buffer!!

Thus, we must only write a forwarding pointer when we've reached the true end
of the source buffer. The only time we actually reach the true end is when we're
evacuating a value starts at the very beginning of the chunk. Hence, we store
the start-of-chunk addresses in an auxillary data structure in the nursery
and use them to check if we've reached the end of a chunk.


*** Traversing burned data:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The left-to-right evacuation mentioned above is important for another reason.
When buffers are NOT evacuated left-to-right, evacuate_packed can encounter
burned data in the middle of a buffer such that there's more data to be
evacuated after it. Thus, we must traverse past this burned field and evacuate
the rest. But this traversal is tricky. The simple strategy of "scan right until
you stop seeing burned things" doesn't work because two neighboring fields
might be burned and we wouldn't know where one field ends and the next one
begins.

For example, consider a sitation where we have a constructor with 4 fields,
(K a b c d), and fields 'a' and 'b' have been evacuated (burned) but 'c' and 'd'
have not. Now someone comes along to try to copy K. How do you reach 'c'?

To accomplish this traversal we maintain a table of "burned addresses",
{ start-of-burned-field -> end-of-burned-field }, for all roots that can create
"burned holes" in the middle of buffers. In the current implementation we only
need to track this info for the roots in the remembered set which can create
burned holes since they are evacuated before the shadow-stack. While evacuating
the roots in the shadow-stack, we always start at the oldest oldest frame which
guarantees a left-to-right traversal of buffers.


Granularity of the burned addresses table
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Does every intermediate packed field within a value pointed to by a root
in a remembered set need its separate entry in the burned address table?
No, IF we guarantee a left-to-right traversal of buffers while evacuating
the remembered set, which ensures that we won't see any burned holes during
this evacuation. To this end, we sort the roots in the remembered set and start
evacuating from the one pointing to the leftmost object in the nursery.

Moreover, this is sufficient while evacuating the shadow-stack as well.
Because at that time we only care about the boundaries of a burned field,
anything within it doesn't need to be traversed.



*** Finding a region's metadata from a pointer into it:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Every time we write an indirection while evacuating, we must adjust refcounts
and outsets. In order to do this we need the address of the metadata for the
pointed-to region, which we don't always have. For example, while evacuating
a young-to-old indirection added by the mutator, we only know the address of
the pointed-to data and nothing else. This stops us from writing *any*
indirections during evacuation, forcing us to always inline everything.
To address this, we need a way to go from a pointer to some data in a region
to that region's metadata, which is stored in its footer.

We could do one of three things here:

(1) always inline EVERYTHING, but this is terrible.

(2) in addition to storing an indirection pointer, we could also store the
    metadata adress with it by using extra space. this means that an
    indirection pointer (and correspondingly all forwarding pointers) will now
    occupy 17 bytes! yikes.

(3) fit all of this information in an 8 byte pointer by using the top 16 bits
    to store a *tag*. this tag could be a distance-to-region-footer offset,
    using which we can reach the footer and extract the metadata address that's
    stored there. but this does introduces an upper bound on the size of the
    biggest chunk that Gibbon can allocate; 65K bytes (2^16).

    TODO(ckoparkar): MR and STH pointed out that if we ensure that the footer's
    address is always aligned to a power of 2, we can store *more* information
    in 16 bits and increase the upper bound the chunk size.


*** Restoring uncauterized write cursors:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Some write cursors don't get uncauterized and need to be restored by hand.
This happens when a region has been allocated but nothing has been written
to it yet. So there will be a write cursor for it on the shadow-stack but there
won't be any read cursors pointing to any data before this write cursor, since
there isn't any data here. Thus this write cursor won't get uncauterized during
evacuation. We need to restore all such start-of-chunk uncauterized write
cursors by allocating fresh chunks for them in the nursery. To accomplish this,
we track all write cursors in a "cauterized environment" that maps a write
cursor to a list of shadow-stack frames that it appears in. Why a list of frames?
Because some write cursors may have multiple frames tracking them. E.g. if we
allocate a region and pass it to a function, and the function immediately pushes
it to the stack again (e.g. maybe because it makes a function call or allocates
a new region etc.), we'll have two frames tracking the *same address* in memory.
Thus, we must track all such frames corresponding to a memory addrerss.


*** Sorting roots on the shadow-stack and remembered set:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The order in which GC roots are processed has a huge impact on the
representation of the evacuated value in the old generation. Ideally we'd like
to reduce the number of indirections in the evacuated value as much as possible.
The only indirections we should add are those that represent "real" sharing.
Consider a situation in which the value shown below is allocated in the nursery,
and the outermost node and the second leaf are both on the shadow-stack.

┌─────────────┐
│  N L 1 L 2  │
└──│─────│────┘
   x     y

If we process x first and then y, we get the following value:

┌─────────────┐      ┌─────────────┐
│  I •────────│──┐   │  N L 1 L 2  │
└──│──────────┘  │   └──│─────│────┘
   y             │      x     │
                 └────────────┘


However, if we process y first and then x, we get the following value:


┌─────────────┐      ┌─────────────┐
│  L 2        │      │  N L 1 I •  │
└──│──────────┘      └──│───────│──┘
   y                    x       │
   │                            │
   └────────────────────────────┘


TODO.


*/

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Garbage Collector; evacuation, promotion etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// If we have variable sized initial chunks due to the region bound analysis,
/// we'll have to store that info in a chunk footer, and then that could guide
/// how big this new chunk should be. Using a default value of 1024 for now.
const CHUNK_SIZE: u64 = 1024;
const MAX_CHUNK_SIZE: u64 = 1 * 1024 * 1024 * 1024;

pub fn cleanup(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
) -> Result<()> {
    // Free the info table.
    unsafe {
        drop(INFO_TABLE.take());
    }
    // Free all the regions.
    let mut oldest_gen = OldestGeneration(generations_ptr);
    let rstack = &Shadowstack(rstack_ptr, GcRootProv::Stk);
    let wstack = &Shadowstack(wstack_ptr, GcRootProv::Stk);
    let nursery = &Nursery(nursery_ptr);
    if C_NUM_GENERATIONS == 1 {
        unsafe {
            if !(*generations_ptr).old_zct.is_null() {
                for frame in rstack.into_iter().chain(wstack.into_iter()) {
                    if !nursery.contains_addr((*frame).endptr) {
                        (*((*generations_ptr).old_zct)).insert(
                            (*frame).endptr as *const C_GibChunkFooter,
                        );
                    }
                }
                for footer in (*((*generations_ptr).old_zct)).drain() {
                    free_region(footer, (*generations_ptr).new_zct, true)?;
                }
            }
        }
    } else {
        todo!("NUM_GENERATIONS > 1")
    }
    // Free ZCTs associated with the oldest generation.
    oldest_gen.free_zcts();
    Ok(())
}

pub fn garbage_collect(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
    _force_major: bool,
) -> Result<()> {
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
        let mut cenv = cauterize_writers(nursery, wstack)?;
        // Prepare to evacuate the readers.
        let chunk_starts = nursery.chunk_starts();
        let mut oldest_gen = OldestGeneration(generations_ptr);
        unsafe {
            // Initialize ZCTs if this is the very first collection.
            if (*nursery_ptr).num_collections == 0 {
                oldest_gen.init_zcts();
            }
            let rem_set = &mut RememberedSet(
                (*generations_ptr).rem_set,
                GcRootProv::RemSet,
            );
            // First evacuate the remembered set, then the shadow-stack.
            let mut benv = evacuate_remembered_set(
                &mut cenv,
                &chunk_starts,
                (*generations_ptr).new_zct,
                &mut oldest_gen,
                rem_set,
            )?;
            rem_set.clear();
            evacuate_shadowstack(
                nursery,
                &mut benv,
                &mut cenv,
                &chunk_starts,
                (*generations_ptr).new_zct,
                &mut oldest_gen,
                rstack,
            )?;
            // // Collect dead regions.
            oldest_gen.collect_regions()?;
        }
        // Reset the allocation area and record stats.
        nursery.clear();
        nursery.bump_num_collections();
        // Restore the remaining cauterized writers. Allocate space for them
        // in the nursery, not oldgen.
        restore_writers(&cenv, nursery)?;
        Ok(())
    } else {
        todo!("NUM_GENERATIONS > 1")
    }
}

/// Write a C_CAUTERIZED_TAG at all write cursors so that the collector knows
/// when to stop copying.
fn cauterize_writers(
    nursery: &Nursery,
    wstack: &Shadowstack,
) -> Result<CauterizedEnv> {
    let mut cenv: CauterizedEnv = HashMap::new();
    for frame in wstack.into_iter() {
        unsafe {
            if !nursery.contains_addr((*frame).ptr) {
                continue;
            }
            let ptr = (*frame).ptr as *mut i8;
            let ptr_next = write(ptr, C_CAUTERIZED_TAG);
            write(ptr_next, frame);
            match cenv.get_mut(&ptr) {
                None => {
                    cenv.insert(ptr, vec![frame]);
                    ()
                }
                Some(frames) => frames.push(frame),
            }
        }
    }
    Ok(cenv)
}

/// See Note [Restoring uncauterized write cursors].
fn restore_writers(cenv: &CauterizedEnv, heap: &mut impl Heap) -> Result<()> {
    for (_wptr, frames) in cenv.iter() {
        /*
        if !(*start_of_chunk) {
            return Err(RtsError::Gc(format!(
                "restore_writers: uncauterized cursor that's not at the \
                 start of a chunk, {:?}",
                wptr
            )));
        }
         */
        let (chunk_start, chunk_end) = Heap::allocate(heap, CHUNK_SIZE)?;
        for frame in frames {
            unsafe {
                (*(*frame)).ptr = chunk_start;
                (*(*frame)).endptr = chunk_end;
            }
        }
    }
    Ok(())
}

/// See Note [Restoring uncauterized write cursors].
type CauterizedEnv = HashMap<*mut i8, Vec<*mut C_GibShadowstackFrame>>;

/// See Note [Traversing burned data].
type BurnedAddressEnv = HashMap<*mut i8, *const i8>;

/// Copy values at all read cursors from the remembered set to the provided
/// destination heap. Update the burned environment along the way.
/// The roots are processed in a left-to-right order based on the addresses of
/// the pointers they contain, to avoid the issue of running into holes due to
/// burning while we're still evacuating the remembered set.
/// See Note [Granularity of the burned addresses table].
unsafe fn evacuate_remembered_set(
    cenv: &mut CauterizedEnv,
    chunk_starts: &HashSet<*mut i8>,
    zct: *mut HashSet<*const C_GibChunkFooter>,
    heap: &mut impl Heap,
    rem_set: &Shadowstack,
) -> Result<BurnedAddressEnv> {
    let mut benv: BurnedAddressEnv = HashMap::new();
    let frames = sort_roots(rem_set);
    for frame in frames {
        let datatype = (*frame).datatype;
        match INFO_TABLE.get().unwrap().get(&datatype) {
            None => {
                return Err(RtsError::Gc(format!(
                    "copy_readers: Unknown datatype, {:?}",
                    datatype
                )));
            }
            // A scalar type that can be copied directly.
            Some(DatatypeInfo::Scalar(size)) => {
                // Allocate space in the destination.
                let (dst, dst_end) =
                    Heap::allocate_first_chunk(heap, 32 + *size as u64, 1)?;
                // The remembered set contains the address of the indirection
                // pointer. We must read it to get the address of the pointed-to
                // data.
                let (src, _): (*mut i8, _) = read((*frame).ptr);
                // Evacuate the data.
                copy_nonoverlapping(src, dst, *size as usize);
                // Update the indirection pointer in oldgen region.
                write((*frame).ptr as *mut i8, dst);
                // Update the outset in oldgen region.
                add_to_outset((*frame).endptr, dst_end);
                // Update the burned address table.
                benv.insert(src, src.add(*size as usize));
            }
            // A packed type that is copied by referring to the info table.
            Some(DatatypeInfo::Packed(packed_info)) => {
                // Allocate space in the destination.
                let (dst, dst_end) =
                    Heap::allocate_first_chunk(heap, CHUNK_SIZE, 1)?;
                // The remembered set contains the address where the indirect-
                // ion pointer is stored. We must read it to get the address of
                // the pointed-to data.
                let (src, _): (*mut i8, _) = read((*frame).ptr);
                // Evacuate the data.
                let (src_after, _dst_after, _dst_after_end, _tag) =
                    evacuate_packed(
                        &mut benv,
                        cenv,
                        chunk_starts,
                        zct,
                        heap,
                        &GcRootProv::RemSet,
                        packed_info,
                        src,
                        dst,
                        dst_end,
                    )?;
                // Update the indirection pointer in oldgen region.
                write((*frame).ptr as *mut i8, dst);
                // Update the outset in oldgen region.
                add_to_outset((*frame).endptr, dst_end);
                // Update the burned address table.
                benv.insert(src, src_after);
            }
        }
    }
    Ok(benv)
}

/// Copy values at all read cursors from the nursery to the provided
/// destination heap. Also uncauterize any writer cursors that are reached.
unsafe fn evacuate_shadowstack(
    nursery: &Nursery,
    benv: &mut BurnedAddressEnv,
    cenv: &mut CauterizedEnv,
    chunk_starts: &HashSet<*mut i8>,
    zct: *mut HashSet<*const C_GibChunkFooter>,
    heap: &mut impl Heap,
    rstack: &Shadowstack,
) -> Result<()> {
    // let frames = rstack.into_iter();
    let frames = sort_roots(rstack);
    for frame in frames {
        let datatype = (*frame).datatype;
        if !nursery.contains_addr((*frame).ptr) {
            let footer = (*frame).endptr as *const C_GibChunkFooter;
            if (*((*footer).reg_info)).refcount == 0 {
                (*zct).insert(footer);
            }
            continue;
        }
        match INFO_TABLE.get().unwrap().get(&datatype) {
            None => {
                return Err(RtsError::Gc(format!(
                    "copy_readers: Unknown datatype, {:?}",
                    datatype
                )));
            }
            // A scalar type that can be copied directly.
            Some(DatatypeInfo::Scalar(size)) => {
                // Allocate space in the destination.
                let (dst, dst_end) =
                    Heap::allocate_first_chunk(heap, 32 + *size as u64, 0)?;
                // Evacuate the data.
                let src = (*frame).ptr as *mut i8;
                copy_nonoverlapping(src, dst, *size as usize);
                // Update the pointers in shadow-stack.
                (*frame).ptr = dst;
                (*frame).endptr = dst_end;
                // Update ZCT.
                (*zct).insert(dst_end as *const C_GibChunkFooter);
            }
            // A packed type that is copied by referring to the info table.
            Some(DatatypeInfo::Packed(packed_info)) => {
                // Allocate space in the destination.
                let (dst, dst_end) =
                    Heap::allocate_first_chunk(heap, CHUNK_SIZE, 0)?;
                // Evacuate the data.
                let src = (*frame).ptr as *mut i8;
                let (src_after, dst_after, dst_after_end, tag) =
                    evacuate_packed(
                        benv,
                        cenv,
                        chunk_starts,
                        zct,
                        heap,
                        &GcRootProv::Stk,
                        packed_info,
                        src,
                        dst,
                        dst_end,
                    )?;
                // Update the pointers in shadow-stack.
                (*frame).ptr = dst;
                (*frame).endptr = dst_after_end;
                // Update ZCT.
                (*zct).insert(dst_end as *const C_GibChunkFooter);
                // Note [Adding a forwarding pointer at the end of every chunk].
                match tag {
                    C_COPIED_TO_TAG | C_COPIED_TAG => {}
                    _ => {
                        if chunk_starts.contains(&src)
                            || tag == C_CAUTERIZED_TAG
                        {
                            write_forwarding_pointer_at(
                                src_after,
                                dst_after,
                                dst_after_end
                                    .offset_from(dst_after)
                                    .try_into()
                                    .unwrap(),
                            );
                        }
                    }
                }
            }
        }
    }
    Ok(())
}

/**

Evacuate a packed value by referring to the info table.

Arguments:

- benv - an environment that provides the ends of burned fields. only
  relevant when evacuating the shadow-stack.
- cenv - an environment that tracks cauterized write cursors
- heap - allocation area to copy data into
- packed_info - information about the fields of this datatype
- need_endof_src - if evacuate_packed MUST traverse the value at src and return
  a proper src_after, or throw an error if it cannot do so.
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
- maybe_tag - return the tag of the the datacon that was just copied.
              copy_readers uses this tag to decide whether it should write a
              forwarding pointer at the end of the source buffer.

 */
unsafe fn evacuate_packed(
    benv: &mut BurnedAddressEnv,
    cenv: &mut CauterizedEnv,
    chunk_starts: &HashSet<*mut i8>,
    zct: *mut HashSet<*const C_GibChunkFooter>,
    heap: &mut impl Heap,
    prov: &GcRootProv,
    packed_info: &HashMap<C_GibPackedTag, DataconInfo>,
    src: *mut i8,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*mut i8, *mut i8, *const i8, C_GibPackedTag)> {
    let (tag, src_after_tag): (C_GibPackedTag, *mut i8) = read_mut(src);
    match tag {
        // Nothing to copy. Just update the write cursor's new
        // address in shadow-stack.
        C_CAUTERIZED_TAG => {
            let (wframe_ptr, _): (*const i8, _) = read(src_after_tag);
            let wframe = wframe_ptr as *mut C_GibShadowstackFrame;
            // Mark this cursor as uncauterized.
            let del = (*wframe).ptr as *mut i8;
            cenv.remove(&del);
            // Update the poiners on the shadow-stack.
            (*wframe).ptr = dst;
            (*wframe).endptr = dst_end;
            Ok((src, dst, dst_end, tag))
        }
        // See Note [Maintaining sharing, Copied and CopiedTo tags].
        C_COPIED_TO_TAG => {
            let (tagged_fwd_ptr, _): (u64, _) = read_mut(src_after_tag);
            let tagged = TaggedPointer::from_u64(tagged_fwd_ptr);
            let fwd_ptr = tagged.pointer();
            let space_reqd = 18;
            let (dst1, dst_end1) =
                Heap::check_bounds(heap, space_reqd, dst, dst_end)?;
            let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
            let dst_after_indr = write(dst_after_tag, fwd_ptr);
            let src_after_burned = match benv.get(&src) {
                None => null_mut(),
                Some(end) => *end as *mut i8,
            };
            // Update outsets and refcounts if evacuating to the oldest
            // generation.
            if heap.is_oldest() {
                let fwd_footer_offset = tagged.tag();
                let fwd_footer_addr = fwd_ptr.add(fwd_footer_offset as usize);
                bump_refcount(fwd_footer_addr);
                add_to_outset(dst_end, fwd_footer_addr);
                match prov {
                    GcRootProv::RemSet => {}
                    GcRootProv::Stk => {
                        (*zct).remove(
                            &(fwd_footer_addr as *const C_GibChunkFooter),
                        );
                        ()
                    }
                }
            }
            Ok((src_after_burned, dst_after_indr, dst_end1, tag))
        }
        // See Note [Maintaining sharing, Copied and CopiedTo tags].
        C_COPIED_TAG => {
            let (mut scan_tag, mut scan_ptr): (C_GibPackedTag, *const i8) =
                read(src_after_tag);
            while scan_tag != C_COPIED_TO_TAG {
                (scan_tag, scan_ptr) = read(scan_ptr);
            }
            // At this point the scan_ptr is one past the
            // C_COPIED_TO_TAG i.e. at the forwarding pointer.
            let offset = scan_ptr.offset_from(src) - 1;
            // The forwarding pointer that's available.
            let (tagged_fwd_avail, _): (u64, _) = read(scan_ptr);
            let tagged = TaggedPointer::from_u64(tagged_fwd_avail);
            let fwd_avail = tagged.pointer();
            // The position in the destination buffer we wanted.
            let fwd_want = fwd_avail.sub(offset as usize);
            let space_reqd = 18;
            let (dst1, dst_end1) =
                Heap::check_bounds(heap, space_reqd, dst, dst_end)?;
            let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
            let dst_after_indr = write(dst_after_tag, fwd_want);
            let src_after_burned = match benv.get(&src) {
                None => null_mut(),
                Some(end) => *end as *mut i8,
            };
            // Update outsets and refcounts if evacuating to the oldest
            // generation.
            if heap.is_oldest() {
                let fwd_footer_offset = tagged.tag();
                let fwd_footer_addr =
                    fwd_avail.add(fwd_footer_offset as usize);
                bump_refcount(fwd_footer_addr);
                add_to_outset(dst_end, fwd_footer_addr);
                match prov {
                    GcRootProv::RemSet => {}
                    GcRootProv::Stk => {
                        (*zct).remove(
                            &(fwd_footer_addr as *const C_GibChunkFooter),
                        );
                        ()
                    }
                }
            }
            Ok((src_after_burned, dst_after_indr, dst_end1, tag))
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
            write_forwarding_pointer_at(
                src,
                dst,
                dst_end.offset_from(dst).try_into().unwrap(),
            );
            // Continue in the next chunk.
            evacuate_packed(
                benv,
                cenv,
                chunk_starts,
                zct,
                heap,
                prov,
                packed_info,
                next_chunk,
                dst,
                dst_end,
            )
        }
        // A pointer to a value in another buffer; copy this value
        // and then switch back to copying rest of the source buffer.
        //
        // POLICY DECISION:
        // Indirections are always inlined in the current version.
        C_INDIRECTION_TAG => {
            let (pointee, _): (*mut i8, _) = read(src_after_tag);
            let (
                src_after_pointee,
                dst_after_pointee,
                dst_after_pointee_end,
                _,
            ) = evacuate_packed(
                benv,
                cenv,
                chunk_starts,
                zct,
                heap,
                prov,
                packed_info,
                pointee,
                dst,
                dst_end,
            )?;
            // Add a forwarding pointer in the source buffer.
            write(src, C_COPIED_TO_TAG);
            let src_after_indr = write_forwarding_pointer_at(
                src,
                dst,
                dst_end.offset_from(dst).try_into().unwrap(),
            );
            // Update the burned environment if we're evacuating a root
            // from the remembered set.
            match prov {
                GcRootProv::RemSet => {
                    benv.insert(pointee, src_after_pointee);
                    ()
                }
                GcRootProv::Stk => (),
            }
            // Return 1 past the indirection pointer as src_after
            // and the dst_after that evacuate_packed returned.
            Ok((src_after_indr, dst_after_pointee, dst_after_pointee_end, tag))
        }
        // Regular datatype, copy.
        _ => {
            let DataconInfo { scalar_bytes, field_tys, num_scalars, .. } =
                packed_info
                    .get(&tag)
                    .expect(&format!("Unknown tag: {:?}", tag));
            // Check bound of the destination buffer before copying.
            // Reserve additional space for a redirection node or a
            // forwarding pointer.
            let space_reqd: usize = (32 + *scalar_bytes).into();
            {
                // Scope for mutable variables src_mut and dst_mut,
                // which are the read and write cursors in the source
                // and destination buffer respectively.

                let (mut dst_mut, mut dst_end_mut) =
                    Heap::check_bounds(heap, space_reqd, dst, dst_end)?;
                // Copy the tag and the fields.
                dst_mut = write(dst_mut, tag);
                dst_mut.copy_from_nonoverlapping(
                    src_after_tag,
                    *scalar_bytes as usize,
                );
                let mut src_mut = src_after_tag.add(*scalar_bytes as usize);
                dst_mut = dst_mut.add(*scalar_bytes as usize);
                // Add forwarding pointers:
                // if there's enough space, write a COPIED_TO tag and
                // dst's address at src. Otherwise just write a COPIED tag.
                // After the forwarding pointer, burn the rest of
                // space previously occupied by scalars.
                let burn = if *scalar_bytes >= 8 {
                    write_forwarding_pointer_at(
                        src,
                        dst,
                        dst_end.offset_from(dst).try_into().unwrap(),
                    )
                } else {
                    write(src, C_COPIED_TAG)
                };
                if src_mut != burn {
                    let i = src_mut.offset_from(burn);
                    write_bytes(burn, C_COPIED_TAG, i as usize);
                }
                // TODO(ckoparkar):
                // (1) instead of recursion, use a worklist
                // (2) handle redirection nodes properly
                for ty in field_tys.iter().skip((*num_scalars) as usize) {
                    let (src1, dst1, dst_end1, field_tag) = evacuate_field(
                        benv,
                        cenv,
                        chunk_starts,
                        zct,
                        heap,
                        prov,
                        ty,
                        src_mut,
                        dst_mut,
                        dst_end_mut,
                    )?;
                    // Must immediately stop copying upon reaching
                    // the cauterized tag.
                    match field_tag {
                        C_CAUTERIZED_TAG => {
                            return Ok((src1, dst1, dst_end1, field_tag));
                        }
                        _ => {
                            src_mut = src1;
                            dst_mut = dst1;
                            dst_end_mut = dst_end1;
                        }
                    }
                }
                Ok((src_mut, dst_mut, dst_end_mut, tag))
            }
        }
    }
}

unsafe fn evacuate_field(
    benv: &mut BurnedAddressEnv,
    cenv: &mut CauterizedEnv,
    chunk_starts: &HashSet<*mut i8>,
    zct: *mut HashSet<*const C_GibChunkFooter>,
    heap: &mut impl Heap,
    prov: &GcRootProv,
    datatype: &C_GibDatatype,
    src: *mut i8,
    dst: *mut i8,
    dst_end: *const i8,
) -> Result<(*mut i8, *mut i8, *const i8, C_GibPackedTag)> {
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
            Ok((src.add(size1), dst.add(size1), dst_end, C_SCALAR_TAG))
        }
        Some(DatatypeInfo::Packed(packed_info)) => evacuate_packed(
            benv,
            cenv,
            chunk_starts,
            zct,
            heap,
            prov,
            packed_info,
            src,
            dst,
            dst_end,
        ),
    }
}

fn sort_roots(
    roots: &Shadowstack,
) -> Box<dyn Iterator<Item = *mut C_GibShadowstackFrame>> {
    // Store all the frames in a vector and sort,
    // see Note [Granularity of the burned addresses table] and
    // Note [Sorting roots on the shadow-stack and remembered set].
    let mut frames_vec: Vec<*mut C_GibShadowstackFrame> = Vec::new();
    for frame in roots.into_iter() {
        frames_vec.push(frame);
    }
    frames_vec.sort_unstable_by(|a, b| unsafe {
        let ptra: *const i8 = (*(*a)).ptr;
        let ptrb: *const i8 = (*(*b)).ptr;
        (ptra).cmp(&ptrb)
    });
    Box::new(frames_vec.into_iter())
}

#[inline]
unsafe fn read<A>(cursor: *const i8) -> (A, *const i8) {
    let cursor2 = cursor as *const A;
    (cursor2.read_unaligned(), cursor2.add(1) as *const i8)
}

#[inline]
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
 * Managing regions, chunks, metadata etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

impl C_GibRegionInfo {
    pub fn new() -> C_GibRegionInfo {
        C_GibRegionInfo {
            id: gensym(),
            refcount: 0,
            outset_len: 0,
            outset: [null(); 10],
            outset2: Box::into_raw(Box::new(HashSet::new())),
        }
    }
}

static mut GENSYM_COUNTER: u64 = 0;

/// ASSUMPTION: no parallelism.
fn gensym() -> u64 {
    unsafe {
        let old = GENSYM_COUNTER;
        GENSYM_COUNTER = old + 1;
        old
    }
}

unsafe fn write_forwarding_pointer_at(
    addr: *mut i8,
    fwd: *const i8,
    tag: u16,
) -> *mut i8 {
    let tagged: u64 = TaggedPointer::new(fwd, tag as u16).as_u64();
    let addr1 = write(addr, C_COPIED_TO_TAG);
    write(addr1, tagged)
}

unsafe fn free_region(
    footer: *const C_GibChunkFooter,
    zct: *mut HashSet<*const C_GibChunkFooter>,
    free_descendants: bool,
) -> Result<()> {
    // Rust drops this heap allocated object when reg_info goes out of scope.
    let reg_info = Box::from_raw((*footer).reg_info);
    // Decrement refcounts of all regions in the outset and add the ones with a
    // zero refcount to the ZCT. Also free the HashSet backing the outset for
    // this region.
    let outset: Box<HashSet<*const i8>> = Box::from_raw(reg_info.outset2);
    for o_ptr in outset.into_iter() {
        let o_new_refcount = decrement_refcount(o_ptr);
        if o_new_refcount == 0 {
            if free_descendants {
                free_region(o_ptr as *const C_GibChunkFooter, zct, true)?;
            } else {
                (*zct).insert(o_ptr as *const C_GibChunkFooter);
            }
        }
    }
    // Free the chunks in this region.
    let first_chunk_footer = trav_to_first_chunk(footer)?;
    let mut free_this = addr_to_free(first_chunk_footer);
    let mut next_chunk_footer = (*first_chunk_footer).next;
    // Free the first chunk.
    libc::free(free_this);
    // Then all others.
    while !next_chunk_footer.is_null() {
        free_this = addr_to_free(next_chunk_footer);
        next_chunk_footer = (*next_chunk_footer).next;
        libc::free(free_this);
    }
    Ok(())
}

unsafe fn addr_to_free(footer: *const C_GibChunkFooter) -> *mut libc::c_void {
    ((footer as *const i8).sub((*footer).size as usize)) as *mut libc::c_void
}

unsafe fn trav_to_first_chunk(
    footer: *const C_GibChunkFooter,
) -> Result<*const C_GibChunkFooter> {
    if (*footer).prev.is_null() {
        if (*footer).seq_no == 0 {
            Ok(footer)
        } else {
            Err(RtsError::Gc(format!(
                "No previous chunk found at seq_no: {}",
                (*footer).seq_no
            )))
        }
    } else {
        trav_to_first_chunk((*footer).prev)
    }
}

unsafe fn add_to_outset(from_addr: *const i8, to_addr: *const i8) {
    let footer = from_addr as *mut C_GibChunkFooter;
    let reg_info = (*footer).reg_info;
    (*((*reg_info).outset2)).insert(to_addr);
}

unsafe fn bump_refcount(addr: *const i8) -> u16 {
    let footer = addr as *mut C_GibChunkFooter;
    let reg_info = (*footer).reg_info;
    (*reg_info).refcount += 1;
    (*reg_info).refcount
}

unsafe fn decrement_refcount(addr: *const i8) -> u16 {
    let footer = addr as *mut C_GibChunkFooter;
    let reg_info = (*footer).reg_info;
    (*reg_info).refcount -= 1;
    (*reg_info).refcount
}

unsafe fn init_footer_at(
    chunk_end: *const i8,
    reg_info: Option<*mut C_GibRegionInfo>,
    seq_no: u16,
    chunk_size: u64,
    refcount: u16,
) -> *const i8 {
    let footer_space = size_of::<C_GibChunkFooter>();
    let footer_start = chunk_end.sub(footer_space);

    let region_info_ptr: *mut C_GibRegionInfo = match reg_info {
        None => {
            let mut region_info = C_GibRegionInfo::new();
            region_info.refcount = refcount;
            Box::into_raw(Box::new(region_info))
        }
        Some(info_ptr) => info_ptr,
    };
    let footer: *mut C_GibChunkFooter = footer_start as *mut C_GibChunkFooter;
    (*footer).reg_info = region_info_ptr;
    (*footer).seq_no = seq_no;
    (*footer).size = chunk_size;
    (*footer).next = null_mut();
    (*footer).prev = null_mut();
    footer_start
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

    fn allocate_first_chunk(
        &mut self,
        size: u64,
        refcount: u16,
    ) -> Result<(*mut i8, *const i8)> {
        if !self.is_oldest() {
            self.allocate(size)
        } else {
            let total_size = size + (size_of::<C_GibChunkFooter>() as u64);
            let (start, end) = self.allocate(total_size)?;
            let footer_start =
                unsafe { init_footer_at(end, None, 0, size, refcount) };
            Ok((start, footer_start))
        }
    }

    fn allocate_next_chunk(
        &mut self,
        dst: *mut i8,
        dst_end: *const i8,
    ) -> Result<(*mut i8, *const i8)> {
        unsafe {
            if !self.is_oldest() {
                let (new_dst, new_dst_end) = Heap::allocate(self, CHUNK_SIZE)?;
                // Write a redirection tag in the old chunk.
                let dst_after_tag = write(dst, C_REDIRECTION_TAG);
                write(dst_after_tag, new_dst);
                Ok((new_dst, new_dst_end))
            } else {
                // Access the old footer to get the region metadata.
                let old_footer = dst_end as *mut C_GibChunkFooter;
                // Allocate space for the new chunk.
                let mut chunk_size = (*old_footer).size * 2;
                if chunk_size > MAX_CHUNK_SIZE {
                    chunk_size = MAX_CHUNK_SIZE;
                }
                let (new_dst, new_dst_end) = Heap::allocate(self, chunk_size)?;
                // Write a redirection tag in the old chunk.
                let dst_after_tag = write(dst, C_REDIRECTION_TAG);
                write(dst_after_tag, new_dst);
                // Initialize a footer at the end of the new chunk.
                let reg_info: *mut C_GibRegionInfo = (*old_footer).reg_info;
                let new_footer_start = init_footer_at(
                    new_dst_end,
                    Some(reg_info),
                    (*old_footer).seq_no + 1,
                    chunk_size,
                    (*reg_info).refcount,
                );
                let new_footer: *mut C_GibChunkFooter =
                    new_footer_start as *mut C_GibChunkFooter;
                (*old_footer).next = new_footer;
                (*new_footer).prev = old_footer;
                Ok((new_dst, new_footer_start))
            }
        }
    }

    fn check_bounds(
        &mut self,
        space_reqd: usize,
        dst: *mut i8,
        dst_end: *const i8,
    ) -> Result<(*mut i8, *const i8)> {
        let space_avail = unsafe { dst_end.offset_from(dst) as usize };
        if space_avail >= space_reqd {
            Ok((dst, dst_end))
        } else {
            self.allocate_next_chunk(dst, dst_end)
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
    fn clear(&mut self) {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            (*nursery).alloc = (*nursery).heap_end;
            (*nursery).chunk_starts_i = 0;
        }
    }

    fn chunk_starts(&self) -> HashSet<*mut i8> {
        let nursery: *mut C_GibNursery = self.0;
        let mut chunk_starts = HashSet::new();
        unsafe {
            let mut run_ptr: *const i8 = (*nursery).chunk_starts;
            let end_ptr = run_ptr.add(
                size_of::<*const i8>() * (*nursery).chunk_starts_i as usize,
            );
            while run_ptr < end_ptr {
                let (chunk_start_addr, next): (*mut i8, _) = read(run_ptr);
                chunk_starts.insert(chunk_start_addr);
                run_ptr = next;
            }
        }
        chunk_starts
    }

    fn contains_addr(&self, addr: *const i8) -> bool {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            (addr >= (*nursery).heap_start) && (addr <= (*nursery).heap_end)
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
            assert!((*nursery).alloc > (*nursery).heap_start);
            (*nursery).alloc.offset_from((*nursery).heap_start) as usize
        }
    }

    fn allocate(&mut self, size: u64) -> Result<(*mut i8, *const i8)> {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            assert!((*nursery).alloc >= (*nursery).heap_start);
            let old = (*nursery).alloc as *mut i8;
            let bump = old.sub(size as usize);
            let start = (*nursery).heap_start as *mut i8;
            // Check if there's enough space in the nursery to fulfill the
            // request.
            if bump >= start {
                (*nursery).alloc = bump;
                Ok((bump, old))
            } else {
                Err(RtsError::Gc(format!(
                    "nursery alloc: out of space, requested={:?}, \
                     available={:?}",
                    size,
                    old.offset_from(start)
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
            assert!((*gen).alloc > (*gen).heap_start);
            (*gen).alloc.offset_from((*gen).heap_start) as usize
        }
    }

    fn allocate(&mut self, size: u64) -> Result<(*mut i8, *const i8)> {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            assert!((*gen).alloc > (*gen).heap_start);
            let old = (*gen).alloc as *mut i8;
            let bump = old.sub(size as usize);
            let start = (*gen).heap_start as *mut i8;
            // Check if there's enough space in the gen to fulfill the request.
            if bump >= start {
                (*gen).mem_allocated += size;
                (*gen).alloc = bump;
                Ok((bump, old))
            } else {
                Err(RtsError::Gc(format!(
                    "gen alloc: out of space, requested={:?}, available={:?}",
                    size,
                    old.offset_from(start)
                )))
            }
        }
    }
}

/// A wrapper over the naked C pointer.
struct OldestGeneration(*mut C_GibGeneration);

impl OldestGeneration {
    fn collect_regions(&mut self) -> Result<()> {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            for footer in (*((*gen).old_zct)).drain() {
                if !(*((*gen).new_zct)).contains(&footer) {
                    free_region(footer, (*gen).new_zct, false)?;
                }
            }
        }
        self.swap_zcts();
        Ok(())
    }

    fn init_zcts(&mut self) {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            (*gen).old_zct = Box::into_raw(Box::new(HashSet::new()));
            (*gen).new_zct = Box::into_raw(Box::new(HashSet::new()));
        }
    }

    fn free_zcts(&mut self) {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            if !(*gen).old_zct.is_null() {
                // Rust will drop these heap objects at the end of this scope.
                Box::from_raw((*gen).old_zct);
                Box::from_raw((*gen).new_zct);
            }
        }
    }

    fn swap_zcts(&mut self) {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            let tmp = (*gen).old_zct;
            (*gen).old_zct = (*gen).new_zct;
            (*gen).new_zct = tmp;
        }
    }
}

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
 * Shadow-stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// Provenance of a GC root; shadow-stack or remembered set.
#[derive(Debug, PartialEq, Eq)]
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

    /// Delete all frames from the shadow-stack.
    fn clear(&mut self) {
        let ss: *mut C_GibShadowstack = self.0;
        unsafe {
            (*ss).alloc = (*ss).start;
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

/// An iterator to traverse the shadow-stack.
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
// use ShadowstackIter as RememberedSetIter;

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
                ));
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
                ));
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
