#![allow(dead_code)]

/*!

Implementation of the new generational garbage collector for Gibbon.

 */

use libc;

use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::mem::size_of;
use std::ptr::{null_mut, write_bytes};

use crate::ffi::types::*;
use crate::measure;
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


*** Smart inlining policies:
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

The current heuristic for when to inline indirections/redirections is very
simple. If the pointed-to region is in the old generation, it is never inlined.
Maybe we can have a smarter policy which inlines indirections/redirections
up to a limit (e.g. 2KB) or tries to infer the size of the object based on
which region it is in. The latter isn't straightforward because a large object
can *start* in one of the smaller chunks and a huge chunk could have a small
object too.

Deferred until after the paper deadline...


*/

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Garbage Collector; evacuation, promotion etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// If we have variable sized initial chunks due to the region bound analysis,
/// we'll have to store that info in a chunk footer, and then that could guide
/// how big this new chunk should be. Using a default value of 1024 for now.
const CHUNK_SIZE: usize = 1024;
const MAX_CHUNK_SIZE: usize = 65500;

const COLLECT_MAJOR_K: u8 = 4;

static mut GC_STATS: *mut C_GibGcStats = null_mut();

pub fn cleanup(
    rstack_ptr: *mut C_GibShadowstack,
    wstack_ptr: *mut C_GibShadowstack,
    nursery_ptr: *mut C_GibNursery,
    generations_ptr: *mut C_GibGeneration,
) -> Result<()> {
    unsafe {
        // Free the info table.
        _INFO_TABLE.drain(..);
        _INFO_TABLE.shrink_to_fit();
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
                    let footer = (*frame).endptr as *const C_GibChunkFooter;
                    if !nursery.contains_addr((*frame).endptr) {
                        (*((*generations_ptr).old_zct))
                            .insert((*footer).reg_info);
                    }
                }
                for reg_info in (*((*generations_ptr).old_zct)).drain() {
                    free_region(
                        (*reg_info).first_chunk_footer,
                        (*generations_ptr).new_zct,
                        true,
                    )?;
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
    gc_stats: *mut C_GibGcStats,
    _force_major: bool,
) -> Result<()> {
    // println!("gc...");
    let rstack = Shadowstack(rstack_ptr, GcRootProv::Stk);
    let wstack = Shadowstack(wstack_ptr, GcRootProv::Stk);
    let mut nursery = Nursery(nursery_ptr);
    if C_NUM_GENERATIONS == 1 {
        // Start by cauterizing the writers.
        let mut cenv = cauterize_writers(&nursery, &wstack)?;
        // Prepare to evacuate the readers.
        let mut oldest_gen = OldestGeneration(generations_ptr);
        unsafe {
            // let evac_major = force_major
            //     || (*nursery_ptr).num_collections.rem_euclid(COLLECT_MAJOR_K.into())
            //         == 0;
            let evac_major = false;

            // Update stats.
            GC_STATS = gc_stats;
            stats_bump_minor_collections();
            if evac_major {
                stats_bump_major_collections();
            }

            // Start collection.
            let mut rem_set =
                RememberedSet((*generations_ptr).rem_set, GcRootProv::RemSet);
            // First evacuate the remembered set, then the shadow-stack.
            let mut benv = evacuate_remembered_set(
                &mut cenv,
                (*generations_ptr).new_zct,
                &nursery,
                &mut oldest_gen,
                &rem_set,
                evac_major,
            )?;
            rem_set.clear();
            evacuate_shadowstack(
                &mut benv,
                &mut cenv,
                (*generations_ptr).new_zct,
                &nursery,
                &mut oldest_gen,
                &rstack,
                evac_major,
            )?;
            // Collect dead regions.
            oldest_gen.collect_regions()?;
        }
        // Reset the allocation area and record stats.
        nursery.clear();
        // Restore the remaining cauterized writers. Allocate space for them
        // in the nursery, not oldgen.
        restore_writers(&cenv, &mut nursery)?;
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
            let ptr = (*frame).ptr;
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
type BurnedAddressEnv = HashMap<*mut i8, *mut i8>;

/// A set of start addresses of regions allocated in the nursery.
type ChunkStartsSet = HashSet<*mut i8>;

/// Things needed during evacuation.
#[derive(Debug)]
struct EvacState<'a> {
    benv: &'a mut BurnedAddressEnv,
    cenv: &'a mut CauterizedEnv,
    zct: *mut Zct,
    nursery: &'a Nursery,
    // heap: Box<&'a mut dyn Heap>,
    prov: &'a GcRootProv,
    evac_major: bool,
}

/// Copy values at all read cursors from the remembered set to the provided
/// destination heap. Update the burned environment along the way.
/// The roots are processed in a left-to-right order based on the addresses of
/// the pointers they contain, to avoid the issue of running into holes due to
/// burning while we're still evacuating the remembered set.
/// See Note [Granularity of the burned addresses table].
unsafe fn evacuate_remembered_set(
    cenv: &mut CauterizedEnv,
    zct: *mut Zct,
    nursery: &Nursery,
    heap: &mut impl Heap,
    rem_set: &Shadowstack,
    evac_major: bool,
) -> Result<BurnedAddressEnv> {
    let mut benv: BurnedAddressEnv = HashMap::new();
    let frames =
        measure!(sort_roots(rem_set), (*GC_STATS).gc_rootset_sort_time);
    for frame in frames {
        let datatype = (*frame).datatype;
        // let packed_info = INFO_TABLE.get_unchecked(datatype as usize);
        // Allocate space in the destination.
        let (dst, dst_end) = Heap::allocate_first_chunk(heap, CHUNK_SIZE, 1)?;
        // The remembered set contains the address where the indirect-
        // ion pointer is stored. We must read it to get the address of
        // the pointed-to data.
        let (tagged_src, _): (u64, _) = read((*frame).ptr);
        let tagged = TaggedPointer::from_u64(tagged_src);
        let src = tagged.untag();
        // Evacuate the data.
        let mut st = EvacState {
            benv: &mut benv,
            cenv,
            zct,
            nursery,
            prov: &GcRootProv::RemSet,
            evac_major,
        };
        let (src_after, _dst_after, _dst_after_end, _tag) =
            evacuate_packed(&mut st, heap, datatype, src, dst, dst_end);
        // Update the indirection pointer in oldgen region.
        write((*frame).ptr, dst);
        // Update the outset in oldgen region.
        add_to_outset((*frame).endptr, dst_end);
        // Update the burned address table.
        benv.insert(src, src_after);
    }
    Ok(benv)
}

/// Copy values at all read cursors from the nursery to the provided
/// destination heap. Also uncauterize any writer cursors that are reached.
unsafe fn evacuate_shadowstack(
    benv: &mut BurnedAddressEnv,
    cenv: &mut CauterizedEnv,
    zct: *mut Zct,
    nursery: &Nursery,
    heap: &mut impl Heap,
    rstack: &Shadowstack,
    evac_major: bool,
) -> Result<()> {
    // let frames = rstack.into_iter();
    let frames = sort_roots(rstack);
    for frame in frames {
        let root_in_nursery = nursery.contains_addr((*frame).endptr);
        if !evac_major && !root_in_nursery {
            let footer = (*frame).endptr as *const C_GibChunkFooter;
            if (*((*footer).reg_info)).refcount == 0 {
                (*zct).insert((*footer).reg_info);
            }
            continue;
        }

        let datatype = (*frame).datatype;        

        // Allocate space in the destination.
        let (dst, dst_end) = Heap::allocate_first_chunk(heap, CHUNK_SIZE, 0)?;
        // Update ZCT.
        let footer = dst_end as *const C_GibChunkFooter;
        measure!(
            (*zct).insert((*footer).reg_info),
            (*GC_STATS).gc_zct_mgmt_time
        );
        // Evacuate the data.
        let mut st = EvacState {
            benv,
            cenv,
            zct,
            nursery,
            prov: &GcRootProv::Stk,
            evac_major,
        };
        let src = (*frame).ptr;
        let src_end = (*frame).endptr;
        let chunk_size = if root_in_nursery {
            let nursery_footer: *mut u16 = (*frame).endptr as *mut u16;
            *nursery_footer as usize
        } else {
            CHUNK_SIZE
        };
        let is_loc_0 = (src_end.offset_from(src)) == chunk_size as isize;

        let (src_after, dst_after, dst_after_end, tag) =
            evacuate_packed(&mut st, heap, datatype, src, dst, dst_end);
        // Update the pointers in shadow-stack.
        (*frame).ptr = dst;
        // TODO(ckoparkar): AUDITME.
        // (*frame).endptr = dst_after_end;
        (*frame).endptr = dst_end;
        // Note [Adding a forwarding pointer at the end of every chunk].
        match tag {
            C_COPIED_TO_TAG | C_COPIED_TAG | C_REDIRECTION_TAG => {}
            _ => {
                if is_loc_0 || tag == C_CAUTERIZED_TAG {
                    assert!(dst_after < dst_after_end);
                    write_forwarding_pointer_at(
                        src_after,
                        dst_after,
                        dst_after_end.offset_from(dst_after) as u16, // .try_into()
                                                                     // .unwrap()
                    );
                }
            }
        }
    }
    Ok(())
}



#[derive(Debug)]
// The actions pushed on the stack while evacuating.
enum EvacAction {
    ProcessTy(C_GibDatatype),
    RestoreSrc(*mut i8)
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
    st: &mut EvacState,
    heap: &mut impl Heap,
    orig_typ: C_GibDatatype,
    orig_src: *mut i8,
    orig_dst: *mut i8,
    orig_dst_end: *mut i8,
) -> (*mut i8, *mut i8, *mut i8, C_GibPackedTag) {
    // These four comprise the main mutable state of the traversal and should be updated 
    // together at the end of every iteration:
    let mut src = orig_src;
    let mut dst = orig_dst;
    let mut dst_end = orig_dst_end;
    // The implicit -1th element of the worklist:
    let mut next_action = EvacAction::ProcessTy(orig_typ);

    // TODO: get rid of this: 
    let (orig_tag, _): (C_GibPackedTag, *mut i8) = read_mut(orig_src);

    #[cfg(feature = "gcstats")]
    eprintln!("Evac packed {:?} -> {:?}", src, dst);

    // Stores everything to process AFTER the next_action.
    let mut worklist: Vec<EvacAction> = Vec::new();    
    
    loop {      
      #[cfg(feature = "gcstats")]    
      eprintln!("  Loop iteration on src {:?} action {:?}, length after this {}", src, next_action, worklist.len());
    
      match next_action {
          EvacAction::RestoreSrc(new_src) => {
              src = new_src;

              // make this reusable somehow (local macro?)
              if let Some(next) = worklist.pop() {
                next_action = next;          
                continue;
              } else {
                break;
              }              
          }
          EvacAction::ProcessTy(next_ty) => {
            let (tag, src_after_tag): (C_GibPackedTag, *mut i8) = read_mut(src);
    
            let packed_info = INFO_TABLE.get_unchecked(next_ty as usize); 
            match tag {    
      /*
              // Nothing to copy. Just update the write cursor's new
              // address in shadow-stack.
              C_CAUTERIZED_TAG => {
                  todo!();
                  let (wframe_ptr, _): (*mut i8, _) = read(src_after_tag);
                  let wframe = wframe_ptr as *mut C_GibShadowstackFrame;
                  // Mark this cursor as uncauterized.
                  let del = (*wframe).ptr;
                  st.cenv.remove(&del);
                  // Update the poiners on the shadow-stack.
                  (*wframe).ptr = dst;
                  (*wframe).endptr = dst_end;
                  (src, dst, dst_end, tag)
              }
              // See Note [Maintaining sharing, Copied and CopiedTo tags].
              C_COPIED_TO_TAG => {
                  todo!();    
                  let (tagged_fwd_ptr, _): (u64, _) = read_mut(src_after_tag);
                  let tagged = TaggedPointer::from_u64(tagged_fwd_ptr);
                  let fwd_ptr = tagged.untag();
                  let space_reqd = 32;
                  let (dst1, dst_end1) =
                      Heap::check_bounds(heap, space_reqd, dst, dst_end);
                  let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
                  let dst_after_indr = write(dst_after_tag, tagged_fwd_ptr);
                  stats_bump_mem_copied(9);
                  // TODO(ckoparkar): check that no code path will try to read/write
                  // at this null pointer.
                  let src_after_burned = match st.benv.get(&src) {
                      None => null_mut(),
                      Some(end) => *end,
                  };
                  // Update outsets and refcounts if evacuating to the oldest
                  // generation.
                  if heap.is_oldest() {
                      let fwd_footer_offset = tagged.get_tag();
                      let fwd_footer_addr = fwd_ptr.add(fwd_footer_offset as usize);
                      handle_old_to_old_indirection(dst_end, fwd_footer_addr);
                      match st.prov {
                          GcRootProv::RemSet => {}
                          GcRootProv::Stk => {
                              let fwd_footer =
                                  fwd_footer_addr as *const C_GibChunkFooter;
                              measure!(
                                  (*(st.zct)).remove(
                                      &((*fwd_footer).reg_info
                                          as *const C_GibRegionInfo),
                                  ),
                                  (*GC_STATS).gc_zct_mgmt_time
                              );
                              ()
                          }
                      }
                  }
                  (src_after_burned, dst_after_indr, dst_end1, tag)
              }
              // See Note [Maintaining sharing, Copied and CopiedTo tags].
              C_COPIED_TAG => {
                  todo!();    
                  let (mut scan_tag, mut scan_ptr): (C_GibPackedTag, *const i8) =
                      read(src_after_tag);
                  while scan_tag != C_COPIED_TO_TAG {
                      (scan_tag, scan_ptr) = read(scan_ptr);
                  }
                  // At this point the scan_ptr is one past the
                  // C_COPIED_TO_TAG i.e. at the forwarding pointer.
                  assert!((src as *const i8) < scan_ptr);
                  let offset = scan_ptr.offset_from(src) - 1;
                  // The forwarding pointer that's available.
                  let (tagged_fwd_avail, _): (u64, _) = read(scan_ptr);
                  let tagged_avail = TaggedPointer::from_u64(tagged_fwd_avail);
                  let fwd_avail = tagged_avail.untag();
                  let fwd_footer_offset_avail = tagged_avail.get_tag();
                  let fwd_footer_addr_avail =
                      fwd_avail.add(fwd_footer_offset_avail as usize);
                  // The position in the destination buffer we wanted.
                  let fwd_want = fwd_avail.sub(offset as usize);
                  let fwd_footer_offset_want =
                      fwd_footer_addr_avail.offset_from(fwd_want);
                  let tagged_want: u64 = TaggedPointer::new(
                      fwd_avail,
                      fwd_footer_offset_want as u16, // try_into().unwrap()
                  )
                  .as_u64();
                  let space_reqd = 32;
                  let (dst1, dst_end1) =
                      Heap::check_bounds(heap, space_reqd, dst, dst_end);
                  let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
                  let dst_after_indr = write(dst_after_tag, tagged_want);
                  stats_bump_mem_copied(9);
                  // TODO(ckoparkar): check that no code path will try to read/write
                  // at this null pointer.
                  let src_after_burned = match st.benv.get(&src) {
                      None => null_mut(),
                      Some(end) => *end,
                  };
                  // Update outsets and refcounts if evacuating to the oldest
                  // generation.
                  if heap.is_oldest() {
                      handle_old_to_old_indirection(dst_end, fwd_footer_addr_avail);
                      match st.prov {
                          GcRootProv::RemSet => {}
                          GcRootProv::Stk => {
                              let fwd_footer =
                                  fwd_footer_addr_avail as *const C_GibChunkFooter;
                              measure!(
                                  (*(st.zct)).remove(
                                      &((*fwd_footer).reg_info
                                          as *const C_GibRegionInfo),
                                  ),
                                  (*GC_STATS).gc_zct_mgmt_time
                              );
                              ()
                          }
                      }
                  }
                  (src_after_burned, dst_after_indr, dst_end1, tag)
              }
      
              // Indicates end-of-current-chunk in the source buffer i.e.
              // there's nothing more to copy in the current chunk.
              // Follow the redirection pointer to the next chunk and
              // continue copying there.
              //
              // POLICY DECISION:
              // Redirections into oldgen are not inlined in the current version.
              // See Note [Smart inlining policies].
              C_REDIRECTION_TAG => {            
                  let (tagged_next_chunk, src_after_next_chunk): (u64, _) =
                      read(src_after_tag);
                  let tagged = TaggedPointer::from_u64(tagged_next_chunk);
                  let next_chunk = tagged.untag();
                  // Add a forwarding pointer in the source buffer.
                  assert!(dst < dst_end);
                  write_forwarding_pointer_at(
                      src,
                      dst,
                      dst_end.offset_from(dst) as u16, // .try_into().unwrap()
                  );
      
                  // If the next chunk is in the nursery, continue evacuating it.
                  // Otherwise, write a redireciton node at dst (pointing to
                  // the start of the oldgen chunk), link the footers and reconcile
                  // the two RegionInfo objects.
                  if st.evac_major || st.nursery.contains_addr(next_chunk) {
                      evacuate_packed(
                          st,
                          heap,
                          packed_info,
                          next_chunk,
                          dst,
                          dst_end,
                      )
                  } else {
                      // TODO(ckoparkar): BUGGY, AUDITME.
                      let dst_after_tag = write(dst, C_REDIRECTION_TAG);
                      let dst_after_redir = write(dst_after_tag, tagged_next_chunk);
                      stats_bump_mem_copied(9);
      
                      // Link footers.
                      let footer1 = dst_end as *mut C_GibChunkFooter;
                      let next_chunk_footer_offset = tagged.get_tag();
                      let footer2 = next_chunk.add(next_chunk_footer_offset as usize)
                          as *mut C_GibChunkFooter;
      
                      // Reconcile RegionInfo objects.
                      let reg_info1 = (*footer1).reg_info;
                      let reg_info2 = (*footer2).reg_info;
                      (*reg_info2).refcount += (*reg_info1).refcount;
                      (*((*reg_info2).outset)).extend(&*((*reg_info1).outset));
                      (*reg_info2).first_chunk_footer =
                          (*reg_info1).first_chunk_footer;
                      (*footer1).next = footer2;
                      (*footer1).reg_info = reg_info2;
      
                      // Update ZCT.
                      measure!(
                          (*(st.zct)).remove(&(reg_info1 as *const C_GibRegionInfo)),
                          (*GC_STATS).gc_zct_mgmt_time
                      );
                      measure!(
                          (*(st.zct)).insert(reg_info2),
                          (*GC_STATS).gc_zct_mgmt_time
                      );
                      // Stop evacuating.
                      (
                          src_after_next_chunk as *mut i8,
                          dst_after_redir,
                          dst_end,
                          tag,
                      )
                  }
              }        
      */    
      
              // A pointer to a value in another buffer; copy this value
              // and then switch back to copying rest of the source buffer.
              //
              // POLICY DECISION:
              // Indirections into oldgen are not inlined in the current version.
              // See Note [Smart inlining policies].
              C_INDIRECTION_TAG => {            
                  let (tagged_pointee, src_after_indr): (u64, _) =
                      read(src_after_tag);
      
                      #[cfg(feature = "gcstats")]
                      eprintln!("   indirection! src {:?} dest {:?}, after {:?}", src_after_tag, tagged_pointee as *mut i8, src_after_indr);      

                  let src_after_indr1 = src_after_indr as *mut i8;
                  let tagged = TaggedPointer::from_u64(tagged_pointee);
                  let pointee = tagged.untag();
                  // Add a forwarding pointer in the source buffer.
                  debug_assert!(dst < dst_end);
      /* TEMP
                  write_forwarding_pointer_at(
                      src,
                      dst,
                      dst_end.offset_from(dst) as u16, // .try_into().unwrap()
                  );
      */            
                  // If the pointee is in the nursery, evacuate it.
                  // Otherwise, write an indirection node at dst and adjust the
                  // refcount and outset.
                  if st.evac_major || st.nursery.contains_addr(pointee) {

                      // TAIL OPTIMIZATION: if we're the last thing, in the worklist, don't bother restoring src:
                      if !worklist.is_empty() {                         
                         worklist.push(EvacAction::RestoreSrc(src_after_indr1));
                      } else {
                        #[cfg(feature = "gcstats")]
                        eprintln!("   tail optimization!");      
                      }
                      src = pointee;
                      // Same type, new location to evac from:
                      next_action = EvacAction::ProcessTy(next_ty); // Fixme, don't push just for the while() to pop.
                      continue;

                      // TODO: restore Benv actions as a separate explicit EvacAction for the stack.
                      /*
                      // Update the burned environment if we're evacuating a root
                      // from the remembered set.
                      match st.prov {
                          GcRootProv::RemSet => {
                              st.benv.insert(pointee, src_after_pointee);
                              ()
                          }
                          GcRootProv::Stk => (),
                      }
                      */

                      // Return 1 past the indirection pointer as src_after
                      // and the dst_after that evacuate_packed returned.
                    /*                      
                      result = (
                          src_after_indr1,
                          dst_after_pointee,
                          dst_after_pointee_end,
                          tag,
                      );
                      */
                  } else {                    
                      let space_reqd = 32;
                      let (dst1, dst_end1) =
                          Heap::check_bounds(heap, space_reqd, dst, dst_end);
                      let dst_after_tag = write(dst1, C_INDIRECTION_TAG);
                      let dst_after_indr = write(dst_after_tag, tagged_pointee);
                      stats_bump_mem_copied(9);
                      let pointee_footer_offset = tagged.get_tag();
                      let pointee_footer =
                          pointee.add(pointee_footer_offset as usize);
                      // TODO(ckoparkar): incorrect pointee_footer_offset causes
                      // treeinsert to segfault.
                      handle_old_to_old_indirection(dst_end1, pointee_footer);
                      // (*zct).insert(
                      //     ((*(pointee_footer as *mut C_GibChunkFooter)).reg_info
                      //         as *const C_GibRegionInfo),
                      // );

                      src = src_after_indr1;
                      dst = dst_after_indr;
                      dst_end = dst_end1;

                      // make this reusable somehow (local macro?)
                      if let Some(next) = worklist.pop() {
                        next_action = next;          
                        continue;
                      } else {
                          break;
                      }
                  }        
              }
      
              // Regular datatype, copy.
              _ => {
                  let DataconInfo { scalar_bytes, field_tys, .. } =
                      packed_info.get_unchecked(tag as usize);
      
                  #[cfg(feature = "gcstats")]
                  eprintln!("   regular datacon, field_tys {:?}", field_tys);
                      
                  let scalar_bytes1 = *scalar_bytes;
      
                  // Check bound of the destination buffer before copying.
                  // Reserve additional space for a redirection node or a
                  // forwarding pointer.
                  let space_reqd: usize = 32 + scalar_bytes1;
                  {
                      // Scope for mutable variables src_mut and dst_mut,
                      // which are the read and write cursors in the source
                      // and destination buffer respectively.
      
                      let (mut dst2, dst_end2) =
                          Heap::check_bounds(heap, space_reqd, dst, dst_end);
                      // Copy the tag and the fields.
                      dst2 = write(dst2, tag);
                      dst2.copy_from_nonoverlapping(src_after_tag, scalar_bytes1);
                      dst2 = dst2.add(scalar_bytes1);
                      stats_bump_mem_copied(1 + scalar_bytes1);
                                                  
                      // Add forwarding pointers:
                      // if there's enough space, write a COPIED_TO tag and
                      // dst's address at src. Otherwise just write a COPIED tag.
                      // After the forwarding pointer, burn the rest of
                      // space previously occupied by scalars.
      
      /* TEMP
                      // let burn = 
                      if scalar_bytes1 >= 8 {
                          debug_assert!(dst < dst_end);
                          write_forwarding_pointer_at(
                              src,
                              dst,
                              dst_end.offset_from(dst) as u16, // .try_into().unwrap()
                          );
                      };
      */
      /*                
                      else {
                          write(src, C_COPIED_TAG)
                      };
                      if src_mut > burn {
                          let i = src_mut.offset_from(burn);
                          write_bytes(burn, C_COPIED_TAG, i as usize);
                      }
      */
                      // TODO(ckoparkar):
                      // (1) instead of recursion, use a worklist
                      // (2) handle redirection nodes properly
                      for ty in field_tys.iter().rev() {                
                          worklist.push(EvacAction::ProcessTy(*ty));
                      }

                      src = src_after_tag.add(scalar_bytes1);
                      dst = dst2;
                      dst_end = dst_end2;
                      
                      // make this reusable somehow (local macro?)
                      if let Some(next) = worklist.pop() {
                        next_action = next;          
                        continue;
                      } else {
                          break;
                      }

                      // TODO: restore cauterize behavior.  But couldn't that go in the cauterize case?
      /*                
                      for ty in field_tys.iter() {
                          eprintln!("    field iter loop over ty {:?}", ty);
                          let packed_info = INFO_TABLE.get_unchecked(*ty as usize);
                          let (src1, dst1, dst_end1, field_tag) = evacuate_packed(
                              st,
                              heap,
                              packed_info,
                              src_mut,
                              dst_mut,
                              dst_end_mut,
                          );
                          match field_tag {
                              // Immediately stop copying upon reaching the
                              // cauterized tag.
                              C_CAUTERIZED_TAG => {
                                  todo!();    
                                  return (src1, dst1, dst_end1, field_tag);
                              }
                              // This redirection would likely be in oldgen and the
                              // next call to evacuate_packed would terminate anyway.
                              // Unless we're evacuating the oldgen as well, in which
                              // case keep evacuating.
                              C_REDIRECTION_TAG if !st.evac_major => {
                                  todo!();
                                  return (src1, dst1, dst_end1, field_tag);
                              }
                              _ => {
                                  src_mut = src1;
                                  dst_mut = dst1;
                                  dst_end_mut = dst_end1;
                              }
                          }
                      }
                      */
                  }                            
              }         
          } // End match
          }
      }      
   }; // End while   
   (src, dst, dst_end, orig_tag)
}

fn sort_roots(
    roots: &Shadowstack,
) -> Box<dyn Iterator<Item = *mut C_GibShadowstackFrame>> {
    // Store all the frames in a vector and sort,
    // see Note [Granularity of the burned addresses table] and
    // Note [Sorting roots on the shadow-stack and remembered set].
    //
    // TODO(ckoparkar): sort roots into oldgen and nursery seperately;
    // for oldgen we want to sort using highest depth first,
    // for nursery we want to start with leftmost root first.
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

#[inline(always)]
unsafe fn read<A>(cursor: *const i8) -> (A, *const i8) {
    let cursor2 = cursor as *const A;
    (cursor2.read_unaligned(), cursor2.add(1) as *const i8)
}

#[inline(always)]
unsafe fn read_mut<A>(cursor: *mut i8) -> (A, *mut i8) {
    let cursor2 = cursor as *const A;
    (cursor2.read_unaligned(), cursor2.add(1) as *mut i8)
}

#[inline(always)]
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
    fn new(first_chunk_footer: *const C_GibChunkFooter) -> C_GibRegionInfo {
        C_GibRegionInfo {
            id: gensym(),
            refcount: 0,
            outset: Box::into_raw(Box::new(HashSet::new())),
            first_chunk_footer: first_chunk_footer,
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

#[inline(always)]
unsafe fn write_forwarding_pointer_at(
    addr: *mut i8,
    fwd: *mut i8,
    tag: u16,
) -> *mut i8 {
    let tagged: u64 = TaggedPointer::new(fwd, tag).as_u64();
    let addr1 = write(addr, C_COPIED_TO_TAG);
    write(addr1, tagged)
}

unsafe fn free_region(
    footer: *const C_GibChunkFooter,
    zct: *mut Zct,
    free_descendants: bool,
) -> Result<()> {
    stats_dec_oldgen_regions();
    // Rust drops this heap allocated object when reg_info goes out of scope.
    let reg_info = Box::from_raw((*footer).reg_info);
    // Decrement refcounts of all regions in the outset and add the ones with a
    // zero refcount to the ZCT. Also free the HashSet backing the outset for
    // this region.
    let outset: Box<Outset> = Box::from_raw(reg_info.outset);
    for o_reg_info in outset.into_iter() {
        (*(o_reg_info as *mut C_GibRegionInfo)).refcount -= 1;
        if (*o_reg_info).refcount == 0 {
            if free_descendants {
                free_region((*o_reg_info).first_chunk_footer, zct, true)?;
            } else {
                (*zct).insert(o_reg_info);
            }
        }
    }
    // Free the chunks in this region.
    let mut free_this = addr_to_free(footer);
    let mut next_chunk_footer = (*footer).next;
    // Free the first chunk and then all others.
    libc::free(free_this);
    while !next_chunk_footer.is_null() {
        free_this = addr_to_free(next_chunk_footer);
        next_chunk_footer = (*next_chunk_footer).next;
        libc::free(free_this);
    }
    drop(reg_info);
    Ok(())
}

unsafe fn addr_to_free(footer: *const C_GibChunkFooter) -> *mut libc::c_void {
    ((footer as *const i8).sub((*footer).size)) as *mut libc::c_void
}

pub unsafe fn handle_old_to_old_indirection(
    from_footer_ptr: *mut i8,
    to_footer_ptr: *mut i8,
) {
    let added = add_to_outset(from_footer_ptr, to_footer_ptr);
    if added {
        bump_refcount(to_footer_ptr);
    }
}

unsafe fn add_to_outset(from_addr: *mut i8, to_addr: *const i8) -> bool {
    let from_reg_info = (*(from_addr as *mut C_GibChunkFooter)).reg_info;
    let to_reg_info = (*(to_addr as *mut C_GibChunkFooter)).reg_info;
    (*((*from_reg_info).outset)).insert(to_reg_info)
}

unsafe fn bump_refcount(addr: *mut i8) -> u16 {
    let reg_info = (*(addr as *mut C_GibChunkFooter)).reg_info;
    (*reg_info).refcount += 1;
    (*reg_info).refcount
}

unsafe fn decrement_refcount(addr: *mut i8) -> u16 {
    let reg_info = (*(addr as *mut C_GibChunkFooter)).reg_info;
    (*reg_info).refcount -= 1;
    (*reg_info).refcount
}

pub unsafe fn init_footer_at(
    chunk_end: *mut i8,
    reg_info: *mut C_GibRegionInfo,
    // Total size of the chunk, *including* space required to store the footer.
    chunk_size: usize,
    refcount: u16,
) -> *mut i8 {
    let footer_space = size_of::<C_GibChunkFooter>();
    let footer_start = chunk_end.sub(footer_space);
    let footer: *mut C_GibChunkFooter = footer_start as *mut C_GibChunkFooter;
    let region_info_ptr: *mut C_GibRegionInfo = if reg_info.is_null() {
        let mut region_info = C_GibRegionInfo::new(footer);
        region_info.refcount = refcount;
        Box::into_raw(Box::new(region_info))
    } else {
        reg_info
    };
    (*footer).reg_info = region_info_ptr;
    (*footer).size = chunk_size - footer_space;
    (*footer).next = null_mut();
    footer_start
}

#[inline(always)]
#[cold]
fn cold() {}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Generic memory allocation
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/// Typeclass for different allocation areas; nurseries, generations etc.
trait Heap {
    fn is_nursery(&self) -> bool;
    fn is_oldest(&self) -> bool;
    fn allocate(&mut self, size: usize) -> Result<(*mut i8, *mut i8)>;
    fn space_available(&self) -> usize;

    fn allocate_first_chunk(
        &mut self,
        size: usize,
        refcount: u16,
    ) -> Result<(*mut i8, *mut i8)> {
        if !self.is_oldest() {
            self.allocate(size)
        } else {
            let total_size = size + size_of::<C_GibChunkFooter>();
            let (start, end) = self.allocate(total_size)?;
            let footer_start = unsafe {
                init_footer_at(end, null_mut(), total_size, refcount)
            };
            stats_bump_oldgen_regions();
            Ok((start, footer_start))
        }
    }

    fn allocate_next_chunk(
        &mut self,
        dst: *mut i8,
        dst_end: *mut i8,
    ) -> (*mut i8, *mut i8) {
        unsafe {
            if !self.is_oldest() {
                let (new_dst, new_dst_end) =
                    Heap::allocate(self, CHUNK_SIZE).unwrap();
                // Write a redirection tag in the old chunk.
                let dst_after_tag = write(dst, C_REDIRECTION_TAG);
                write(dst_after_tag, new_dst);
                (new_dst, new_dst_end)
            } else {
                // Access the old footer to get the region metadata.
                let old_footer = dst_end as *mut C_GibChunkFooter;
                // Allocate space for the new chunk.
                let mut chunk_size = (*old_footer).size * 2;
                if chunk_size > MAX_CHUNK_SIZE {
                    chunk_size = MAX_CHUNK_SIZE;
                }
                let (new_dst, new_dst_end) =
                    Heap::allocate(self, chunk_size).unwrap();
                // Initialize a footer at the end of the new chunk.
                let reg_info: *mut C_GibRegionInfo = (*old_footer).reg_info;
                let new_footer_start = init_footer_at(
                    new_dst_end,
                    reg_info,
                    chunk_size,
                    (*reg_info).refcount,
                );
                // Write a redirection tag in the old chunk.
                let footer_offset: u16 =
                    new_footer_start.offset_from(new_dst) as u16; // .try_into().unwrap()

                let tagged: u64 =
                    TaggedPointer::new(new_dst, footer_offset).as_u64();
                let dst_after_tag = write(dst, C_REDIRECTION_TAG);
                write(dst_after_tag, tagged);
                // Link the footers.
                let new_footer: *mut C_GibChunkFooter =
                    new_footer_start as *mut C_GibChunkFooter;
                (*old_footer).next = new_footer;
                (new_dst, new_footer_start)
            }
        }
    }

    #[inline(always)]
    fn check_bounds(
        &mut self,
        space_reqd: usize,
        dst: *mut i8,
        dst_end: *mut i8,
    ) -> (*mut i8, *mut i8) {
        assert!(dst < dst_end);
        let space_avail = unsafe { dst_end.offset_from(dst) as usize };
        if space_avail >= space_reqd {
            (dst, dst_end)
        } else {
            cold();
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
    #[inline(always)]
    fn clear(&mut self) {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            (*nursery).alloc = (*nursery).heap_end;
        }
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
    #[inline(always)]
    fn is_nursery(&self) -> bool {
        true
    }

    #[inline(always)]
    fn is_oldest(&self) -> bool {
        false
    }

    #[inline(always)]
    fn space_available(&self) -> usize {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            assert!((*nursery).alloc > (*nursery).heap_start);
            (*nursery).alloc.offset_from((*nursery).heap_start) as usize
        }
    }

    #[inline(always)]
    fn allocate(&mut self, size: usize) -> Result<(*mut i8, *mut i8)> {
        let nursery: *mut C_GibNursery = self.0;
        unsafe {
            assert!((*nursery).alloc >= (*nursery).heap_start);
            let old = (*nursery).alloc as *mut i8;
            let bump = old.sub(size);
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
    #[inline(always)]
    fn is_nursery(&self) -> bool {
        false
    }

    #[inline(always)]
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

    #[inline(always)]
    fn allocate(&mut self, size: usize) -> Result<(*mut i8, *mut i8)> {
        let gen: *mut C_GibGeneration = self.0;
        unsafe {
            assert!((*gen).alloc > (*gen).heap_start);
            let old = (*gen).alloc as *mut i8;
            let bump = old.sub(size);
            let start = (*gen).heap_start as *mut i8;
            // Check if there's enough space in the gen to fulfill the request.
            if bump >= start {
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
            for reg_info in (*((*gen).old_zct)).drain() {
                let footer = (*reg_info).first_chunk_footer;
                // TODO(ckoparkar): review ZCT usage.
                if (*reg_info).refcount == 0
                    && !(*((*gen).new_zct)).contains(&reg_info)
                    && !(*((*gen).new_zct)).contains(
                        &((*footer).reg_info as *const C_GibRegionInfo),
                    )
                {
                    free_region(
                        (*reg_info).first_chunk_footer,
                        (*gen).new_zct,
                        false,
                    )?;
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
    #[inline(always)]
    fn is_nursery(&self) -> bool {
        false
    }

    #[inline(always)]
    fn is_oldest(&self) -> bool {
        true
    }

    #[inline(always)]
    fn space_available(&self) -> usize {
        0
    }

    #[inline(always)]
    fn allocate(&mut self, size: usize) -> Result<(*mut i8, *mut i8)> {
        // let gen: *mut C_GibGeneration = self.0;
        unsafe {
            let start = libc::malloc(size) as *mut i8;
            if start.is_null() {
                Err(RtsError::Gc(format!("oldest gen alloc: malloc failed")))
            } else {
                let end = start.add(size);
                stats_bump_mem_allocated(size);
                Ok((start, end))
            }
        }
    }
}

pub fn init_zcts(generations_ptr: *mut C_GibGeneration) {
    if C_NUM_GENERATIONS == 1 {
        let mut oldest_gen = OldestGeneration(generations_ptr);
        oldest_gen.init_zcts();
    } else {
        todo!("NUM_GENERATIONS > 1");
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
// TODO(ckoparkar): delete the second parameter here.

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

type _DataconEnv = Vec<DataconInfo>;
type _DatatypeEnv = Vec<_DatatypeInfo>;

#[derive(Debug, Clone)]
struct DataconInfo {
    /// Bytes before the first packed field.
    scalar_bytes: usize,
    /// Number of scalar fields.
    num_scalars: u8,
    /// Number of packed fields.
    num_packed: u8,
    /// Field types.
    field_tys: Vec<C_GibDatatype>,
}

#[derive(Debug, Clone)]
enum _DatatypeInfo {
    _Scalar(usize),
    _Packed(_DataconEnv),
}

/// The global info table.
static mut _INFO_TABLE: _DatatypeEnv = Vec::new();

#[inline(always)]
pub fn info_table_initialize(size: usize) {
    unsafe {
        // If a datatype is not packed, info_table_insert_scalar will
        // overwrite this entry.
        _INFO_TABLE = vec![_DatatypeInfo::_Packed(Vec::new()); size];
    }
}

#[inline(always)]
pub fn info_table_insert_packed_dcon(
    datatype: C_GibDatatype,
    datacon: C_GibPackedTag,
    scalar_bytes: usize,
    num_scalars: u8,
    num_packed: u8,
    field_tys: Vec<C_GibDatatype>,
) -> Result<()> {
    let dcon_info =
        DataconInfo { scalar_bytes, num_scalars, num_packed, field_tys };
    let entry = unsafe { _INFO_TABLE.get_unchecked_mut(datatype as usize) };
    match entry {
        _DatatypeInfo::_Packed(packed_info) => {
            while packed_info.len() <= datacon.into() {
                packed_info.push(dcon_info.clone());
            }
            packed_info[datacon as usize] = dcon_info;
            Ok(())
        }
        _DatatypeInfo::_Scalar(_) => Err(RtsError::InfoTable(format!(
            "Expected a packed entry for datatype {:?}, got a scalar.",
            datatype
        ))),
    }
}

pub fn info_table_insert_scalar(datatype: C_GibDatatype, size: usize) {
    unsafe {
        _INFO_TABLE[datatype as usize] = _DatatypeInfo::_Scalar(size);
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */
type DataconEnv = &'static [DataconInfo];
type DatatypeEnv = &'static [DatatypeInfo];
type DatatypeInfo = DataconEnv;

/// The global info table.
static mut INFO_TABLE: &[DatatypeInfo] = &[];

pub fn info_table_finalize() {
    unsafe {
        let info_table: *mut DatatypeInfo =
            libc::malloc(_INFO_TABLE.len() * size_of::<DatatypeInfo>())
                as *mut DatatypeInfo;
        let mut info_table_alloc = info_table;
        for ty in _INFO_TABLE.iter() {
            match ty {
                _DatatypeInfo::_Scalar(_size) => {
                    // let ty_info = DatatypeInfo::Scalar(*size);
                    // // info_table_alloc.write_unaligned(ty_info);
                    // *info_table_alloc = ty_info;
                    info_table_alloc = info_table_alloc.add(1);
                }
                _DatatypeInfo::_Packed(_packed_info) => {
                    let packed_info = &_packed_info[..];
                    *info_table_alloc = packed_info;
                    info_table_alloc = info_table_alloc.add(1);
                }
            }
        }
        INFO_TABLE = std::slice::from_raw_parts(info_table, _INFO_TABLE.len());
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Update GC statistics
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#[cfg(feature = "gcstats")]
#[inline(always)]
fn stats_bump_minor_collections() {
    unsafe {
        (*GC_STATS).minor_collections += 1;
    }
}

#[cfg(not(feature = "gcstats"))]
#[inline(always)]
fn stats_bump_minor_collections() {}

#[cfg(feature = "gcstats")]
#[inline(always)]
fn stats_bump_major_collections() {
    unsafe {
        (*GC_STATS).major_collections += 1;
    }
}

#[cfg(not(feature = "gcstats"))]
#[inline(always)]
fn stats_bump_major_collections() {}

#[cfg(feature = "gcstats")]
#[inline(always)]
fn stats_bump_oldgen_regions() {
    unsafe {
        (*GC_STATS).oldgen_regions += 1;
    }
}

#[cfg(not(feature = "gcstats"))]
#[inline(always)]
fn stats_bump_oldgen_regions() {}

#[cfg(feature = "gcstats")]
#[inline(always)]
fn stats_dec_oldgen_regions() {
    unsafe {
        (*GC_STATS).oldgen_regions -= 1;
    }
}

#[cfg(not(feature = "gcstats"))]
#[inline(always)]
fn stats_dec_oldgen_regions() {}

#[cfg(feature = "gcstats")]
#[inline(always)]
fn stats_bump_mem_allocated(size: usize) {
    unsafe {
        (*GC_STATS).mem_allocated += size;
    }
}

#[cfg(not(feature = "gcstats"))]
#[inline(always)]
fn stats_bump_mem_allocated(_size: usize) {}

#[cfg(feature = "gcstats")]
#[inline(always)]
fn stats_bump_mem_copied(size: usize) {
    unsafe {
        (*GC_STATS).mem_copied += size;
    }
}

#[cfg(not(feature = "gcstats"))]
#[inline(always)]
fn stats_bump_mem_copied(_size: usize) {}

#[cfg(feature = "gcstats")]
#[macro_export]
macro_rules! measure {
    ( $x:expr, $addr:expr ) => {{
        let start = std::time::Instant::now();
        let y = $x;
        let duration = start.elapsed();
        $addr += duration.as_secs_f64();
        y
    }};
}

#[cfg(not(feature = "gcstats"))]
#[macro_export]
macro_rules! measure {
    ( $x:expr, $addr:expr ) => {{
        $x
    }};
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
