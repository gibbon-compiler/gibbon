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
