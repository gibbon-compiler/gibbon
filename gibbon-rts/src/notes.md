*
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
