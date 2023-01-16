/*!

Use the high 16 bits to *tag* a pointer. This module is a slightly modified
version of tagged_ptr module in [`tagged-box`].
Also see https://stackoverflow.com/a/18426582.

[`tagged-box`]: https://github.com/Kixiron/tagged-box/blob/48f4eba26ad390cecfefa4cbb86e59290fa874b7/src/tagged_pointer.rs

*/

use core::mem::size_of;
use std::fmt;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/// The number of bits reserved for the tag.
const TAG_BITS: u64 = 16;

/// The number of bits reserved for the pointer address.
const POINTER_BITS: u64 = 48;

/// A mask to remove the upper free bits of a tagged pointer
const TAG_MASK: u64 = u64::MAX >> TAG_BITS;

// /// The maximum allowed value of a tag.
// pub const MAX_TAG: u16 = u16::MAX;

// /// The maximum allowed value of a pointer address.
// pub const MAX_POINTER: u64 = u64::MAX >> TAG_BITS;

/// The tagged pointer, the upper bits are used to store arbitrary data.
#[derive(Debug)]
pub struct TaggedPointer(u64);

impl TaggedPointer {
    #[inline(always)]
    pub fn new(ptr: *mut i8, tag: u16) -> TaggedPointer {
        let tagged = TaggedPointer::store_tag(ptr, tag);
        TaggedPointer(tagged)
    }

    #[inline(always)]
    pub fn from_u64(tagged: u64) -> TaggedPointer {
        TaggedPointer(tagged)
    }

    #[inline(always)]
    pub fn from_usize(tagged: usize) -> TaggedPointer {
        debug_assert!(size_of::<usize>() == size_of::<u64>());
        TaggedPointer(tagged as u64)
    }

    #[inline(always)]
    pub fn as_u64(&self) -> u64 {
        self.0
    }

    #[inline(always)]
    fn store_tag(ptr: *mut i8, tag: u16) -> u64 {
        (ptr as u64) | ((tag as u64) << POINTER_BITS)
    }

    #[inline(always)]
    pub fn get_tag(&self) -> u16 {
        (self.0 >> POINTER_BITS) as u16
    }

    // Do we need to use:
    //
    // uintptr_t ptr2 = (((uintptr_t)tagged & ((1ull << 48) - 1)) |
    //                   ~(((uintptr_t)tagged & (1ull << 47)) - 1))
    #[inline(always)]
    pub fn untag(&self) -> *mut i8 {
        (self.0 & TAG_MASK) as *mut i8
    }
}

impl fmt::Binary for TaggedPointer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let val = self.0;
        fmt::Binary::fmt(&val, f) // delegate to u64's implementation
    }
}

#[test]
fn test_pointer_tagging() {
    let mut data: u16 = 65535;
    let ptr = unsafe { libc::malloc(1024) as *mut i8 };
    let mut tagged_number = TaggedPointer::new(ptr, data).as_u64();
    let mut tagged = TaggedPointer::from_u64(tagged_number);
    assert!(tagged.untag() == ptr);
    assert!(tagged.get_tag() == data);

    data = 0;
    tagged_number = TaggedPointer::new(ptr, data).as_u64();
    tagged = TaggedPointer::from_u64(tagged_number);
    assert!(tagged.untag() == ptr);
    assert!(tagged.get_tag() == data);
}
