//! Rust bindings for Gibbon RTS.

pub use gibbon_rts_ng::*;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * This module just re-exports the FFI as is. In future we could expose safe
 * versions, e.g. functions that use references instead of raw pointers.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

pub enum RW {
    Read,
    Write,
}

pub fn ss_push(rw: RW, ptr: *const i8, endptr: *const i8, ty: GibDatatype) {
    unsafe {
        let sstk = match rw {
            RW::Read => gib_global_read_shadowstacks,
            RW::Write => gib_global_write_shadowstacks,
        };
        gib_shadowstack_push_noinline(
            sstk,
            ptr,
            endptr,
            GibGcRootProv::Stk,
            ty,
        );
    }
}

pub fn ss_pop(rw: RW) -> *const GibShadowstackFrame {
    unsafe {
        let sstk = match rw {
            RW::Read => gib_global_read_shadowstacks,
            RW::Write => gib_global_write_shadowstacks,
        };
        gib_shadowstack_pop_noinline(sstk)
    }
}

#[inline(always)]
pub fn bounds_check(ptr: &mut *mut i8, endptr: &mut *mut i8, req: isize) {
    unsafe {
        if (*endptr).offset_from(*ptr) < req {
            gib_grow_region(ptr, endptr);
        }
    }
}

#[inline(always)]
pub fn read<A>(cursor: *const i8) -> (A, *const i8) {
    unsafe {
        let cursor2 = cursor as *const A;
        (cursor2.read_unaligned(), cursor2.add(1) as *const i8)
    }
}

#[inline(always)]
pub fn read_mut<A>(cursor: *mut i8) -> (A, *mut i8) {
    unsafe {
        let cursor2 = cursor as *const A;
        (cursor2.read_unaligned(), cursor2.add(1) as *mut i8)
    }
}

#[inline(always)]
pub fn write<A>(cursor: *mut i8, val: A) -> *mut i8 {
    unsafe {
        let cursor2 = cursor as *mut A;
        cursor2.write_unaligned(val);
        cursor2.add(1) as *mut i8
    }
}
