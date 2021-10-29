#![allow(non_camel_case_types)]

use libc;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Translating Gibbon's types to Rust
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

pub type C_GibPackedTag = libc::c_uchar;
pub type C_GibBoxedTag = libc::c_uchar;
pub type C_GibInt = libc::c_longlong;
pub type C_GibFloat = libc::c_float;
pub type C_GibSym = libc::c_ulonglong;
pub type C_GibBool = bool;
pub type C_GibPtr = *const libc::c_char;
pub type C_GibCursor = *const libc::c_char;

#[repr(C)]
pub struct C_GibCursorsPair {
    pub start: C_GibCursor,
    pub end: C_GibCursor,
}
