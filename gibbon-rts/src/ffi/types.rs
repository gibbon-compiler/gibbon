#![allow(non_camel_case_types)]

use libc;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Translating Gibbon's types to Rust
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

pub type C_GibPackedTag = u8;
pub type C_GibBoxedTag = u8;
pub type C_GibInt = i64;
pub type C_GibFloat = f32;
pub type C_GibSym = u64;
pub type C_GibBool = bool;
pub type C_GibPtr = *const i8;
pub type C_GibCursor = *const i8;

#[repr(C)]
pub struct C_GibCursorsPair {
    pub start: C_GibCursor,
    pub end: C_GibCursor,
}
