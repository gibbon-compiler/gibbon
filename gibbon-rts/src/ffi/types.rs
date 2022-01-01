#![allow(non_camel_case_types)]

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Translating Gibbon's types to Rust
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// These typedefs must match their counterparts in C:
// gibbon-compiler/cbits/gibbon.h.

pub type C_GibPackedTag = u8;
pub type C_GibBoxedTag = u8;
pub type C_GibInt = i64;
pub type C_GibFloat = f32;
pub type C_GibSym = u64;
pub type C_GibBool = bool;
pub type C_GibPtr = *const i8;
pub type C_GibCursor = *const i8;

/// An enum in C, which is 4 bytes.
pub type C_GibDatatype = u32;
