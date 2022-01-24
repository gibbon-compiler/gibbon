/*!

The foreign function interface which exposes this RTS to C.
See gibbon-compiler/cbits/gibbon.h.

 */

use std::slice;

use crate::ffi::types::*;
use crate::gc;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Translating Gibbon's types to Rust
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

pub mod types {
    #![allow(non_camel_case_types)]

    // These typedefs must match their counterparts in C.
    // See gibbon-compiler/cbits/gibbon.h.

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

    /// An enum in C, which is 4 bytes.
    pub type C_GibCursorBindType = u32;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * FFI functions
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#[no_mangle]
/// The user is responsible for initializing the info table before
/// calling the get/set methods on it.
pub extern "C" fn gib_info_table_initialize() -> i32 {
    match gc::info_table_initialize() {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn gib_info_table_insert_packed_dcon(
    datatype: C_GibDatatype,
    datacon: C_GibPackedTag,
    scalar_bytes: u8,
    num_scalars: u8,
    num_packed: u8,
    c_field_tys: *const C_GibDatatype,
    c_field_tys_length: u8,
) -> i32 {
    let field_tys: Vec<C_GibDatatype> = unsafe {
        slice::from_raw_parts(c_field_tys, c_field_tys_length as usize)
            .to_vec()
    };
    match gc::info_table_insert_packed_dcon(
        datatype,
        datacon,
        scalar_bytes,
        num_scalars,
        num_packed,
        field_tys,
    ) {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn gib_info_table_insert_scalar(
    datatype: C_GibDatatype,
    size: u8,
) -> i32 {
    match gc::info_table_insert_scalar(datatype, size) {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}

#[no_mangle]
pub extern "C" fn gib_collect_minor() -> i32 {
    match gc::collect_minor() {
        Ok(()) => 0,
        Err(err) => {
            if cfg!(debug_assertions) {
                println!("{:?}", err);
            }
            -1
        }
    }
}
