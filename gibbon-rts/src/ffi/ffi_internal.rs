//

use std::collections::HashMap;
use std::slice;

use crate::ffi::types::*;
use crate::mem;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

#[no_mangle]
/// The user is responsible for initializing the info table before
/// calling the get/set methods on it.
pub extern "C" fn gib_init_info_table() -> i32 {
    match mem::init_info_table() {
        None => -1,
        Some(()) => 0,
    }
}

#[no_mangle]
pub extern "C" fn gib_insert_dcon_into_info_table(
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
    match mem::insert_dcon_into_info_table(
        datatype,
        datacon,
        scalar_bytes,
        num_scalars,
        num_packed,
        field_tys,
    ) {
        Some(()) => 0,
        None => -1,
    }
}

#[no_mangle]
pub extern "C" fn gib_collect() -> i32 {
    match mem::collect() {
        Some(()) => 0,
        None => -1,
    }
}
