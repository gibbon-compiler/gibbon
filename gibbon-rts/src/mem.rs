/*!

Memory Management; regions, chunks, GC etc.

 */

use std::collections::HashMap;
use std::lazy::{Lazy, OnceCell};

use crate::ffi::types as ffi;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Info table
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#[derive(Debug)]
struct DataconInfo {
    num_scalars: u8,
    num_packed: u8,
    field_tys: Vec<ffi::C_GibDatatype>,
}

type DatatypeInfo = HashMap<ffi::C_GibPackedTag, DataconInfo>;

/// The global info table.
static mut INFO_TABLE: OnceCell<HashMap<ffi::C_GibDatatype, DatatypeInfo>> =
    OnceCell::new();

pub fn init_info_table() -> Option<()> {
    unsafe {
        match INFO_TABLE.set(HashMap::new()) {
            Ok(()) => Some(()),
            Err(_) => None,
        }
    }
}

pub fn insert_dcon_into_info_table(
    datatype: ffi::C_GibDatatype,
    datacon: ffi::C_GibPackedTag,
    num_scalars: u8,
    num_packed: u8,
    field_tys: Vec<ffi::C_GibDatatype>,
) -> Option<()> {
    unsafe {
        let tbl = match INFO_TABLE.get_mut() {
            None => return None,
            Some(tbl) => tbl,
        };
        let datatype_info = tbl.entry(datatype).or_default();
        if (datatype_info.contains_key(&datacon)) {
            return None;
        }
        datatype_info.insert(
            datacon,
            DataconInfo { num_scalars, num_packed, field_tys },
        );
        if cfg!(debug_assertions) {
            println!("{:?}", tbl);
        }
        Some(())
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * GC
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

extern "C" {
    // Nursery.
    static mut gib_global_nursery_from_space_start: *const u8;
    static mut gib_global_nursery_to_space_start: *const u8;
    static mut gib_global_nursery_to_space_end: *const u8;
    static mut gib_global_nursery_alloc_ptr: *const u8;
    static mut gib_global_nursery_alloc_ptr_end: *const u8;

    // Shadow stack for input locations.
    static mut gib_global_input_shadowstack_start: *const u8;
    static mut gib_global_input_shadowstack_end: *const u8;
    static mut gib_global_input_shadowstack_curr: *const u8;

    // Shadow stack for output locations.
    static mut gib_global_output_shadowstack_start: *const u8;
    static mut gib_global_output_shadowstack_end: *const u8;
    static mut gib_global_output_shadowstack_curr: *const u8;
}

pub fn collect() -> Option<()> {
    println!("Trigger GC!!!");
    return None;
}
