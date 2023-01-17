//! Generate heaps for testing the garbage collector.

use core::mem::size_of;
use std::vec::*;

use gibbon_rts_sys::tagged_pointer::*;
use gibbon_rts_sys::*;

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/*

pub type Name = String;

/// Data constructor.
pub struct DCon {
    con_name: String,
    tag: GibPackedTag,
    num_shortcut: usize,
    field_tys: Vec<Ty>,
}

/// Data definition.
pub struct DDef {
    ty_name: Name,
    contrs: Vec<DCon>,
}

/// Types.
pub enum Ty {
    CharTy,
    BoolTy,
    IntTy,
    FloatTy,
    ProdTy(Vec<Ty>),
    VectorTy(Box<Ty>),
    ListTy(Box<Ty>),
    PackedTy(Box<Ty>),
}

/// Gibbon region.
pub type Region = String;

/// A Value enum that can represent any Gibbon value.
pub enum Value {
    CursorV(GibCursor),
    CharV(GibChar),
    BoolV(GibBool),
    IntV(GibInt),
    FloatV(GibFloat),
    ProdV(Vec<Value>),
    VectorV(Vec<Value>),
    ListV(Vec<Value>),
    BoxedV(Box<Value>),
    // Packed.
    ShortcutV(GibTaggedPtr),
    IndirV(GibTaggedPtr),
    PackedV(Region, GibPackedTag, Vec<Value>),
}

*/

/// A Object enum that can represent a few different Gibbon objects.
#[derive(Debug, PartialEq)]
enum Object {
    K0,
    // Constructors with scalar fields.
    KS1(GibInt),
    KS2(GibChar, GibBool),
    KS3(GibChar, GibBool, GibFloat),
    KS4(GibChar, GibBool, GibBool, GibInt),
    // Constructor with packed fields.
    KP(Vec<Object>),
    // Constructor with both scalar and packed fields.
    KSP2(GibInt, Box<Object>),
    KSP3(GibBool, Box<Object>, Box<Object>),
    KSP4(GibTaggedPtr, GibInt, Box<Object>, Box<Object>),
    KSP5(GibChar, GibBool, GibFloat, Box<Object>, Box<Object>),
    KSP6(GibChar, GibBool, GibFloat, GibInt, Box<Object>, Box<Object>),

    // Meta, control constructors
    // ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

    // Indicates that this object should be allocated in a fresh region.
    FreshNurseryReg(usize, Box<Object>),
    FreshOldgenReg(usize, Box<Object>),
    // Used to indicate cauterization.
    Incomplete,
}

impl Object {
    fn sans_metadata(&self) -> Object {
        match self {
            Object::K0 => Object::K0,
            Object::KSP2(i, obj) => {
                Object::KSP2(*i, Box::new((*obj).sans_metadata()))
            }
            Object::FreshNurseryReg(_, obj) => (*obj).sans_metadata(),
            Object::FreshOldgenReg(_, obj) => (*obj).sans_metadata(),
            _ => todo!(),
        }
    }
}

#[repr(u8)]
#[derive(Debug, PartialEq, Eq)]
enum ObjectTag {
    K0 = 0,
    KS1 = 1,
    KS2 = 2,
    KS3 = 3,
    KS4 = 4,
    KP = 5,
    KSP2 = 6,
    KSP3 = 7,
    KSP4 = 8,
    KSP5 = 9,
    KSP6 = 10,
    Indir = INDIRECTION_TAG,
    Redir = REDIRECTION_TAG,
}

/// Key into the info table.
const OBJECT_T: GibDatatype = 7;

fn get_info(
    tag: &ObjectTag,
) -> (
    usize,            // scalar bytes
    usize,            // num shortcut
    u8,               // num scalars
    u8,               // num packed
    Vec<GibDatatype>, // field tys
    u8,               // field tys length
) {
    match tag {
        ObjectTag::K0 => (0, 0, 0, 0, Vec::new(), 0),
        ObjectTag::KS1 => {
            let size = size_of::<GibInt>();
            (size, 0, 1, 0, Vec::new(), 0)
        }
        ObjectTag::KS2 => {
            let size = size_of::<GibChar>() + size_of::<GibBool>();
            (size, 0, 2, 0, Vec::new(), 0)
        }
        ObjectTag::KS3 => {
            let size = size_of::<GibChar>()
                + size_of::<GibBool>()
                + size_of::<GibFloat>();
            (size, 0, 3, 0, Vec::new(), 0)
        }
        ObjectTag::KS4 => {
            let size = size_of::<GibChar>()
                + size_of::<GibBool>()
                + size_of::<GibBool>()
                + size_of::<GibInt>();
            (size, 0, 4, 0, Vec::new(), 0)
        }
        ObjectTag::KP => {
            todo!()
        }
        ObjectTag::KSP2 => {
            let size = size_of::<GibInt>();
            let field_tys = vec![OBJECT_T];
            let len = field_tys.len() as u8;
            (size, 0, 1, len, field_tys, len)
        }
        ObjectTag::KSP3 => {
            let size = size_of::<GibBool>();
            let field_tys = vec![OBJECT_T, OBJECT_T];
            let len = field_tys.len() as u8;
            (size, 0, 1, len, field_tys, len)
        }
        ObjectTag::KSP4 => {
            let size = size_of::<GibTaggedPtr>() + size_of::<GibInt>();
            let field_tys = vec![OBJECT_T, OBJECT_T];
            let len = field_tys.len() as u8;
            (size, 1, 1, len, field_tys, len)
        }
        ObjectTag::KSP5 => {
            let size = size_of::<GibChar>()
                + size_of::<GibBool>()
                + size_of::<GibFloat>();
            let field_tys = vec![OBJECT_T, OBJECT_T];
            let len = field_tys.len() as u8;
            (size, 0, 3, len, field_tys, len)
        }
        ObjectTag::KSP6 => {
            let size = size_of::<GibChar>()
                + size_of::<GibBool>()
                + size_of::<GibFloat>()
                + size_of::<GibInt>();
            let field_tys = vec![OBJECT_T, OBJECT_T];
            let len = field_tys.len() as u8;
            (size, 0, 3, len, field_tys, len)
        }
        ObjectTag::Indir => {
            panic!("INDIRECTION_TAG shouldn't be in the info table")
        }
        ObjectTag::Redir => {
            panic!("REDIRECTION_TAG shouldn't be in the info table")
        }
    }
}

fn info_table_initialize() {
    let tags = vec![
        ObjectTag::K0,
        ObjectTag::KS1,
        ObjectTag::KS2,
        ObjectTag::KS3,
        ObjectTag::KS4,
        // ObjectTag::KP,
        ObjectTag::KSP2,
        ObjectTag::KSP3,
        ObjectTag::KSP4,
        ObjectTag::KSP5,
        ObjectTag::KSP6,
    ];
    // 7 built-in types + the OBJECT_T packed type.
    gib_info_table_initialize(8);
    // Initialize info table for rest of the types.
    for tag in tags {
        let (sb, nshct, ns, np, ft, ftl) = get_info(&tag);
        gib_info_table_insert_packed_dcon(
            OBJECT_T,
            tag as u8,
            sb,
            nshct,
            ns,
            np,
            (*ft).as_ptr(),
            ftl,
        );
    }
    gib_info_table_finalize();
}

enum SerAction<'a> {
    ProcessObj(&'a Object),
    RestoreDst(*mut i8, *mut i8),
}

fn serialize(obj0: &Object, orig_dst: *mut i8, orig_dst_end: &mut *mut i8) {
    let mut worklist: Vec<SerAction> = Vec::new();
    worklist.push(SerAction::ProcessObj(obj0));

    let mut dst = orig_dst;
    let mut dst_end = *orig_dst_end;

    while !worklist.is_empty() {
        if let Some(act) = worklist.pop() {
            match act {
                SerAction::RestoreDst(new_dst, new_dst_end) => {
                    dst = new_dst;
                    dst_end = new_dst_end;
                }
                SerAction::ProcessObj(obj1) => match obj1 {
                    Object::FreshNurseryReg(size, obj) => {
                        bounds_check(&mut dst, &mut dst_end, 32);
                        let chunk = unsafe { gib_alloc_region(*size) };
                        unsafe {
                            gib_indirection_barrier_noinline(
                                dst,
                                dst_end,
                                chunk.start,
                                chunk.end,
                                OBJECT_T,
                            );
                        }
                        worklist.push(SerAction::RestoreDst(dst, dst_end));
                        dst = chunk.start;
                        dst_end = chunk.end;
                        worklist.push(SerAction::ProcessObj(obj));
                    }
                    Object::FreshOldgenReg(size, obj) => {
                        assert!(!dst.is_null() && !dst_end.is_null());
                        bounds_check(&mut dst, &mut dst_end, 32);
                        let chunk = unsafe { gib_alloc_region_on_heap(*size) };
                        unsafe {
                            gib_indirection_barrier_noinline(
                                dst,
                                dst_end,
                                chunk.start,
                                chunk.end,
                                OBJECT_T,
                            );
                        }
                        worklist.push(SerAction::RestoreDst(dst, dst_end));
                        dst = chunk.start;
                        dst_end = chunk.end;
                        worklist.push(SerAction::ProcessObj(obj));
                    }
                    Object::K0 => {
                        assert!(!dst.is_null() && !dst_end.is_null());
                        bounds_check(&mut dst, &mut dst_end, 32);
                        let dst_after_tag = write(dst, ObjectTag::K0);
                        dst = dst_after_tag;
                    }
                    Object::KSP2(i, obj) => {
                        assert!(!dst.is_null() && !dst_end.is_null());
                        bounds_check(&mut dst, &mut dst_end, 32);
                        let dst_after_tag = write(dst, ObjectTag::KSP2);
                        let dst_after_int = write(dst_after_tag, *i);
                        dst = dst_after_int;
                        worklist.push(SerAction::ProcessObj(obj));
                    }
                    _ => todo!(),
                },
            }
        } else {
            panic!("empty worklist")
        }
    }

    // Update orig_dst_end to point to the end of value.
    *orig_dst_end = dst_end;
}

fn deserialize(src: *const i8) -> Object {
    let (x, _) = deserialize_(src);
    x
}

fn deserialize_(src: *const i8) -> (Object, *const i8) {
    let (tag, src_after_tag) = read(src);
    match tag {
        ObjectTag::K0 => (Object::K0, src_after_tag),
        ObjectTag::KSP2 => {
            let (i, src_after_int): (i64, *const i8) = read(src_after_tag);
            let (field1, src_after_field1) = deserialize_(src_after_int);
            (Object::KSP2(i, Box::new(field1)), src_after_field1)
        }
        ObjectTag::Indir => {
            let (tagged_pointee, src_after_indr): (GibTaggedPtr, _) =
                read(src_after_tag);
            let tagged = TaggedPointer::from_usize(tagged_pointee);
            let pointee = tagged.untag();
            let (field, _) = deserialize_(pointee);
            (field, src_after_indr)
        }
        ObjectTag::Redir => {
            let (tagged_pointee, _): (GibTaggedPtr, _) = read(src_after_tag);
            let tagged = TaggedPointer::from_usize(tagged_pointee);
            let pointee = tagged.untag();
            deserialize_(pointee)
        }
        _ => {
            println!("deserialize got {:?}", tag as u8);
            panic!("error")
        }
    }
}

fn print_packed(src: *const i8) {
    print_packed_(src);
    println!("");
}

fn print_packed_(src: *const i8) -> *const i8 {
    let (tag, src_after_tag) = read(src);
    match tag {
        ObjectTag::K0 => {
            print!("{:p}:(K0) ", src);
            src_after_tag
        }
        ObjectTag::KSP2 => {
            print!("{:p}:(KSP2 ", src);
            let (i, src_after_int): (i64, *const i8) = read(src_after_tag);
            print!("{} ", i);
            let src_after_field1 = print_packed_(src_after_int);
            print!(")");
            src_after_field1
        }
        ObjectTag::Indir => {
            let (tagged_pointee, src_after_indr): (GibTaggedPtr, _) =
                read(src_after_tag);
            let tagged = TaggedPointer::from_usize(tagged_pointee);
            let pointee = tagged.untag();
            print!("{:p}:(->i ", src);
            print_packed_(pointee);
            print!(")");
            src_after_indr
        }
        ObjectTag::Redir => {
            let (tagged_pointee, _): (GibTaggedPtr, _) = read(src_after_tag);
            let tagged = TaggedPointer::from_usize(tagged_pointee);
            let pointee = tagged.untag();
            print!("{:p}:(->r ", src);
            let src_after_redir_data = print_packed_(pointee);
            print!(")");
            src_after_redir_data
        }
        _ => {
            println!("print_packed got {:?}", tag as u8);
            panic!("error")
        }
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/// Test GC on a simple reverse-like heap.
pub fn test_reverse1(n: u8) -> bool {
    // Initialize info-table.
    info_table_initialize();

    // Create an object to GC.
    let ls = mkrevlist(n);
    // println!("{:?}", ls);

    // Put the object on the Gibbon heap.
    let chunk0 = unsafe { gib_alloc_region(128) };
    let dst = chunk0.start;
    let mut dst_end = chunk0.end;
    serialize(&ls, dst, &mut dst_end);
    // print_packed(dst);

    // Trigger GC.
    ss_push(RW::Read, dst, dst_end, OBJECT_T);
    unsafe {
        gib_perform_GC(false);
    }

    // Reconstruct packed value after GC.
    let ls2 = unsafe {
        let stk = gib_global_read_shadowstacks as *const GibShadowstack;
        let frame = (*stk).start as *const GibShadowstackFrame;
        // print_packed((*frame).ptr);
        deserialize((*frame).ptr)
    };

    // Clear info-table.
    gib_info_table_clear();

    // Return result.
    // assert!(ls2 == ls.sans_metadata());
    ls2 == ls.sans_metadata()
}

/// Returns a list: Cons n ->i Cons (n-1)  ... ->i Cons 1 -> Nil.
fn mkrevlist(n: u8) -> Object {
    if n == 0 {
        Object::K0
    } else {
        let next = mkrevlist(n - 1);
        Object::KSP2(
            n as i64,
            Box::new(Object::FreshNurseryReg(128, Box::new(next))),
        )
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/// Test GC on a split root---one which starts in the nursery and
/// ends in oldgen due to eager promotion.
pub fn test_split_root(n: u8) -> bool {
    // Initialize info-table.
    info_table_initialize();

    // Make nursery smaller.
    let old_size = unsafe { gib_nursery_realloc(gib_global_nurseries, 128) };

    // Create an object to GC.
    let mut ls = mkrevlist(n);
    ls = ls.sans_metadata();
    // println!("{:?}", ls);

    // Put the object on the Gibbon heap.
    let chunk0 = unsafe { gib_alloc_region(64) };
    let dst = chunk0.start;
    let mut dst_end = chunk0.end;
    serialize(&ls, dst, &mut dst_end);
    // print_packed(dst);

    // Trigger GC.
    ss_push(RW::Read, dst, dst_end, OBJECT_T);
    unsafe {
        gib_perform_GC(false);
    }

    // Clear info-table.
    gib_info_table_clear();

    // Restore nursery.
    unsafe {
        gib_nursery_realloc(gib_global_nurseries, old_size);
    }

    // Return result.
    true
}
