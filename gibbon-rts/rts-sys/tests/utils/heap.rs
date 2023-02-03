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
    // Initial chunk: the serializer doesn't write indirections to objects
    // in these chunks.
    InitNurseryReg(usize, Box<Object>),
    InitOldgenReg(usize, Box<Object>),
    // Used to indicate cauterization.
    Incomplete,
}

impl Object {
    fn sans_metadata(&self) -> Object {
        match self {
            Object::K0 => Object::K0,
            Object::KSP2(i, obj) => Object::KSP2(*i, Box::new((*obj).sans_metadata())),
            Object::FreshNurseryReg(_, obj) => (*obj).sans_metadata(),
            Object::FreshOldgenReg(_, obj) => (*obj).sans_metadata(),
            Object::InitNurseryReg(_, obj) => (*obj).sans_metadata(),
            Object::InitOldgenReg(_, obj) => (*obj).sans_metadata(),
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

impl ObjectTag {
    fn get_info(
        &self,
    ) -> (
        usize,            // scalar bytes
        usize,            // num shortcut
        u8,               // num scalars
        u8,               // num packed
        Vec<GibDatatype>, // field tys
        u8,               // field tys length
    ) {
        match self {
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
                let size = size_of::<GibChar>() + size_of::<GibBool>() + size_of::<GibFloat>();
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
                let size = size_of::<GibChar>() + size_of::<GibBool>() + size_of::<GibFloat>();
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
        let (sb, nshct, ns, np, ft, ftl) = tag.get_info();
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

fn serialize(obj_0: &Object) -> (*const i8, *const i8) {
    let mut worklist: Vec<SerAction> = Vec::new();
    let (orig_dst, mut dst, mut dst_end) = match obj_0 {
        Object::InitNurseryReg(size, obj) => {
            let chunk0 = unsafe { gib_alloc_region(*size) };
            worklist.push(SerAction::ProcessObj(obj));
            (chunk0.start, chunk0.start, chunk0.end)
        }
        Object::InitOldgenReg(size, obj) => {
            let chunk0 = unsafe { gib_alloc_region_on_heap(*size) };
            worklist.push(SerAction::ProcessObj(obj));
            (chunk0.start, chunk0.start, chunk0.end)
        }
        _ => {
            let chunk0 = unsafe { gib_alloc_region(1024) };
            worklist.push(SerAction::ProcessObj(obj_0));
            (chunk0.start, chunk0.start, chunk0.end)
        }
    };

    while !worklist.is_empty() {
        let Some(act) = worklist.pop() else { panic!("empty worklist") };
        match act {
            SerAction::RestoreDst(new_dst, new_dst_end) => {
                dst = new_dst;
                dst_end = new_dst_end;
            }
            SerAction::ProcessObj(obj_1) => match obj_1 {
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
                        dst = dst.add(9);
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
                        dst = dst.add(9);
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
                Object::KSP3(b, obj1, obj2) => {
                    assert!(!dst.is_null() && !dst_end.is_null());
                    bounds_check(&mut dst, &mut dst_end, 32);
                    let dst_after_tag = write(dst, ObjectTag::KSP3);
                    let dst_after_bool = write(dst_after_tag, *b);
                    dst = dst_after_bool;
                    worklist.push(SerAction::ProcessObj(obj2));
                    worklist.push(SerAction::ProcessObj(obj1));
                }
                _ => todo!(),
            },
        }
    }

    (orig_dst, dst_end)
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
            let (i, src_after_int): (GibInt, _) = read(src_after_tag);
            let (field1, src_after_field1) = deserialize_(src_after_int);
            (Object::KSP2(i, Box::new(field1)), src_after_field1)
        }
        ObjectTag::KSP3 => {
            let (b, src_after_bool): (GibBool, _) = read(src_after_tag);
            let (field1, src_after_field1) = deserialize_(src_after_bool);
            let (field2, src_after_field2) = deserialize_(src_after_field1);
            (Object::KSP3(b, Box::new(field1), Box::new(field2)), src_after_field2)
        }
        ObjectTag::Indir => {
            let (tagged_pointee, src_after_indr): (GibTaggedPtr, _) = read(src_after_tag);
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
            let (i, src_after_int): (GibInt, _) = read(src_after_tag);
            print!("{} ", i);
            let src_after_field1 = print_packed_(src_after_int);
            print!(")");
            src_after_field1
        }
        ObjectTag::KSP3 => {
            print!("{:p}:(KSP3 ", src);
            let (b, src_after_bool): (GibBool, _) = read(src_after_tag);
            print!("{} ", b);
            let src_after_field1 = print_packed_(src_after_bool);
            print!(" ");
            let src_after_field2 = print_packed_(src_after_field1);
            print!(")");
            src_after_field2
        }
        ObjectTag::Indir => {
            let (tagged_pointee, src_after_indr): (GibTaggedPtr, _) = read(src_after_tag);
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

    // Create an object to evacuate.
    let ls = Object::InitNurseryReg(128, Box::new(mkrevlist(n)));
    // println!("{:?}", ls);

    // Put the object on the Gibbon heap.
    let (start, end) = serialize(&ls);
    // print_packed(start);

    // Trigger GC.
    ss_push(RW::Read, start, end, OBJECT_T);
    unsafe {
        gib_perform_GC(false);
    }

    // Reconstruct packed value after GC.
    let frame = ss_peek(RW::Read);
    // print_packed((*frame).ptr);
    let ls2 = unsafe { deserialize((*frame).ptr) };

    // Clear info-table.
    gib_info_table_clear();

    // Return result.
    ls2 == ls.sans_metadata()
}

/// Returns a list: Cons n ->i Cons (n-1)  ... ->i Cons 1 ->i Nil.
fn mkrevlist(n: u8) -> Object {
    if n == 0 {
        Object::K0
    } else {
        let next = mkrevlist(n - 1);
        Object::KSP2(n as i64, Box::new(Object::FreshNurseryReg(128, Box::new(next))))
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/// Test GC on a split root---one which starts in the nursery and
/// ends in oldgen due to eager promotion.
pub fn test_split_root() -> bool {
    // Initialize info-table.
    info_table_initialize();

    // Create an object to evacuate. It is big enough to trigger
    // eager promotion in a region of size 64.
    let ls = Object::InitNurseryReg(64, Box::new(mklist(4)));
    // println!("{:?}", ls);

    // Put the object on the Gibbon heap.
    let (start, end) = serialize(&ls);
    // print_packed(start);

    // Trigger GC.
    ss_push(RW::Read, start, end, OBJECT_T);
    unsafe {
        gib_perform_GC(false);
    }

    // Reconstruct packed value after GC.
    let frame = ss_peek(RW::Read);
    // print_packed((*frame).ptr);
    let ls2 = unsafe { deserialize((*frame).ptr) };

    // Clear info-table.
    gib_info_table_clear();

    // Always return true for now, GC triggers exception.
    ls2 == ls
}

/// Returns a list: Cons n Cons (n-1) Cons 1 Nil.
fn mklist(n: u8) -> Object {
    if n == 0 {
        Object::K0
    } else {
        Object::KSP2(n as i64, Box::new(mklist(n - 1)))
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ */

/// Usual redirection pointers are copied as is since they point to oldgen
/// data due to eager promotion. However, any redirections encountered while
/// inlining objects pointed to by indirections should not be copied as is.
/// Copying them directly breaks the invariant that redirections should
/// always be the last thing in a chunk.
pub fn test_redirections_in_inlined_data() -> bool {
    // Initialize info-table.
    info_table_initialize();

    // Create objects to evacuate.
    // The first packed field of 'ls' lives in its own region and is is big
    // enough to trigger eager promotion, and thus will have a redirection.
    // This redirection should not be copied directly!
    let ls = Object::KSP3(
        // A scalar field.
        true,
        // This will turn into an indirection pointer due to FreshNurseryReg.
        Box::new(Object::FreshNurseryReg(64, Box::new(mklist(4)))),
        // A packed field that will be inaccessible if a redirection pointer
        // in the previous field is inlined.
        Box::new(Object::K0),
    );
    // println!("{:?}", ls);

    // Put the object on the Gibbon heap.
    let (start, end) = serialize(&ls);
    // print_packed(start);

    // Trigger GC.
    ss_push(RW::Read, start, end, OBJECT_T);
    let nursery: &mut GibNursery = unsafe { &mut *gib_global_nurseries };
    let stats = ValueStats::from_frame(ss_peek(RW::Read), nursery);
    // println!("stats: {:?}", stats);
    assert_eq!(stats.num_indirections, 1);
    assert_eq!(stats.num_redirections, 1);
    unsafe {
        gib_perform_GC(false);
    }

    // Reconstruct packed value after GC.
    let frame = ss_peek(RW::Read);
    // print_packed((*frame).ptr);
    let ls2 = unsafe { deserialize((*frame).ptr) };
    let stats2 = ValueStats::from_frame(frame, nursery);
    // println!("stats2: {:?}", stats2);

    // Clear info-table.
    gib_info_table_clear();

    // Check that the redirection is not copied as is.
    stats2.num_redirections == 0
}
