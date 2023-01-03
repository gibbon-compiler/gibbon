//! Generate heaps for testing the garbage collector.

use gibbon_rts_ng::*;
use std::vec::*;

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

#[derive(Debug)]
pub enum Object {
    K0(),
    // Constructors with scalar fields.
    KS1(GibInt),
    KS2(GibChar, GibBool),
    KS3(GibChar, GibBool, GibFloat),
    KS4(GibChar, GibBool, GibBool, GibInt),
    // Constructor with packed fields.
    KP(Vec<TDatatype>),
    // Constructor with both scalar and packed fields.
    KSP2(GibInt, Box<TDatatype>),
    KSP3(GibBool, Box<TDatatype>, Box<TDatatype>),
    KSP4(GibTaggedPtr, GibInt, Box<TDatatype>, Box<TDatatype>),
    KSP5(GibChar, GibBool, GibFloat, Box<TDatatype>, Box<TDatatype>),
    KSP6(GibChar, GibBool, GibFloat, GibInt, Box<TDatatype>, Box<TDatatype>),
    // Indicates that this object should be allocated in a fresh region.
    FreshReg(Box<TDatatype>),
}
