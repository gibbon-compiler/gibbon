/*!

The foreign function interface which exposes this RTS to C.

See gibbon-compiler/cbits/gibbon.h.

 */

mod ffi_internal;
pub use ffi_internal::*;

pub mod types;
