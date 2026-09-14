#ifndef _GIBBON_H
#define _GIBBON_H

#include <stdio.h>
#include <stdint.h>
#include <inttypes.h>
#include <stdbool.h>
#include <uthash.h>
#include <assert.h>
#include <limits.h>
#include <time.h>
#include <string.h>

#ifdef _GIBBON_PARALLEL
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#endif

#define GIB_PRAGMA(x) _Pragma(#x)

#if defined(__clang__)
#define GIB_PRAGMA_MESSAGE(msg)        \
    GIB_PRAGMA(clang diagnostic push)  \
    GIB_PRAGMA(clang diagnostic ignored "-W#pragma-messages") \
    GIB_PRAGMA(message msg)            \
    GIB_PRAGMA(clang diagnostic pop)
#else
#define GIB_PRAGMA_MESSAGE(msg) GIB_PRAGMA(message msg)
#endif

#if defined(__clang__)
#define GIB_PRAGMA_UNROLL(n) GIB_PRAGMA(unroll n)
#elif defined(__GNUC__) && (__GNUC__ >= 8)
#define GIB_PRAGMA_UNROLL(n) GIB_PRAGMA(GCC unroll n)
#else
#define GIB_PRAGMA_UNROLL(n)
#endif
/*
 * CPP macros used in the RTS:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * _GIBBON_VERBOSITY=int     verbosity level for debug output
 * _GIBBON_DEBUG             enables various assertions if present
 * _GIBBON_GCSTATS           collect and print GC statistics if present
 * _GIBBON_GENGC             only use old reference counted GC set to 0
 * _GIBBON_BOUNDSCHECK       boundscheck vector accesses
 * _GIBBON_BUMPALLOC_LISTS   bump allocated linked lists
 * _GIBBON_BUMPALLOC_HEAP    bump allocated gib_alloc
 * _GIBBON_POINTER           pointer mode gib_alloc
 * _GIBBON_PARALLEL          parallel mode
 * _GIBBON_EAGER_PROMOTION   disable eager promotion if set to 0
 * _GIBBON_SIMPLE_WRITE_BARRIER disable eliminate-indirection-chains optimization
 * _GIBBON_ENABLE_PAPI           enable instrumentation via papi
 *
 */


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Translating Gibbon's types to C
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */



/*
 * The C type that backs the corresponding Gibbon type must have the same
 * size as encoded in 'sizeOfTy' in Gibbon.Language.
 *
 *
 * Current convention regarding typedef usage:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * RTS variables/functions that leak their types into Gibbon (e.g. the Gibbon
 * primitive SizeParam is translated to gib_global_size_param, VSliceP to
 * gib_vector_slice etc.) are defined using a typedef'd type. This allows us to
 * change their C type *without* changing anything in the Gibbon code generator.
 *
 * Other declarations directly use C types:
 * https://www.kernel.org/doc/html/v4.10/process/coding-style.html#typedefs
 *
 */


/*
 * A note on GibInt and the RTS ABI
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * `GibInt` used to mean different things on either side of the RTS/generated-
 * code boundary: the code generator defined `GIBBON_INT32` into the
 * *generated* translation unit under `--int32`, which made `GibInt` mean
 * `int32_t` there, while the separately-built RTS translation unit (which
 * never defined `GIBBON_INT32`) kept `GibInt` as `int64_t`.  That split is
 * gone.
 *
 * `--int32` is gone entirely, and a bare, unannotated source `Int` is `W64`
 * (`Gibbon.HaskellFrontend.desugarType`).  A narrow program type comes from
 * writing `Int8`/`Int16`/`Int32`/`Int64`, and the compiler carries that width
 * through L0-L4 like any other explicit one (`GibInt32`, below).
 * `GibInt` itself no longer changes meaning: it is `int64_t`, unconditionally,
 * on every generated translation unit and in the RTS, matching every other
 * shared struct/prototype that already had to be pinned this way (like
 * `GibVector.lower` / `.upper`).  Generated code no longer defines
 * `GIBBON_INT32` (the code generator only ever emits `GibInt8`/`GibInt16`/
 * `GibInt32`/`GibInt64`/`GibInt` now, chosen from the program's own inferred
 * width -- see `Gibbon.Passes.Codegen.codegenTy`), but this header does not
 * key any type definition on that macro either, so an out-of-tree build that
 * still defines it changes nothing.
 */

typedef uint8_t GibPackedTag;
typedef uint8_t GibBoxedTag;

/* Exact-width signed integers for generated program scalars (Int8/16/32/64).
 * These are the ONLY types Codegen ever emits for an `IntTy w` value; `GibInt`
 * (below) is reserved for compiler/RTS infrastructure -- sizes, counts,
 * offsets, indices -- which stays 64-bit regardless of any source program's
 * declared widths.  All four come straight from <stdint.h>, which this RTS
 * already assumes provides fixed-width types (GibSym/GibPackedTag do too). */
typedef int8_t  GibInt8;
typedef int16_t GibInt16;
typedef int32_t GibInt32;
typedef int64_t GibInt64;

_Static_assert(sizeof(GibInt8)  == 1, "GibInt8 must be exactly 1 byte");
_Static_assert(sizeof(GibInt16) == 2, "GibInt16 must be exactly 2 bytes");
_Static_assert(sizeof(GibInt32) == 4, "GibInt32 must be exactly 4 bytes");
_Static_assert(sizeof(GibInt64) == 8, "GibInt64 must be exactly 8 bytes");

/* Compiler/RTS infrastructure integer: always 64-bit, always `int64_t`.  See
 * the ABI note above -- this used to switch width under `GIBBON_INT32`. */
typedef int64_t GibInt;
_Static_assert(sizeof(GibInt) == 8, "GibInt must be exactly 8 bytes");

/* Explicit integer-width conversion (the source `toInt8`/`toInt16`/`toInt32`/
 * `toInt64` primitives).
 *
 * Semantics: for destination width N, return the unique signed N-bit
 * two's-complement value congruent to the input modulo 2^N.  Truncating, never
 * saturating, never an overflow report.
 *
 * Why these are functions rather than a plain `(GibInt8) x` cast: converting an
 * out-of-range integer to a signed C type is IMPLEMENTATION-DEFINED (C17
 * 6.3.1.3p3) -- a conforming implementation may raise a signal instead of
 * wrapping.  Conversion to an UNSIGNED type is fully defined modulo 2^N, so the
 * reduction is done there and the high half is mapped into the negative range
 * with ordinary in-range arithmetic before any signed conversion happens.
 *
 * Consequently these contain: no signed overflow, no negation of INT64_MIN, no
 * out-of-range signed conversion, no dependence on the host's `char` signedness
 * (they never use bare `char`), and no dependence on byte order (they never
 * reinterpret storage).  The operand is taken as `GibInt64`; generated code
 * widens the exact-width signed source to `GibInt64` first, which is always
 * value-preserving because every source width is narrower or equal.
 *
 * `static inline` in the header: no ABI surface, and both GCC and Clang fold
 * these to the same one or two instructions a bare cast would have produced. */

#define GIB_DEFINE_INT_NARROW(NAME, DSTTY, UDSTTY, NBITS)               \
    static inline DSTTY NAME(GibInt64 x)                                \
    {                                                                   \
        /* Defined modulo 2^64, for every input including INT64_MIN. */ \
        uint64_t u = (uint64_t) x;                                      \
        /* Reduce modulo 2^NBITS; still entirely unsigned, still defined. */ \
        uint64_t m = u & ((((uint64_t) 1) << (NBITS)) - 1);             \
        uint64_t half = ((uint64_t) 1) << ((NBITS) - 1);                \
        if (m < half) {                                                 \
            /* In [0, 2^(N-1)): representable, so this cast is in range. */ \
            return (DSTTY) (UDSTTY) m;                                  \
        } else {                                                        \
            /* In [2^(N-1), 2^N): subtract 2^N in int64_t, which is wide  \
             * enough for every N <= 32, giving a value in                \
             * [-2^(N-1), -1] -- again in range for DSTTY. */            \
            int64_t signed_val = (int64_t) m - (int64_t) (((uint64_t) 1) << (NBITS)); \
            return (DSTTY) signed_val;                                  \
        }                                                               \
    }

GIB_DEFINE_INT_NARROW(gib_int_to_int8,  GibInt8,  uint8_t,   8)
GIB_DEFINE_INT_NARROW(gib_int_to_int16, GibInt16, uint16_t, 16)
GIB_DEFINE_INT_NARROW(gib_int_to_int32, GibInt32, uint32_t, 32)

/* Destination W64: every source width sign-extends into GibInt64 without loss,
 * so there is nothing to reduce.  Kept as a function so all four destinations
 * go through one audited implementation and codegen has no special case. */
static inline GibInt64 gib_int_to_int64(GibInt64 x)
{
    return x;
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Deterministic integer arithmetic
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * `+`, `-`, `*`, `/`, `%` and `^` on a Gibbon Int8/Int16/Int32/Int64, defined
 * so that the answer is the same one the interpreters and the packed SIMD
 * helpers produce -- under GCC and Clang, at -O0, -O2 and -O3.
 *
 * The specification (identical to "Deterministic integer arithmetic" in
 * `Gibbon.Language.Syntax`): for width N, all of `+`, `-`, `*` and `^` are
 * two's-complement modular, i.e. the unique signed N-bit value congruent to
 * the mathematical result modulo 2^N.  `/` truncates toward zero and `%` takes
 * the sign of the dividend, both as C specifies -- except that the two cases C
 * leaves UNDEFINED are pinned here instead: `MIN / -1` is `MIN`, `MIN % -1` is
 * `0`, and a zero divisor is a deterministic diagnostic rather than a trap.
 *
 * Why these are functions and not the bare C operators, which is what codegen
 * used to emit:
 *
 *   - signed overflow in C is UNDEFINED BEHAVIOUR (C17 6.5p5), not wraparound.
 *     `INT32_MAX + 1` is not "-2147483648"; it is a licence for the optimizer
 *     to assume the addition never happens.  The SIMD path, meanwhile, wraps
 *     for real, because that is what the hardware does.  So the scalar and
 *     vector paths of the SAME loop were not specified to agree, and at -O2/-O3
 *     they are free to disagree.
 *   - `INT_MIN / -1` and `INT_MIN % -1` are undefined (C17 6.5.5p6) and on
 *     x86-64 raise SIGFPE, not a wrong answer.
 *   - division by zero is undefined and also traps.
 *
 * How they avoid re-introducing what they are removing:
 *
 *   - every value is reduced in UNSIGNED arithmetic, which C defines as modulo
 *     2^N for every input (C17 6.2.5p9).  No signed operation is ever allowed
 *     to overflow.
 *   - the unsigned result is mapped back to the signed type by
 *     `gib_u2s_i{8,16,32,64}` below, using only in-range arithmetic.  There is
 *     NO out-of-range unsigned-to-signed cast anywhere: that conversion is
 *     IMPLEMENTATION-DEFINED (C17 6.3.1.3p3) and a conforming implementation
 *     may raise a signal instead of wrapping, which is exactly the class of
 *     "works here, breaks there" bug this helper avoids.
 *   - INTEGER PROMOTION is handled by widening to `uint64_t` before operating.
 *     `uint8_t` and `uint16_t` do NOT stay unsigned under the usual arithmetic
 *     conversions: they promote to signed `int` (C17 6.3.1.1p2), so a
 *     "safely unsigned" `(uint8_t)a * (uint8_t)b` is in fact a signed `int`
 *     multiply that can overflow and be undefined.  Widening first makes the
 *     operand type explicit and removes the hazard for all four widths;
 *     truncation back to N bits happens deliberately, at the end, in
 *     `gib_u2s_*`.
 *   - each is a `static inline` function, not a macro, so an argument with a
 *     side effect is evaluated exactly once.
 */

/* The helpers below reduce a value modulo 2^N and interpret the result as
 * signed.  That is only the two's-complement answer if the target actually is
 * two's-complement, so require it rather than assume it.  (C23 makes this
 * mandatory; these assertions make the dependency explicit on older targets.) */
_Static_assert(INT8_MIN  == -INT8_MAX  - 1, "GibInt8 must be two's-complement");
_Static_assert(INT16_MIN == -INT16_MAX - 1, "GibInt16 must be two's-complement");
_Static_assert(INT32_MIN == -INT32_MAX - 1, "GibInt32 must be two's-complement");
_Static_assert(INT64_MIN == -INT64_MAX - 1, "GibInt64 must be two's-complement");
_Static_assert(((uint64_t) -1) == UINT64_MAX, "unsigned conversion must be modular");

/* Unsigned -> signed, for N < 64.  The argument is ALREADY reduced to N bits
 * (it has the unsigned N-bit type), so there is nothing to mask: the top half
 * of the range is simply mapped into the negative range.
 *
 * Both branches produce a value already representable in DSTTY before any
 * signed conversion happens -- there is no out-of-range unsigned-to-signed
 * cast anywhere, which is the conversion C leaves IMPLEMENTATION-DEFINED
 * (C17 6.3.1.3p3).
 *
 * The subtraction is done at 32 bits, not 64.  That is not only about register
 * width: keeping the work at the value's own scale is what lets both compilers
 * recognise the whole thing as a bit reinterpretation and auto-vectorise a
 * narrow loop at its OWN lane width.  An earlier version of these helpers
 * widened everything to uint64_t; GCC then unpacked a plain W8 add loop out to
 * 64-bit lanes and back, costing about 6x. */
#define GIB_DEFINE_U2S(NAME, DSTTY, UDSTTY, NBITS)                      \
    static inline DSTTY NAME(UDSTTY u)                                  \
    {                                                                   \
        if (u < (((UDSTTY) 1) << ((NBITS) - 1))) {                      \
            return (DSTTY) u;                                           \
        } else {                                                        \
            return (DSTTY) ((int32_t) u - (((int32_t) 1) << (NBITS)));  \
        }                                                               \
    }

GIB_DEFINE_U2S(gib_u2s_i8,  GibInt8,  uint8_t,   8)
GIB_DEFINE_U2S(gib_u2s_i16, GibInt16, uint16_t, 16)

/* N == 32 needs its own body: 2^32 does not fit in int32_t, so the top half is
 * mapped down at 64 bits.  The result is in [-2^31, -1], representable in
 * GibInt32. */
static inline GibInt32 gib_u2s_i32(uint32_t u)
{
    if (u <= (uint32_t) INT32_MAX) {
        return (GibInt32) u;
    } else {
        return (GibInt32) ((int64_t) u - (((int64_t) 1) << 32));
    }
}

/* N == 64 needs its own body: `1 << 64` is undefined, so there is no mask to
 * apply and no 2^N to subtract as a shift.  Subtracting 2^63 lands the top half
 * in [0, 2^63-1], which is representable; adding INT64_MIN back is an addition
 * of a negative to a non-negative and so cannot overflow. */
static inline GibInt64 gib_u2s_i64(uint64_t u)
{
    if (u <= (uint64_t) INT64_MAX) {
        return (GibInt64) u;
    } else {
        return (GibInt64) (u - ((uint64_t) INT64_MAX + 1)) + INT64_MIN;
    }
}

/* Add / subtract / multiply / negate / exponentiate, per width.
 *
 * `(UTY) a` on a signed operand is defined for every input, including
 * INT64_MIN, and yields the value modulo 2^N.  Modular arithmetic then stays
 * exact: reduction mod 2^N is a ring homomorphism, so computing in any wider
 * unsigned type and truncating back to UTY leaves the same N low bits.
 *
 * WTY is that wider unsigned working type, and it exists ONLY to defeat
 * INTEGER PROMOTION.  `uint8_t` and `uint16_t` do not stay unsigned under the
 * usual arithmetic conversions: they promote to signed `int` (C17 6.3.1.1p2),
 * so an innocent-looking `(uint16_t) a * (uint16_t) b` is a SIGNED int
 * multiply that overflows for ordinary inputs and is undefined.  Naming the
 * working type makes the operand type explicit at every operation.
 *
 * WTY is `uint32_t` for N <= 32 and `uint64_t` for N == 64, which is wide
 * enough in every case: the largest W16 product is 65535 * 65535 = 4294836225,
 * below 2^32, and at N == 32 the uint32_t arithmetic IS the answer with
 * nothing to truncate.  Deliberately not `uint64_t` everywhere -- see the note
 * on GIB_DEFINE_U2S for what that costs a vectorised byte loop. */
#define GIB_DEFINE_INT_ARITH(SUF, TY, UTY, WTY, U2S)                    \
    static inline TY gib_add_##SUF(TY a, TY b)                          \
    {                                                                   \
        return U2S((UTY) ((WTY) (UTY) a + (WTY) (UTY) b));              \
    }                                                                   \
    static inline TY gib_sub_##SUF(TY a, TY b)                          \
    {                                                                   \
        return U2S((UTY) ((WTY) (UTY) a - (WTY) (UTY) b));              \
    }                                                                   \
    static inline TY gib_mul_##SUF(TY a, TY b)                          \
    {                                                                   \
        return U2S((UTY) ((WTY) (UTY) a * (WTY) (UTY) b));              \
    }                                                                   \
    /* Negation is `0 - a`; note gib_neg(MIN) == MIN, which is the       \
     * modular answer and the one the hardware gives. */                 \
    static inline TY gib_neg_##SUF(TY a)                                \
    {                                                                   \
        return U2S((UTY) (((WTY) 0) - (WTY) (UTY) a));                  \
    }                                                                   \
    static inline TY gib_div_##SUF(TY a, TY b)                          \
    {                                                                   \
        if (b == 0) {                                                   \
            fprintf(stderr, "Gibbon: integer division by zero\n");       \
            exit(1);                                                    \
        }                                                               \
        /* The one quotient that is not representable is MIN / -1.  Route \
         * every `/ -1` through modular negation so the singular case is  \
         * handled without ever forming the overflowing signed quotient   \
         * (which on x86-64 raises SIGFPE rather than returning). */      \
        if (b == -1) {                                                  \
            return U2S((UTY) (((WTY) 0) - (WTY) (UTY) a));              \
        }                                                               \
        /* b is neither 0 nor -1, so |a/b| <= |a| < 2^(N-1): the signed  \
         * division cannot overflow and needs no guard. */               \
        return (TY) (a / b);                                            \
    }                                                                   \
    static inline TY gib_mod_##SUF(TY a, TY b)                          \
    {                                                                   \
        if (b == 0) {                                                   \
            fprintf(stderr, "Gibbon: integer remainder by zero\n");      \
            exit(1);                                                    \
        }                                                               \
        /* x % -1 is 0 for every x, MIN included; taking it directly     \
         * avoids the undefined MIN % -1. */                             \
        if (b == -1) {                                                  \
            return 0;                                                   \
        }                                                               \
        return (TY) (a % b);                                            \
    }                                                                   \
    /* Modular exponentiation by squaring: O(log e) multiplies, all of   \
     * them unsigned, with the single truncation at the end.  A negative  \
     * exponent returns 1 -- see the note in `Gibbon.Language.Syntax`;    \
     * that is what compiled code already produced for every base but 2,  \
     * where the old helper shifted by a negative count instead. */       \
    static inline TY gib_exp_##SUF(TY a, TY e)                          \
    {                                                                   \
        if (e < 0) {                                                    \
            return 1;                                                   \
        }                                                               \
        /* Squaring stays at 64 bits regardless of N: this loop is not a \
         * vectorisation candidate, and mod 2^64 still fixes mod 2^N. */ \
        uint64_t base = (uint64_t) (UTY) a;                             \
        uint64_t acc = 1;                                               \
        uint64_t k = (uint64_t) e;                                      \
        while (k != 0) {                                                \
            if ((k & 1) != 0) {                                         \
                acc *= base;                                            \
            }                                                           \
            base *= base;                                               \
            k >>= 1;                                                    \
        }                                                               \
        return U2S((UTY) acc);                                          \
    }

GIB_DEFINE_INT_ARITH(i8,  GibInt8,  uint8_t,  uint32_t, gib_u2s_i8)
GIB_DEFINE_INT_ARITH(i16, GibInt16, uint16_t, uint32_t, gib_u2s_i16)
GIB_DEFINE_INT_ARITH(i32, GibInt32, uint32_t, uint32_t, gib_u2s_i32)
GIB_DEFINE_INT_ARITH(i64, GibInt64, uint64_t, uint64_t, gib_u2s_i64)

typedef char GibChar;
typedef float GibFloat;
typedef uint64_t GibSym;
typedef bool GibBool;
typedef char* GibPtr;
typedef char* GibCursor;
typedef uintptr_t GibTaggedPtr;
typedef uint64_t GibThreadId;


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shorthands
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define KB 1024lu
#define MB (KB * 1024lu)
#define GB (MB * 1024lu)

#define ATTR_ALWAYS_INLINE __attribute__((always_inline))
#define ATTR_HOT __attribute__((hot))

#ifdef _GIBBON_POINTER
#define UNUSED_IN_POINTER_BAK __attribute__((unused))
#else
#define UNUSED_IN_POINTER_BAK
#endif

#define LIKELY(x) __builtin_expect((bool) (x), 1)
#define UNLIKELY(x) __builtin_expect((bool) (x), 0)
#define IGNORE(x) (void) (x)


/*
 * Inlining macros taken from GHC:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * INLINE_HEADER is for inline functions in header files (macros)
 * STATIC_INLINE is for inline functions in source files
 * EXTERN_INLINE is for functions that we want to inline sometimes, we also
 * compile a static version of the function.
 *
 */

#define INLINE_HEADER static inline

// Never inlined into the generated program.
//
// Not a micro-optimisation -- it is required for the benchmark numbers to mean
// anything.  These three are called from the program itself: the allocator at
// every region-growth site, and the save/restore pair inside each timed loop in
// `main` -- which is also where the traversal loops are inlined.  Built with
// -flto (Gibbon/Common.hs: optc = " -O3  -flto ") and -mavx2, letting the
// linker inline the save/restore pair into `main` perturbs that function's
// register allocation and scheduling, and the cost lands on the traversals
// sharing it.  Measured on a 10M-element SoA list: identical instruction
// counts and FEWER cache misses, but IPC fell 3.70 -> 2.99 and folds over a
// map's output went 0.0048s -> 0.0145s.  It showed up even at --iterate 1,
// where the feature never runs, which is what identified it as code generation
// rather than anything the reclaim does.
//
// `noinline` on ALL THREE is what fixes it; on the allocator alone it does not
// (measured 0.0138s, still 3x). Portable, so gcc and clang are both covered.
#define GIB_NOINLINE __attribute__((noinline))
#define STATIC_INLINE static inline
#define EXTERN_INLINE extern inline

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Globals and their accessors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


// Chunk sizes of buffers, see GitHub #79 and #110.
size_t gib_get_biginf_init_chunk_size(void);
size_t gib_get_inf_init_chunk_size(void);

// Runtime arguments, values updated by the flags parser.
//
// The exported accessors are pinned to `int64_t` (see the GibInt/ABI note
// above).  The `GibInt`-returning wrappers below are header-local, so
// generated code keeps seeing a `GibInt` here -- which matters because the
// code generator feeds these results straight to `printf` with a conversion
// specifier chosen for `GibInt`.
int64_t gib_get_size_param_i64(void);
int64_t gib_get_iters_param_i64(void);

INLINE_HEADER GibInt gib_get_size_param(void)
{
    return (GibInt) gib_get_size_param_i64();
}

INLINE_HEADER GibInt gib_get_iters_param(void)
{
    return (GibInt) gib_get_iters_param_i64();
}

char *gib_read_bench_prog_param(void);
char *gib_read_benchfile_param(void);
char *gib_read_arrayfile_param(void);
uint64_t gib_read_arrayfile_length_param(void);
uint64_t get_papi_region_id(void);
void increment_papi_region_id(void);

// Number of regions allocated.
int64_t gib_read_region_count(void);

// Invariant: should always be equal to max(sym_table_keys).
GibSym gib_read_gensym_counter(void);


// Must be same as "Gibbon.Language.Constants".
//
// These are the top of a one-byte space the compiler fills from below:
// [0, 150) ordinary constructor tags, [150, 249) their random-access variants,
// which carry a size field.  A new reserved tag must come out of the range
// below 249 only by lowering GIB_SELECTIVE_INDIRECTION_TAG and `ranTagBase`
// together; `getTagOfDataCon` rejects a program that would otherwise overrun.
#define GIB_REDIRECTION_TAG 255
#define GIB_INDIRECTION_TAG 254
#define GIB_SELECTIVE_INDIRECTION_TAG 249

// Tags reserved for the garbage collector.
#define GIB_CAUTERIZED_TAG 253
#define GIB_COPIED_TO_TAG 252
#define GIB_COPIED_TAG 251
#define GIB_SCALAR_TAG 250
#define GIB_PTR_ALIGN 8


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Pointer tagging
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define GIB_TAG_BITS 16
#define GIB_POINTER_BITS 48
static const GibTaggedPtr GIB_POINTER_MASK = (UINTPTR_MAX >> GIB_TAG_BITS);

#define GIB_STORE_TAG(ptr, tag)                                               \
    (GibTaggedPtr) (((GibTaggedPtr) ptr) | (((GibTaggedPtr) tag) << GIB_POINTER_BITS)) \

#define GIB_UNTAG(tagged)                              \
    (char *) (((GibTaggedPtr) tagged) & GIB_POINTER_MASK) \

#define GIB_GET_TAG(tagged)                               \
    (uint16_t) (((GibTaggedPtr) tagged) >> GIB_POINTER_BITS) \



INLINE_HEADER void gib_store_taggedptr_unaligned(GibCursor p, GibTaggedPtr x) {
    memcpy(p, &x, sizeof(GibTaggedPtr));
}

INLINE_HEADER GibTaggedPtr gib_load_taggedptr_unaligned(GibCursor p) {
    GibTaggedPtr x;
    memcpy(&x, p, sizeof(GibTaggedPtr));
    return x;
}

INLINE_HEADER uintptr_t gib_load_uintptr_unaligned(GibCursor p) {
    uintptr_t x;
    memcpy(&x, p, sizeof(uintptr_t));
    return x;
}

INLINE_HEADER size_t gib_align_up_sz(size_t n, size_t a) {
    return (n + (a - 1)) & ~(a - 1);
}

#define GIB_LOAD_UINTPTR(p) gib_load_uintptr_unaligned((GibCursor)(p))
#define GIB_LOAD_TAGGEDPTR(p) gib_load_taggedptr_unaligned((GibCursor)(p))
#define GIB_STORE_TAGGEDPTR(p, x) gib_store_taggedptr_unaligned((GibCursor)(p), (GibTaggedPtr)(x))

INLINE_HEADER void gib_unwrap_selective_indirections(GibCursor *ends,
                                                     GibCursor *curs,
                                                     int len) {
    if (len <= 0 || curs[0] == NULL ||
        *(GibPackedTag *) curs[0] != GIB_SELECTIVE_INDIRECTION_TAG) {
        return;
    }

    GibCursor dcon_cur = curs[0];
    GibCursor dcon_src =
        (GibCursor) gib_load_uintptr_unaligned(dcon_cur + sizeof(GibPackedTag));
    GibCursor dcon_end =
        (GibCursor) gib_load_uintptr_unaligned(dcon_cur + sizeof(GibPackedTag) +
                                               sizeof(uintptr_t));
    uint64_t mask =
        *(uint64_t *)(dcon_cur + sizeof(GibPackedTag) + (2 * sizeof(uintptr_t)));

    curs[0] = dcon_src;
    ends[0] = dcon_end;

    for (int i = 1; i < len && i < 64; i++) {
        if ((mask & (((uint64_t) 1) << i)) == 0) {
            continue;
        }

        GibCursor cur = curs[i];
        if (cur == NULL ||
            *(GibPackedTag *) cur != GIB_SELECTIVE_INDIRECTION_TAG) {
            fprintf(stderr,
                    "Expected selective indirection wrapper in SoA buffer %d\n",
                    i);
            exit(1);
        }

        GibCursor src =
            (GibCursor) gib_load_uintptr_unaligned(cur + sizeof(GibPackedTag));
        GibCursor end =
            (GibCursor) gib_load_uintptr_unaligned(cur + sizeof(GibPackedTag) +
                                                   sizeof(uintptr_t));

        curs[i] = src;
        ends[i] = end;
    }
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Allocators
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void *gib_alloc(size_t size);
void *gib_scoped_alloc(size_t size);
void gib_free(void *ptr);

// Bump allocation.
void gib_ptr_bumpalloc_save_state(void);
void gib_ptr_bumpalloc_restore_state(void);

// Region chunk log.
//
// A benchmark iteration (`iterate`) rewinds its write cursors to the start of
// the output region and runs again, so every iteration re-grows that region
// from its first chunk.  `gib_grow_region_on_heap` links the new chunk in with
// `old_footer->next = new_footer`, which OVERWRITES the link the previous
// iteration left there -- orphaning that whole chain, unreachable even from
// `reg_info->first_chunk_footer`, and never freed.  Memory therefore grew by
// one entire output value per iteration.
//
// These three functions bracket an iteration and reclaim exactly what it grew.
// They mirror `gib_{list,ptr}_bumpalloc_save_state`/`_restore_state` above,
// which bracket the same region of the generated loop for the list and pointer
// bump heaps, and whose stated intent -- "cancels out the effect of
// intermediate allocations" -- was simply never implemented for region chunks.
//
// Declared here, ahead of `gib_grow_region_on_heap` (an INLINE_HEADER function
// compiled into the generated program, not into libgibbon_rts), which calls
// `gib_region_chunk_log`.
//
// Compiled in only under -D_GIBBON_REGIONRESET=1; otherwise these are stubs.

// Nesting depth of iteration brackets.  100 matches the existing bump-allocator
// saved-pointer stacks; `iterate` does not nest in practice.
#define GIB_CHUNK_LOG_MAX_DEPTH 100
// Initial log capacity, in chunk pointers.  Grows by doubling, and the capacity
// reached in the first iteration is retained for the rest of the run.
#define GIB_CHUNK_LOG_INIT_CAP 256

// Allocates a region-growth chunk and, when an iteration bracket is open,
// records it for reclamation.  With the feature compiled out this is exactly
// gib_alloc, so the generated program's code does not depend on the setting.
// __attribute__((malloc)) is load-bearing, not decoration: without it the
// compiler must assume the returned pointer may alias anything, which degrades
// alias analysis in EVERY caller.  gib_alloc is plain malloc and carries that
// knowledge implicitly; an opaque wrapper throws it away, and the cost lands in
// the inlined traversal loops in main, not here.
GIB_NOINLINE __attribute__((malloc))
void *gib_region_chunk_alloc(size_t size);
void gib_region_chunk_save_state(void);
void gib_region_chunk_restore_state(void);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Arenas
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_arena {
  int ind;
  char *mem; // TODO(vollmerm): make this a list of chunks?
  void *reflist;
} GibArena;

GibArena *gib_alloc_arena(void);
void gib_free_arena(GibArena *ar);
GibCursor gib_extend_arena(GibArena *ar, int size);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Arena-based dictionaries
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_symdict {
  struct gib_symdict *next;
  GibSym key;
  void *ptrval;
} GibSymDict;


GibSymDict *gib_dict_alloc(GibArena *ar);
GibSymDict *gib_dict_insert_ptr(GibArena *ar, GibSymDict *ptr, GibSym key, GibPtr val);
GibPtr gib_dict_lookup_ptr(GibSymDict *ptr, GibSym key);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Sets
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_symset {
  int val;
  UT_hash_handle hh;
} GibSymSet;


GibSymSet *gib_empty_set(void);
GibSymSet *gib_insert_set(GibSymSet *set, int sym);
GibBool gib_contains_set(GibSymSet *set, int sym);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Sym Hash
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// TODO(): val needs to be GibInt.
struct gib_sym_hash {
  int key;
  int val;
  UT_hash_handle hh;
};

typedef struct gib_sym_hash GibSymHash;
typedef struct gib_sym_hash GibIntHash;

GibSymHash *gib_empty_hash(void);
GibSymHash *gib_insert_hash(GibSymHash *hash, int k, int v);
GibSym gib_lookup_hash(GibSymHash *hash, int k);
GibBool gib_contains_hash(GibSymHash *hash, int sym);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Symbol table
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define MAX_SYMBOL_LEN 256

typedef struct gib_symtable {
    GibSym idx;                 /* key */
    char value[MAX_SYMBOL_LEN];
    UT_hash_handle hh;         /* makes this structure hashable */
} GibSymtable;

void gib_add_symbol(GibSym idx, char *value);
void gib_set_newline(GibSym idx);
void gib_set_space(GibSym idx);
void gib_set_comma(GibSym idx);
void gib_set_leftparen(GibSym idx);
void gib_set_rightparen(GibSym idx);
int gib_print_symbol(GibSym idx);
GibSym gib_gensym(void);
void gib_free_symtable(void);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Vectors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_vector {
    // Bounds on the vector.
    int64_t lower, upper;

    // Size of each element.
    size_t elt_size;

    // Elements of the vector.
    void *data;

} GibVector;

// Comparison function.
typedef int (*GibCmpFn)(const void *, const void*) ;

// Indices and lengths are `int64_t`, not `GibInt`: these cross the
// RTS/generated-code boundary (see the GibInt/ABI note above).
GibVector *gib_vector_alloc(int64_t num, size_t elt_size);
inline __attribute__((always_inline)) GibCursor *gib_array_alloc(GibCursor *data, size_t arr_size);
int64_t gib_vector_length(GibVector *vec);
GibBool gib_vector_is_empty(GibVector *vec);
GibVector *gib_vector_slice(int64_t i, int64_t n, GibVector *vec);
void *gib_vector_nth(GibVector *vec, int64_t i);
GibVector *gib_vector_inplace_update(GibVector *vec, int64_t i, void* elt);
GibVector *gib_vector_copy(GibVector *vec);
GibVector *gib_vector_inplace_sort(GibVector *vec, GibCmpFn cmp);
GibVector *gib_vector_sort(GibVector *vec, GibCmpFn cmp);
GibVector *gib_vector_concat(GibVector *vec);
void gib_vector_free(GibVector *vec);
GibVector *gib_vector_merge(GibVector *vec1, GibVector *vec2);
void gib_print_timing_array(GibVector *times);
double gib_sum_timing_array(GibVector *times);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Linked lists
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Bump allocation.
void gib_list_bumpalloc_save_state(void);
void gib_list_bumpalloc_restore_state(void);

typedef struct gib_list {
    size_t data_size;
    void *data;
    struct gib_list *next;
} GibList;

GibList *gib_list_alloc(size_t data_size);
GibBool gib_list_is_empty(GibList *ls);
GibList *gib_list_cons(void *elt, GibList *ls);
void *gib_list_head(GibList *ls);
GibList *gib_list_tail(GibList *ls);
void gib_list_free(GibList *ls);
GibList *gib_list_copy(GibList *ls);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ppm images
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// `GibPixel` is laid out by both the RTS and generated code, so its fields are
// pinned to `int64_t` rather than `GibInt` (see the GibInt/ABI note above);
// with `GibInt` these would be a hard struct-layout split under `--int32`.
// Nothing reaches this today -- `Write3dPpmFile` is unimplemented in every
// layer of the compiler -- but the pinning keeps the surface uniform.
typedef struct gib_pixel {
    int64_t field0;
    int64_t field1;
    int64_t field2;
} GibPixel;

void gib_write_ppm(char* filename, int64_t width, int64_t height, GibVector *pixels);
void gib_write_ppm_loop(FILE *fp, int64_t idx, int64_t end, GibVector *pixels);

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Threads and parallelism
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

extern bool gib_global_thread_requested_gc;

extern uint64_t gib_global_num_threads;

INLINE_HEADER GibThreadId gib_get_thread_id(void)
{
#ifdef _GIBBON_PARALLEL
    return __cilkrts_get_worker_number();
#else
    return (GibThreadId) 0;
#endif
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Memory Management; regions, chunks, GC etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


typedef struct gib_chunk {
    GibCursor start;
    GibCursor end;
} GibChunk;

// Prototype scalar-buffer count metadata for SoA chunks. Each footer stores a
// single cyclic count for this region/buffer: non-final footers store the count
// for the next chunk, and the final footer stores the count for the first chunk.
typedef struct gib_scalar_count_footer {
    uint64_t count;
    uint8_t is_touched;
    uint8_t _padding[7];
} GibScalarCountFooter;

typedef struct gib_shadowstack {
    char *start;
    char *end;
    char *alloc;
} GibShadowstack;

// Provenance of a GC root: shadow-stack or remembered set.
typedef enum {
    Stk,
    RemSet,
} GibGcRootProv;

typedef struct gib_shadowstack_frame {
    // Pointer to packed data.
    char *ptr;

    // Pointer to the end of the chunk where this packed data lives.
    char *endptr;

    // Provenance of the GC root located at ptr.
    GibGcRootProv gc_root_prov;

    // An enum in C, which is 4 bytes.
    // The enum (GibDatatype) will be defined in the generated program.
    uint32_t datatype;
} GibShadowstackFrame;

// Type snonyms for convenience.
typedef GibShadowstackFrame GibRememberedSetElt;
typedef GibShadowstack GibRememberedSet;

typedef struct gib_nursery {
    // Allocation area.
    size_t heap_size;
    char *heap_start;
    char *heap_end;
    char *alloc;
} GibNursery;

typedef struct gib_old_generation {
    // Remembered set to store old to young pointers.
    GibRememberedSet *rem_set;

    // Zero count tables; pointers to structures that are initialized and
    // tracked on the Rust Heap.
    void *old_zct;
    void *new_zct;

} GibOldgen;

typedef struct gib_region_info {
    GibSym id;
    uint16_t refcount;
    // Pointers to a structure that is initialized and tracked on the Rust heap.
    void *outset;
    char *first_chunk_footer;
} GibRegionInfo;

typedef struct gib_oldgen_footer {
    GibRegionInfo *reg_info;
    size_t size;
    struct gib_oldgen_footer *next;
    GibScalarCountFooter scalar_counts;
} GibOldgenChunkFooter;

// Per-region scalar-count bookkeeping.
//
// In the header rather than the .c because the per-element bump's fast path is
// inlined into the generated program and reads it directly.  The cyclic
// convention (see above) is why a bump needs this at all: chunk k's count lives
// in chunk k-1's footer, so the bump has to find the PREVIOUS chunk rather than
// increment the footer it was handed.
typedef struct gib_scalar_count_region_state {
    GibRegionInfo *reg_info;
    GibOldgenChunkFooter *current_footer;
    GibOldgenChunkFooter *write_footer;
    GibScalarCountFooter first_counts;
} GibScalarCountRegionState;

typedef struct gib_nursery_footer {
    uint16_t size;
    GibScalarCountFooter scalar_counts;
} GibNurseryChunkFooter;

typedef struct gib_gc_stats {
    // Number of copying minor collections (maintained by Rust RTS).
    uint64_t minor_collections;

    // Number of copying major collections (maintained by Rust RTS).
    uint64_t major_collections;

    // Overall memory allocated (maintained by C and Rust RTS).
    uint64_t mem_allocated_in_nursery;
    uint64_t mem_allocated_in_oldgen;

    // Overall memory copied from nursery to oldgen (maintained by Rust RTS).
    uint64_t mem_copied;

    // Overall memory burned by due to forwarding/burning (maintained by Rust RTS).
    uint64_t mem_burned;

    // Total number of forwarding pointers that could be added vs not added.
    uint64_t ctors_forwarded;
    uint64_t ctors_not_forwarded;

    // Total number of indirections inlined vs not inlined.
    uint64_t indirs_inlined;
    uint64_t indirs_not_inlined;

    // Total number of redirections inlined vs not inlined.
    uint64_t redirs_inlined;
    uint64_t redirs_not_inlined;

    // Number of regions in the nursery (maintained by C RTS).
    uint64_t nursery_regions;

    // Number of regions in the old generation (maintained by C and Rust RTS).
    uint64_t oldgen_regions;

    // Number of chunks created due to growing regions in the nursery (maintained by C RTS).
    uint64_t nursery_chunks;

    // Number of chunks created due to growing regions in the old generation (maintained by Rust RTS).
    uint64_t oldgen_chunks;

    // Total GC time (maintained by C RTS).
    double gc_elapsed_time;
    double gc_cpu_time;

    // Fine grained stats to measure various different parts of the collector
    // (maintained by Rust RTS).
    double gc_rootset_sort_time;
    double gc_burn_time;
    double gc_find_fwdptr_time;
    double gc_info_tbl_lkp_time;
    double gc_zct_mgmt_time;

    // Other stats (maintained by Rust RTS).
    uint64_t fwd_env_size;
    uint64_t fwd_env_lookups;
    uint64_t fwd_env_inserts;
    uint64_t skipover_env_size;
    uint64_t skipover_env_lookups;
    uint64_t skipover_env_inserts;
    uint64_t rootset_size;

} GibGcStats;

typedef struct gib_gc_state_snapshot {
    // nursery
    char *nursery_alloc;
    char *nursery_heap_start;

    // generations
    char *gen_rem_set_alloc;
    void *gen_old_zct;
    void *gen_new_zct;

    // shadow-stacks
    char *ss_read_alloc;
    char *ss_write_alloc;

    // region metadata
    uint64_t num_regions;
    GibRegionInfo **reg_info_addrs;
    char **outsets;

} GibGcStateSnapshot;

// Whether storage is initialized or not.
extern bool gib_storage_initialized;

// Array of nurseries, indexed by thread_id.
extern GibNursery *gib_global_nurseries;
// Old generation.
extern GibOldgen *gib_global_oldgen;

// Shadow stacks for readable and writeable locations respectively,
// indexed by thread_id.
//
// TODO(ckoparkar): not clear how shadow stacks would be when we have
// parallel mutators.. These arrays are abstract enough for now.
extern GibShadowstack *gib_global_read_shadowstacks;
extern GibShadowstack *gib_global_write_shadowstacks;

// Collect GC statistics.
extern GibGcStats *gib_global_gc_stats;

// Convenience macro.
#define GC_STATS gib_global_gc_stats

// Convenience macros since we don't really need the arrays of nurseries and
// shadowstacks since mutators are still sequential.
#define DEFAULT_READ_SHADOWSTACK gib_global_read_shadowstacks
#define DEFAULT_WRITE_SHADOWSTACK gib_global_write_shadowstacks
#define DEFAULT_NURSERY gib_global_nurseries
#define DEFAULT_GENERATION gib_global_oldgen


#if defined GIB_NURSERY_SIZE

#if GIB_NURSERY_SIZE < 1024
// The nursery size provided is too small, set it to 64 bytes.
#define GIB_NURSERY_SIZE 1024
#endif

// GIB_NURSERY_SIZE not defined, initialize it to a default value.
#else
#define GIB_NURSERY_SIZE (4 * MB)
#endif

#if defined GIB_INIT_CHUNK_SIZE

#if GIB_INIT_CHUNK_SIZE < 1024
// Keep a conservative lower bound for metadata, redirections, and small values.
#define GIB_INIT_CHUNK_SIZE 1024
#endif

// GIB_INIT_CHUNK_SIZE not defined, initialize it to a default value.
#else
#define GIB_INIT_CHUNK_SIZE 1024
#endif



#define GIB_MAX_CHUNK_SIZE 65500

// TODO: The shadow stack doesn't grow and we don't check for
// overflows at the moment. But this stack probably wouldn't overflow since
// each stack frame is only 16 bytes.
#define GIB_SHADOWSTACK_SIZE (sizeof(GibShadowstackFrame) * 4 * 1024 * 1024)

// Same as SHADOWSTACK_SIZE, overflows are not checked.
#define GIB_REMEMBERED_SET_SIZE (sizeof(GibRememberedSetElt) * 4 * 1024 * 1024)


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Implemented in the Rust RTS
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

int gib_info_table_initialize(size_t size);
int gib_info_table_finalize(void);
int gib_info_table_clear(void);
int gib_info_table_print(void);
int gib_info_table_insert_scalar(uint32_t datatype, size_t size);
int gib_info_table_insert_packed_dcon(
    uint32_t datatype,
    uint8_t datacon,
    size_t scalar_bytes,
    size_t num_shortcut,
    uint8_t num_scalars,
    uint8_t num_packed,
    uint32_t *field_tys,
    uint8_t field_tys_length
);
int gib_garbage_collect(
    GibShadowstack *rstack,
    GibShadowstack *wstack,
    GibNursery *nursery,
    GibOldgen *generation,
    GibGcStats *stats,
    bool force_major
);
int gib_free_region_(GibOldgenChunkFooter *footer);
void gib_add_old_to_old_indirection(
    char *from_footer,
    char *to_footer
);
char *gib_init_footer_at(
    char *chunk_end,
    size_t chunk_size,
    uint16_t refcount
);
void gib_init_zcts(GibOldgen *generation);
void gib_insert_into_new_zct(
    GibOldgen *generation,
    GibRegionInfo *reg_info
);
void *gib_clone_zct(void *zct);
void *gib_clone_outset(void *outset);
void *gib_free_zct(void *zct);
void *gib_free_outset(void *outset);
int gib_gc_cleanup(
    GibShadowstack *rstack,
    GibShadowstack *wstack,
    GibNursery *nursery,
    GibOldgen *generation
);
void gib_get_rust_struct_sizes(
    size_t *stack,
    size_t *frame,
    size_t *nursery,
    size_t *generation,
    size_t *reg_info,
    size_t *footer,
    size_t *gc_stats
);
void gib_print_nursery_and_oldgen(
    GibShadowstack *rstack,
    GibShadowstack *wstack,
    GibNursery *nursery,
    GibOldgen *oldgen
);
// Print the Rust GC configuration.
void gib_print_rust_gc_config(void);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ensure that C and Rust agree on sizes
 * of structs that cross the boundary.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
void gib_check_rust_struct_sizes(void);


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Print GC configuration
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Print the GC configuration.
void gib_print_gc_config(void);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Region allocation and growth
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Region allocation.
GibChunk gib_alloc_region(size_t size);
GibChunk gib_alloc_region_on_heap(size_t size);
INLINE_HEADER void gib_grow_region(char **writeloc_addr, char **footer_addr);
void gib_grow_region_noinline(char **writeloc_addr, char **footer_addr);
void gib_free_region(char *footer_ptr);
void gib_scalar_count_footer_begin(void);
// Per-element scalar-count bump.
//
// This is the hottest call in an annotated SoA producer: it fires once per
// scalar buffer per constructor application.  Measured before it was inlined,
// on a 20M-element SoA list, maintaining counts cost +82% on the producer, with
// 47% of program cycles in this function and its region-state lookup against
// 12% in the list construction being annotated.
//
// The fast path is the only one that matters: an oldgen footer whose region
// already has a state in the table, which after the first element is every
// element.  It is kept free of a call and a stack frame; everything else --
// NULL, nursery footers, and the first touch of a region (which appends to the
// table and may realloc) -- goes out of line to
// `gib_scalar_count_footer_bump_slow`.
void gib_scalar_count_footer_bump_slow(char *footer_ptr);

// The table the fast path reads.  Defined in gibbon_rts.c.
extern GibScalarCountRegionState *gib_global_scalar_count_region_states;
extern size_t gib_global_scalar_count_region_states_length;

void gib_scalar_count_footer_set(char *footer_ptr, uint64_t count);
void gib_scalar_count_footer_end(const char *build_fun_name);
void gib_scalar_count_footer_print(char *footer_ptr);
uint64_t gib_scalar_count_footer_get(char *footer_ptr);
char *gib_scalar_count_first_footer(char *footer_ptr);
char *gib_scalar_count_footer_next(char *footer_ptr);
void gib_scalar_count_copy_chain(char *dst_final_footer_ptr, char *src_final_footer_ptr);
void gib_scalar_count_copy_all(char **dst_final_footers, char **src_final_footers, int len);
void gib_scalar_count_on_grow(char *old_footer_ptr, char *new_footer_ptr);
INLINE_HEADER void gib_scalar_count_footer_init(GibScalarCountFooter *footer);

/*
 * Deferred scalar counts.
 *
 * Resolving which footer an element's count belongs to only changes when the
 * region grows, so it is hoisted out of the element loop: the generated
 * producer increments a global counter, and the batched total is delivered
 * into the correct footer at growth (gib_scalar_count_on_grow, before its
 * cyclic state transition) and after the producer's outermost call
 * (gib_scalar_count_finalize).  This counts the same events as
 * gib_scalar_count_footer_bump, so the resulting footers are identical.
 *
 * Slot = base + the buffer's position in the SoA cursor array (0 = tag
 * buffer), with base assigned per producer program-wide.  Each SoA buffer is
 * its own region, so the slot/region mapping is 1:1 and on_grow can find a
 * slot from reg_info alone.
 *
 * See Note [Deferred scalar counts] in Gibbon.Passes.AssignScalarCountSlots.
 */


#define GIB_SCALAR_COUNT_MAX_SLOTS 256

// The counter the generated code increments.  Not static: the bump is inlined
// into the program.
extern uint64_t gib_scalar_count_pending[GIB_SCALAR_COUNT_MAX_SLOTS];

// Bind slots [base, base+len) to the regions owning `final_footers[0..len)`,
// called at a producer's outermost call site BEFORE the call.  The region is
// allocated by the caller, so its footer is already live at this point.
void gib_scalar_count_bind(char **final_footers, size_t base, int len);

// Flush slots [base, base+len) into their footers; called AFTER the call.
// Must run before the `gib_scalar_count_copy_all` at the same call site.
void gib_scalar_count_finalize(char **final_footers, size_t base, int len);

// Drop every slot binding.  Paired with the region-state reset, since a slot
// holds a `GibRegionInfo *` into a chunk the reset may free.
void gib_scalar_count_forget_slots(void);

// A region that starts in the nursery and is promoted to the oldgen changes
// BOTH its footer and its `reg_info`, and `gib_scalar_count_on_grow` is not
// called on that path -- so a slot bound to the nursery footer would keep
// writing there for the rest of the production, losing every count after the
// promotion.  (The per-element bump did not have this problem: it re-resolved
// the footer on every element.)  This delivers what the nursery chunk holds
// and re-points the slot at the promoted region.
void gib_scalar_count_on_promote(char *old_nursery_footer, char *new_oldgen_footer);

#ifdef _GIBBON_SCALAR_COUNT_DIFF
// Differential mode: the per-element bump is ALSO emitted, so the footers carry
// the authoritative counts and each flush VERIFIES rather than applies.  A
// mismatch aborts naming the slot -- see gib_scalar_count_diff_check.
void gib_scalar_count_diff_report(void);
#endif


// Trigger GC.
void gib_perform_GC(bool force_major);

// Functions related to counting the number of allocated regions.
GibChunk gib_alloc_counted_region(size_t size);
void gib_print_global_region_count(void);
void *gib_alloc_counted_struct(size_t size);

/*
 * ~~~~~~~~~~~~~~~~~~~~
 * Region growth
 * ~~~~~~~~~~~~~~~~~~~~
 */


INLINE_HEADER void gib_grow_region(char **writeloc_addr, char **footer_addr);
INLINE_HEADER void gib_grow_region_in_nursery_fast(
    bool collected,
    bool old_chunk_in_nursery,
    size_t size,
    GibOldgenChunkFooter *old_footer,
    char **writeloc_addr,
    char **footer_addr
);
void gib_grow_region_in_nursery_slow(
    bool collected,
    bool old_chunk_in_nursery,
    size_t size,
    GibOldgenChunkFooter *old_footer,
    char **writeloc_addr,
    char **footer_addr
);
INLINE_HEADER void gib_grow_region_on_heap(
    bool old_chunk_in_nursery,
    size_t size,
    GibOldgenChunkFooter *old_footer,
    char **writeloc_addr,
    char **footer_addr
);
INLINE_HEADER bool gib_addr_in_nursery(char *ptr);

// Increment one count.  Defined here, not in the .c, so the inlined fast path
// below and the out-of-line slow path share ONE definition.
//
// The `is_touched` guard is a branch rather than an unconditional store: it is
// perfectly predicted after the first element, and measured faster than
// `is_touched = 1; count++;`.
INLINE_HEADER void gib_scalar_count_footer_bump_fixed(GibScalarCountFooter *footer)
{
    if (!footer->is_touched) {
        footer->count = 0;
        footer->is_touched = 1;
    }

    footer->count++;
}

INLINE_HEADER void gib_scalar_count_footer_bump(char *footer_ptr)
{
    if (footer_ptr == NULL || gib_addr_in_nursery(footer_ptr)) {
        gib_scalar_count_footer_bump_slow(footer_ptr);
        return;
    }
    GibRegionInfo *reg_info = ((GibOldgenChunkFooter *) footer_ptr)->reg_info;
    for (size_t i = 0; i < gib_global_scalar_count_region_states_length; i++) {
        GibScalarCountRegionState *st = &gib_global_scalar_count_region_states[i];
        if (st->reg_info == reg_info) {
            // The cyclic convention: chunk k's count lives in chunk k-1's
            // footer, so before the region has grown there is no previous
            // chunk and the count accumulates in `first_counts` (plus the
            // current footer, which the final chunk's reader consults).
            GibScalarCountFooter *tgt;
            if (st->write_footer == NULL) {
                gib_scalar_count_footer_bump_fixed(&st->first_counts);
                tgt = &st->current_footer->scalar_counts;
            } else {
                tgt = &st->write_footer->scalar_counts;
            }
            gib_scalar_count_footer_bump_fixed(tgt);
            return;
        }
    }
    gib_scalar_count_footer_bump_slow(footer_ptr);
}


INLINE_HEADER void gib_scalar_count_footer_init(GibScalarCountFooter *footer)
{
    footer->count = 0;
    footer->is_touched = 0;
    memset(footer->_padding, 0, sizeof(footer->_padding));
}


INLINE_HEADER void gib_grow_region(char **writeloc_addr, char **footer_addr)
{
    char *footer_ptr = *footer_addr;
    size_t newsize;
    bool old_chunk_in_nursery;
    GibOldgenChunkFooter *old_footer = NULL;

    if (gib_addr_in_nursery(footer_ptr)) {
        old_chunk_in_nursery = true;
        uint16_t oldsize = ((GibNurseryChunkFooter *) footer_ptr)->size;
        newsize = oldsize * 2;
    } else {
        old_chunk_in_nursery = false;
        old_footer = (GibOldgenChunkFooter *) footer_ptr;
        newsize = sizeof(GibOldgenChunkFooter) + (old_footer->size);
        newsize = newsize * 2;
        if (newsize > GIB_MAX_CHUNK_SIZE) {
            newsize = GIB_MAX_CHUNK_SIZE;
        }
    }

#if defined _GIBBON_EAGER_PROMOTION && _GIBBON_EAGER_PROMOTION == 0
    // If the old chunk is in nursery, try to grow it in the nursery.
    // Otherwise put it on the heap since we don't have a remembered set for
    // redirection pointers yet.
    if (old_chunk_in_nursery) {
        gib_grow_region_in_nursery_fast(
            false,
            old_chunk_in_nursery,
            newsize,
            old_footer,
            writeloc_addr,
            footer_addr
        );
    } else {
        gib_grow_region_on_heap(
            old_chunk_in_nursery,
            newsize,
            old_footer,
            writeloc_addr,
            footer_addr
        );
    }
#else
    gib_grow_region_on_heap(
        old_chunk_in_nursery,
        newsize,
        old_footer,
        writeloc_addr,
        footer_addr
    );
#endif

}

INLINE_HEADER void gib_grow_region_in_nursery_fast(
    bool collected,
    bool old_chunk_in_nursery,
    size_t size,
    GibOldgenChunkFooter *old_footer,
    char **writeloc_addr,
    char **footer_addr
) {
    GibNursery *nursery = DEFAULT_NURSERY;
    char *old = nursery->alloc;
    char *bump = old - size - sizeof(GibNurseryChunkFooter);

    if (bump >= nursery->heap_start) {

#ifdef _GIBBON_GCSTATS
        GC_STATS->nursery_chunks++;
        GC_STATS->mem_allocated_in_nursery += size;
#endif


        nursery->alloc = bump;
        char *footer = old - sizeof(GibNurseryChunkFooter);
        GibNurseryChunkFooter *nursery_footer = (GibNurseryChunkFooter *) footer;
        nursery_footer->size = size;
        gib_scalar_count_footer_init(&nursery_footer->scalar_counts);
        char *heap_start = bump;
        char *heap_end = footer;

        // Write a redirection tag at writeloc and make it point to the start of
        // this fresh chunk, but store a tagged pointer here.
        uint16_t new_footer_offset = heap_end - heap_start;
        GibTaggedPtr tagged = GIB_STORE_TAG(heap_start, new_footer_offset);
        GibCursor writeloc = *writeloc_addr;
        *(GibPackedTag *) writeloc = GIB_REDIRECTION_TAG;
        writeloc += 1;
        //*(GibTaggedPtr *) writeloc = tagged;
        gib_store_taggedptr_unaligned(writeloc, tagged);

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
        fprintf(stderr, "Growing a region without eager promotion old=(%p,%p) in nursery=%d, new=(%p,%p) in nursery=%d\n",
                *writeloc_addr, *footer_addr, old_chunk_in_nursery, heap_start, heap_end, true);
        fprintf(stderr, "  allocated %zu bytes in the nursery\n", size);
        fprintf(stderr, "  wrote a redirection pointer at %p to %p\n", *writeloc_addr, heap_start);
#endif

        // Update start and end cursors.
        *(char **) writeloc_addr = heap_start;
        *(char **) footer_addr = heap_end;

        return;

    } else {
        gib_grow_region_in_nursery_slow(
            collected,
            old_chunk_in_nursery,
            size,
            old_footer,
            writeloc_addr,
            footer_addr
        );

        return;
    }
}


INLINE_HEADER void gib_grow_region_on_heap(
    bool old_chunk_in_nursery,
    size_t size,
    GibOldgenChunkFooter *old_footer,
    char **writeloc_addr,
    char **footer_addr
) {
    //char *heap_start = (char *) gib_alloc(size);
    size_t size_aligned = gib_align_up_sz(size, GIB_PTR_ALIGN);
    // Allocate THROUGH the chunk-log allocator rather than calling gib_alloc
    // and then logging separately.
    //
    // This function is INLINE_HEADER, so it is inlined at every region-growth
    // site in the generated program.  An extra call here perturbs register
    // allocation and code layout program-wide: measured on a 10M-element SoA
    // list, a separate gib_region_chunk_log() call left instruction count
    // unchanged but dropped IPC from 3.70 to 2.99 and made folds over the
    // map's output 3x slower -- pure code-alignment fallout, which
    // -falign-loops=32 erased.  Routing through one allocator keeps the
    // emitted code identical whether or not the feature is compiled in.
    char *heap_start =  (char *) gib_region_chunk_alloc(size_aligned);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_grow_region: gib_alloc failed: %zu", size);
        exit(1);
    }
    char *heap_end = heap_start + size_aligned;

#ifdef _GIBBON_GCSTATS
    GC_STATS->oldgen_chunks++;
    GC_STATS->mem_allocated_in_oldgen += size;
#endif

    // Write a new footer for this chunk and link it with the old chunk's footer.
    char *new_footer_start = NULL;
    GibOldgenChunkFooter *new_footer = NULL;
    if (old_chunk_in_nursery) {
        //new_footer_start = gib_init_footer_at(heap_end, size, 0);
        new_footer_start = gib_init_footer_at(heap_end, size_aligned, 0);
        new_footer = (GibOldgenChunkFooter *) new_footer_start;
        gib_insert_into_new_zct(DEFAULT_GENERATION, new_footer->reg_info);
        gib_scalar_count_on_promote((char *) old_footer, new_footer_start);
    } else {
        new_footer_start = heap_end - sizeof(GibOldgenChunkFooter);
        new_footer = (GibOldgenChunkFooter *) new_footer_start;
        new_footer->reg_info = old_footer->reg_info;
        new_footer->size = (size_t) (new_footer_start - heap_start);
        new_footer->next = (GibOldgenChunkFooter *) NULL;
        gib_scalar_count_footer_init(&new_footer->scalar_counts);
        // Link with the old chunk's footer.
        //
        // NOTE: this assignment is what leaks.  When a benchmark iteration has
        // rewound to the first chunk, `old_footer->next` still points at the
        // PREVIOUS iteration's chain, and overwriting it here strands that
        // chain permanently.  The log below records the chunk so the iteration
        // bracket can free it; see gib_region_chunk_log.
        old_footer->next = (GibOldgenChunkFooter *) new_footer;
        gib_scalar_count_on_grow((char *) old_footer, new_footer_start);
    }

    // Write a redirection tag at writeloc and make it point to the start of
    // this fresh chunk, but store a tagged pointer here.
    uint16_t new_footer_offset = new_footer_start - heap_start;
    GibTaggedPtr tagged = GIB_STORE_TAG(heap_start, new_footer_offset);
    GibCursor writeloc = *writeloc_addr;
    *(GibPackedTag *) writeloc = GIB_REDIRECTION_TAG;
    writeloc += 1;
    gib_store_taggedptr_unaligned(writeloc, tagged);
    //*(GibTaggedPtr *) writeloc = tagged;

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    fprintf(stderr, "Growing a region old=(%p,%p) in nursery=%d, new=(%p,%p) in nursery=%d \n",
            *writeloc_addr, *footer_addr, old_chunk_in_nursery, heap_start, new_footer_start, false);
    fprintf(stderr,
            "  allocated %zu bytes for region %" PRIu64 " on the heap\n",
            size,
            (new_footer->reg_info)->id);
    fprintf(stderr, "  wrote a redirection pointer at %p to %p\n",
            *writeloc_addr, heap_start);
#endif

    // Update start and end cursors.
    *(char **) writeloc_addr = heap_start;
    *(char **) footer_addr = new_footer_start;

    return;
}



/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Nursery
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// TODO:
// If we allocate the nursery at a high address AND ensure that all of the
// subsequent mallocs return a block at addresses lower than this, we can
// implement addr_in_nursery with one address check instead than two. -- RRN
INLINE_HEADER bool gib_addr_in_nursery(char *ptr)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    return ((ptr >= nursery->heap_start) && (ptr <= nursery->heap_end));
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow-stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

INLINE_HEADER void gib_shadowstack_push(
    GibShadowstack *stack,
    char *ptr,
    char *endptr,
    GibGcRootProv gc_root_prov,
    uint32_t datatype
)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_end = stack->end;
    char **stack_alloc_ptr_addr = &(stack->alloc);
    size_t size = sizeof(GibShadowstackFrame);
    assert((stack_alloc_ptr + size) <= stack_end);
    GibShadowstackFrame *frame = (GibShadowstackFrame *) stack_alloc_ptr;
    frame->ptr = ptr;
    frame->endptr = endptr;
    frame->gc_root_prov = gc_root_prov;
    frame->datatype = datatype;
    (*stack_alloc_ptr_addr) += size;
    return;
}

INLINE_HEADER GibShadowstackFrame *gib_shadowstack_pop(GibShadowstack *stack)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_start = stack->start;
    char **stack_alloc_ptr_addr = &(stack->alloc);
    size_t size = sizeof(GibShadowstackFrame);
    assert((stack_alloc_ptr - size) >= stack_start);
    (*stack_alloc_ptr_addr) -= size;
    GibShadowstackFrame *frame = (GibShadowstackFrame *) (*stack_alloc_ptr_addr);
    return frame;
}

INLINE_HEADER GibShadowstackFrame *gib_shadowstack_peek(GibShadowstack *stack)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_start = stack->start;
    size_t size = sizeof(GibShadowstackFrame);
    char *frame_start = stack_alloc_ptr - size;
    assert(frame_start >= stack_start);
    GibShadowstackFrame *frame = (GibShadowstackFrame *) frame_start;
    return frame;
 }

INLINE_HEADER int32_t gib_shadowstack_length(GibShadowstack *stack)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_start = stack->start;
    return ( (stack_alloc_ptr - stack_start) / sizeof(GibShadowstackFrame) );
}

INLINE_HEADER void gib_shadowstack_print_all(GibShadowstack *stack)
{
    char *run_ptr = stack->start;
    char *end_ptr = stack->alloc;
    GibShadowstackFrame *frame;
    while (run_ptr < end_ptr) {
        frame = (GibShadowstackFrame *) run_ptr;
        printf("ptr=%p, endptr=%p, datatype=%d\n",
               (void *)frame->ptr, (void *)frame->endptr, frame->datatype);
        run_ptr += sizeof(GibShadowstackFrame);
    }
    return;
}

void gib_shadowstack_push_noinline(
    GibShadowstack *stack,
    char *ptr,
    char *endptr,
    GibGcRootProv gc_root_prov,
    uint32_t datatype
);
GibShadowstackFrame *gib_shadowstack_pop_noinline(GibShadowstack *stack);
GibShadowstackFrame *gib_shadowstack_peek_noinline(GibShadowstack *stack);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Remembered set
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define gib_remset_push(stack, ptr, endptr, datatype)                   \
    gib_shadowstack_push(stack, ptr, (char *) endptr, RemSet, datatype)

#define gib_remset_pop(stack) \
    gib_shadowstack_pop(stack)

#define gib_remset_length(stack) \
    gib_shadowstack_length(stack)

#define gib_remset_print_all(stack) \
    gib_shadowstack_print_all(stack)

INLINE_HEADER void gib_remset_reset(GibRememberedSet *set)
{
    set->alloc = set->start;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Write barrier
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * INLINE!!!
 *
 * The following is how different types of indirections are handled:
 *
 * (1) oldgen -> nursery
 *
 *     Add to remembered set.
 *
 * (2) oldgen -> oldgen
 *
 *     Same as old Gibbon, bump refcount and insert into outset.
 *
 */

void gib_add_old_to_old_indirection(
    char *from_footer,
    char *to_footer
);

INLINE_HEADER void gib_indirection_barrier(
    // Address where the indirection tag is written.
    GibCursor from,
    GibCursor from_footer,
    // Address of the pointed-to data.
    GibCursor to,
    GibCursor to_footer,
    // Data type written at from/to.
    uint32_t datatype
)
{

#if defined _GIBBON_SIMPLE_WRITE_BARRIER && _GIBBON_SIMPLE_WRITE_BARRIER == 1
    GIB_PRAGMA_MESSAGE("Simple write barrier is enabled.")
#else
    GIB_PRAGMA_MESSAGE("Simple write barrier is disabled.")
    {
        // Optimization: don't create long chains of indirection pointers.
        GibPackedTag pointed_to_tag = *(GibPackedTag *) to;
        char *after_pointed_to_tag = to + 1;
        uintptr_t tagged_ptr;
        char *pointee, *pointee_end;
        uint16_t pointee_offset;
        while (pointed_to_tag == GIB_INDIRECTION_TAG) {
            //tagged_ptr = *(uintptr_t *) after_pointed_to_tag;
            tagged_ptr = gib_load_uintptr_unaligned(after_pointed_to_tag);
            pointee = GIB_UNTAG(tagged_ptr);
            pointee_offset = GIB_GET_TAG(tagged_ptr);
            pointee_end = pointee + pointee_offset;
            // Edit to and to_footer.
            to = pointee;
            to_footer = pointee_end;
            pointed_to_tag = *(GibPackedTag *) to;
            after_pointed_to_tag = to + 1;
        }
    }
#endif

    // Write the indirection.
    uint16_t footer_offset = to_footer - to;
    GibTaggedPtr tagged = GIB_STORE_TAG(to, footer_offset);
    GibCursor writeloc = from;
    *(GibPackedTag *) writeloc = GIB_INDIRECTION_TAG;
    writeloc += sizeof(GibPackedTag);
    gib_store_taggedptr_unaligned(writeloc, tagged);
    //*(GibTaggedPtr *) writeloc = tagged;

    // If we're using the non-generational GC, all indirections will be
    // old-to-old indirections.

#if defined _GIBBON_GENGC && _GIBBON_GENGC == 0
    IGNORE(datatype);
    gib_add_old_to_old_indirection(from_footer, to_footer);
    return;
#else

#ifdef _GIBBON_DEBUG
    assert(from <= from_footer);
    assert(to <= to_footer);
#endif
    // Add to remembered set if it's an old to young pointer.
    bool from_old = !gib_addr_in_nursery(from);
    bool to_young = gib_addr_in_nursery(to);

    if (from_old) {
        if (to_young) {

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
            fprintf(stderr, "Writing an old-to-young indirection, %p -> %p.\n", from, to);
#endif

            // (3) oldgen -> nursery
            GibOldgen *oldgen = DEFAULT_GENERATION;
            // Store the address of the indirection pointer, *NOT* the address of
            // the indirection tag, in the remembered set.
            char *indr_addr = (char *) from + sizeof(GibPackedTag);
            gib_remset_push(oldgen->rem_set, indr_addr, from_footer, datatype);
            return;
        } else {

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
            fprintf(stderr, "Writing an old-to-old indirection, %p -> %p.\n", from, to);
#endif

            // (4) oldgen -> oldgen
            gib_add_old_to_old_indirection(from_footer, to_footer);
            return;
        }
    } else {

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
        fprintf(stderr, "Writing a young-to-%s indirection, %p -> %p.\n",
                (to_young ? "young" : "old"), from, to);
#endif

   }

    return;
#endif // _GIBBON_GENGC == 1
}

// A copy of gib_indirection_barrier that is not inlined, for use via Rust.
void gib_indirection_barrier_noinline(
    // Address where the indirection tag is written.
    GibCursor from,
    GibCursor from_footer,
    // Address of the pointed-to data.
    GibCursor to,
    GibCursor to_footer,
    // Data type written at from/to.
    uint32_t datatype
);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Save and restore GC's state
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

GibGcStateSnapshot *gib_gc_init_state(uint64_t num_regions);
void gib_gc_save_state(GibGcStateSnapshot *snapshot, uint64_t num_regions, ...);
void gib_gc_restore_state(GibGcStateSnapshot *snapshot);
void gib_gc_free_state(GibGcStateSnapshot *snapshot);




/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Helpers
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void gib_show_usage(char **argv);
double gib_avg(const double* arr, int n);
double gib_difftimespecs(struct timespec *t0, struct timespec *t1);
int gib_compare_doubles(const void *a, const void *b);
// `int64_t`, not `GibInt`: these cross the RTS/generated-code boundary (see
// the GibInt/ABI note above).
int64_t gib_expll(int64_t base, int64_t pow);
int64_t gib_get_num_processors(void);

// Copied from: https://stackoverflow.com/a/47074187
//
// ASSUMPTIONS:
// (1) x is a power of 2, and
// (2) log(2) is less than 256
INLINE_HEADER uint8_t gib_log2(size_t x)
{
    return sizeof(uint32_t) * CHAR_BIT - __builtin_clz(x) - 1;
}

// From Chandler Carruth's CppCon 2015 talk.
INLINE_HEADER void escape(void *p) {
    __asm__ __volatile__("" : : "g"(p) : "memory");
}

// From Chandler Carruth's CppCon 2015 talk.
INLINE_HEADER void clobber(void) {
    __asm__ __volatile__("" : : : "memory");
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * RTS initialization and clean up
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

size_t gib_nursery_realloc(GibNursery *nursery, size_t nsize);
int gib_init(int argc, char **argv);
int gib_exit(void);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * ABI width pin
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * The RTS is built once, into a single unnamespaced `gibbon-rts/build`
 * directory, and is shared by every generated translation unit regardless of
 * its integer widths.  `GIBBON_INT32` no longer exists, and `GibInt` has one
 * stable, unconditional meaning (see the ABI note above), so the specific
 * `GibInt`-switches-width hazard this section was written for is gone.  The
 * assertions stay anyway, as
 * defense in depth: they pin every
 * prototype and shared struct below to an explicit `int64_t` so that if
 * `GibInt`'s meaning is EVER changed again -- deliberately or by accident --
 * a struct or prototype here that quietly reintroduced it fails LOUDLY at
 * compile time instead of producing a silent RTS/generated-code ABI split
 * (e.g. `vslice (-1) 2 v` reaching `gib_vector_slice` as 4294967295).
 *
 * These assertions are evaluated in *both* translation units, so they fire at
 * compile time in whichever one drifts.  `sizeof` on a call expression does
 * not evaluate the call; `_Generic` matches the pointed-to function type
 * exactly, so it also pins the parameters.
 */

#define GIB_ABI_PIN_MSG(fn) \
    "RTS ABI: " fn " must not use GibInt; it crosses the RTS/generated-code " \
    "boundary and the RTS is not rebuilt for --int32"

_Static_assert(sizeof(((GibPixel *) 0)->field0) == 8 &&
               sizeof(((GibPixel *) 0)->field1) == 8 &&
               sizeof(((GibPixel *) 0)->field2) == 8,
               GIB_ABI_PIN_MSG("GibPixel"));

_Static_assert(_Generic(&gib_vector_alloc,
                        GibVector *(*)(int64_t, size_t): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_vector_alloc"));

_Static_assert(_Generic(&gib_vector_length,
                        int64_t (*)(GibVector *): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_vector_length"));

_Static_assert(_Generic(&gib_vector_slice,
                        GibVector *(*)(int64_t, int64_t, GibVector *): 1,
                        default: 0),
               GIB_ABI_PIN_MSG("gib_vector_slice"));

_Static_assert(_Generic(&gib_vector_nth,
                        void *(*)(GibVector *, int64_t): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_vector_nth"));

_Static_assert(_Generic(&gib_vector_inplace_update,
                        GibVector *(*)(GibVector *, int64_t, void *): 1,
                        default: 0),
               GIB_ABI_PIN_MSG("gib_vector_inplace_update"));

_Static_assert(_Generic(&gib_write_ppm,
                        void (*)(char *, int64_t, int64_t, GibVector *): 1,
                        default: 0),
               GIB_ABI_PIN_MSG("gib_write_ppm"));

_Static_assert(_Generic(&gib_write_ppm_loop,
                        void (*)(FILE *, int64_t, int64_t, GibVector *): 1,
                        default: 0),
               GIB_ABI_PIN_MSG("gib_write_ppm_loop"));

_Static_assert(_Generic(&gib_expll,
                        int64_t (*)(int64_t, int64_t): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_expll"));

_Static_assert(_Generic(&gib_get_num_processors,
                        int64_t (*)(void): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_get_num_processors"));

_Static_assert(_Generic(&gib_get_size_param_i64,
                        int64_t (*)(void): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_get_size_param_i64"));

_Static_assert(_Generic(&gib_get_iters_param_i64,
                        int64_t (*)(void): 1, default: 0),
               GIB_ABI_PIN_MSG("gib_get_iters_param_i64"));

#endif // #ifndef _GIBBON_H
