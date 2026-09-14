// The imports here must be kept in sync with
// 'hashIncludes' in Gibbon.Passes.Codegen.

#include "gibbon_rts.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <math.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <alloca.h>
#include <sys/mman.h>
#include <malloc.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <unistd.h>
#include <fcntl.h>
#include <stdarg.h>
#include <errno.h>
#include <uthash.h>

#ifdef _WIN64
#include <windows.h>
#endif

#ifdef _GIBBON_POINTER
#include <gc.h>
#endif

#ifdef _GIBBON_PARALLEL
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#endif

#ifdef _GIBBON_ENABLE_PAPI
#include <papi.h>
#endif

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Globals and their accessors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Chunk sizes of buffers, see GitHub #79 and #110.
static size_t gib_global_biginf_init_chunk_size = 4 * GB;
static size_t gib_global_inf_init_chunk_size = GIB_INIT_CHUNK_SIZE;

// Runtime arguments, values updated by the flags parser.
// `int64_t`, not `GibInt`: these back the pinned accessors below.
static int64_t gib_global_size_param = 1;
static int64_t gib_global_iters_param = 1;
static char *gib_global_bench_prog_param = (char *) NULL;
static char *gib_global_benchfile_param = (char *) NULL;
static char *gib_global_arrayfile_param = (char *) NULL;
static uint64_t gib_global_arrayfile_length_param = 0;

// Number of regions allocated.
static int64_t gib_global_region_count = 0;

// Invariant: should always be equal to max(sym_table_keys).
static GibSym gib_global_gensym_counter = 0;

//PAPI: specify the region to instrument
static uint64_t papi_region_id = 0;


size_t gib_get_biginf_init_chunk_size(void)
{
    return gib_global_biginf_init_chunk_size;
}

size_t gib_get_inf_init_chunk_size(void)
{
    return gib_global_inf_init_chunk_size;
}

// The `GibInt`-returning `gib_get_size_param` / `gib_get_iters_param` that
// callers actually use are `INLINE_HEADER` wrappers in gibbon_rts.h; only
// these fixed-width accessors are exported.
int64_t gib_get_size_param_i64(void)
{
    return gib_global_size_param;
}

int64_t gib_get_iters_param_i64(void)
{
    return gib_global_iters_param;
}

char *gib_read_bench_prog_param(void)
{
    if (gib_global_bench_prog_param == NULL) {
        fprintf(stderr, "gib_read_bench_prog_param: benchmark program was not set! Set using --bench-prog.\n");
        exit(1);
    } else {
        return gib_global_bench_prog_param;
    }
}

char *gib_read_benchfile_param(void)
{
    if (gib_global_benchfile_param == NULL) {
        fprintf(stderr, "gib_read_benchfile_param: benchmark input file was not set! Set using --bench-input.\n");
        exit(1);
    } else {
        return gib_global_benchfile_param;
    }
}

char *gib_read_arrayfile_param(void)
{
    if (gib_global_arrayfile_param == NULL) {
        fprintf(stderr, "gib_read_arrayfile_param: array input file was not set! Set using --array-input.\n");
        exit(1);
    } else {
        return gib_global_arrayfile_param;
    }
}

uint64_t gib_read_arrayfile_length_param(void)
{
    return gib_global_arrayfile_length_param;
}

int64_t gib_read_region_count(void)
{
    return gib_global_region_count;
}

GibSym gib_read_gensym_counter(void)
{
    return gib_global_gensym_counter;
}

#ifndef GIB_PTR_ALIGN
#define GIB_PTR_ALIGN 8
#endif

__attribute__((unused))
static inline size_t gib_align_up_sz_rt(size_t n, size_t a) {
    return (n + (a - 1)) & ~(a - 1);
}

__attribute__((unused))
static inline uintptr_t gib_align_up_ptr_rt(uintptr_t p, uintptr_t a) {
    return (p + (a - 1)) & ~(a - 1);
}

uint64_t get_papi_region_id(void)
{
    return papi_region_id;
}

void increment_papi_region_id(void)
{
    papi_region_id++;
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Allocators
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/*
 * If parallelism is enabled, we always use a nursery/malloc based allocator
 * since Boehm GC is not thread-safe in its default configuration. It can be
 * made thread-safe by building it with appropriate flags, but we don't do that.
 * Presently, all parallel pointer-based programs will leak memory.
 */

#ifdef _GIBBON_POINTER

#ifdef _GIBBON_BUMPALLOC_HEAP
GIB_PRAGMA_MESSAGE("Using bump allocator.")

static __thread char *gib_global_ptr_bumpalloc_heap_ptr = (char *) NULL;
static __thread char *gib_global_ptr_bumpalloc_heap_ptr_end = (char *) NULL;
static char *gib_global_ptr_saved_heap_ptr_stack[100];
static int gib_global_ptr_num_saved_heap_ptr = 0;

// For simplicity just use a single large slab:
static inline void gib_init_ptr_bumpalloc(void)
{
    gib_global_ptr_bumpalloc_heap_ptr =
        (char*) malloc(gib_global_biginf_init_chunk_size);
    gib_global_ptr_bumpalloc_heap_ptr_end =
        gib_global_ptr_bumpalloc_heap_ptr + gib_global_biginf_init_chunk_size;
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Arena size for bump alloc: %zu\n", gib_global_biginf_init_chunk_size);
    printf("gib_init_ptr_bumpalloc DONE: heap_ptr = %p\n",
           gib_global_ptr_bumpalloc_heap_ptr);
#endif
}

static inline void *gib_ptr_bumpalloc(size_t n)
{
    if (! gib_global_ptr_bumpalloc_heap_ptr) {
        gib_init_ptr_bumpalloc();
    }
    if (gib_global_ptr_bumpalloc_heap_ptr + n <
        gib_global_ptr_bumpalloc_heap_ptr_end) {
        char* old= gib_global_ptr_bumpalloc_heap_ptr;
        gib_global_ptr_bumpalloc_heap_ptr += n;
        return old;
    } else {
        fprintf(stderr, "Warning: bump allocator ran out of memory.");
        exit(1);
    }
}

// Snapshot the current heap pointer value across all threads.
void gib_ptr_bumpalloc_save_state(void)
{
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Saving(%p): pos %d", heap_ptr, gib_global_ptr_num_saved_heap_ptr);
#endif
    char *heap_ptr = gib_global_ptr_bumpalloc_heap_ptr;
    gib_global_ptr_saved_heap_ptr_stack[gib_global_ptr_num_saved_heap_ptr] = heap_ptr;
    gib_global_ptr_num_saved_heap_ptr++;
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("\n");
#endif
}

void gib_ptr_bumpalloc_restore_state(void)
{
    if(gib_global_ptr_num_saved_heap_ptr <= 0) {
        fprintf(stderr, "Bad call to gib_ptr_bumpalloc_restore_state!  Saved stack empty!\ne");
        exit(1);
    }
    gib_global_ptr_num_saved_heap_ptr--;
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Restoring(%p): pos %d, discarding %p",
           gib_global_ptr_saved_heap_ptr_stack[gib_global_ptr_num_saved_heap_ptr],
           gib_global_ptr_num_saved_heap_ptr,
           gib_global_ptr_bumpalloc_heap_ptr);
#endif
    gib_global_ptr_bumpalloc_heap_ptr =
        gib_global_ptr_saved_heap_ptr_stack[gib_global_ptr_num_saved_heap_ptr];
}

void *gib_alloc(size_t n) { return gib_ptr_bumpalloc(n); }
void gib_free(void *ptr) {}

#else // ifdef _GIBBON_BUMPALLOC_HEAP

void gib_ptr_bumpalloc_save_state(void) {}
void gib_ptr_bumpalloc_restore_state(void) {}

#ifndef _GIBBON_PARALLEL
// void *gib_alloc(size_t n) { return GC_MALLOC(n); }
// void gib_free(void *ptr) { GC_FREE(ptr); }
void *gib_alloc(size_t n) { return malloc(n); }
void gib_free(void *ptr) { free(ptr); }
#else // ifndef _GIBBON_PARALLEL
void *gib_alloc(size_t n) { return malloc(n); }
void gib_free(void *ptr) { free(ptr); }
#endif // ifndef _GIBBON_PARALLEL

#endif // ifdef _GIBBON_BUMPALLOC_HEAP

#else // ifdef _GIBBON_POINTER

void gib_ptr_bumpalloc_save_state(void) {}
void gib_ptr_bumpalloc_restore_state(void) {}

void *gib_alloc(size_t n) { return malloc(n); }
void gib_free(void *ptr) { free(ptr); }

#endif // ifdef _GIBBON_POINTER

// Could try alloca() here.  Better yet, we could keep our own,
// separate stack and insert our own code to restore the pointer
// before any function that (may have) called gib_scoped_alloc returns.
void *gib_scoped_alloc(size_t n) { return alloca(n); }

// Stack allocation is either too small or blows our stack.
// We need a way to make a giant stack if we want to use alloca.

// Our global pointer.  No parallelism.
// static char* stack_scoped_region;
// char* alloc_scoped() { return stack_scoped_region; }



/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Arenas
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

GibArena *gib_alloc_arena(void)
{
    GibArena *ar = gib_alloc(sizeof(GibArena));
    ar->ind = 0;
    ar->mem = (char *) gib_alloc(GIB_MAX_CHUNK_SIZE);
    ar->reflist = 0;
    return ar;
}

void gib_free_arena(GibArena *ar)
{
    gib_free(ar->mem);
    // TODO(vollmerm): free everything in ar->reflist
    gib_free(ar);
    return;
}

GibCursor gib_extend_arena(GibArena *ar, int size)
{
    GibCursor ret = ar->mem + ar->ind;
    ar->ind += size;
    return ret;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Arena-based dictionaries
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


GibSymDict *gib_dict_alloc(GibArena *ar)
{
    return (GibSymDict *) gib_extend_arena(ar, sizeof(GibSymDict));
}

GibSymDict *gib_dict_insert_ptr(GibArena *ar, GibSymDict *ptr, GibSym key, GibPtr val)
{
    GibSymDict *ret = gib_dict_alloc(ar);
    ret->key = key;
    ret->ptrval = val;
    ret->next = ptr;
    return ret;
}

GibPtr gib_dict_lookup_ptr(GibSymDict *ptr, GibSym key)
{
    while (ptr != 0) {
        if (ptr->key == key) {
            return ptr->ptrval;
        } else {
            ptr = ptr->next;
        }
    }
    fprintf(stderr, "Error, key %" PRId64 " not found!\n",key);
    exit(1);
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Sets
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


GibSymSet *gib_empty_set(void)
{
    return (GibSymSet *) NULL;
}

GibSymSet *gib_insert_set(GibSymSet *set, int sym)
{
    GibSymSet *s;
    HASH_FIND_INT(set, &sym, s);  /* sym already in the hash? */
    if (s==NULL) {
        s = (GibSymSet *) gib_alloc(sizeof(GibSymSet));
        s->val = sym;
        HASH_ADD_INT(set,val,s);
    }
    return set;
}

GibBool gib_contains_set(GibSymSet *set, int sym)
{
    GibSymSet *s;
    HASH_FIND_INT(set, &sym, s);
    return (s!=NULL);
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Sym Hash
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


GibSymHash *gib_empty_hash(void)
{
    return (GibSymHash *) NULL;
}

GibSymHash *gib_insert_hash(GibSymHash *hash, int k, int v)
{
    GibSymHash *s;
    // NOTE: not checking for duplicates!
    s = (GibSymHash *) gib_alloc(sizeof(GibSymHash));
    s->val = v;
    s->key = k;
    HASH_ADD_INT(hash,key,s);

    return hash;
}

GibSym gib_lookup_hash(GibSymHash *hash, int k)
{
    GibSymHash *s;
    HASH_FIND_INT(hash,&k,s);
    if (s==NULL) {
        return k; // NOTE: return original key if val not found
        // TODO(vollmerm): come up with something better to do here
    } else {
        return s->val;
    }
}

GibBool gib_contains_hash(GibSymHash *hash, int sym)
{
    GibSymHash *s;
    HASH_FIND_INT(hash,&sym,s);
    return (s!=NULL);
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Symbol table
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

static GibSym newline_symbol = -1;
static GibSym space_symbol = -1;
static GibSym comma_symbol = -1;
static GibSym leftparen_symbol = -1;
static GibSym rightparen_symbol = -1;


// important! initialize to NULL
static GibSymtable *global_sym_table = (GibSymtable *) NULL;

void gib_add_symbol(GibSym idx, char *value)
{
    GibSymtable *s;
    s = (GibSymtable *) gib_alloc(sizeof(GibSymtable));
    s->idx = idx;
    strcpy(s->value, value);
    HASH_ADD(hh, global_sym_table, idx, sizeof(GibSym), s);
    if (idx > gib_global_gensym_counter) {
        gib_global_gensym_counter = idx;
    }
    return;
}

void gib_set_newline(GibSym idx)
{
    newline_symbol = idx;
    gib_add_symbol(idx,"NEWLINE");
    return;
}

void gib_set_space(GibSym idx)
{
    space_symbol = idx;
    gib_add_symbol(idx,"SPACE");
    return;
}

void gib_set_comma(GibSym idx)
{
    comma_symbol = idx;
    gib_add_symbol(idx,"COMMA");
    return;
}

void gib_set_leftparen(GibSym idx)
{
    leftparen_symbol = idx;
    gib_add_symbol(idx,"LEFTPAREN");
    return;
}

void gib_set_rightparen(GibSym idx)
{
    rightparen_symbol = idx;
    gib_add_symbol(idx,"RIGHTPAREN");
    return;
}

int gib_print_symbol(GibSym idx)
{
    if (idx == comma_symbol) {
        return printf(",");
    } else if (idx == newline_symbol) {
        return printf("\n");
    } else if (idx == space_symbol) {
        return printf(" ");
    } else if (idx == leftparen_symbol) {
        return printf("(");
    } else if (idx == rightparen_symbol) {
        return printf(")");
    } else {
        GibSymtable *s;
        HASH_FIND(hh, global_sym_table, &idx, sizeof(GibSym), s);
        if (s == NULL) {
            return printf("%" PRIu64, idx);
        } else {
            return printf("%s", s->value);
        }

    }
}

GibSym gib_gensym(void)
{
    GibSym idx;
#ifdef _GIBBON_PARALLEL
    idx = __atomic_add_fetch(&gib_global_gensym_counter, 1, __ATOMIC_SEQ_CST);
#else
    gib_global_gensym_counter += 1;
    idx = gib_global_gensym_counter;
#endif
    return idx;
}


void gib_free_symtable(void)
{
    GibSymtable *elt, *tmp;
    HASH_ITER(hh, global_sym_table, elt, tmp) {
        HASH_DEL(global_sym_table,elt);
        gib_free(elt);
    }
    return;
}


GibCursor *gib_array_alloc(GibCursor *arr, size_t size)
{

    GibCursor *arr_on_heap = (GibCursor *) malloc(sizeof(GibCursor) * size);
    if (arr_on_heap == NULL) {
        fprintf(stderr, "gib_array_alloc: malloc failed: %zu", sizeof(GibCursor) * size);
        exit(1);
    }

    GIB_PRAGMA_UNROLL(2)
    for (size_t i = 0; i < size; i++){
        arr_on_heap[i] = arr[i];
    }

    return arr_on_heap;
}



/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Vectors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

GibVector *gib_vector_alloc(int64_t num, size_t elt_size)
{
    GibVector *vec = (GibVector *) gib_alloc(sizeof(GibVector));
    if (vec == NULL) {
        fprintf(stderr, "alloc_vector: gib_alloc failed: %zu", sizeof(GibVector));
        exit(1);
    }
    void *data = (void *) gib_alloc(num * elt_size);
    if (data == NULL) {
        fprintf(stderr, "alloc_vector: gib_alloc failed: %zu", sizeof(num * elt_size));
        exit(1);
    }
    vec->lower = 0;
    vec->upper = num;
    vec->elt_size = elt_size;
    vec->data = data;
    return vec;
}

int64_t gib_vector_length(GibVector *vec)
{
    return (vec->upper - vec->lower);
}

GibBool gib_vector_is_empty(GibVector *vec)
{
    return (gib_vector_length(vec) == 0);
}

GibVector *gib_vector_slice(int64_t i, int64_t n, GibVector *vec)
{
#ifdef _GIBBON_BOUNDSCHECK
    // See Note [GibVector range and indexing contract].  `i` is relative and
    // the range is half-open, so a negative offset or length places `lower`
    // before `data` (or `upper` before `lower`), and every later
    // gib_vector_nth on the result computes an address outside the allocation.
    // The two checks below only ever tested the upper direction.
    //
    // This is deliberately INSIDE the opt-in check rather than unconditional.
    // `VfyAbiNegSlice.hs` and `VfyAbiNegSliceUpper.hs` pass negative arguments
    // here on purpose: they are ABI probes that assert a negative index still
    // arrives as int64 (-1, not 4294967295), and they read back the resulting
    // nonsensical length (2 and -2).  Rejecting negative slices in the default
    // build would break those probes, and whether Gibbon should reject them at
    // all is a separate decision from the vector indexing contract below.
    if (i < 0 || n < 0) {
        fprintf(stderr, "gib_vector_slice: negative offset or length, i=%" PRId64
                " n=%" PRId64 "\n", i, n);
        exit(1);
    }
#endif
    int64_t lower = vec->lower + i;
    int64_t upper = vec->lower + i + n;
    if ((lower > vec->upper)) {
        fprintf(stderr, "gib_vector_slice: lower out of bounds, %" PRId64
                " > %" PRId64, lower, vec->upper);
        exit(1);
    }
    if ((upper > vec->upper)) {
        fprintf(stderr, "gib_vector_slice: upper out of bounds, %" PRId64
                " > %" PRId64, upper, vec->upper);
        exit(1);
    }
    GibVector *vec2 = (GibVector *) gib_alloc(sizeof(GibVector));
    if (vec == NULL) {
        fprintf(stderr, "gib_vector_slice: gib_alloc failed: %zu", sizeof(GibVector));
        exit(1);
    }
    vec2->lower = lower;
    vec2->upper = upper;
    vec2->elt_size = vec->elt_size;
    vec2->data = vec->data;
    return vec2;
}

/*
 * Note [GibVector range and indexing contract]
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Established by direct probe, not by reading code:
 *
 *   - `lower` and `upper` are ABSOLUTE element indices into `data`, and the
 *     range is HALF-OPEN: [lower, upper).  Hence
 *     gib_vector_length(v) == v->upper - v->lower, and gib_vector_alloc(n)
 *     yields lower = 0, upper = n.
 *   - The `i` passed to gib_vector_nth is RELATIVE to the vector/slice, not
 *     absolute.  For `s = gib_vector_slice(3, 3, v)` (lower=3, upper=6),
 *     `gib_vector_nth(s, 0)` returns v's element 3.  Measured, not assumed.
 *   - Therefore the valid indices are exactly 0 .. length-1, for a slice
 *     exactly as for an unsliced vector, and the backing address is
 *     data + elt_size * (lower + i).
 *   - A zero-length vector has no valid index.  gib_vector_alloc(0) and an
 *     empty slice at the end (lower == upper) are both legal.
 *
 * The bounds check below was previously dead code AND wrong twice over.  It
 * could never be compiled (`stdderr`), and its predicate
 * `i < vec->lower || i > vec->upper` compared a RELATIVE index against
 * ABSOLUTE bounds.  On the slice above it REJECTED the valid indices 0,1,2 and
 * ACCEPTED the invalid 3,4,5,6; even on an unsliced vector it accepted
 * `i == upper`, one past the end.  Changing `>` to `>=` would not have fixed
 * it -- the relative/absolute confusion had to be resolved first.
 *
 * Enabling this check is opt-in (`make ... BOUNDSCHECK=1`, i.e.
 * -D_GIBBON_BOUNDSCHECK) because it costs a branch on every element access.
 * Without it, an out-of-range index is silent memory corruption: the returned
 * pointer is outside the allocation, and gib_vector_inplace_update writes
 * through it, so the failure surfaces later and elsewhere -- typically as
 * `malloc(): corrupted top size` at an unrelated allocation.
 */
// The callers must cast the return value.
void *gib_vector_nth(GibVector *vec, int64_t i)
{
#ifdef _GIBBON_BOUNDSCHECK
    // Half-open, relative.  Checked BEFORE the address arithmetic below, so
    // `vec->lower + i` cannot overflow on a rejected index.
    int64_t gib_vec_len = vec->upper - vec->lower;
    if (i < 0 || i >= gib_vec_len) {
        fprintf(stderr,
                "gib_vector_nth: index out of bounds: %" PRId64
                " not in [0, %" PRId64 ") "
                "(slice [%" PRId64 ", %" PRId64 "), elt_size %zu)\n",
                i, gib_vec_len, vec->lower, vec->upper, vec->elt_size);
        exit(1);
    }
#endif
    return ((char*)vec->data + (vec->elt_size * (vec->lower + i)));
}

GibVector *gib_vector_inplace_update(GibVector *vec, int64_t i, void* elt)
{
    void* dst = gib_vector_nth(vec, i);
    memcpy(dst, elt, vec->elt_size);
    return vec;
}

GibVector *gib_vector_copy(GibVector *vec)
{
    int64_t len = gib_vector_length(vec);
    void *start = gib_vector_nth(vec, 0);
    GibVector *vec2 = gib_vector_alloc(len, vec->elt_size);
    memcpy(vec2->data, start, len * vec->elt_size);
    return vec2;
}

GibVector *gib_vector_inplace_sort(GibVector *vec, int (*compar)(const void *, const void*))
{
    void *start = gib_vector_nth(vec, 0);
    qsort(start, gib_vector_length(vec), vec->elt_size, compar);
    return vec;
}

GibVector *gib_vector_sort(GibVector *vec, int (*compar)(const void *, const void*))
{
    GibVector *vec2 = gib_vector_copy(vec);
    gib_vector_inplace_sort(vec2, compar);
    return vec2;
}

GibVector *gib_vector_concat(GibVector *vec)
{
    // Length of the input vector.
    int64_t len = gib_vector_length(vec);
    // Length of the concatenated vector.
    int64_t result_len = 0;
    // Size of each element in the concatenated vector.
    int64_t result_elt_size = 0;
    GibVector **elt_ref, *elt;
    for (int64_t i = 0; i < len; i++) {
        elt_ref = gib_vector_nth(vec, i);
        elt = *elt_ref;
        result_elt_size = elt->elt_size;
        result_len += gib_vector_length(elt);
    }

    // Concatenated vector.
    GibVector *result = gib_vector_alloc(result_len, result_elt_size);
    int64_t elt_len;
    // A counter that tracks the index of elements in 'result'.
    int64_t k = 0;
    for (int64_t i = 0; i < len; i++) {
        elt_ref = gib_vector_nth(vec, i);
        elt = *elt_ref;
        elt_len = gib_vector_length(elt);

        for (int64_t j = 0; j < elt_len; j++) {
            void* k_elt = gib_vector_nth(elt, j);
            gib_vector_inplace_update(result, k, k_elt);
            k++;
        }
    }

    return result;
}

void gib_vector_free(GibVector *vec)
{
    gib_free(vec->data);
    gib_free(vec);
    return;
}

GibVector *gib_vector_merge(GibVector *vec1, GibVector *vec2)
{
    if (vec1->upper != vec2->lower) {
        fprintf(stderr,"gib_vector_merge: non-contiguous slices, (%" PRId64
                ",%" PRId64 "), (%" PRId64 ",%" PRId64 ")",
               vec1->lower, vec1->upper, vec2->lower, vec2->upper);
        exit(1);
    }
    GibVector *merged = (GibVector *) gib_alloc(sizeof(GibVector));
    if (merged == NULL) {
        fprintf(stderr, "gib_vector_merge: gib_alloc failed: %zu", sizeof(GibVector));
        exit(1);
    }
    merged->lower = vec1->lower;
    merged->upper = vec2->upper;
    merged->elt_size = vec1->elt_size;
    merged->data = vec1->data;
    return merged;
}

void gib_print_timing_array(GibVector *times) {
    printf("ITER TIMES: [");
    double *d;
    int64_t n = gib_vector_length(times);
    for(int64_t i = 0; i < n; i++) {
        d = gib_vector_nth(times, i);
        if (i == (n-1)) {
            printf("%f",*d);
        }
        else {
            printf("%f, ",*d);
        }
    }
    printf("]\n");
    return;
}

double gib_sum_timing_array(GibVector *times)
{
    double *d;
    double acc = 0;
    for(int i = 0; i < gib_vector_length(times); i++) {
        d = gib_vector_nth(times, i);
        acc += *d;
    }
    return acc;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Linked lists
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


#ifdef _GIBBON_BUMPALLOC_LISTS
// #define _GIBBON_DEBUG
GIB_PRAGMA_MESSAGE("Using bump allocator.")

static __thread char *gib_global_list_bumpalloc_heap_ptr = (char *) NULL;
static __thread char *gib_global_list_bumpalloc_heap_ptr_end = (char *) NULL;
static char *gib_global_list_saved_heap_ptr_stack[100];
static int gib_global_list_num_saved_heap_ptr = 0;

// For simplicity just use a single large slab:
void gib_init_list_bumpalloc(void)
{
    gib_global_list_bumpalloc_heap_ptr =
        (char*) gib_alloc(gib_global_biginf_init_chunk_size);
    gib_global_list_bumpalloc_heap_ptr_end =
        gib_global_list_bumpalloc_heap_ptr + gib_global_biginf_init_chunk_size;
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Arena size for bump alloc: %zu\n", gib_global_biginf_init_chunk_size);
    printf("gib_init_list_bumpalloc DONE: heap_ptr = %p\n",
           gib_global_list_bumpalloc_heap_ptr);
#endif
}

void *gib_list_bumpalloc(size_t n)
{
    if (! gib_global_list_bumpalloc_heap_ptr) {
        gib_init_list_bumpalloc();
    }
    if (gib_global_list_bumpalloc_heap_ptr + n <
        gib_global_list_bumpalloc_heap_ptr_end) {
        char* old= gib_global_list_bumpalloc_heap_ptr;
        gib_global_list_bumpalloc_heap_ptr += n;
        return old;
    } else {
        fprintf(stderr, "Warning: bump allocator ran out of memory.");
        exit(1);
    }
}

// Snapshot the current heap pointer value across all threads.
void gib_list_bumpalloc_save_state(void)
{
    char *heap_ptr = gib_global_list_bumpalloc_heap_ptr;
    gib_global_list_saved_heap_ptr_stack[gib_global_list_num_saved_heap_ptr] = heap_ptr;
    gib_global_list_num_saved_heap_ptr++;
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Saved(%p): pos %d\n", heap_ptr, gib_global_list_num_saved_heap_ptr);
    printf("\n");
#endif
}

void gib_list_bumpalloc_restore_state(void)
{
    if(gib_global_list_num_saved_heap_ptr <= 0) {
        fprintf(stderr, "Bad call to gib_list_bumpalloc_restore_state!  Saved stack empty!\ne");
        exit(1);
    }
    gib_global_list_num_saved_heap_ptr--;
    gib_global_list_bumpalloc_heap_ptr =
        gib_global_list_saved_heap_ptr_stack[gib_global_list_num_saved_heap_ptr];
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Restored(%p): pos %d, discarding %p",
           gib_global_list_saved_heap_ptr_stack[gib_global_list_num_saved_heap_ptr],
           gib_global_list_num_saved_heap_ptr,
           gib_global_list_bumpalloc_heap_ptr);
#endif
}

#else
// Regular malloc mode:
void gib_init_list_bumpalloc(void) {}
void *gib_list_bumpalloc(size_t n) { return gib_alloc(n); }
void gib_list_bumpalloc_save_state(void) {}
void gib_list_bumpalloc_restore_state(void) {}

#endif // _GIBBON_BUMPALLOC_LISTS


// List API.

GibList *gib_list_alloc(size_t data_size)
{
    // GibList *ls = gib_alloc(sizeof(GibList));
    GibList *ls = gib_list_bumpalloc(sizeof(GibList));
    ls->data_size = data_size;
    ls->data = (void *) NULL;
    ls->next = (GibList *) NULL;
    return ls;
}

GibBool gib_list_is_empty(GibList *ls)
{
    return ls->next == NULL;
}

GibList *gib_list_cons(void *elt, GibList *ls)
{
    // void* data = gib_alloc(ls->data_size);
    void* data = gib_list_bumpalloc(ls->data_size);
    if (data == NULL) {
        fprintf(stderr, "gib_list_cons: gib_alloc failed: %zu", ls->data_size);
        exit(1);
    }
    memcpy(data, elt, ls->data_size);
    // GibList *res = gib_alloc(sizeof(GibList));
    GibList *res = gib_list_bumpalloc(sizeof(GibList));
    res->data_size = ls->data_size;
    res->data = data;
    res->next = (GibList*) ls;
    return res;
}

void *gib_list_head(GibList *ls)
{
    return ls->data;
}

GibList* gib_list_tail(GibList *ls)
{
    return ls->next;
}

void gib_list_free(GibList *ls)
{
    gib_free(ls->data);
    gib_free(ls);
    return;
}

GibList *gib_list_copy(GibList *ls)
{
    GibList *ls2 = gib_list_alloc(ls->data_size);
    if (ls->data != NULL) {
        void* data = gib_list_bumpalloc(ls->data_size);
        memcpy(data, ls->data, ls->data_size);
        ls2->data = data;
    }
    ls2->next = ls->next;
    return ls2;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ppm images
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Example: writePpm("gibbon_rgb_1000.ppm", 1000, 1000, pixels);
void gib_write_ppm(char* filename, int64_t width, int64_t height, GibVector *pixels)
{
    FILE *fp;
    fp = fopen(filename, "w+");
    fprintf(fp, "P3\n");
    // fprintf(fp, "%lld %lld\n255\n", width, height);
    fprintf(fp, "%" PRId64 " %" PRId64 "\n255\n", width, height);
    int64_t len = gib_vector_length(pixels);
    gib_write_ppm_loop(fp, 0, len, pixels);
    fclose(fp);
    return;
}

void gib_write_ppm_loop(FILE *fp, int64_t idx, int64_t end, GibVector *pixels)
{
    bool fltIf_5768_6575 = idx == end;

    if (fltIf_5768_6575) {
        return;
    } else {
        GibPixel *tmp_112;
        tmp_112 = (GibPixel *) gib_vector_nth(pixels, idx);
        GibPixel tup = *tmp_112;
        int64_t x = tup.field0;
        int64_t y = tup.field1;
        int64_t z = tup.field2;
        // write to file.
        // fprintf(fp, "%lld %lld %lld\n", x, y, z);
        fprintf(fp, "%" PRId64 " %" PRId64 " %" PRId64 "\n", x, y, z);
        gib_write_ppm_loop(fp, (idx+1), end, pixels);
    }
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Threads and parallelism
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Whether a thread is blocked on GC.
bool gib_global_thread_requested_gc = false;

// Number of threads a.k.a. cilk workers.
uint64_t gib_global_num_threads = 1;


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Memory Management; regions, chunks, GC etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/*

  Gibbon has "growing regions" i.e each logical region is backed by a singly
  linked-list of smaller chunks which grows as required. In addition to actual
  data, each chunk stores some additional metadata (GibOldgenChunkFooter) to chain
  the chunks together in a list and for garbage collection. The footer:

  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  data | reg_info | size | next
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  The metadata after the serialized data serves various purposes:

  - reg_info: A pointer to a GibRegionInfo struct that contains
  various metadata. Of particular interest to us are the fields:

  = id: A unique identifier for a region.

  = refcount and outset: Whenever an inter-region indirection is created, we
    record that information using these two fields. Suppose we have an
    indirection from region A that points to some chunk in region B. Then A's
    outset will store a pointer to that chunk's footer, and B's refcount will
    be bumped by 1. Note that all there's only 1 refcount cell, and 1 outset
    per logical region, and chunks only store a pointer to them.

  = first_chunk_footer: Address of the first chunk in this region;
    used to garbage collect the linked-list of chunks.

  - size: Used during bounds checking to calculate the size of the next
    region in the linked list.

  - next: Pointer to the next chunk's footer.


  There are two ways in which a region may be freed:

  (1) Whenever it goes out of scope

  The RTS tries to free a region whenever it goes out of scope. But this doesn't
  always succeed as regions sometimes contain values that "escape". One reason
  why this'll happen is if there's an indirection from A->B, and A lives longer
  than B. In such a case, when B goes out of scope it's refcount won't be 0,
  and the RTS won't free it. This brings us to (2).

  (2)

  When the RTS successfully frees a region, it decrements the refcounts of all
  the regions it points to (via the outset). At the same time, if it encounters
  a region in the outset whoose refcount becomes 0 after the decrement, it
  calls gib_free_region on that. This way we can be sure that all regions will
  eventually be garbage collected before the program exits.


*/


// If a region is over this size, alloc to refcounted heap directly.
static size_t gib_nursery_size = GIB_NURSERY_SIZE;
static size_t gib_nursery_region_max_size = (GIB_NURSERY_SIZE / 2);


// Whether storage is initialized or not.
bool gib_storage_initialized = false;

// Array of nurseries, indexed by thread_id.
GibNursery *gib_global_nurseries = (GibNursery *) NULL;
// Old generation.
GibOldgen *gib_global_oldgen = (GibOldgen *) NULL;

// Shadow stacks for readable and writeable locations respectively,
// indexed by thread_id.
//
// TODO: not clear how shadow stacks would be when we have
// parallel mutators.. These arrays are abstract enough for now.
GibShadowstack *gib_global_read_shadowstacks = (GibShadowstack *) NULL;
GibShadowstack *gib_global_write_shadowstacks = (GibShadowstack *) NULL;

// Collect GC statistics.
GibGcStats *gib_global_gc_stats = (GibGcStats *) NULL;



/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ensure that C and Rust agree on sizes
 * of structs that cross the boundary.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
void gib_check_rust_struct_sizes(void)
{
    // Sizes in the Rust RTS.
    size_t *stack, *frame, *nursery, *generation, *reg_info, *footer, *gc_stats;
    stack = (size_t *) gib_alloc(sizeof(size_t) * 7);
    frame = (size_t *) ((char *) stack + sizeof(size_t));
    nursery = (size_t *) ((char *) frame + sizeof(size_t));
    generation = (size_t *) ((char *) nursery + sizeof(size_t));
    reg_info = (size_t *) ((char *) generation + sizeof(size_t));
    footer = (size_t *) ((char *) reg_info + sizeof(size_t));
    gc_stats = (size_t *) ((char *) footer + sizeof(size_t));
    gib_get_rust_struct_sizes(stack, frame, nursery, generation, reg_info, footer, gc_stats);

    // Check if they match with sizes in the C RTS.
    assert(*stack == sizeof(GibShadowstack));
    assert(*frame == sizeof(GibShadowstackFrame));
    assert(*nursery == sizeof(GibNursery));
    assert(*generation == sizeof(GibOldgen));
    assert(*reg_info == sizeof(GibRegionInfo));
    assert(*footer == sizeof(GibOldgenChunkFooter));
    assert(*gc_stats == sizeof(GibGcStats));

    // Done.
    gib_free(stack);

    return;
}

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Print GC configuration
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


void gib_print_gc_config(void) {
    printf("Rust config\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    fflush(stdout);
    gib_print_rust_gc_config();
    fflush(stdout);
    printf("\n");


    printf("C config\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");

#if defined _GIBBON_GENGC && _GIBBON_GENGC == 0
    GIB_PRAGMA_MESSAGE("Generational GC is disabled.")
    printf("Generational GC is disabled.\n");
#else
    GIB_PRAGMA_MESSAGE("Generational GC is enabled.")
    printf("Generational GC is enabled.\n");
#endif

#if defined _GIBBON_EAGER_PROMOTION && _GIBBON_EAGER_PROMOTION == 0
    GIB_PRAGMA_MESSAGE("Eager promotion is disabled.")
    printf("Eager promotion is disabled.\n");
#else
    GIB_PRAGMA_MESSAGE("Eager promotion is enabled.")
    printf("Eager promotion is enabled.\n");
#endif

#if defined _GIBBON_SIMPLE_WRITE_BARRIER && _GIBBON_SIMPLE_WRITE_BARRIER == 0
    GIB_PRAGMA_MESSAGE("Simple write barrier is disabled.")
    printf("Simple write barrier is disabled.\n");
#else
    GIB_PRAGMA_MESSAGE("Simple write barrier is enabled.")
    printf("Simple write barrier is enabled.\n");
#endif

    printf("Nursery size=%zu\n", (size_t) gib_nursery_size);
    printf("Max chunk size=%zu\n", (size_t) GIB_MAX_CHUNK_SIZE);
    printf("Initial chunk size=%zu\n", (size_t) GIB_INIT_CHUNK_SIZE);
    printf("\n");
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Region allocation and growth
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

STATIC_INLINE void gib_perform_GC_(bool force_major);

/*
 * ~~~~~~~~~~~~~~~~~~~~
 * Region allocation
 * ~~~~~~~~~~~~~~~~~~~~
 */

GibChunk gib_alloc_region(size_t size);
STATIC_INLINE GibChunk gib_alloc_region_in_nursery_fast(size_t size, bool collected);
static GibChunk gib_alloc_region_in_nursery_slow(size_t size, bool collected);
GibChunk gib_alloc_region_on_heap(size_t size);


GibChunk gib_alloc_region(size_t size)
{
    return gib_alloc_region_in_nursery_fast(size, false);
}

STATIC_INLINE GibChunk gib_alloc_region_in_nursery_fast(size_t size, bool collected)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    char *old = nursery->alloc;
    char *bump = old - size - sizeof(GibNurseryChunkFooter);
    if (LIKELY((bump >= nursery->heap_start))) {

#ifdef _GIBBON_GCSTATS
        GC_STATS->nursery_regions++;
        GC_STATS->mem_allocated_in_nursery += size;
#endif
        nursery->alloc = bump;
        char *footer = old - sizeof(GibNurseryChunkFooter);
        GibNurseryChunkFooter *nursery_footer = (GibNurseryChunkFooter *) footer;
        nursery_footer->size = size;
        gib_scalar_count_footer_init(&nursery_footer->scalar_counts);

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
        fprintf(stderr, "Allocated a nursery chunk of size %ld, (%p, %p).\n",
                size, bump, footer);
#endif

        return (GibChunk) {bump, footer};
    } else {
        return gib_alloc_region_in_nursery_slow(size, collected);
    }
}

static GibChunk gib_alloc_region_in_nursery_slow(size_t size, bool collected)
{
    if (UNLIKELY((size > gib_nursery_region_max_size))) {
        return gib_alloc_region_on_heap(size);
    }
    if (collected) {
        fprintf(stderr, "Couldn't free space after garbage collection.\n");
        exit(1);
    }

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    fprintf(stderr, "Performing a minor collection.\n");
    fflush(stderr);
#endif

    gib_perform_GC_(false);

    return gib_alloc_region_in_nursery_fast(size, true);
}

// GibChunk gib_alloc_region_on_heap(size_t size)
// {
//     size_t size_aligned = gib_align_up_sz(size, GIB_PTR_ALIGN);
// char *heap_start = gib_alloc(size_aligned);
// if (heap_start == NULL) {
//     fprintf(stderr, "gib_alloc_region_on_heap: gib_alloc failed: %zu", size_aligned);
//     exit(1);
// }
// char *heap_end = heap_start + size_aligned;
// char *footer_start = gib_init_footer_at(heap_end, size_aligned, 1);
// #ifdef _GIBBON_GCSTATS
//     GC_STATS->oldgen_regions++;
//     GC_STATS->mem_allocated_in_oldgen += size;
// #endif
//
// #if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
//         fprintf(stderr, "Allocated a oldgen chunk of size %ld, (%p, %p).\n",
//                 size, heap_start, footer_start);
// #endif
//
//     return (GibChunk) {heap_start, footer_start};
// }

GibChunk gib_alloc_region_on_heap(size_t size)
{
    size_t size_aligned = gib_align_up_sz(size, GIB_PTR_ALIGN);

    char *heap_start = (char *) gib_alloc(size_aligned);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_alloc_region_on_heap: gib_alloc failed: %zu", size_aligned);
        exit(1);
    }

    char *heap_end = heap_start + size_aligned;

    // IMPORTANT: pass size_aligned consistently.
    char *footer_start = gib_init_footer_at(heap_end, size_aligned, 1);

    return (GibChunk) {heap_start, footer_start};
}


/*
 * ~~~~~~~~~~~~~~~~~~~~
 * Region growth
 * ~~~~~~~~~~~~~~~~~~~~
 */

void gib_grow_region_noinline(char **writeloc_addr, char **footer_addr)
{
    gib_grow_region(writeloc_addr, footer_addr);
    return;
}

void gib_grow_region_in_nursery_slow(
    bool collected,
    bool old_chunk_in_nursery,
    size_t size,
    GibOldgenChunkFooter *old_footer,
    char **writeloc_addr,
    char **footer_addr
) {
    // TODO: grow the nursery up to an upper bound?
    if (size > gib_nursery_region_max_size) {
        gib_grow_region_on_heap(
            old_chunk_in_nursery,
            size,
            old_footer,
            writeloc_addr,
            footer_addr
        );
        return;
    }

    if (collected) {
        fprintf(stderr, "Couldn't free space after garbage collection.\n");
        exit(1);
    }

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    fprintf(stderr, "Performing a minor collection.\n");
    fflush(stderr);
#endif

    gib_perform_GC_(false);

    gib_grow_region_in_nursery_fast(
        true,
        old_chunk_in_nursery,
        size,
        old_footer,
        writeloc_addr,
        footer_addr
    );
}


/*
 * ~~~~~~~~~~~~~~~~~~~~
 * Other stuff
 * ~~~~~~~~~~~~~~~~~~~~
 */

void gib_free_region(char *footer_ptr)
{
    if (gib_addr_in_nursery(footer_ptr)) {
        return;
    }
    GibOldgenChunkFooter *footer = (GibOldgenChunkFooter *) footer_ptr;
    if ((footer->reg_info)->refcount == 1) {
        (footer->reg_info)->refcount--;
        gib_free_region_(footer);
    }
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Region chunk log
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * Reclaims the chunks a benchmark iteration grew.  See the declarations in
 * gibbon_rts.h for why they leak without this.
 *
 * Shape deliberately mirrors gib_list_bumpalloc_save_state/_restore_state: a
 * no-argument checkpoint/rollback pair over a saved stack, called from the same
 * two guarded blocks of the generated `iterate` loop.
 *
 * Two properties this file must not lose:
 *
 *   1. Logging happens ONLY while a bracket is open (depth > 0).  Chunks grown
 *      before the loop -- notably the whole input value, which for List.hs is a
 *      100M-element list -- are therefore never logged and can never be freed.
 *      This is what makes the scheme safe without any per-region bookkeeping.
 *
 *   2. `restore_state` frees in BULK, at the end of an iteration.  That is not
 *      an optimisation, it is a correctness property OF THE MEASUREMENT.
 *      Measured: freeing each stale chunk just before allocating its
 *      replacement leaves the pages resident and the next iteration takes 0
 *      page faults, silently making iterations 2..n warm and the reported
 *      times optimistic.  Freeing in bulk lets the allocator return the pages,
 *      so the next iteration re-faults exactly as it does today (7966 faults in
 *      the same test).  Per-iteration timings must be UNCHANGED by this
 *      feature; a speedup means fidelity was lost.
 *
 * Thread-local, matching the bump-allocator globals above.  A chunk grown on a
 * worker thread is logged in that thread's log and simply not reclaimed, rather
 * than being freed from a thread that does not own it.
 */

#if _GIBBON_REGIONRESET

// The log holds the chunk BASES, exactly as gib_alloc returned them, so
// nothing has to reconstruct a base from a footer address later.
// Defined with the scalar-count machinery further down.  Freeing a chunk
// invalidates any cached pointer INTO that chunk, and the scalar-count layer
// keeps two of them (`current_footer` and `write_footer`, see
// GibScalarCountRegionState).  Those are per-iteration derived state and have
// to be rewound along with the write cursors, or the next iteration writes
// through a dangling pointer -- a heap-use-after-free inside
// gib_scalar_count_footer_set, reachable from any loopified SoA map.
static void gib_scalar_count_forget_region_states(void);

static char **gib_global_chunk_log = (char **) NULL;
static size_t gib_global_chunk_log_len = 0;
static size_t gib_global_chunk_log_cap = 0;
static size_t gib_global_chunk_log_marks[GIB_CHUNK_LOG_MAX_DEPTH];
static int gib_global_chunk_log_depth = 0;

static void gib_region_chunk_log(char *chunk_start)
{
    // Inert unless an iteration bracket is open.  Every non-benchmark program,
    // and every allocation outside the timed loop, takes this branch.
    if (gib_global_chunk_log_depth <= 0) {
        return;
    }
    if (gib_global_chunk_log_len == gib_global_chunk_log_cap) {
        size_t newcap = (gib_global_chunk_log_cap == 0)
                        ? GIB_CHUNK_LOG_INIT_CAP
                        : (gib_global_chunk_log_cap * 2);
        char **grown = (char **) realloc(gib_global_chunk_log,
                                         newcap * sizeof(char *));
        // Best effort: a failure here costs us the reclaim of this one chunk,
        // which is the pre-existing behaviour.  It must never fail the program.
        if (grown == NULL) {
            return;
        }
        gib_global_chunk_log = grown;
        gib_global_chunk_log_cap = newcap;
    }
    gib_global_chunk_log[gib_global_chunk_log_len] = chunk_start;
    gib_global_chunk_log_len++;
}

// noinline in BOTH configurations, deliberately.  The program is built with
// -flto (Common.hs: optc = " -O3  -flto "), so without this the linker inlines
// the trivial feature-off wrapper but not the logging one, and whole-program
// optimisation then differs by build flag.  Measured on a 10M-element SoA list:
// identical instruction counts and FEWER cache misses, yet IPC fell 3.70 -> 2.99
// and folds over the map's output went 0.0048s -> 0.0135s.  An opaque call in
// both cases keeps the generated code independent of the setting.
GIB_NOINLINE __attribute__((malloc))
void *gib_region_chunk_alloc(size_t size)
{
    void *p = gib_alloc(size);
    if (p != NULL) {
        gib_region_chunk_log((char *) p);
    }
    return p;
}

GIB_NOINLINE
void gib_region_chunk_save_state(void)
{
    if (gib_global_chunk_log_depth >= GIB_CHUNK_LOG_MAX_DEPTH) {
        fprintf(stderr,
                "Bad call to gib_region_chunk_save_state! Saved stack full!\n");
        exit(1);
    }
    gib_global_chunk_log_marks[gib_global_chunk_log_depth] =
        gib_global_chunk_log_len;
    gib_global_chunk_log_depth++;
}

GIB_NOINLINE
void gib_region_chunk_restore_state(void)
{
    if (gib_global_chunk_log_depth <= 0) {
        fprintf(stderr,
                "Bad call to gib_region_chunk_restore_state! Saved stack empty!\n");
        exit(1);
    }
    gib_global_chunk_log_depth--;
    size_t mark = gib_global_chunk_log_marks[gib_global_chunk_log_depth];
    // Plain free, in bulk.  Deliberately nothing more: the allocator handing
    // these pages straight back to the next iteration is what a real program
    // doing n back-to-back maps also experiences, so forcing them out (with
    // madvise, say) would model nothing and would only make the benchmark
    // artificially slow.
    //
    // What must NOT happen is chunks being reused WITHOUT a free cycle --
    // rewinding and overwriting them in place leaves the data resident and
    // skips work a cold run genuinely pays.  That is why growth still
    // allocates normally and this only releases.
    bool freed_any = gib_global_chunk_log_len > mark;
    // Freed in REVERSE allocation order, which is load-bearing for the SPEED
    // of whatever traverses the result next, not just for tidiness.
    //
    // The allocator hands freed blocks back most-recently-freed-first.  Freeing
    // ascending therefore makes the next iteration re-allocate DESCENDING, so
    // the rebuilt value runs backwards through memory and every traversal of it
    // walks against the prefetcher.  Measured on a 10M-element SoA list, folds
    // over the map's output went 0.0047s -> 0.0142s, a 3x regression, while the
    // map itself got faster -- the sort of asymmetry that looks like a layout
    // win/loss in the tables and is really an allocator artifact.
    for (size_t i = gib_global_chunk_log_len; i > mark; i--) {
        gib_free(gib_global_chunk_log[i - 1]);
    }
    if (freed_any) {
        // MUST accompany the frees.  The scalar-count states are keyed by
        // GibRegionInfo, which outlives the chunks, so a stale entry is found
        // again on the next iteration and written through -- into memory we
        // just released.  They are rebuilt lazily from live footers, and
        // losing `first_counts` is correct: the next iteration rewrites the
        // region from its first chunk and footer_set/bump repopulate both the
        // state and the footer.
        gib_scalar_count_forget_region_states();
    }
    // Length is rewound but CAPACITY is retained, so iteration 1 sizes the log
    // for the whole run and no later iteration reallocs.  Measured: 7 reallocs
    // total over 200 iterations x 14000 chunks, all 7 in iteration 1.
    gib_global_chunk_log_len = mark;

    // Return the freed pages to the OS.
    //
    // Without this the allocator decides, per allocation pattern, whether the
    // next iteration re-faults its pages or reuses them warm -- and it decides
    // DIFFERENTLY for different layouts.  Measured on List at 100M elements:
    // reclaim cut AoS's page faults 1,319,915 -> 795,797 (warm reuse, 1.63x
    // faster) while leaving SoA's at 1,210,087 -> 1,209,999 (still cold, no
    // change).  That is not a layout result, it is an allocator artifact, and
    // it reversed the AoS/SoA ordering in the benchmark tables.
    //
    // Forcing the pages back makes every configuration pay the same
    // first-touch cost the un-fixed compiler paid, so what the tables compare
    // is the layouts rather than glibc's free-list heuristics.
#if defined(__GLIBC__)
    if (freed_any) {
        malloc_trim(0);
    }
#endif
}

#else // _GIBBON_REGIONRESET

// Feature compiled out: the generated code still emits the calls (exactly as it
// unconditionally emits the bumpalloc pair), and they do nothing.
// Feature compiled out: allocation is exactly gib_alloc, so the generated
// program's machine code is the same either way, and the brackets are no-ops.
GIB_NOINLINE __attribute__((malloc))
void *gib_region_chunk_alloc(size_t size) { return gib_alloc(size); }
GIB_NOINLINE void gib_region_chunk_save_state(void) {}
GIB_NOINLINE void gib_region_chunk_restore_state(void) {}

#endif // _GIBBON_REGIONRESET

void gib_perform_GC(bool force_major)
{
    gib_perform_GC_(force_major);
}

STATIC_INLINE void gib_perform_GC_(bool force_major)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibOldgen *oldgen = DEFAULT_GENERATION;
    GibGcStats *gc_stats = GC_STATS;

#ifdef _GIBBON_GCSTATS
    struct timespec begin;
    struct timespec end;
    clock_gettime(CLOCK_MONOTONIC_RAW, &begin);
    int err = gib_garbage_collect(rstack, wstack, nursery, oldgen, gc_stats, force_major);
    if (err < 0) {
        fprintf(stderr, "Couldn't perform minor collection, errorno=%d.", err);
        exit(1);
    }
    clock_gettime(CLOCK_MONOTONIC_RAW, &end);
    double pause_time = gib_difftimespecs(&begin, &end);
    gc_stats->gc_elapsed_time += pause_time;
    gc_stats->gc_cpu_time += gc_stats->gc_elapsed_time / CLOCKS_PER_SEC;

#ifdef _GIBBON_PRINT_PAUSE_TIMES
    printf("pause_time: %f\n", pause_time);
#endif

#else
    int err = gib_garbage_collect(rstack, wstack, nursery, oldgen, gc_stats, force_major);
    if (err < 0) {
        fprintf(stderr, "Couldn't perform minor collection, errorno=%d.", err);
        exit(1);
    }
#endif

    return;
}

static void gib_bump_global_region_count(void);

typedef struct gib_scalar_count_debug_state {
    uint64_t depth;
#ifdef _GIBBON_DEBUG
    size_t length;
    size_t capacity;
    char **footers;
#endif
} GibScalarCountDebugState;


static GibScalarCountDebugState gib_global_scalar_count_debug_state = {
    .depth = 0,
#ifdef _GIBBON_DEBUG
    .length = 0,
    .capacity = 0,
    .footers = NULL,
#endif
};

// Not static: the per-element bump's fast path is inlined into the generated
// program (see gib_scalar_count_footer_bump in gibbon_rts.h), so it needs to
// read the table directly.  `capacity` stays private -- only the out-of-line
// append path grows the table.
GibScalarCountRegionState *gib_global_scalar_count_region_states = NULL;
size_t gib_global_scalar_count_region_states_length = 0;
static size_t gib_global_scalar_count_region_states_capacity = 0;


static GibScalarCountFooter *gib_scalar_count_footer_for_addr(char *footer_ptr)
{
    if (gib_addr_in_nursery(footer_ptr)) {
        return &((GibNurseryChunkFooter *) footer_ptr)->scalar_counts;
    } else {
        return &((GibOldgenChunkFooter *) footer_ptr)->scalar_counts;
    }
}

static void gib_scalar_count_debug_touch(char *footer_ptr)
{
#ifndef _GIBBON_DEBUG
    (void) footer_ptr;
#else
    GibScalarCountDebugState *state = &gib_global_scalar_count_debug_state;

    for (size_t i = 0; i < state->length; i++) {
        if (state->footers[i] == footer_ptr) {
            return;
        }
    }

    if (state->length == state->capacity) {
        size_t new_capacity = state->capacity == 0 ? 8 : state->capacity * 2;
        char **new_footers = realloc(state->footers, new_capacity * sizeof(char *));
        if (new_footers == NULL) {
            fprintf(stderr, "gib_scalar_count_debug_touch: realloc failed\n");
            exit(1);
        }
        state->footers = new_footers;
        state->capacity = new_capacity;
    }

    state->footers[state->length] = footer_ptr;
    state->length++;
#endif
}

static void gib_scalar_count_footer_copy_fixed(
    GibScalarCountFooter *dst,
    const GibScalarCountFooter *src
) {
    dst->count = src->count;
    dst->is_touched = src->is_touched;
    memcpy(dst->_padding, src->_padding, sizeof(dst->_padding));
}

static void gib_scalar_count_footer_set_fixed(GibScalarCountFooter *footer, uint64_t count)
{
    footer->count = count;
    footer->is_touched = 1;
    memset(footer->_padding, 0, sizeof(footer->_padding));
}

static uint64_t gib_scalar_count_footer_get_fixed(const GibScalarCountFooter *footer)
{
    if (!footer->is_touched) {
        return 0;
    }

    return footer->count;
}

static bool gib_scalar_count_footer_is_touched(const GibScalarCountFooter *footer)
{
    return footer->is_touched != 0;
}

static GibScalarCountRegionState *gib_scalar_count_region_state_for_footer(
    GibOldgenChunkFooter *footer
) {
    GibRegionInfo *reg_info = footer->reg_info;

    for (size_t i = 0; i < gib_global_scalar_count_region_states_length; i++) {
        GibScalarCountRegionState *state = &gib_global_scalar_count_region_states[i];
        if (state->reg_info == reg_info) {
            return state;
        }
    }

    if (gib_global_scalar_count_region_states_length ==
        gib_global_scalar_count_region_states_capacity) {
        size_t new_capacity =
            gib_global_scalar_count_region_states_capacity == 0
                ? 8
                : gib_global_scalar_count_region_states_capacity * 2;
        GibScalarCountRegionState *new_states =
            realloc(gib_global_scalar_count_region_states,
                    new_capacity * sizeof(GibScalarCountRegionState));
        if (new_states == NULL) {
            fprintf(stderr, "gib_scalar_count_region_state_for_footer: realloc failed\n");
            exit(1);
        }
        gib_global_scalar_count_region_states = new_states;
        gib_global_scalar_count_region_states_capacity = new_capacity;
    }

    GibScalarCountRegionState *state =
        &gib_global_scalar_count_region_states[gib_global_scalar_count_region_states_length];
    gib_global_scalar_count_region_states_length++;
    state->reg_info = reg_info;
    state->current_footer = footer;
    state->write_footer = NULL;
    gib_scalar_count_footer_init(&state->first_counts);
    return state;
}

// Drop every cached region state.  `gib_scalar_count_footer_begin` does the
// same at depth 0; this is the entry point for the region-chunk log, which has
// to invalidate them whenever it frees the chunks they point into.
#if _GIBBON_REGIONRESET
static void gib_scalar_count_forget_region_states(void)
{
    gib_global_scalar_count_region_states_length = 0;
    gib_scalar_count_forget_slots();
}
#endif

// Deferred scalar counts.  See the block comment in gibbon_rts.h.

// The counter the generated per-element code increments.  Cache-line aligned.
_Alignas(64) uint64_t gib_scalar_count_pending[GIB_SCALAR_COUNT_MAX_SLOTS] = {0};

// A slot's region.  Each SoA buffer is its own region, so this is 1:1 and
// `on_grow` can find the slot from `reg_info` alone.  NULL = unbound.
static GibRegionInfo *gib_scalar_count_slot_reg[GIB_SCALAR_COUNT_MAX_SLOTS] = {NULL};

// Nursery fallback: a slot bound to a nursery footer writes it directly,
// mirroring the nursery branch of gib_scalar_count_footer_bump_slow.
static char *gib_scalar_count_slot_nursery[GIB_SCALAR_COUNT_MAX_SLOTS] = {NULL};

// One past the highest slot ever bound, so `on_grow` scans only what is used.
static size_t gib_scalar_count_slots_high_water = 0;

#ifdef _GIBBON_SCALAR_COUNT_DIFF
// Differential mode: the per-element bump is emitted TOO, so the footers hold
// the authoritative counts and a flush verifies instead of applying.
static uint64_t gib_scalar_count_diff_snapshot[GIB_SCALAR_COUNT_MAX_SLOTS] = {0};
static uint64_t gib_scalar_count_diff_checks = 0;
#endif

// Unused in differential mode, where a flush verifies rather than applies.
#ifndef _GIBBON_SCALAR_COUNT_DIFF
static void gib_scalar_count_footer_add_fixed(GibScalarCountFooter *footer, uint64_t n)
{
    if (!footer->is_touched) {
        footer->count = 0;
        footer->is_touched = 1;
    }

    footer->count += n;
}
#endif

static GibScalarCountRegionState *gib_scalar_count_region_state_lookup(
    GibRegionInfo *reg_info
) {
    for (size_t i = 0; i < gib_global_scalar_count_region_states_length; i++) {
        GibScalarCountRegionState *state = &gib_global_scalar_count_region_states[i];
        if (state->reg_info == reg_info) {
            return state;
        }
    }

    return NULL;
}

#ifdef _GIBBON_SCALAR_COUNT_DIFF
// Where a flush lands, given the cyclic convention: before the region has grown
// there is no previous chunk, so the count accumulates in `first_counts` (plus
// the current footer, which the final chunk's reader consults); afterwards it
// belongs to the previous chunk's footer.  This is exactly the routing
// `gib_scalar_count_footer_bump_slow` performs per element.  Only differential
// mode needs the target as a value; the applying path writes through the two
// branches directly because the un-grown case touches `first_counts` too.
static GibScalarCountFooter *gib_scalar_count_flush_target(
    GibScalarCountRegionState *state
) {
    if (state->write_footer == NULL) {
        return &state->current_footer->scalar_counts;
    }

    return &state->write_footer->scalar_counts;
}

static void gib_scalar_count_diff_check(
    size_t slot,
    const GibScalarCountFooter *target,
    uint64_t pending
) {
    uint64_t observed = target->is_touched ? target->count : 0;
    uint64_t expected = gib_scalar_count_diff_snapshot[slot] + pending;

    if (observed != expected) {
        fprintf(stderr,
                "gibbon: DEFERRED SCALAR COUNT MISMATCH on slot %zu: "
                "the per-element bumps produced %" PRIu64 " since the last flush, "
                "the deferred counter produced %" PRIu64 ".\n"
                "This means a flush was missed or double-applied; a loopified "
                "consumer would read the wrong trip count.\n",
                slot,
                observed - gib_scalar_count_diff_snapshot[slot],
                pending);
        exit(1);
    }

    gib_scalar_count_diff_checks++;
}
#endif

// Deliver `gib_scalar_count_pending[slot]` into its footer and reset it.
// Called O(chunks) times per buffer, never per element.
static void gib_scalar_count_flush_slot(size_t slot)
{
    uint64_t pending = gib_scalar_count_pending[slot];

    // No bumps means no touch -- preserving the distinction `footer_get` makes
    // between "counted zero elements" and "never written".
    if (pending == 0) {
        return;
    }

    if (gib_scalar_count_slot_nursery[slot] != NULL) {
        GibScalarCountFooter *footer =
            gib_scalar_count_footer_for_addr(gib_scalar_count_slot_nursery[slot]);
#ifdef _GIBBON_SCALAR_COUNT_DIFF
        gib_scalar_count_diff_check(slot, footer, pending);
        gib_scalar_count_diff_snapshot[slot] = footer->is_touched ? footer->count : 0;
#else
        gib_scalar_count_footer_add_fixed(footer, pending);
        gib_scalar_count_debug_touch(gib_scalar_count_slot_nursery[slot]);
#endif
        gib_scalar_count_pending[slot] = 0;
        return;
    }

    GibRegionInfo *reg_info = gib_scalar_count_slot_reg[slot];
    if (reg_info == NULL) {
        // Unbound slot with a non-zero count: the producer wrote elements that
        // no finalize claimed.  Dropping them silently is the one thing this
        // scheme must not do quietly.
        fprintf(stderr,
                "gibbon: scalar-count slot %zu accumulated %" PRIu64
                " elements but was never bound to a region.\n",
                slot, pending);
        exit(1);
    }

    GibScalarCountRegionState *state = gib_scalar_count_region_state_lookup(reg_info);
    if (state == NULL) {
        // The region-state table was reset underneath this slot (region reset).
        gib_scalar_count_pending[slot] = 0;
        return;
    }

#ifdef _GIBBON_SCALAR_COUNT_DIFF
    GibScalarCountFooter *target = gib_scalar_count_flush_target(state);
    gib_scalar_count_diff_check(slot, target, pending);
    gib_scalar_count_diff_snapshot[slot] = target->is_touched ? target->count : 0;
#else
    if (state->write_footer == NULL) {
        gib_scalar_count_footer_add_fixed(&state->first_counts, pending);
        gib_scalar_count_footer_add_fixed(&state->current_footer->scalar_counts, pending);
        gib_scalar_count_debug_touch((char *) state->current_footer);
    } else {
        gib_scalar_count_footer_add_fixed(&state->write_footer->scalar_counts, pending);
        gib_scalar_count_debug_touch((char *) state->write_footer);
    }
#endif

    gib_scalar_count_pending[slot] = 0;
}

// Flush every slot bound to `reg_info`.  Called from `gib_scalar_count_on_grow`
// before its state transition, while the routing still names the chunk being
// abandoned.
static void gib_scalar_count_flush_region(GibRegionInfo *reg_info)
{
    for (size_t slot = 0; slot < gib_scalar_count_slots_high_water; slot++) {
        if (gib_scalar_count_slot_reg[slot] == reg_info) {
            gib_scalar_count_flush_slot(slot);
#ifdef _GIBBON_SCALAR_COUNT_DIFF
            // The target footer is about to change, and the one the bumps will
            // write next was just zeroed by the caller's transition.
            gib_scalar_count_diff_snapshot[slot] = 0;
#endif
        }
    }
}

// Point a slot at a region, without disturbing what it has already counted.
static void gib_scalar_count_bind_slot_to_footer(size_t slot, char *footer_ptr)
{
    gib_scalar_count_slot_reg[slot] = NULL;
    gib_scalar_count_slot_nursery[slot] = NULL;

    if (footer_ptr == NULL) {
        return;
    }

    if (gib_addr_in_nursery(footer_ptr)) {
        gib_scalar_count_slot_nursery[slot] = footer_ptr;
#ifdef _GIBBON_SCALAR_COUNT_DIFF
        {
            GibScalarCountFooter *f = gib_scalar_count_footer_for_addr(footer_ptr);
            gib_scalar_count_diff_snapshot[slot] = f->is_touched ? f->count : 0;
        }
#endif
        return;
    }

    GibOldgenChunkFooter *footer = (GibOldgenChunkFooter *) footer_ptr;
    // Creates the state if absent, with current_footer = this chunk and
    // write_footer = NULL -- the same initial state a first bump would have
    // produced.
    GibScalarCountRegionState *state =
        gib_scalar_count_region_state_for_footer(footer);
    gib_scalar_count_slot_reg[slot] = state->reg_info;
#ifdef _GIBBON_SCALAR_COUNT_DIFF
    {
        // Seed from what the target already holds: a second production into
        // the same region must not be compared against the running total of
        // every earlier one.
        GibScalarCountFooter *tgt = gib_scalar_count_flush_target(state);
        gib_scalar_count_diff_snapshot[slot] = tgt->is_touched ? tgt->count : 0;
    }
#endif
}

static void gib_scalar_count_bind_slot(size_t slot, char *footer_ptr)
{
#ifdef _GIBBON_SCALAR_COUNT_DIFF
    // Registered here rather than in main so generated programs need no change.
    static bool diff_report_registered = false;
    if (!diff_report_registered) {
        diff_report_registered = true;
        atexit(gib_scalar_count_diff_report);
    }
#endif

    if (slot >= GIB_SCALAR_COUNT_MAX_SLOTS) {
        fprintf(stderr,
                "gibbon: scalar-count slot %zu exceeds GIB_SCALAR_COUNT_MAX_SLOTS (%d).\n",
                slot, GIB_SCALAR_COUNT_MAX_SLOTS);
        exit(1);
    }

    gib_scalar_count_pending[slot] = 0;

    if (slot + 1 > gib_scalar_count_slots_high_water) {
        gib_scalar_count_slots_high_water = slot + 1;
    }

    gib_scalar_count_bind_slot_to_footer(slot, footer_ptr);
}

void gib_scalar_count_bind(char **final_footers, size_t base, int len)
{
    if (final_footers == NULL || len <= 0) {
        return;
    }

    for (int i = 0; i < len; i++) {
        gib_scalar_count_bind_slot(base + (size_t) i, final_footers[i]);
    }
}

void gib_scalar_count_finalize(char **final_footers, size_t base, int len)
{
    (void) final_footers;

    if (len <= 0) {
        return;
    }

    for (int i = 0; i < len; i++) {
        size_t slot = base + (size_t) i;
        if (slot >= GIB_SCALAR_COUNT_MAX_SLOTS) {
            continue;
        }
        gib_scalar_count_flush_slot(slot);
        gib_scalar_count_slot_reg[slot] = NULL;
        gib_scalar_count_slot_nursery[slot] = NULL;
    }
}

void gib_scalar_count_on_promote(char *old_nursery_footer, char *new_oldgen_footer)
{
    if (old_nursery_footer == NULL || new_oldgen_footer == NULL) {
        return;
    }

    for (size_t slot = 0; slot < gib_scalar_count_slots_high_water; slot++) {
        if (gib_scalar_count_slot_nursery[slot] != old_nursery_footer) {
            continue;
        }

        // Deliver what the nursery chunk actually holds, into the nursery
        // footer -- which is where the per-element bump put it too.
        gib_scalar_count_flush_slot(slot);

        // Then re-point the slot at the promoted region.  Promotion allocates
        // a FRESH reg_info (see gib_init_footer_at at the call site), so this
        // is a different region, not a new chunk of the same one; everything
        // written from here on belongs to it.
        gib_scalar_count_slot_nursery[slot] = NULL;
        gib_scalar_count_bind_slot_to_footer(slot, new_oldgen_footer);
    }
}

void gib_scalar_count_forget_slots(void)
{
    for (size_t slot = 0; slot < gib_scalar_count_slots_high_water; slot++) {
        gib_scalar_count_pending[slot] = 0;
        gib_scalar_count_slot_reg[slot] = NULL;
        gib_scalar_count_slot_nursery[slot] = NULL;
#ifdef _GIBBON_SCALAR_COUNT_DIFF
        gib_scalar_count_diff_snapshot[slot] = 0;
#endif
    }
    gib_scalar_count_slots_high_water = 0;
}

#ifdef _GIBBON_SCALAR_COUNT_DIFF
void gib_scalar_count_diff_report(void)
{
    if (gib_scalar_count_diff_checks == 0) {
        fprintf(stderr,
                "gibbon: --scalar-counts-diff verified nothing: no flush point "
                "was reached.\n");
        return;
    }

    fprintf(stderr,
            "gibbon: deferred scalar counts agreed with the per-element bumps "
            "at %" PRIu64 " flush points.\n",
            gib_scalar_count_diff_checks);
}
#endif

// The debug bracket exists to PRINT the footers a producer touched.  It must
// not reset counting state: it is emitted as the first statement of every
// `OPT:StoreScalarCounts` producer, which under `--defer-scalar-counts` is
// after the caller's `gib_scalar_count_bind` and before any `pending[k]++`.
// Clearing slots there destroyed the binding the bracket had just been given,
// and clearing the region states discarded the per-region `first_counts` the
// cyclic footer convention accumulates.  Only the list of touched footers --
// the thing actually printed -- is scoped to one production.
//
// Invalidating region states when their chunks are freed is
// `gib_scalar_count_forget_region_states`, called from the region-chunk log.
void gib_scalar_count_footer_begin(void)
{
    GibScalarCountDebugState *state = &gib_global_scalar_count_debug_state;

    if (state->depth == 0) {
#ifdef _GIBBON_DEBUG
        state->length = 0;
#endif
    }
    state->depth++;
}

void gib_scalar_count_on_grow(char *old_footer_ptr, char *new_footer_ptr)
{
    if (old_footer_ptr == NULL || new_footer_ptr == NULL) {
        return;
    }

    // Nursery scalar-count metadata is deliberately left as a later step.
    if (gib_addr_in_nursery(old_footer_ptr) || gib_addr_in_nursery(new_footer_ptr)) {
        return;
    }

    GibOldgenChunkFooter *old_footer = (GibOldgenChunkFooter *) old_footer_ptr;
    GibOldgenChunkFooter *new_footer = (GibOldgenChunkFooter *) new_footer_ptr;
    GibScalarCountRegionState *region_state =
        gib_scalar_count_region_state_for_footer(old_footer);

    // Deliver any deferred count BEFORE the transition, while the routing
    // still names the chunk being abandoned.  After this the old footer is
    // zeroed and the counts that follow belong to the next chunk.
    gib_scalar_count_flush_region(region_state->reg_info);

    region_state->write_footer = old_footer;
    region_state->current_footer = new_footer;
    gib_scalar_count_footer_init(&old_footer->scalar_counts);
    gib_scalar_count_footer_copy_fixed(&new_footer->scalar_counts,
                                       &region_state->first_counts);
    if (gib_scalar_count_footer_is_touched(&region_state->first_counts)) {
        gib_scalar_count_debug_touch(new_footer_ptr);
    }
}

// The SLOW path.  The fast path lives in gibbon_rts.h and handles the common
// case -- an oldgen footer whose region state is already in the table -- without
// a call or a stack frame.  Measured: `region_state_for_footer`'s prologue
// (`sub $0x28,%rsp`) alone was 46% of that function's cycles, for a lookup whose
// scan body is ~7%; the cost was the call, not the search.
void gib_scalar_count_footer_bump_slow(char *footer_ptr)
{
    if (footer_ptr == NULL) {
        return;
    }

    if (gib_addr_in_nursery(footer_ptr)) {
        GibScalarCountFooter *footer = gib_scalar_count_footer_for_addr(footer_ptr);
        gib_scalar_count_footer_bump_fixed(footer);
        gib_scalar_count_debug_touch(footer_ptr);
        return;
    }

    GibOldgenChunkFooter *footer = (GibOldgenChunkFooter *) footer_ptr;
    GibScalarCountRegionState *region_state =
        gib_scalar_count_region_state_for_footer(footer);

    if (region_state->write_footer == NULL) {
        gib_scalar_count_footer_bump_fixed(&region_state->first_counts);
        gib_scalar_count_footer_bump_fixed(&region_state->current_footer->scalar_counts);
        gib_scalar_count_debug_touch((char *) region_state->current_footer);
    } else {
        gib_scalar_count_footer_bump_fixed(&region_state->write_footer->scalar_counts);
        gib_scalar_count_debug_touch((char *) region_state->write_footer);
    }
}

void gib_scalar_count_footer_set(char *footer_ptr, uint64_t count)
{
    if (footer_ptr == NULL) {
        return;
    }

    if (gib_addr_in_nursery(footer_ptr)) {
        GibScalarCountFooter *footer = gib_scalar_count_footer_for_addr(footer_ptr);
        gib_scalar_count_footer_set_fixed(footer, count);
        gib_scalar_count_debug_touch(footer_ptr);
        return;
    }

    GibOldgenChunkFooter *footer = (GibOldgenChunkFooter *) footer_ptr;
    GibScalarCountRegionState *region_state =
        gib_scalar_count_region_state_for_footer(footer);

    if (region_state->write_footer == NULL) {
        gib_scalar_count_footer_set_fixed(&region_state->first_counts, count);
        gib_scalar_count_footer_set_fixed(&region_state->current_footer->scalar_counts, count);
        gib_scalar_count_debug_touch((char *) region_state->current_footer);
    } else {
        gib_scalar_count_footer_set_fixed(&region_state->write_footer->scalar_counts, count);
        gib_scalar_count_debug_touch((char *) region_state->write_footer);
    }
}

uint64_t gib_scalar_count_footer_get(char *footer_ptr)
{
    GibScalarCountFooter *footer = gib_scalar_count_footer_for_addr(footer_ptr);
    return gib_scalar_count_footer_get_fixed(footer);
}

char *gib_scalar_count_first_footer(char *footer_ptr)
{
    if (footer_ptr == NULL || gib_addr_in_nursery(footer_ptr)) {
        return NULL;
    }

    GibOldgenChunkFooter *footer = (GibOldgenChunkFooter *) footer_ptr;
    return footer->reg_info->first_chunk_footer;
}

char *gib_scalar_count_footer_next(char *footer_ptr)
{
    if (footer_ptr == NULL || gib_addr_in_nursery(footer_ptr)) {
        return NULL;
    }

    GibOldgenChunkFooter *footer = (GibOldgenChunkFooter *) footer_ptr;
    return (char *) footer->next;
}

void gib_scalar_count_copy_chain(char *dst_final_footer_ptr, char *src_final_footer_ptr)
{
    if (dst_final_footer_ptr == NULL || src_final_footer_ptr == NULL) {
        return;
    }

    // Nursery chunks do not carry an oldgen footer chain.  A nursery value can
    // only be copied directly here; the normal multi-chunk case below is
    // O(chunks) over the oldgen footer list.
    if (gib_addr_in_nursery(dst_final_footer_ptr) ||
        gib_addr_in_nursery(src_final_footer_ptr)) {
        GibScalarCountFooter *dst =
            gib_scalar_count_footer_for_addr(dst_final_footer_ptr);
        GibScalarCountFooter *src =
            gib_scalar_count_footer_for_addr(src_final_footer_ptr);
        gib_scalar_count_footer_copy_fixed(dst, src);
        if (gib_scalar_count_footer_is_touched(src)) {
            gib_scalar_count_debug_touch(dst_final_footer_ptr);
        }
        return;
    }

    GibOldgenChunkFooter *dst_final =
        (GibOldgenChunkFooter *) dst_final_footer_ptr;
    GibOldgenChunkFooter *src_final =
        (GibOldgenChunkFooter *) src_final_footer_ptr;
    GibOldgenChunkFooter *dst =
        (GibOldgenChunkFooter *) dst_final->reg_info->first_chunk_footer;
    GibOldgenChunkFooter *src =
        (GibOldgenChunkFooter *) src_final->reg_info->first_chunk_footer;

    while (dst != NULL && src != NULL) {
        gib_scalar_count_footer_copy_fixed(&dst->scalar_counts,
                                           &src->scalar_counts);
        if (gib_scalar_count_footer_is_touched(&src->scalar_counts)) {
            gib_scalar_count_debug_touch((char *) dst);
        }
        dst = dst->next;
        src = src->next;
    }

#ifdef _GIBBON_DEBUG
    if (dst != NULL || src != NULL) {
        fprintf(stderr,
                "gib_scalar_count_copy_chain: source/destination chunk count mismatch\n");
    }
#endif
}

void gib_scalar_count_copy_all(char **dst_final_footers, char **src_final_footers, int len)
{
    if (dst_final_footers == NULL || src_final_footers == NULL || len <= 0) {
        return;
    }

    for (int i = 0; i < len; i++) {
        gib_scalar_count_copy_chain(dst_final_footers[i], src_final_footers[i]);
    }
}

void gib_scalar_count_footer_end(const char *build_fun_name)
{
    GibScalarCountDebugState *state = &gib_global_scalar_count_debug_state;

    if (state->depth == 0) {
        fprintf(stderr, "gib_scalar_count_footer_end called without a matching begin\n");
        return;
    }

    state->depth--;
    if (state->depth != 0) {
        return;
    }

    // No final repair pass is needed here.  The cyclic invariant is maintained
    // eagerly in gib_scalar_count_on_grow: each fresh final footer is seeded
    // with first_counts, and the previous footer accumulates the next chunk.
#ifdef _GIBBON_DEBUG
    printf("SCALAR_COUNT_FOOTERS %s touched=%zu\n", build_fun_name, state->length);
    for (size_t i = 0; i < state->length; i++) {
        gib_scalar_count_footer_print(state->footers[i]);
    }
#else
    (void) build_fun_name;
#endif
}

void gib_scalar_count_footer_print(char *footer_ptr)
{
#ifndef _GIBBON_DEBUG
    (void) footer_ptr;
#else
    GibScalarCountFooter *footer = gib_scalar_count_footer_for_addr(footer_ptr);
    const char *kind = gib_addr_in_nursery(footer_ptr) ? "nursery" : "oldgen";
    bool touched = gib_scalar_count_footer_is_touched(footer);

    printf("SCALAR_COUNT_FOOTER footer=%p kind=%s touched=%u\n",
           (void *) footer_ptr,
           kind,
           touched ? 1 : 0);
    if (touched) {
        printf("SCALAR_COUNT count=%" PRIu64 "\n", footer->count);
    }
#endif
}

// Functions related to counting the number of allocated regions.
GibChunk gib_alloc_counted_region(size_t size)
{
    // Bump the count.
    gib_bump_global_region_count();
    return gib_alloc_region(size);
}

void *gib_alloc_counted_struct(size_t n) {
    gib_bump_global_region_count();
    return gib_alloc(n);
}

static void gib_bump_global_region_count(void)
{
#ifdef _GIBBON_PARALLEL
    __atomic_add_fetch(&gib_global_region_count, 1, __ATOMIC_SEQ_CST);
    return;
#else
    gib_global_region_count++;
#endif
    return;
}

void gib_print_global_region_count(void)
{
    printf("REGION_COUNT: %" PRId64 "\n", gib_global_region_count);
    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Storage management
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Initialize nurseries, shadow stacks and generations.
UNUSED_IN_POINTER_BAK static void gib_storage_initialize(void);
UNUSED_IN_POINTER_BAK static void gib_storage_free(void);
static void gib_nursery_initialize(GibNursery *nursery, size_t nsize);
static void gib_nursery_free(GibNursery *nursery);
static void gib_oldgen_initialize(GibOldgen *oldgen);
static void gib_oldgen_free(GibOldgen *oldgen);
static void gib_shadowstack_initialize(GibShadowstack *stack, size_t stack_size);
static void gib_shadowstack_free(GibShadowstack *stack);
static void gib_gc_stats_initialize(GibGcStats *stats);
static void gib_gc_stats_free(GibGcStats *stats);

// Initialize nurseries, shadow stacks and generations.
UNUSED_IN_POINTER_BAK static void gib_storage_initialize(void)
{
    if (gib_storage_initialized) {
        return;
    }

    // Initialize the stats object.
    gib_global_gc_stats = (GibGcStats *) gib_alloc(sizeof(GibGcStats));
    gib_gc_stats_initialize(gib_global_gc_stats);

    // Initialize nurseries.
    uint64_t n;
    gib_global_nurseries = (GibNursery *) gib_alloc(gib_global_num_threads *
                                                    sizeof(GibNursery));
    for (n = 0; n < gib_global_num_threads; n++) {
        gib_nursery_initialize(&(gib_global_nurseries[n]), gib_nursery_size);
    }

    // Initialize old generation.
    gib_global_oldgen = (GibOldgen *) gib_alloc(sizeof(GibOldgen));
    gib_oldgen_initialize(gib_global_oldgen);

    // Initialize shadow stacks.
    uint64_t ss;
    gib_global_read_shadowstacks =
            (GibShadowstack *) gib_alloc(gib_global_num_threads *
                                         sizeof(GibShadowstack));
    gib_global_write_shadowstacks =
            (GibShadowstack *) gib_alloc(gib_global_num_threads *
                                         sizeof(GibShadowstack));
    for (ss = 0; ss < gib_global_num_threads; ss++) {
        gib_shadowstack_initialize(&(gib_global_read_shadowstacks[ss]),
                                   GIB_SHADOWSTACK_SIZE);
        gib_shadowstack_initialize(&(gib_global_write_shadowstacks[ss]),
                                   GIB_SHADOWSTACK_SIZE);
    }

    return;
}

UNUSED_IN_POINTER_BAK static void gib_storage_free(void)
{
    if (!gib_storage_initialized) {
        return;
    }

    // Free nurseries.
    uint64_t n;
    for (n = 0; n < gib_global_num_threads; n++) {
        gib_nursery_free(&(gib_global_nurseries[n]));
     }
    gib_free(gib_global_nurseries);

    // Free oldgen.
    gib_oldgen_free(gib_global_oldgen);
    gib_free(gib_global_oldgen);

    // Free shadow-stacks.
    uint64_t ss;
    for (ss = 0; ss < gib_global_num_threads; ss++) {
        gib_shadowstack_free(&(gib_global_read_shadowstacks[ss]));
        gib_shadowstack_free(&(gib_global_write_shadowstacks[ss]));
    }
    gib_free(gib_global_read_shadowstacks);
    gib_free(gib_global_write_shadowstacks);

    // Free the stats object.
    gib_gc_stats_free(gib_global_gc_stats);
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Nursery
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

size_t gib_nursery_realloc(GibNursery *nursery, size_t size)
{
    size_t old_size = nursery->heap_size;
    gib_free(nursery->heap_start);
    gib_nursery_initialize(nursery, size);
    gib_nursery_size = size;
    gib_nursery_region_max_size = size / 2;
    return old_size;
}

static void gib_nursery_initialize(GibNursery *nursery, size_t nsize)
{
    nursery->heap_size = nsize;
    nursery->heap_start = (char *) gib_alloc(nsize);
    if (nursery->heap_start == NULL) {
        fprintf(stderr, "gib_nursery_initialize: gib_alloc failed: %zu",
                (size_t) nsize);
        exit(1);
    }
    nursery->heap_end = nursery->heap_start + nsize;
    nursery->alloc = nursery->heap_end;

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    printf("Nursery info: start=%p, end=%p, alloc=%p, size=%zu\n\n",
           nursery->heap_start, nursery->heap_end, nursery->alloc, nsize);
#endif

    return;
}

// Free data associated with a nursery.
static void gib_nursery_free(GibNursery *nursery)
{
    gib_free(nursery->heap_start);
    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Old generation
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

static void gib_oldgen_initialize(GibOldgen *oldgen)
{
    oldgen->old_zct = (void *) NULL;
    oldgen->new_zct = (void *) NULL;
    // Initialize the remembered set.
    oldgen->rem_set = (GibRememberedSet *) gib_alloc(sizeof(GibRememberedSet));
    if (oldgen->rem_set == NULL) {
        fprintf(stderr, "gib_oldgen_initialize: gib_alloc failed: %zu",
                sizeof(GibRememberedSet));
        exit(1);
    }
    gib_shadowstack_initialize(oldgen->rem_set, GIB_REMEMBERED_SET_SIZE);

    return;
}

static void gib_oldgen_free(GibOldgen *oldgen)
{
    gib_shadowstack_free(oldgen->rem_set);
    gib_free(oldgen->rem_set);
    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow-stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Initialize a shadow stack.
static void gib_shadowstack_initialize(GibShadowstack* stack, size_t stack_size)
{
    stack->start = (char *) gib_alloc(stack_size);
    if (stack->start == NULL) {
        fprintf(stderr, "gib_shadowstack_initialize: gib_alloc failed: %zu",
                stack_size);
        exit(1);
    }
    stack->end = stack->start + stack_size;
    stack->alloc = stack->start;
    return;
}

static void gib_shadowstack_free(GibShadowstack* stack)
{
    gib_free(stack->start);
    return;
}

void gib_shadowstack_push_noinline(
    GibShadowstack *stack,
    char *ptr,
    char *endptr,
    GibGcRootProv gc_root_prov,
    uint32_t datatype
)
{
    gib_shadowstack_push(stack, ptr, endptr, gc_root_prov, datatype);
    return;
}

GibShadowstackFrame *gib_shadowstack_pop_noinline(GibShadowstack *stack)
{
    return gib_shadowstack_pop(stack);
}


GibShadowstackFrame *gib_shadowstack_peek_noinline(GibShadowstack *stack)
{
    return gib_shadowstack_peek(stack);
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Remembered set
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */



/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Write barrier
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void gib_indirection_barrier_noinline(
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
    gib_indirection_barrier(from, from_footer, to, to_footer, datatype);
    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * GC statistics
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


static void gib_gc_stats_initialize(GibGcStats *stats)
{
    stats->minor_collections = 0;
    stats->major_collections = 0;
    stats->mem_allocated_in_nursery = 0;
    stats->mem_allocated_in_oldgen = 0;
    stats->mem_copied = 0;
    stats->mem_burned = 0;
    stats->ctors_forwarded = 0;
    stats->ctors_not_forwarded = 0;
    stats->indirs_inlined = 0;
    stats->indirs_not_inlined = 0;
    stats->redirs_inlined = 0;
    stats->redirs_not_inlined = 0;
    stats->nursery_regions = 0;
    stats->oldgen_regions = 0;
    stats->nursery_chunks = 0;
    stats->oldgen_chunks = 0;
    stats->gc_elapsed_time = 0;
    stats->gc_cpu_time = 0;
    stats->gc_rootset_sort_time = 0;
    stats->gc_burn_time = 0;
    stats->gc_find_fwdptr_time = 0;
    stats->gc_info_tbl_lkp_time = 0;
    stats->gc_zct_mgmt_time = 0;
    stats->fwd_env_size = 0;
    stats->fwd_env_lookups = 0;
    stats->fwd_env_inserts = 0;
    stats->skipover_env_size = 0;
    stats->skipover_env_lookups = 0;
    stats->skipover_env_inserts = 0;
    stats->rootset_size = 0;
}

static void gib_gc_stats_free(GibGcStats *stats)
{
    gib_free(stats);
}

#ifdef _GIBBON_GCSTATS
static void gib_gc_stats_print(GibGcStats *stats)
{
    printf("\nGC statistics\n----------------------------------------\n");
    printf("Major collections:\t\t %" PRIu64 "\n", stats->major_collections);
    printf("Minor collections:\t\t %" PRIu64 "\n", stats->minor_collections);

    printf("\n");
    printf("Mem allocated in nursery:\t %ld\n", stats->mem_allocated_in_nursery);
    printf("Mem allocated in oldgen:\t %ld\n", stats->mem_allocated_in_oldgen);
    printf("Mem copied (nursery->oldgen):\t %ld\n", stats->mem_copied);
    printf("Mem burned:\t\t\t %ld\n", stats->mem_burned);

    printf("\n");
    printf("Ctors forwarded:\t\t %" PRIu64 "\n", stats->ctors_forwarded);
    printf("Ctors not forwarded:\t\t %" PRIu64 "\n", stats->ctors_not_forwarded);

    printf("\n");
    printf("Indirs inlined:\t\t\t %" PRIu64 "\n", stats->indirs_inlined);
    printf("Indirs not inlined:\t\t %" PRIu64 "\n", stats->indirs_not_inlined);

    printf("\n");
    printf("Redirs inlined:\t\t\t %" PRIu64 "\n", stats->redirs_inlined);
    printf("Redirs not inlined:\t\t %" PRIu64 "\n", stats->redirs_not_inlined);

    printf("\n");
    printf("Nursery regions:\t\t %lu\n", stats->nursery_regions);
    printf("Oldgen regions:\t\t\t %lu\n", stats->oldgen_regions);

    printf("\n");
    printf("Nursery chunks:\t\t\t %lu\n", stats->nursery_chunks);
    printf("Oldgen chunks:\t\t\t %lu\n", stats->oldgen_chunks);

    printf("\n");
    printf("GC elapsed time:\t\t %e\n", stats->gc_elapsed_time);
    printf("GC cpu time:\t\t\t %e\n", stats->gc_cpu_time);

    printf("\n");
    printf("Rootset sort time:\t\t %e\n", stats->gc_rootset_sort_time);
    printf("Burn time:\t\t\t %e\n", stats->gc_burn_time);
    printf("Fwd ptr scan time:\t\t %e\n", stats->gc_find_fwdptr_time);
    printf("Info table lookup time:\t\t %e\n", stats->gc_info_tbl_lkp_time);
    printf("ZCT mgmt time:\t\t\t %e\n", stats->gc_zct_mgmt_time);

    printf("\n");
    // TODO: use PRIu64.
    printf("Fwd env size:\t\t\t %ld\n", stats->fwd_env_size);
    printf("Fwd env lookups:\t\t %ld\n", stats->fwd_env_lookups);
    printf("Fwd env inserts:\t\t %ld\n", stats->fwd_env_inserts);
    printf("Skipover env size:\t\t %ld\n", stats->skipover_env_size);
    printf("Skipover env lookups:\t\t %ld\n", stats->skipover_env_lookups);
    printf("Skipover env inserts:\t\t %ld\n", stats->skipover_env_inserts);
    printf("Root set size:\t\t\t %ld\n", stats->rootset_size);
}
#endif // ifdef _GIBBON_GCSTATS


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Save and restore GC's state
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

GibGcStateSnapshot *gib_gc_init_state(uint64_t num_regions)
{
    GibGcStateSnapshot *snapshot = gib_alloc(sizeof(GibGcStateSnapshot));
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu", sizeof(GibGcStateSnapshot));
        exit(1);
    }
    snapshot->nursery_heap_start = gib_alloc(gib_nursery_size);
    if (snapshot->nursery_heap_start == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu", (size_t) gib_nursery_size);
        exit(1);
    }
    snapshot->reg_info_addrs = gib_alloc(num_regions * sizeof(GibRegionInfo*));
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu",
                num_regions * sizeof(GibRegionInfo *));
        exit(1);
    }
    snapshot->outsets = gib_alloc(num_regions * sizeof(char*));
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu",
                num_regions * sizeof(void*));
        exit(1);
    }
    return snapshot;
}

void gib_gc_save_state(GibGcStateSnapshot *snapshot, uint64_t num_regions, ...)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibOldgen *oldgen = DEFAULT_GENERATION;

    // nursery
    snapshot->nursery_alloc = nursery->alloc;
    memcpy(snapshot->nursery_heap_start, nursery->heap_start, gib_nursery_size);

    // old generation
    snapshot->gen_rem_set_alloc = (oldgen->rem_set)->alloc;
    snapshot->gen_old_zct = gib_clone_zct(oldgen->old_zct);
    snapshot->gen_new_zct = gib_clone_zct(oldgen->new_zct);

    // shadow-stacks
    snapshot->ss_read_alloc = rstack->alloc;
    snapshot->ss_write_alloc = wstack->alloc;

    // regions
    snapshot->num_regions = num_regions;
    char *footer_addr;
    GibOldgenChunkFooter *footer;
    GibRegionInfo *reg_info;
    void *outset;
    va_list ap;
    uint64_t i;
    va_start(ap, num_regions);
    for (i = 0; i < num_regions; i++) {
        footer_addr = va_arg(ap, char *);
        if (!gib_addr_in_nursery(footer_addr)) {
            footer = (GibOldgenChunkFooter *) footer_addr;
            reg_info = footer->reg_info;
            outset = gib_clone_outset(reg_info->outset);
            snapshot->reg_info_addrs[i] = reg_info;
            snapshot->outsets[i] = outset;
            // memcpy(&(snapshot->reg_info_addrs[i]), reg_info_addr, sizeof(GibRegionInfo *));
            // memcpy(&(snapshot->outsets[i]), &outset, sizeof(void *));
        }
        else {
            snapshot->reg_info_addrs[i] = (GibRegionInfo *) NULL;
            snapshot->outsets[i] = (void *) NULL;
        }
    }
    va_end(ap);

    return;
}

void gib_gc_restore_state(GibGcStateSnapshot *snapshot)
{
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_restore_state: NULL snapshot");
        exit(1);
    }

    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibOldgen *oldgen = DEFAULT_GENERATION;

    // nursery
    nursery->alloc = snapshot->nursery_alloc;
    memcpy(nursery->heap_start, snapshot->nursery_heap_start, gib_nursery_size);

    // oldgen
    (oldgen->rem_set)->alloc = snapshot->gen_rem_set_alloc;
    // gib_free_zct(oldgen->old_zct);
    // gib_free_zct(oldgen->new_zct);
    oldgen->old_zct = snapshot->gen_old_zct;
    oldgen->new_zct = snapshot->gen_new_zct;

    // shadow-stacks
    rstack->alloc = snapshot->ss_read_alloc;
    wstack->alloc = snapshot->ss_write_alloc;

    // regions
    uint64_t i;
    GibRegionInfo *reg_info;
    for (i = 0; i < snapshot->num_regions; i++) {
        if (snapshot->reg_info_addrs[i] != NULL) {
            reg_info = snapshot->reg_info_addrs[i];
            gib_free_outset(reg_info->outset);
            reg_info->outset = snapshot->outsets[i];
        }
    }
}

void gib_gc_free_state(GibGcStateSnapshot *snapshot)
{
    gib_free(snapshot->nursery_heap_start);
    gib_free(snapshot->reg_info_addrs);
    gib_free(snapshot->outsets);
    gib_free(snapshot);
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Helpers
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


void gib_show_usage(char** argv)
{
    printf("\n");
    printf("This binary was generated by the Gibbon compiler.\n");
    printf("\n");
    printf("Usage: %s [OPTIONS...]\n", argv[0]);

    printf("\n");
    printf("Options:\n");
    printf(" --biginf-buffer-size <bytes>   Set the buffer size (default %" PRId64 ").\n", gib_global_biginf_init_chunk_size);
    printf(" --inf-buffer-size <bytes>      Set the buffer size (default %" PRId64 ").\n", gib_global_inf_init_chunk_size);
    printf(" --bench-input <path>           Set the input file read for benchmarking. Applies only\n");
    printf("                                If the program was *compiled* with --bench-fun. \n");
    printf("\n");
    printf(" --array-input <path>           Set the file from which to read the array input.\n");
    printf(" --array-input-length <int>     Set the size of the array input file.\n");
    printf(" --iterate <int>                Set the number of timing iterations to perform (default 1).\n");
    // TODO: Rectify the definition of size-param
    printf(" --size-param <int>             A parameter for size available as a language primitive which allows user to specify the size at runtime (default 1).\n");
    return;
}

double gib_avg(const double* arr, int n)
{
    double sum = 0.0;
    for(int i=0; i<n; i++) sum += arr[i];
    return sum / (double)n;
}

double gib_difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
            + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

int gib_compare_doubles(const void *a, const void *b)
{
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}

// Exponentiation
/* Kept only for ABI compatibility: the code generator no longer emits a call
 * to this.  `ExpP` now emits the width-specific `gib_exp_i{8,16,32,64}`, and
 * `FExpP` -- which used to call this INTEGER helper on two floats -- emits
 * `powf`.
 *
 * The body is delegated rather than left as it was, so that an out-of-tree
 * caller gets the specified answer instead of the three bugs this had:
 * `base == 2` was computed as `1 << pow` where the `1` is an `int`, so
 * gib_expll(2, 31) returned -2147483648 and gib_expll(2, 40) returned 256
 * (shift count >= width); every other base looped `pow` times multiplying
 * signed values, which is undefined on overflow and takes O(pow) time; and a
 * negative exponent shifted by a negative count. */
int64_t gib_expll(int64_t base, int64_t pow)
{
    return gib_exp_i64(base, pow);
}

// https://www.cprogramming.com/snippets/source-code/find-the-number-of-cpu-cores-for-windows-mac-or-linux
int64_t gib_get_num_processors(void)
{
#ifdef _WIN64
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return sysinfo.dwNumberOfProcessors;
#else
    return sysconf(_SC_NPROCESSORS_ONLN);
#endif
}

// Requires -std=gnu11
int dbgprintf(const char *format, ...)
{
    int code = 0;
    va_list args;
    va_start(args, format);
#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 3
    code = vprintf(format, args);
#endif
    va_end(args);
    return code;
}

void check_args(int i, int argc, char **argv, char *parameter){
    if (i+1 >= argc) {
        fprintf(stderr, "Not enough arguments after %s, expected <int>.\n", parameter);
        gib_show_usage(argv);
        exit(1);
    }
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * RTS initialization and clean up
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Called from gib_main_expr.
int gib_init(int argc, char **argv)
{

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 2
    // Print the GC configuration.
    gib_print_gc_config();
#endif

    // Ensure that C and Rust agree on sizes of structs that cross the boundary.
    gib_check_rust_struct_sizes();

    // parameters to parse:
    //
    //   num iterations: How many times to repeat a benchmark.
    //   tree size: An integer passes to `build_tree()`.

    struct rlimit lim;
    int code;
    if ( (code = getrlimit(RLIMIT_STACK, &lim)) ) {
        fprintf(stderr, " [gibbon rts] failed to getrlimit, code %d\n", code);
        exit(1);
    }

    lim.rlim_cur = 4 * 1024LU * 1024LU * 1024LU; // 1GB stack.
    // lim.rlim_cur = 512LU * 1024LU * 1024LU; // 500MB stack.
    // lim.rlim_max = lim.rlim_cur; // Normal users may only be able to decrease this.

    // WARNING: Haven't yet figured out why this doesn't work on MacOS...
#ifndef __APPLE__
    code = setrlimit(RLIMIT_STACK, &lim);
    while (code) {
        fprintf(stderr, " [gibbon rts] Failed to set stack size to %lu, code %d\n",
                (uint64_t)lim.rlim_cur, code);
        lim.rlim_cur /= 2;
        // lim.rlim_max /= 2;
        if(lim.rlim_cur < 100 * 1024) {
            fprintf(stderr, " [gibbon rts] Failed setrlimit stack size to something reasonable; giving up.\n");
            break; // abort();
        }
        code = setrlimit(RLIMIT_STACK, &lim);
    }
#endif

    // int got_numargs = argc; // How many numeric arguments have we got.

    int i;
    for (i = 1; i < argc; ++i)
    {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            gib_show_usage(argv);
            exit(0);
        }
        else if (strcmp(argv[i], "--biginf-buffer-size") == 0 && i < argc - 1) {
            check_args(i, argc, argv, "--biginf-buffer-size");
            gib_global_biginf_init_chunk_size = atoll(argv[i + 1]);
            i++;
        }
        else if (strcmp(argv[i], "--inf-buffer-size") == 0 && i < argc - 1) {
            check_args(i, argc, argv, "--inf-buffer-size");
            gib_global_inf_init_chunk_size = atoll(argv[i + 1]);
            i++;
        }
        else if ((strcmp(argv[i], "--bench-input") == 0)) {
            check_args(i, argc, argv, "--bench-input");
            gib_global_benchfile_param = argv[i+1];
            i++;
        }
        else if ((strcmp(argv[i], "--array-input") == 0)) {
            check_args(i, argc, argv, "--array-input");
            gib_global_arrayfile_param = argv[i+1];
            i++;
        }
        else if (strcmp(argv[i], "--array-input-length") == 0 && i < argc - 1) {
            check_args(i, argc, argv, "--array-input-length");
            gib_global_arrayfile_length_param = atoll(argv[i+1]);
            i++;
        }
        else if (strcmp(argv[i], "--bench-prog") == 0 && i < argc - 1) {
            check_args(i, argc, argv, "--bench-prog");
            int len = strlen(argv[i+1]);
            gib_global_bench_prog_param = (char*) gib_alloc((len+1)*sizeof(char));
            strncpy(gib_global_bench_prog_param,argv[i+1],len);
            i++;
        }
        else if ((strcmp(argv[i], "--iterate") == 0)) {
            check_args(i, argc, argv, "--iterate");
            gib_global_iters_param = atoll(argv[i+1]);
            i++;
        }
        else if ((strcmp(argv[i], "--size-param") == 0)) {
            check_args(i, argc, argv, "--size-param");
            gib_global_size_param = atoll(argv[i+1]);
            i++;
        }
        // If present, we expect the two arguments to be <size> <iters>
        else {
            fprintf(stderr, "Extra arguments left over: ");
            for(; i < argc; i++) fprintf(stderr, "%s ", argv[i]);
            gib_show_usage(argv);
            exit(1);
        }
    }

    // Initialize gib_global_bench_prog_param to an empty string in case
    // the runtime argument --bench-prog isn't passed.
    if (gib_global_bench_prog_param == NULL) {
        gib_global_bench_prog_param = (char*) gib_alloc(1*sizeof(char));
        *gib_global_bench_prog_param = '\n';
    }

    // Initialize number of threads before the storage.
#ifdef _GIBBON_PARALLEL
    gib_global_num_threads = __cilkrts_get_nworkers();
#endif

#if defined _GIBBON_VERBOSITY && _GIBBON_VERBOSITY >= 2
    printf("Number of threads: %ld\n", gib_global_num_threads);
#endif

#ifndef _GIBBON_POINTER
    // Initialize the nursery and shadow stack.
    gib_storage_initialize();
    GibOldgen *oldgen = DEFAULT_GENERATION;
    gib_init_zcts(oldgen);

    // Minimal test to see if FFI is set up correctly.
    gib_check_rust_struct_sizes();

#endif // ifndef _GIBBON_POINTER

    return 0;
}

// Called from gib_main_expr.
int gib_exit(void)
{
    gib_free(gib_global_bench_prog_param);

#ifndef _GIBBON_POINTER

#ifdef _GIBBON_GCSTATS
    // Print GC statistics.
    gib_gc_stats_print(GC_STATS);
#endif

    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibOldgen *oldgen = DEFAULT_GENERATION;

    // Free all objects initialized by the Rust RTS.
    gib_gc_cleanup(rstack, wstack, nursery, oldgen);
    // Next, free all objects initialized by the C RTS.
    gib_storage_free();

#endif // ifndef _GIBBON_POINTER

    // gib_free_symtable();

    return 0;
}
