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

/*
 * CPP macros used in the RTS:
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * _GIBBON_VERBOSITY=int     verbosity level for debug output
 * _GIBBON_DEBUG             enables various assertions if present
 * _GIBBON_GCSTATS           collect GC statistics if present
 * _GIBBON_PRINT_GCSTATS     print GC statistics if present
 * _GIBBON_NONGENGC          only use old reference counted GC if present
 * _GIBBON_BOUNDSCHECK       boundscheck vector accesses
 * _GIBBON_BUMPALLOC_LISTS   bump allocated linked lists
 * _GIBBON_BUMPALLOC_HEAP    bump allocated gib_alloc
 * _GIBBON_POINTER           pointer mode gib_alloc
 * _GIBBON_PARALLEL          parallel mode
 * _GIBBON_NO_EAGER_PROMOTE  disable eager promotion
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


typedef uint8_t GibPackedTag;
typedef uint8_t GibBoxedTag;
typedef int64_t GibInt;
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

#define LIKELY(x) __builtin_expect((bool) (x), 1)
#define UNLIKELY(x) __builtin_expect((bool) (x), 0)

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
GibInt gib_get_size_param(void);
GibInt gib_get_iters_param(void);
char *gib_read_bench_prog_param(void);
char *gib_read_benchfile_param(void);
char *gib_read_arrayfile_param(void);
uint64_t gib_read_arrayfile_length_param(void);

// Number of regions allocated.
int64_t gib_read_region_count(void);

// Invariant: should always be equal to max(sym_table_keys).
GibSym gib_read_gensym_counter(void);


// Must be same as "Gibbon.Language.Constants".
#define GIB_REDIRECTION_TAG 255
#define GIB_INDIRECTION_TAG 254

// Tags reserved for the garbage collector.
#define GIB_CAUTERIZED_TAG 253
#define GIB_COPIED_TO_TAG 252
#define GIB_COPIED_TAG 251
#define GIB_SCALAR_TAG 250


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

GibVector *gib_vector_alloc(GibInt num, size_t elt_size);
GibInt gib_vector_length(GibVector *vec);
GibBool gib_vector_is_empty(GibVector *vec);
GibVector *gib_vector_slice(GibInt i, GibInt n, GibVector *vec);
void *gib_vector_nth(GibVector *vec, GibInt i);
GibVector *gib_vector_inplace_update(GibVector *vec, GibInt i, void* elt);
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

typedef struct gib_pixel {
    GibInt field0;
    GibInt field1;
    GibInt field2;
} GibPixel;

void gib_write_ppm(char* filename, GibInt width, GibInt height, GibVector *pixels);
void gib_write_ppm_loop(FILE *fp, GibInt idx, GibInt end, GibVector *pixels);

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Threads and parallelism
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// TODO(ckoparkar): only a single thread for now.
// extern uint64_t gib_global_num_threads;
// extern GibThreadId gib_thread_id();

#define gib_global_num_threads 1
#define gib_thread_id() 0


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Memory Management; regions, chunks, GC etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


typedef struct gib_chunk {
    GibCursor start;
    GibCursor end;
} GibChunk;

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
} GibOldgenChunkFooter;

typedef uint16_t GibNurseryChunkFooter;

typedef struct gib_gc_stats {
    // Number of copying minor collections (maintained by Rust RTS).
    uint64_t minor_collections;

    // Number of copying major collections (maintained by Rust RTS).
    uint64_t major_collections;

    // Overall memory allocated (maintained by C and Rust RTS).
    size_t mem_allocated;

    // Overall memory copied (maintained by Rust RTS).
    size_t mem_copied;

    // Overall memory burned (maintained by Rust RTS).
    size_t mem_burned;

    // Total number of forwarding pointers that could be added vs not added.
    uint64_t forwarded;
    uint64_t not_forwarded;

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


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ensure that C and Rust agree on sizes
 * of structs that cross the boundary.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
void gib_check_rust_struct_sizes(void);

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

#define GIB_MAX_CHUNK_SIZE 65500

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


INLINE_HEADER void gib_grow_region(char **writeloc_addr, char **footer_addr)
{
    char *footer_ptr = *footer_addr;
    size_t newsize;
    bool old_chunk_in_nursery;
    GibOldgenChunkFooter *old_footer = NULL;

    if (gib_addr_in_nursery(footer_ptr)) {
        old_chunk_in_nursery = true;
        GibNurseryChunkFooter oldsize = *(GibNurseryChunkFooter *) footer_ptr;
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

#ifdef _GIBBON_DISABLE_EAGER_PROMOTION
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
#endif

        nursery->alloc = bump;
        char *footer = old - sizeof(GibNurseryChunkFooter);
        *(GibNurseryChunkFooter *) footer = size;
        char *heap_start = bump;
        char *heap_end = footer;

        // Write a redirection tag at writeloc and make it point to the start of
        // this fresh chunk, but store a tagged pointer here.
        uint16_t new_footer_offset = heap_end - heap_start;
        GibTaggedPtr tagged = GIB_STORE_TAG(heap_start, new_footer_offset);
        GibCursor writeloc = *writeloc_addr;
        *(GibPackedTag *) writeloc = GIB_REDIRECTION_TAG;
        writeloc += 1;
        *(GibTaggedPtr *) writeloc = tagged;

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
    char *heap_start = (char *) gib_alloc(size);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_grow_region: gib_alloc failed: %zu", size);
        exit(1);
    }
    char *heap_end = heap_start + size;

#ifdef _GIBBON_GCSTATS
    GC_STATS->oldgen_chunks++;
    GC_STATS->mem_allocated += size;
#endif

    // Write a new footer for this chunk and link it with the old chunk's footer.
    char *new_footer_start = NULL;
    GibOldgenChunkFooter *new_footer = NULL;
    if (old_chunk_in_nursery) {
        new_footer_start = gib_init_footer_at(heap_end, size, 0);
        new_footer = (GibOldgenChunkFooter *) new_footer_start;
        gib_insert_into_new_zct(DEFAULT_GENERATION, new_footer->reg_info);
    } else {
        new_footer_start = heap_end - sizeof(GibOldgenChunkFooter);
        new_footer = (GibOldgenChunkFooter *) new_footer_start;
        new_footer->reg_info = old_footer->reg_info;
        new_footer->size = (size_t) (new_footer_start - heap_start);
        new_footer->next = (GibOldgenChunkFooter *) NULL;
        // Link with the old chunk's footer.
        old_footer->next = (GibOldgenChunkFooter *) new_footer;
    }

    // Write a redirection tag at writeloc and make it point to the start of
    // this fresh chunk, but store a tagged pointer here.
    uint16_t new_footer_offset = new_footer_start - heap_start;
    GibTaggedPtr tagged = GIB_STORE_TAG(heap_start, new_footer_offset);
    GibCursor writeloc = *writeloc_addr;
    *(GibPackedTag *) writeloc = GIB_REDIRECTION_TAG;
    writeloc += 1;
    *(GibTaggedPtr *) writeloc = tagged;

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
               frame->ptr, frame->endptr, frame->datatype);
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
    {
        // Optimization: don't create long chains of indirection pointers.
        GibPackedTag pointed_to_tag = *(GibPackedTag *) to;
        char *after_pointed_to_tag = to + 1;
        uintptr_t tagged_ptr;
        char *pointee, *pointee_end;
        uint16_t pointee_offset;
        while (pointed_to_tag == GIB_INDIRECTION_TAG) {
            tagged_ptr = *(uintptr_t *) after_pointed_to_tag;
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
    // Write the indirection.
    uint16_t footer_offset = to_footer - to;
    GibTaggedPtr tagged = GIB_STORE_TAG(to, footer_offset);
    GibCursor writeloc = from;
    *(GibPackedTag *) writeloc = GIB_INDIRECTION_TAG;
    writeloc += sizeof(GibPackedTag);
    *(GibTaggedPtr *) writeloc = tagged;

    // If we're using the non-generational GC, all indirections will be
    // old-to-old indirections.

#ifdef _GIBBON_NONGENGC
    gib_add_old_to_old_indirection(from_footer, to_footer);
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
#endif // _GIBBON_NONGENGC
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
GibInt gib_expll(GibInt base, GibInt pow);
GibInt gib_get_num_processors(void);

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
    asm volatile("" : : "g"(p) : "memory");
}

// From Chandler Carruth's CppCon 2015 talk.
INLINE_HEADER void clobber() {
    asm volatile("" : : : "memory");
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * RTS initialization and clean up
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

size_t gib_nursery_realloc(GibNursery *nursery, size_t nsize);
int gib_init(int argc, char **argv);
int gib_exit(void);

#endif // #ifndef _GIBBON_H
