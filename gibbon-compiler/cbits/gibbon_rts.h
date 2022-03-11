#ifndef _GIBBON_H
#define _GIBBON_H

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <uthash.h>

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
typedef float GibFloat;
typedef uint64_t GibSym;
typedef bool GibBool;
typedef char* GibPtr;
typedef char* GibCursor;
typedef uint64_t GibThreadId;


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
static const uintptr_t GIB_POINTER_MASK = (UINTPTR_MAX >> GIB_TAG_BITS);

#define GIB_STORE_TAG(ptr, tag)                                               \
    (uintptr_t) (((uintptr_t) ptr) | (((uintptr_t) tag) << GIB_POINTER_BITS)) \

#define GIB_UNTAG(tagged)                              \
    (char *) (((uintptr_t) tagged) & GIB_POINTER_MASK) \

#define GIB_GET_TAG(tagged)                               \
    (uint16_t) (((uintptr_t) tagged) >> GIB_POINTER_BITS) \


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Allocators
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void *gib_alloc(size_t size);
void *gib_counted_alloc(size_t size);
void *gib_scoped_alloc(size_t size);


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

typedef struct gib_shadowstack_frame {
    // Pointer to packed data.
    char *ptr;

    // Pointer to the end of the chunk where this packed data lives.
    char *endptr;

    // An enum in C, which is 4 bytes.
    // The enum (GibDatatype) will be defined in the generated program.
    uint32_t datatype;
} GibShadowstackFrame;

// Type snonyms for convenience.
typedef GibShadowstackFrame GibRememberedSetElt;
typedef GibShadowstack GibRememberedSet;

// Abstract definitions are sufficient.
typedef struct gib_nursery GibNursery;
typedef struct gib_generation GibGeneration;
typedef struct gib_region_info GibRegionInfo;

// Array of nurseries, indexed by thread_id.
extern GibNursery *gib_global_nurseries;

// Shadow stacks for readable and writeable locations respectively,
// indexed by thread_id.
//
// TODO(ckoparkar): not clear how shadow stacks would be when we have
// parallel mutators.. These arrays are abstract enough for now.
extern GibShadowstack *gib_global_read_shadowstacks;
extern GibShadowstack *gib_global_write_shadowstacks;

// Convenience macros since we don't really need the arrays of nurseries and
// shadowstacks since mutators are still sequential.
// #define DEFAULT_NURSERY gib_global_nurseries
#define DEFAULT_NURSERY (&(gib_global_nurseries[0]))
#define DEFAULT_READ_SHADOWSTACK (&(gib_global_read_shadowstacks[0]))
#define DEFAULT_WRITE_SHADOWSTACK (&(gib_global_write_shadowstacks[0]))

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
void gib_grow_region(char **writeloc_addr, char **footer_addr);

// Functions related to counting the number of allocated regions.
GibChunk gib_alloc_counted_region(size_t size);
void gib_print_global_region_count(void);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Nursery
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
bool gib_addr_in_nursery(char *ptr);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow-stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void gib_shadowstack_push(
    GibShadowstack *stack,
    char *ptr,
    char *endptr,
    uint32_t datatype
);
GibShadowstackFrame *gib_shadowstack_pop(GibShadowstack *stack);
int32_t gib_shadowstack_length(GibShadowstack *stack);
void gib_shadowstack_print_all(GibShadowstack *stack);

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Remembered set
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
#define gib_remset_push(stack, ptr, endptr, datatype) \
    gib_shadowstack_push(stack, ptr, (char *) endptr, datatype)
#define gib_remset_pop(stack) \
    gib_shadowstack_pop(stack)
#define gib_remset_length(stack) \
    gib_shadowstack_length(stack)
#define gib_remset_print_all(stack) \
    gib_shadowstack_print_all(stack)
void gib_remset_reset(GibRememberedSet *set);


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Write barrier
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * INLINE!!!
 *
 */
void gib_indirection_barrier(
    GibCursor from,
    GibCursor from_footer_ptr,
    GibCursor to,
    GibCursor to_footer_ptr,
    uint32_t datatype
);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Implemented in the Rust RTS
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

int gib_info_table_initialize(void);
int gib_info_table_insert_scalar(uint32_t datatype, size_t size);
int gib_info_table_insert_packed_dcon(
    uint32_t datatype,
    uint8_t datacon,
    size_t scalar_bytes,
    uint8_t num_scalars,
    uint8_t num_packed,
    uint32_t *field_tys,
    uint8_t field_tys_length
);
int gib_garbage_collect(
    GibShadowstack *rstack,
    GibShadowstack *wstack,
    GibNursery *nursery,
    GibGeneration *generations,
    bool force_major
);
int gib_handle_old_to_old_indirection(
    char *from_footer,
    char *to_footer
);
char *gib_init_footer_at(
    char *chunk_end,
    size_t chunk_size,
    uint16_t refcount
);
void gib_init_zcts(GibGeneration *generations);
void gib_add_to_old_zct(
    GibGeneration *generations,
    GibRegionInfo *reg_info
);
int gib_gc_cleanup(
    GibShadowstack *rstack,
    GibShadowstack *wstack,
    GibNursery *nursery,
    GibGeneration *generations
);
void gib_get_rust_struct_sizes(
    size_t *stack,
    size_t *frame,
    size_t *nursery,
    size_t *generation,
    size_t *reg_info,
    size_t *footer
);


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


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Main functions
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


// This function must be provided by the code generator.
int gib_main_expr(void);

// Defined in the RTS.
int main(int argc, char** argv);


#endif // #ifndef _GIBBON_H
