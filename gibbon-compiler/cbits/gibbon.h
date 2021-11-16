#ifndef _GIBBON_H
#define _GIBBON_H 1

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
 * Other declarations use regular C types:
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


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Globals and their accessors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/*
 * These globals don't need to be delcared here; they can be
 * accessed using the functions given below.
 *

// Chunk sizes of buffers, see GitHub #79 and #110.
extern int64_t gib_global_biginf_init_chunk_size;
extern int64_t gib_global_inf_init_chunk_size;
extern int64_t gib_global_max_chunk_size;

// Runtime arguments, values updated by the flags parser.
extern GibInt gib_global_size_param;
extern GibInt gib_global_iters_param;
extern char *gib_global_bench_prog_param;
extern char *gib_global_benchfile_param;
extern char *gib_global_arrayfile_param;
extern int64_t gib_global_arrayfile_length_param;

// Number of regions allocated.
extern int64_t gib_global_region_count;

// Invariant: should always be equal to max(sym_table_keys).
extern GibSym gib_global_gensym_counter;

 *
 */


// Chunk sizes of buffers, see GitHub #79 and #110.
uint64_t gib_get_biginf_init_chunk_size(void);
uint64_t gib_get_inf_init_chunk_size(void);

// Runtime arguments, values updated by the flags parser.
GibInt gib_get_size_param(void);
GibInt gib_get_iters_param(void);
char *gib_read_bench_prog_param(void);
char *gib_read_benchfile_param(void);
char *gib_read_arrayfile_param(void);
int64_t gib_read_arrayfile_length_param(void);

// Number of regions allocated.
int64_t gib_read_region_count(void);

// Invariant: should always be equal to max(sym_table_keys).
GibSym gib_read_gensym_counter(void);


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
 * Shorthands
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define KB 1024lu
#define MB (KB * 1024lu)
#define GB (MB * 1024lu)


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Allocators
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Bump allocation for linked-lists
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void gib_init_bumpalloc(void);
void *gib_bumpalloc(int64_t n);
void gib_save_alloc_state(void);
void gib_restore_alloc_state(void);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Bump allocated nursery for regions.
 * See GitHub #122.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


void gib_init_nursery(void);
void *gib_alloc_in_nursery(int64_t n);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Various allocators
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

void *gib_alloc(uint64_t size);
void *gib_counted_alloc(uint64_t size);
void *gib_scoped_alloc(uint64_t size);


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
 * Memory Management; regions, chunks, GC etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define MAX_OUTSET_LENGTH 10

typedef struct gib_region_meta {
    GibSym reg_id;
    uint16_t reg_refcount;
    GibCursor reg_heap;
    uint16_t reg_outset_len;
    GibCursor reg_outset[MAX_OUTSET_LENGTH];
} GibRegionMeta;

typedef struct gib_region_footer {
    GibRegionMeta *rf_reg_metadata_ptr;

    int64_t rf_seq_no;
    bool rf_nursery_allocated;
    uint64_t rf_size;
    struct gib_region_footer *rf_next;
    struct gib_region_footer *rf_prev;
} GibRegionFooter;

typedef struct gib_chunk {
    GibCursor chunk_start;
    GibCursor chunk_end;
} GibChunk;

GibRegionMeta *gib_alloc_region(uint64_t size);
GibChunk gib_alloc_chunk(GibCursor end_old_chunk);
void gib_bump_refcount(GibCursor end_b, GibCursor end_a);
void gib_free_region(GibCursor end_reg);

// Helpers for GC.
void gib_insert_into_outset(GibCursor ptr, GibRegionMeta *reg);
void gib_remove_from_outset(GibCursor ptr, GibRegionMeta *reg);
GibRegionFooter *gib_trav_to_first_chunk(GibRegionFooter *footer);
uint16_t gib_get_ref_count(GibCursor end_ptr);
GibBool gib_is_big(GibInt i, GibCursor cur);

// Functions related to counting the number of allocated regions.
GibRegionMeta *gib_alloc_counted_region(int64_t size);
void gib_bump_global_region_count(void);
void gib_print_global_region_count(void);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * New RTS
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_cursors_pair {
    GibCursor cp_start;
    GibCursor cp_end;
} GibCursorsPair;

GibCursorsPair *gib_alloc_region2(uint64_t size);
int gib_init_info_table(void);
int gib_insert_dcon_into_info_table(
    uint32_t datatype,
    uint8_t datacon,
    uint8_t num_scalars,
    uint8_t num_packed,
    uint32_t *field_tys,
    uint8_t field_tys_length
);

// Only use this while testing the Rust RTS!
void gib_reset_nursery(void);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Vectors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_vector {
    // Bounds on the vector.
    int64_t vec_lower, vec_upper;

    // Size of each element.
    size_t vec_elt_size;

    // Actual elements of the vector.
    void *vec_data;
} GibVector;

GibVector *gib_vector_alloc(GibInt num, size_t elt_size);
GibInt gib_vector_length(GibVector *vec);
GibBool gib_vector_is_empty(GibVector *vec);
GibVector *gib_vector_slice(GibInt i, GibInt n, GibVector *vec);
void *gib_vector_nth(GibVector *vec, GibInt i);
GibVector *gib_vector_inplace_update(GibVector *vec, GibInt i, void* elt);
GibVector *gib_vector_copy(GibVector *vec);
GibVector *gib_vector_inplace_sort(GibVector *vec, int (*compar)(const void *, const void*));
GibVector *gib_vector_sort(GibVector *vec, int (*compar)(const void *, const void*));
GibVector *gib_vector_concat(GibVector *vec);
void gib_vector_free(GibVector *vec);
GibVector *gib_vector_merge(GibVector *vec1, GibVector *vec2);
void gib_print_timing_array(GibVector *times);
double gib_sum_timing_array(GibVector *times);


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Linked lists
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_list {
    size_t ll_data_size;
    void *ll_data;
    struct gib_list* ll_next;
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
 * Main functions
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


// This function must be provided by the code generator.
int gib_main_expr(void);

int main(int argc, char** argv);


#endif // #ifndef _GIBBON_H
