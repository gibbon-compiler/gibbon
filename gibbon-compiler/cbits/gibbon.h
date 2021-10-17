#ifndef _GIBBON_H_
#define _GIBBON_H_

#include <stdio.h>
#include <stdint.h>
#include <stdbool.h>
#include <uthash.h>

/* -----------------------------------------------------------------------------
 * Basic types
 * -----------------------------------------------------------------------------
 */

// Must be consistent with sizeOfTy defined in Gibbon.Language.Syntax.

typedef unsigned char TagTyPacked;
typedef unsigned char TagTyBoxed;
typedef long long IntTy;
typedef float FloatTy;
typedef unsigned long long SymTy;
typedef bool BoolTy;
typedef char* PtrTy;
typedef char* CursorTy;


/* -----------------------------------------------------------------------------
 * Common Globals
 * -----------------------------------------------------------------------------
 */

// Chunk sizes of buffers, see GitHub #79 and #110.
extern long long gib_global_biginf_init_chunk_size;
extern long long gib_global_inf_init_chunk_size;
extern long long gib_global_max_chunk_size;

// Runtime arguments, values updated by the flags parser.
extern long long gib_global_size_param;
extern long long gib_global_iters_param;
extern char *gib_global_bench_prog_param;
extern char *gib_global_benchfile_param;
extern char *gib_global_arrayfile_param;
extern long long gib_global_arrayfile_length_param;

// Number of regions allocated.
extern long long gib_global_region_count;

// Invariant: should always be equal to max(sym_table_keys).
extern SymTy gib_global_gensym_counter;


/* -----------------------------------------------------------------------------
 * Helpers
 * -----------------------------------------------------------------------------
 */

char *gib_read_benchfile_param();
char *gib_read_arrayfile_param();
long long gib_read_arrayfile_length_param();
void gib_show_usage(char **argv);
double gib_avg(const double* arr, int n);
double gib_difftimespecs(struct timespec *t0, struct timespec *t1);
int gib_compare_doubles(const void *a, const void *b);
long long gib_expll(long long base, long long pow);
int gib_get_num_processors();


/* -----------------------------------------------------------------------------
 * Shorthands
 * -----------------------------------------------------------------------------
 */

#define KB 1024lu
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)


/* -----------------------------------------------------------------------------
 * Allocators
 * -----------------------------------------------------------------------------
 */


/* -------------------------------------
 * Bump allocation for linked-lists
 * -------------------------------------
 */

extern __thread char *gib_global_bumpalloc_heap_ptr;
extern __thread char *gib_global_bumpalloc_heap_ptr_end;
extern char *gib_global_saved_heap_ptr_stack[100];
extern int gib_global_num_saved_heap_ptr;

void gib_init_bumpalloc();
void *gib_bumpalloc(long long n);
void gib_save_alloc_state();
void gib_restore_alloc_state();


/* -------------------------------------
 * Bump allocated nursery for regions.
 * See GitHub #122.
 * -------------------------------------
 */

#define NURSERY_SIZE 0
#define NURSERY_ALLOC_UPPER_BOUND 1024

extern __thread char *gib_global_nursery_heap_ptr;
extern __thread char *gib_global_nursery_heap_ptr_end;

void gib_init_nursery();
void *gib_alloc_in_nursery(long long n);


/* -----------------------------------------------------------------------------
 * Arenas
 * -----------------------------------------------------------------------------
 */

typedef struct mem_arena {
  int ind;
  char* mem; // TODO(vollmerm): make this a list of chunks?
  void* reflist;
} mem_arena_t;

typedef mem_arena_t* ArenaTy;

ArenaTy gib_alloc_arena();
void gib_free_arena(ArenaTy ar);
CursorTy gib_extend_arena(ArenaTy ar, int size);


/* -------------------------------------
 * Arena-based dictionaries
 * -------------------------------------
 */

typedef struct dict_item {
  struct dict_item * next;
  int key;
  void * ptrval;
} dict_item_t;


dict_item_t *gib_dict_alloc(ArenaTy ar);
dict_item_t *gib_dict_insert_ptr(ArenaTy ar, dict_item_t *ptr, SymTy key, PtrTy val);
PtrTy gib_dict_lookup_ptr(dict_item_t *ptr, SymTy key);


/* -----------------------------------------------------------------------------
 * Sets
 * -----------------------------------------------------------------------------
 */

struct set_elem {
  int val;
  UT_hash_handle hh;
};

typedef struct set_elem* SymSetTy;

SymSetTy gib_empty_set();
SymSetTy gib_insert_set(SymSetTy set, int sym);
BoolTy gib_contains_set(SymSetTy set, int sym);


/* -----------------------------------------------------------------------------
 * Sym Hash
 * -----------------------------------------------------------------------------
 */

struct sym_hash_elem {
  int key;
  int val;
  UT_hash_handle hh;
};

typedef struct sym_hash_elem* SymHashTy;
typedef struct sym_hash_elem* IntHashTy;

SymHashTy gib_empty_hash();
SymHashTy gib_insert_hash(SymHashTy hash, int k, int v);
IntTy gib_lookup_hash(SymHashTy hash, int k);
BoolTy gib_contains_hash(SymHashTy hash, int sym);


/* -----------------------------------------------------------------------------
 * Symbol table
 * -----------------------------------------------------------------------------
 */

#define MAX_SYMBOL_LEN 256

typedef struct SymTable_elem {
    SymTy idx;                 /* key */
    char value[MAX_SYMBOL_LEN];
    UT_hash_handle hh;         /* makes this structure hashable */
} SymTable_elem;

extern SymTable_elem *global_sym_table;

void gib_add_symbol(SymTy idx, char *value);
void gib_set_newline(SymTy idx);
void gib_set_space(SymTy idx);
void gib_set_comma(SymTy idx);
void gib_set_leftparen(SymTy idx);
void gib_set_rightparen(SymTy idx);
int gib_print_symbol(SymTy idx);
SymTy gib_gensym();
void gib_free_symtable();


/* -----------------------------------------------------------------------------
 * Memory Management; regions, chunks, GC etc.
 * -----------------------------------------------------------------------------
 */

#define MAX_OUTSET_LENGTH 10

typedef struct RegionTy_struct {
    SymTy reg_id;
    uint reg_refcount;
    CursorTy reg_heap;
    uint reg_outset_len;
    CursorTy reg_outset[MAX_OUTSET_LENGTH];
} RegionTy;

typedef struct RegionFooter_struct {
    RegionTy *rf_reg_metadata_ptr;

    IntTy rf_seq_no;
    bool rf_nursery_allocated;
    IntTy rf_size;
    struct RegionFooter_struct *rf_next;
    struct RegionFooter_struct *rf_prev;
} RegionFooter;

typedef struct ChunkTy_struct {
    CursorTy chunk_start;
    CursorTy chunk_end;
} ChunkTy;

void gib_insert_into_outset(CursorTy ptr, RegionTy *reg);
void gib_remove_from_outset(CursorTy ptr, RegionTy *reg);
RegionTy *gib_alloc_region(IntTy size);
RegionTy *gib_alloc_counted_region(IntTy size);
ChunkTy gib_alloc_chunk(CursorTy end_old_chunk);
RegionFooter *gib_trav_to_first_chunk(RegionFooter *footer);
uint gib_get_ref_count(CursorTy end_ptr);
void gib_bump_refcount(CursorTy end_b, CursorTy end_a);
void gib_free_region(CursorTy end_reg);
BoolTy gib_is_big(IntTy i, CursorTy cur);
void gib_bump_global_region_count();
void gib_print_global_region_count();



/* -----------------------------------------------------------------------------
 * Vectors
 * -----------------------------------------------------------------------------
 */

typedef struct VectorTy_struct {
    // Bounds on the vector.
    IntTy vec_lower, vec_upper;

    // Size of each element.
    IntTy vec_elt_size;

    // Actual elements of the vector.
    void* vec_data;
} VectorTy;

VectorTy *gib_vector_alloc(IntTy num, IntTy elt_size);
IntTy gib_vector_length(VectorTy *vec);
BoolTy gib_vector_is_empty(VectorTy *vec);
VectorTy *gib_vector_slice(IntTy i, IntTy n, VectorTy *vec);
void* gib_vector_nth(VectorTy *vec, IntTy i);
VectorTy *gib_vector_inplace_update(VectorTy *vec, IntTy i, void* elt);
VectorTy *gib_vector_copy(VectorTy *vec);
VectorTy *gib_vector_inplace_sort(VectorTy *vec, int (*compar)(const void *, const void*));
VectorTy *gib_vector_sort(VectorTy *vec, int (*compar)(const void *, const void*));
VectorTy *gib_vector_concat(VectorTy *vec);
void gib_vector_free(VectorTy *vec);
VectorTy *gib_vector_merge(VectorTy *vec1, VectorTy *vec2);
void gib_print_timing_array(VectorTy *times);
double gib_sum_timing_array(VectorTy *times);


/* -----------------------------------------------------------------------------
 * Linked lists
 * -----------------------------------------------------------------------------
 */

typedef struct ListTy_struct {
    IntTy ll_data_size;
    void *ll_data;
    struct ListTy_struct* ll_next;
} ListTy;

ListTy *gib_list_alloc(IntTy data_size);
BoolTy gib_list_is_empty(ListTy *ls);
ListTy *gib_list_cons(void *elt, ListTy *ls);
void *gib_list_head(ListTy *ls);
ListTy *gib_list_tail(ListTy *ls);
void gib_list_free(ListTy *ls);
ListTy *gib_list_copy(ListTy *ls);


/* -----------------------------------------------------------------------------
 * Ppm images
 * -----------------------------------------------------------------------------
 */

typedef struct __Pixel_struct {
    IntTy field0;
    IntTy field1;
    IntTy field2;
} __Pixel;

void gib_write_ppm(char* filename, IntTy width, IntTy height, VectorTy *pixels);
void gib_write_ppm_loop(FILE *fp, IntTy idx, IntTy end, VectorTy *pixels);


/* -----------------------------------------------------------------------------
 * Main functions
 * -----------------------------------------------------------------------------
 */


// This function must be provided by the code generator.
int gib_main_expr();

int main(int argc, char** argv);


#endif // _GIBBON_H_
