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
extern long long global_init_biginf_buf_size;
extern long long global_init_inf_buf_size;
extern long long global_max_chunk_size;

// Runtime arguments, values updated by the flags parser.
extern long long global_size_param;
extern long long global_iters_param;
extern char *global_bench_prog_param;
extern char *global_benchfile_param;
extern char *global_arrayfile_param;
extern long long global_arrayfile_length_param;

// Number of regions allocated.
extern long long global_region_count;

// Invariant: should always be equal to max(sym_table_keys).
extern SymTy global_gensym_counter;


/* -----------------------------------------------------------------------------
 * Helpers
 * -----------------------------------------------------------------------------
 */

char *read_benchfile_param();
char *read_arrayfile_param();
long long read_arrayfile_length_param();
void show_usage(char **argv);
double avg(const double* arr, int n);
double difftimespecs(struct timespec *t0, struct timespec *t1);
int compare_doubles(const void *a, const void *b);
long long expll(long long base, long long pow);
int get_num_processors();


/* -----------------------------------------------------------------------------
 * Shorthands
 * -----------------------------------------------------------------------------
 */

#define KB 1024lu
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

#define MAX(a,b) (((a)>(b))?(a):(b))
#define MIN(a,b) (((a)<(b))?(a):(b))


/* -----------------------------------------------------------------------------
 * Allocators
 * -----------------------------------------------------------------------------
 */


/* -------------------------------------
 * Bump allocation for linked-lists
 * -------------------------------------
 */

extern __thread char *bumpalloc_heap_ptr;
extern __thread char* bumpalloc_heap_ptr_end;
extern char *saved_heap_ptr_stack[100];
extern int num_saved_heap_ptr;

void init_bumpalloc();
void *bump_alloc(long long n);
void save_alloc_state();
void restore_alloc_state();


/* -------------------------------------
 * Bump allocated nursery for regions.
 * See GitHub #122.
 * -------------------------------------
 */

#define NURSERY_SIZE 0
#define NURSERY_ALLOC_UPPER_BOUND 1024

extern __thread char *nursery_heap_ptr;
extern __thread char *nursery_heap_ptr_end;

void init_nursery();
void *alloc_in_nursery(long long n);



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

ArenaTy alloc_arena();
void free_arena(ArenaTy ar);
CursorTy extend_arena(ArenaTy ar, int size);


/* -------------------------------------
 * Arena-based dictionaries
 * -------------------------------------
 */

typedef struct dict_item {
  struct dict_item * next;
  int key;
  void * ptrval;
} dict_item_t;


dict_item_t *dict_alloc(ArenaTy ar);
dict_item_t *dict_insert_ptr(ArenaTy ar, dict_item_t *ptr, SymTy key, PtrTy val);
PtrTy dict_lookup_ptr(dict_item_t *ptr, SymTy key);


/* -----------------------------------------------------------------------------
 * Sets
 * -----------------------------------------------------------------------------
 */

struct set_elem {
  int val;
  UT_hash_handle hh;
};

typedef struct set_elem* SymSetTy;

SymSetTy empty_set();
SymSetTy insert_set(SymSetTy set, int sym);
BoolTy contains_set(SymSetTy set, int sym);


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

SymHashTy empty_hash();
SymHashTy insert_hash(SymHashTy hash, int k, int v);
IntTy lookup_hash(SymHashTy hash, int k);
BoolTy contains_hash(SymHashTy hash, int sym);


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

void add_symbol(SymTy idx, char *value);
void set_newline(SymTy idx);
void set_space(SymTy idx);
void set_comma(SymTy idx);
void set_leftparen(SymTy idx);
void set_rightparen(SymTy idx);
int print_symbol(SymTy idx);
SymTy gensym();
void free_symtable();


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

void insert_into_outset(CursorTy ptr, RegionTy *reg);
void remove_from_outset(CursorTy ptr, RegionTy *reg);
RegionTy *alloc_region(IntTy size);
RegionTy *alloc_counted_region(IntTy size);
ChunkTy alloc_chunk(CursorTy end_old_chunk);
RegionFooter *trav_to_first_chunk(RegionFooter *footer);
uint get_ref_count(CursorTy end_ptr);
void bump_ref_count(CursorTy end_b, CursorTy end_a);
void free_region(CursorTy end_reg);
BoolTy is_big(IntTy i, CursorTy cur);
void bump_global_region_count();
void print_global_region_count();



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

VectorTy *vector_alloc(IntTy num, IntTy elt_size);
IntTy vector_length(VectorTy *vec);
BoolTy vector_is_empty(VectorTy *vec);
VectorTy *vector_slice(IntTy i, IntTy n, VectorTy *vec);
void* vector_nth(VectorTy *vec, IntTy i);
VectorTy *vector_inplace_update(VectorTy *vec, IntTy i, void* elt);
VectorTy *vector_copy(VectorTy *vec);
VectorTy *vector_inplace_sort(VectorTy *vec, int (*compar)(const void *, const void*));
VectorTy *vector_sort(VectorTy *vec, int (*compar)(const void *, const void*));
VectorTy *vector_concat(VectorTy *vec);
void vector_free(VectorTy *vec);
VectorTy *vector_merge(VectorTy *vec1, VectorTy *vec2);
void print_timing_array(VectorTy *times);
double sum_timing_array(VectorTy *times);


/* -----------------------------------------------------------------------------
 * Linked lists
 * -----------------------------------------------------------------------------
 */

typedef struct ListTy_struct {
    IntTy ll_data_size;
    void *ll_data;
    struct ListTy_struct* ll_next;
} ListTy;

ListTy *list_alloc(IntTy data_size);
BoolTy list_is_empty(ListTy *ls);
ListTy *list_cons(void *elt, ListTy *ls);
void *list_head(ListTy *ls);
ListTy *list_tail(ListTy *ls);
void list_free(ListTy *ls);
ListTy *list_copy(ListTy *ls);


/* -----------------------------------------------------------------------------
 * Ppm images
 * -----------------------------------------------------------------------------
 */

typedef struct __Pixel_struct {
    IntTy field0;
    IntTy field1;
    IntTy field2;
} __Pixel;

void writePpm(char* filename, IntTy width, IntTy height, VectorTy *pixels);
void writePpm_loop(FILE *fp, IntTy idx, IntTy end, VectorTy *pixels);


/* -----------------------------------------------------------------------------
 * Main functions
 * -----------------------------------------------------------------------------
 */


// fun fact: __ prefix is actually reserved and this is an undefined behavior.
// This function must be provided by the code generator.
int __main_expr();

int main(int argc, char** argv);


#endif // _GIBBON_H_
