#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <math.h>
#include <stdbool.h>
#include <string.h>
#include <time.h>
#include <alloca.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
// #include <sys/sysinfo.h>
#ifdef _WIN64
#include <windows.h>
#endif
#include <unistd.h>
#include <fcntl.h>
#include <stdarg.h> // For va_start etc
#include <errno.h>
#include <utlist.h>
#include <uthash.h>
#include <utarray.h>
#ifdef _POINTER
#include <gc.h>
#endif
#ifdef _PARALLEL
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#endif

#define KB 1024lu
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

#define REDIRECTION_TAG 255
#define INDIRECTION_TAG 254

// Initial size of BigInfinite buffers
static long long global_init_biginf_buf_size = (4 * GB);

// Initial size of Infinite buffers
static long long global_init_inf_buf_size = 512;

// Maximum size of a chunk, see GitHub #110.
static long long global_inf_buf_max_chunk_size = 1 * GB;

static long long global_size_param = 1;
static long long global_iters_param = 1;

static char* global_benchfile_param = NULL;
static char* global_arrayfile_param = NULL;
// Number of lines in the arrayfile
static long long global_arrayfile_length_param = -1;

// Sequential for now:
static const int num_workers = 1;

// Count the number of regions allocated.
static long long global_region_count = 0;
static bool global_region_count_flag = false;

#ifdef _PARALLEL
static inline void bump_global_region_count() {
    __atomic_add_fetch(&global_region_count, 1, __ATOMIC_SEQ_CST);
    return;
}
#else
static inline void bump_global_region_count() {
    global_region_count++;
    return;
}
#endif

static inline void print_global_region_count() {
    printf("REGION_COUNT: %lld\n", global_region_count);
    return;
}

#define REDIRECTION_NODE_SIZE 9
#define MAX(a,b) (((a)>(b))?(a):(b))
#define MIN(a,b) (((a)<(b))?(a):(b))

// https://www.cprogramming.com/snippets/source-code/find-the-number-of-cpu-cores-for-windows-mac-or-linux
static int get_num_processors() {
#ifdef _WIN64
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return sysinfo.dwNumberOfProcessors;
#else
    return sysconf(_SC_NPROCESSORS_ONLN);
#endif
}

// Requires -std=gnu11
int dbgprintf(const char *format, ...) {
    int code = 0;
    va_list args;
    va_start(args, format);
#ifdef _DEBUG
    code = vprintf(format, args);
#endif
    va_end(args);
    return code;
}


// -----------------------------------------------------------------------------
// Allocators
// -----------------------------------------------------------------------------


// -------------------------------------
// Bump allocation for linked-lists
// -------------------------------------


#ifdef _BUMPALLOC
// #define _DEBUG
#warning "Using bump allocator."

__thread char* bumpalloc_heap_ptr = (char*)NULL;
__thread char* bumpalloc_heap_ptr_end = (char*)NULL;

char* saved_heap_ptr_stack[100];
int num_saved_heap_ptr = 0;

// For simplicity just use a single large slab:
static inline void INITBUMPALLOC() {
      bumpalloc_heap_ptr = (char*)malloc(global_init_biginf_buf_size);
      bumpalloc_heap_ptr_end = bumpalloc_heap_ptr + global_init_biginf_buf_size;
#ifdef _DEBUG
      printf("Arena size for bump alloc: %lld\n", global_init_biginf_buf_size);
      printf("BUMPALLOC/INITBUMPALLOC DONE: heap_ptr = %p\n", bumpalloc_heap_ptr);
#endif
}

static inline void* BUMPALLOC(long long n) {
      if (! bumpalloc_heap_ptr) {
          INITBUMPALLOC();
      }
      if (bumpalloc_heap_ptr + n < bumpalloc_heap_ptr_end) {
          char* old= bumpalloc_heap_ptr;
          bumpalloc_heap_ptr += n;
          return old;
      } else {
          fprintf(stderr, "Warning: bump allocator ran out of memory.");
          exit(1);
      }
}

// Snapshot the current heap pointer value across all threads.
void save_alloc_state() {
  dbgprintf("Saving(%p): pos %d", heap_ptr, num_saved_heap_ptr);
  saved_heap_ptr_stack[num_saved_heap_ptr] = heap_ptr;
  num_saved_heap_ptr++;
  dbgprintf("\n");
}

void restore_alloc_state() {
  if(num_saved_heap_ptr <= 0) {
    fprintf(stderr, "Bad call to restore_alloc_state!  Saved stack empty!\ne");
    exit(1);
  }
  num_saved_heap_ptr--;
  dbgprintf("Restoring(%p): pos %d, discarding %p",
            saved_heap_ptr_stack[num_saved_heap_ptr], num_saved_heap_ptr, bumpalloc_heap_ptr);
  bumpalloc_heap_ptr = saved_heap_ptr_stack[num_saved_heap_ptr];
}


#else
// Regular malloc mode:
void INITBUMPALLOC() {}
void save_alloc_state() {}
void restore_alloc_state() {}

#define BUMPALLOC(n) malloc(n)

#endif // BUMPALLOC


// -------------------------------------
// Bump allocated nursery for regions
// -------------------------------------

// See https://github.com/iu-parfunc/gibbon/issues/122.

__thread char* nursery_heap_ptr = (char*)NULL;
__thread char* nursery_heap_ptr_end = (char*)NULL;

#define NURSERY_SIZE 0
// #define NURSERY_SIZE global_init_biginf_buf_size
#define NURSERY_ALLOC_UPPER_BOUND 1024

static inline void init_nursery() {
    nursery_heap_ptr = (char*)malloc(NURSERY_SIZE);
    if (nursery_heap_ptr == NULL) {
      printf("init_region: malloc failed: %d", NURSERY_SIZE);
      exit(1);
    }
    nursery_heap_ptr_end = nursery_heap_ptr + NURSERY_SIZE;
#ifdef _DEBUG
    printf("init_nursery: DONE, heap_ptr = %p\n", nursery_heap_ptr);
#endif
}

static inline void* alloc_in_nursery(long long n) {
    if (! nursery_heap_ptr) {
        init_nursery();
    }
    if (nursery_heap_ptr + n < nursery_heap_ptr_end) {
        char* old = nursery_heap_ptr;
        nursery_heap_ptr += n;
#ifdef _DEBUG
        printf("alloc_in_nursery: DONE, %lld\n", n);
#endif
        return old;
    } else {
        return NULL;
    }
}

// -------------------------------------
// ALLOC and ALLOC_PACKED macros
// -------------------------------------


/*

If parallelism is enabled, we always use a nursery/malloc based allocator
since Boehm GC is not thread-safe in its default configuration. It can be
made thread-safe by building it with appropriate flags, but we don't do that.
Presently, all parallel pointer-based programs will leak memory.

*/

#ifdef _PARALLEL
#define ALLOC(n) malloc(n)
#define ALLOC_PACKED_SMALL(n) alloc_in_nursery(n)
#define ALLOC_PACKED_BIG(n) malloc(n)
char *ALLOC_COUNTED(size_t size) {
    bump_global_region_count();
    return ALLOC(size);
}
#else
  #ifdef _POINTER
#define ALLOC(n) GC_MALLOC(n)
#define ALLOC_PACKED_SMALL(n) GC_MALLOC(n)
#define ALLOC_PACKED_BIG(n) GC_MALLOC(n)
char *ALLOC_COUNTED(size_t size) {
    bump_global_region_count();
    return GC_MALLOC(size);
}
  #else
#define ALLOC(n) malloc(n)
#define ALLOC_PACKED_SMALL(n) alloc_in_nursery(n)
#define ALLOC_PACKED_BIG(n) malloc(n)
char *ALLOC_COUNTED(size_t size) {
    bump_global_region_count();
    return ALLOC(size);
}
  #endif // _POINTER
#endif // _PARALLEL


// Could try alloca() here.  Better yet, we could keep our own,
// separate stack and insert our own code to restore the pointer
// before any function that (may have) called ALLOC_SCOPED returns.

// #define ALLOC_SCOPED() alloca(1024)
#define ALLOC_SCOPED(n) alloca(n)
// #define ALLOC_SCOPED() alloc_scoped()

// Stack allocation is either too small or blows our stack.
// We need a way to make a giant stack if we want to use alloca.
// #define ALLOC_SCOPED() ALLOC(global_init_biginf_buf_size)

// Our global pointer.  No parallelism.
// static char* stack_scoped_region;
// char* alloc_scoped() { return stack_scoped_region; }



// -------------------------------------
// Basic types
// -------------------------------------

// Must be consistent with sizeOfTy defined in Gibbon.Language.Syntax.

typedef unsigned char TagTyPacked;
typedef unsigned char TagTyBoxed;
typedef long long IntTy;
typedef char CharTy;
typedef float FloatTy;
typedef unsigned long long SymTy;
typedef bool BoolTy;
typedef char* PtrTy;
typedef char* CursorTy;

// -------------------------------------
// Arenas and dictionaries
// -------------------------------------

typedef struct mem_arena {
  int ind;
  char* mem; // TODO(vollmerm): make this a list of chunks?
  void* reflist;
} mem_arena_t;

typedef mem_arena_t* ArenaTy;

ArenaTy alloc_arena() {
  ArenaTy ar = ALLOC(sizeof(mem_arena_t));
  ar->ind = 0;
  ar->mem = malloc(global_inf_buf_max_chunk_size);
  ar->reflist = 0;
  return ar;
}

void free_arena(ArenaTy ar) {
  free(ar->mem);
  // TODO(vollmerm): free everything in ar->reflist
  free(ar);
}

CursorTy extend_arena(ArenaTy ar, int size) {
  CursorTy ret = ar->mem + ar->ind;
  ar->ind += size;
  return ret;
}

typedef struct dict_item {
  struct dict_item * next;
  int key;
  void * ptrval;
} dict_item_t;

dict_item_t * dict_alloc(ArenaTy ar) {
  return (dict_item_t *) extend_arena(ar, sizeof(dict_item_t)); // ALLOC(sizeof(dict_item_t));
}

dict_item_t *dict_insert_ptr(ArenaTy ar, dict_item_t *ptr, SymTy key, PtrTy val) {
  dict_item_t *ret = dict_alloc(ar);
  ret->key = key;
  ret->ptrval = val;
  ret->next = ptr;
  return ret;
}

PtrTy dict_lookup_ptr(dict_item_t *ptr, SymTy key) {
  while (ptr != 0) {
    if (ptr->key == key) {
      return ptr->ptrval;
    } else {
      ptr = ptr->next;
    }
  }
  printf("Error, key %lld not found!\n",key);
  exit(1);
}

// -------------------------------------
// Sets
// -------------------------------------


struct set_elem {
  int val;
  UT_hash_handle hh;
};

typedef struct set_elem* SymSetTy;

SymSetTy empty_set() {
  return NULL;
}

SymSetTy insert_set(SymSetTy set, int sym) {
  SymSetTy s;
  HASH_FIND_INT(set, &sym, s);  /* sym already in the hash? */
  if (s==NULL) {
    s = malloc(sizeof(struct set_elem));
    s->val = sym;
    HASH_ADD_INT(set,val,s);
  }
  return set;
}

BoolTy contains_set(SymSetTy set, int sym) {
  SymSetTy s;
  HASH_FIND_INT(set, &sym, s);
  return (s!=NULL);
}

// -------------------------------------
// Sym Hash
// -------------------------------------

struct sym_hash_elem {
  int key;
  int val;
  UT_hash_handle hh;
};

typedef struct sym_hash_elem* SymHashTy;

typedef struct sym_hash_elem* IntHashTy;

SymHashTy empty_hash() {
  return NULL;
}

SymHashTy insert_hash(SymHashTy hash, int k, int v) {
  SymHashTy s;
  // NOTE: not checking for duplicates!
  // s = malloc(sizeof(struct sym_hash_elem));
  s = ALLOC(sizeof(struct sym_hash_elem));
  s->val = v;
  s->key = k;
  HASH_ADD_INT(hash,key,s);

  return hash;
}

IntTy lookup_hash(SymHashTy hash, int k) {
  SymHashTy s;
  HASH_FIND_INT(hash,&k,s);
  if (s==NULL) {
    return k; // NOTE: return original key if val not found
              // TODO(vollmerm): come up with something better to do here
  } else {
    return s->val;
  }
}

BoolTy contains_hash(SymHashTy hash, int sym) {
  SymHashTy s;
  HASH_FIND_INT(hash,&sym,s);
  return (s!=NULL);
}

// -------------------------------------
// Helpers
// -------------------------------------

char* read_benchfile_param() {
  if (global_benchfile_param == NULL) {
    fprintf(stderr, "read_benchfile_param: benchmark input file was not set! Set using --bench-input.\n");
    exit(1);
  } else
    return global_benchfile_param;
}

char* read_arrayfile_param() {
  if (global_arrayfile_param == NULL) {
    fprintf(stderr, "read_arrayfile_param: array input file was not set! Set using --array-input.\n");
    exit(1);
  } else
    return global_arrayfile_param;
}

IntTy read_arrayfile_length_param() {
  if (global_arrayfile_length_param == -1) {
    fprintf(stderr, "read_arrayfile_length_param: array input file length was not set! Set using --array-input-length.\n");
    exit(1);
  } else
    return global_arrayfile_length_param;
}


// fun fact: __ prefix is actually reserved and this is an undefined behavior.
// These functions must be provided by the code generator.
int __main_expr();


void show_usage(char** argv)
{
    printf("\n");
    printf("This binary was generated by the Gibbon compiler.\n");
    printf("\n");
    printf("Usage: %s [OPTS] [size] [iters]\n", argv[0]);

    printf("\n");
    printf("Options:\n");
    printf(" --buffer-size <bytes>      Set the buffer size (default %lld).\n", global_init_biginf_buf_size);
    printf(" --bench-input <path>       Set the input file read for benchmarking. Applies only\n");
    printf("                            IF the program was *compiled* with --bench-fun. \n");
    return;
}

double avg(const double* arr, int n)
{
    double sum = 0.0;
    for(int i=0; i<n; i++) sum += arr[i];
    return sum / (double)n;
}

double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
      + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

int compare_doubles(const void *a, const void *b)
{
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}

// Exponentiation
IntTy expll(IntTy base, IntTy pow) {
    if (base == 2) {
        return (1 << pow);
    } else {
        IntTy i, result = 1;
        for (i = 0; i < pow; i++)
            result *= base;
        return result;
    }
 }

// -------------------------------------
// Symbol table
// -------------------------------------

#define global_max_symbol_len 256

// Invariant: should always be equal to max(sym_table_keys)
static SymTy global_gensym_counter = 0;

// Its value is updated by the flags parser.
static char *global_bench_prog_param;

static SymTy newline_symbol = -1;
static SymTy space_symbol = -1;
static SymTy comma_symbol = -1;
static SymTy leftparen_symbol = -1;
static SymTy rightparen_symbol = -1;

typedef struct SymTable_elem {
    SymTy idx;                 /* key */
    char value[global_max_symbol_len];
    UT_hash_handle hh;         /* makes this structure hashable */
} SymTable_elem;

// important! initialize to NULL
SymTable_elem *global_sym_table = NULL;

void add_symbol(SymTy idx, char *value) {
    struct SymTable_elem *s;
    s = ALLOC(sizeof(struct SymTable_elem));
    s->idx = idx;
    strcpy(s->value, value);
    HASH_ADD(hh, global_sym_table, idx, sizeof(IntTy), s);
    if (idx > global_gensym_counter) {
        global_gensym_counter = idx;
    }
}

void set_newline(SymTy idx) {
  newline_symbol = idx;
  add_symbol(idx,"NEWLINE");
}

void set_space(SymTy idx) {
  space_symbol = idx;
  add_symbol(idx,"SPACE");
}

void set_comma(SymTy idx) {
  comma_symbol = idx;
  add_symbol(idx,"COMMA");
}

void set_leftparen(SymTy idx) {
  leftparen_symbol = idx;
  add_symbol(idx,"LEFTPAREN");
}

void set_rightparen(SymTy idx) {
  rightparen_symbol = idx;
  add_symbol(idx,"RIGHTPAREN");
}

IntTy print_symbol(SymTy idx) {
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
    struct SymTable_elem *s;
    HASH_FIND(hh, global_sym_table, &idx, sizeof(SymTy), s);
    if (s == NULL) {
        return printf("%lld", idx);
    } else {
        return printf("%s", s->value);
    }

  }
}

#ifdef _PARALLEL
SymTy gensym() {
    SymTy idx = __atomic_add_fetch(&global_gensym_counter, 1, __ATOMIC_SEQ_CST);
    return idx;
}
#else
SymTy gensym() {
    global_gensym_counter += 1;
    SymTy idx = global_gensym_counter;
    return idx;
}
#endif

void free_symtable() {
    struct SymTable_elem *elt, *tmp;
    HASH_ITER(hh, global_sym_table, elt, tmp) {
        HASH_DEL(global_sym_table,elt);
    }
    free(elt);
    free(tmp);
}

/*

----------------------------------------
Garbage collection
----------------------------------------

   Gibbon has "growing regions" i.e each logical region is backed by a doubly linked-list
   of smaller chunks which grows as required. In addition to actual data, each chunk
   stores some additional metadata (RegionFooter) to chain the chunks together in a list
   and for garbage collection. The footer:

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   serialized data | rf_reg_metadata_ptr | rf_seq_no | rf_nursery_allocated | rf_size | rf_next | rf_prev
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The metadata after the serialized data serves various purposes:

   - rf_reg_metadata_ptr: A pointer to a RegionTy struct that contains various metadata.
     Of particular interest to us are the fields:

     = reg_id: A unique identifier for a region.

     = refcount and outset: Whenever an inter-region indirection is created, we record that information
       using these two fields. Suppose we have an indirection from region A that points to some chunk
       in region B. Then A's outset will store a pointer to that chunk's footer, and B's refcount will
       be bumped by 1. Note that all there's only 1 refcount cell, and 1 outset per logical region,
       and chunks only store a pointer to them.

   - rf_seq_no: The index of this particular chunk in the list.

   - rf_nursery_allocated: Whether this chunk was allocated in a nursery.

   - rf_size: Used during bounds checking to calculate the size of the next region in
     the linked list.

   - rf_next / rf_prev: Point to the next and previous chunk respectively.


There are two ways in which a region may be freed:

(1) Whenever it goes out of scope

  The RTS tries to free a region whenever it goes out of scope. But this doesn't always succeed as
  regions sometimes contain values that "escape". One reason why this'll happen is if there's an
  indirection from A->B, and A lives longer than B.
  In such a case, when B goes out of scope it's refcount won't be 0, and the RTS won't free it.
  This brings us to (2).

(2)

  When the RTS successfully frees a region, it decrements the refcounts of all the regions it
  points to (via the outset). At the same time, if it encounters a region in the outset whoose
  refcount becomes 0 after the decrement, it calls free_region on that. This way we can be sure
  that all regions will eventually be garbage collected before the program exits.



Why is it a doubly linked-list?
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

Due to way that bounds-checking works, the pointers in the outset may actually point to any
arbitrary chunk in the chain. However, we must call free_region on the first one to ensure that
all of them are GC'd. So we need pointers to traverse backward get to the first one.
'trav_to_first_chunk' accomplishes this.

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

static inline void insert_into_outset(CursorTy ptr, RegionTy *reg) {
    uint outset_len = reg->reg_outset_len;
    // Check for duplicates.
    for (uint i = 0; i < outset_len; i++) {
        if (ptr == reg->reg_outset[i]) {
            return;
        }
    }
    // Otherwise, insert into the outset.
    reg->reg_outset[outset_len] = ptr;
    reg->reg_outset_len = outset_len + 1;
    return;
}

static inline void remove_from_outset(CursorTy ptr, RegionTy *reg) {
    uint outset_len = reg->reg_outset_len;
    CursorTy *outset = reg->reg_outset;
    int i;
    if (outset_len == 0) {
        fprintf(stderr, "remove_from_outset: empty outset\n");
        exit(1);
    }
    // Position of 'ptr' in the outset.
    int elt_idx = -1;
    for (i = 0; i < outset_len; i++) {
        if (ptr == outset[i]) {
            elt_idx = i;
        }
    }
    if (elt_idx == -1) {
        fprintf(stderr, "remove_from_outset: element not found\n");
        exit(1);
    }
    // Move all elements ahead of 'elt_idx' back by one position.
    for (i = elt_idx; i < outset_len; i++) {
        outset[i] = outset[i+1];
    }
    return;
}

RegionTy *alloc_region(IntTy size) {
    // Allocate the region metadata.
    RegionTy *reg = ALLOC(sizeof(RegionTy));
    if (reg == NULL) {
        printf("alloc_region: allocation failed: %ld", sizeof(RegionTy));
        exit(1);
    }

    // Allocate the first chunk.
    IntTy total_size = size + sizeof(RegionFooter);
    CursorTy heap;
    bool nursery_allocated = true;
    if (size <= NURSERY_ALLOC_UPPER_BOUND) {
        heap = ALLOC_PACKED_SMALL(total_size);
        if (heap == NULL) {
            heap = malloc(total_size);
            nursery_allocated = false;
        }
    } else {
        heap = ALLOC_PACKED_BIG(total_size);
        nursery_allocated = false;
    }
    if (heap == NULL) {
        printf("alloc_region: malloc failed: %lld", total_size);
        exit(1);
    }
    // Not heap+total_size, since we must keep space for the footer.
    CursorTy heap_end = heap + size;

    // Initialize metadata fields.
    reg->reg_id = gensym();
    reg->reg_refcount = 1;
    reg->reg_heap = heap;
    reg->reg_outset_len = 0;

#ifdef _DEBUG
    printf("Allocated a region(%lld): %lld bytes, nursery=%d.\n", reg->reg_id, size, nursery_allocated);
#endif

    // Write the footer.
    RegionFooter *footer = (RegionFooter *) heap_end;
    footer->rf_reg_metadata_ptr = reg;
    footer->rf_seq_no = 1;
    footer->rf_nursery_allocated = nursery_allocated;
    footer->rf_size = size;
    footer->rf_next = NULL;
    footer->rf_prev = NULL;

    return reg;
}

RegionTy *alloc_counted_region(IntTy size) {
    // Bump the count.
    bump_global_region_count();
    return alloc_region(size);
}

ChunkTy alloc_chunk(CursorTy end_old_chunk) {
    // Get size from current footer.
    RegionFooter *footer = (RegionFooter *) end_old_chunk;
    IntTy newsize = footer->rf_size * 2;
    // See #110.
    if (newsize > global_inf_buf_max_chunk_size) {
        newsize = global_inf_buf_max_chunk_size;
    }
    IntTy total_size = newsize + sizeof(RegionFooter);

    // Allocate.
    CursorTy start = ALLOC_PACKED_BIG(total_size);
    if (start == NULL) {
        printf("alloc_chunk: malloc failed: %lld", total_size);
        exit(1);
    }
    CursorTy end = start + newsize;

    // Link the next chunk's footer.
    footer->rf_next = (RegionFooter *) end;

    // Write the footer.
    RegionFooter* new_footer = (RegionFooter *) end;
    new_footer->rf_reg_metadata_ptr = footer->rf_reg_metadata_ptr;
    new_footer->rf_seq_no = footer->rf_seq_no + 1;
    new_footer->rf_nursery_allocated = false;
    new_footer->rf_size = newsize;
    new_footer->rf_next = NULL;
    new_footer->rf_prev = footer;

#ifdef _DEBUG
    RegionTy *reg = (RegionTy*) new_footer->rf_reg_metadata_ptr;
    printf("alloc_chunk: allocated %lld bytes for region %lld.\n", total_size, reg->reg_id);
#endif

    return (ChunkTy) {start , end};
}

RegionFooter* trav_to_first_chunk(RegionFooter *footer) {
    if (footer->rf_seq_no == 1) {
        return footer;
    } else if (footer->rf_prev == NULL) {
        fprintf(stderr, "No previous chunk found at rf_seq_no: %lld", footer->rf_seq_no);
        return NULL;
    } else {
        trav_to_first_chunk((RegionFooter *) footer->rf_prev);
    }
    return NULL;
}

uint get_ref_count(CursorTy end_ptr) {
    RegionFooter *footer = (RegionFooter *) end_ptr;
    RegionTy *reg = (RegionTy *) footer->rf_reg_metadata_ptr;
    return reg->reg_refcount;
}

// B is the pointer, and A is the pointee (i.e B -> A).
// Bump A's refcount and update B's outset.
static inline void bump_ref_count(CursorTy end_b, CursorTy end_a) {
    // Grab footers.
    RegionFooter *footer_a = (RegionFooter *) end_a;
    RegionFooter *footer_b = (RegionFooter *) end_b;

    // Grab metadata.
    RegionTy *reg_a = (RegionTy *) footer_a->rf_reg_metadata_ptr;
    RegionTy *reg_b = (RegionTy *) footer_b->rf_reg_metadata_ptr;

    // Bump A's refcount.
    uint current_refcount, new_refcount;
    current_refcount = reg_a->reg_refcount;
    new_refcount = current_refcount + 1;
    reg_a->reg_refcount = new_refcount;

#ifdef _DEBUG
    printf("bump_ref_count: %lld -> %lld\n", reg_b->reg_id, reg_a->reg_id);
    printf("bump_ref_count: old-refcount=%d, old-outset-len=%d:\n", current_refcount, reg_b->reg_outset_len);
    assert(current_refcount == reg_b->reg_outset_len+1);
#endif

    // Add A to B's outset.
    insert_into_outset(end_a, reg_b);

#ifdef _DEBUG
    // printf("bump_ref_count: Added %p to %lld's outset, %p.\n", end_a, reg_b->reg_id, reg_b);
    printf("bump_ref_count: new-refcount=%d, new-outset-len=%d\n", new_refcount, reg_b->reg_outset_len);
    assert(new_refcount == reg_b->reg_outset_len+1);
#endif

    return;
}

void free_region(CursorTy end_reg) {
    // Grab footer and the metadata.
    RegionFooter *footer = (RegionFooter *) end_reg;
    RegionTy *reg = (RegionTy *) footer->rf_reg_metadata_ptr;

    //
    RegionFooter *first_chunk_footer, *next_chunk_footer;
    CursorTy first_chunk, next_chunk;

    // Decrement current reference count.
    uint current_refcount, new_refcount;
    current_refcount = reg->reg_refcount;
    new_refcount = 0;
    if (current_refcount != 0) {
        new_refcount = current_refcount - 1;
        reg->reg_refcount = new_refcount;
    }

#ifdef _DEBUG
    printf("free_region(%lld): refcounts (1): old-refcount=%d, new-refcount=%d:\n", reg->reg_id, current_refcount, new_refcount);
#endif


    // Free this region recount is 0.
    if (new_refcount == 0) {

#ifdef _DEBUG
        printf("free_region(%lld): outset length: %d\n", reg->reg_id, reg->reg_outset_len);
#endif

        // Decrement refcounts, free regions with refcount==0 and also free
        // elements of the outset.
        if (reg->reg_outset_len != 0) {
            uint outset_len = reg->reg_outset_len;
            CursorTy *outset = reg->reg_outset;
            RegionFooter *elt_footer;
            RegionTy *elt_reg;
            uint elt_current_refcount, elt_new_refcount;
            CursorTy to_be_removed[MAX_OUTSET_LENGTH];
            uint to_be_removed_idx = 0;
            for (int i = 0; i < outset_len; i++) {
                elt_footer = (RegionFooter *) outset[i];
                elt_reg = (RegionTy *) elt_footer->rf_reg_metadata_ptr;
#ifdef _DEBUG
                elt_current_refcount = elt_reg->reg_refcount;
#endif
                elt_new_refcount = elt_current_refcount - 1;
                elt_reg->reg_refcount = elt_new_refcount;
#ifdef _DEBUG
                printf("free_region(%lld): old-refcount=%d, new-refcount=%d:\n",
                       elt_reg->reg_id, elt_current_refcount, elt_reg->reg_refcount);
#endif
                if (elt_new_refcount == 0) {
                    // See [Why is it a doubly linked-list?] above
                    first_chunk_footer = trav_to_first_chunk(elt_footer);
                    if (first_chunk_footer != NULL) {
                        free_region((CursorTy) first_chunk_footer);
                    }
                }
                to_be_removed[to_be_removed_idx] = outset[i];
                to_be_removed_idx++;
            }
            // Remove elements from the outset.
            for (uint i = 0; i < to_be_removed_idx; i++) {
                remove_from_outset(to_be_removed[i], reg);
            }
        }


#ifdef _DEBUG
        // Bookkeeping
        IntTy num_freed_chunks = 0, total_bytesize = 0;
#endif

        // Free the chunks in this region.
        first_chunk = end_reg - footer->rf_size;
        first_chunk_footer = footer;
        next_chunk = (char*) footer->rf_next;

#ifdef _DEBUG
        printf("free_region(%lld): first chunk in nursery: %d\n",
               reg->reg_id,
               first_chunk_footer->rf_nursery_allocated);
#endif

        if (! first_chunk_footer->rf_nursery_allocated) {
            #ifdef _DEBUG
            num_freed_chunks++;
            total_bytesize = total_bytesize + first_chunk_footer->rf_size;
            #endif
            free(first_chunk);
        }

        while (next_chunk != NULL) {
            next_chunk_footer = (RegionFooter *) next_chunk;
            #ifdef _DEBUG
            num_freed_chunks++;
            total_bytesize = total_bytesize + next_chunk_footer->rf_size;
            #endif
            free(next_chunk - next_chunk_footer->rf_size);
            next_chunk = (char*) next_chunk_footer->rf_next;
        }

#ifdef _DEBUG
        printf("free_region(%lld): Freed %lld bytes across %lld chunks.\n",
               reg->reg_id, total_bytesize, num_freed_chunks);
#endif

        // Free the metadata.
        free(reg);

    } else {
#ifdef _DEBUG
        printf("free_region(%lld): non-zero refcount: %d.\n",
               reg->reg_id, reg->reg_refcount);
#endif
    }
}

// Assume that all nodes with size information have tags >= 150.
BoolTy is_big(IntTy i, CursorTy cur) {
    TagTyPacked tag = *(TagTyPacked *) cur;
    if (tag >= 150) {
        cur += 1;
        IntTy size = *(IntTy *) cur;
        if (size >= i) {
            return true;
        } else {
            return false;
        }
    }
    return false;
}

// -------------------------------------
// Vectors
// -------------------------------------

typedef struct VectorTy_struct {
    // Bounds on the vector.
    IntTy vec_lower, vec_upper;

    // Size of each element.
    IntTy vec_elt_size;

    // Actual elements of the vector.
    void* vec_data;
} VectorTy;

VectorTy* vector_alloc(IntTy num, IntTy elt_size) {
    VectorTy *vec = ALLOC(sizeof(VectorTy));
    if (vec == NULL) {
        printf("alloc_vector: malloc failed: %ld", sizeof(VectorTy));
        exit(1);
    }
    void* data = ALLOC(num * elt_size);
    if (data == NULL) {
        printf("alloc_vector: malloc failed: %ld", sizeof(num * elt_size));
        exit(1);
    }
    vec->vec_lower = 0;
    vec->vec_upper = num;
    vec->vec_elt_size = elt_size;
    vec->vec_data = data;
    return vec;
}

IntTy vector_length(VectorTy *vec) {
    return (vec->vec_upper - vec->vec_lower);
}

BoolTy vector_is_empty(VectorTy *vec) {
    return (vector_length(vec) == 0);
}

VectorTy* vector_slice(IntTy i, IntTy n, VectorTy *vec) {
    IntTy lower = vec->vec_lower + i;
    IntTy upper = vec->vec_lower + i + n;
    if ((lower > vec->vec_upper)) {
        printf("vector_slice: lower out of bounds, %lld > %lld", lower, vec->vec_upper);
        exit(1);
    }
    if ((upper > vec->vec_upper)) {
        printf("vector_slice: upper out of bounds: %lld > %lld", upper, vec->vec_upper);
        exit(1);
    }
    VectorTy *vec2 = ALLOC(sizeof(VectorTy));
    if (vec == NULL) {
        printf("vector_slice: malloc failed: %ld", sizeof(VectorTy));
        exit(1);
    }
    vec2->vec_lower = lower;
    vec2->vec_upper = upper;
    vec2->vec_elt_size = vec->vec_elt_size;
    vec2->vec_data = vec->vec_data;
    return vec2;
}

// The callers must cast the return value.
static inline void* vector_nth(VectorTy *vec, IntTy i) {
    // if (i < vec->lower || i > vec->upper) {
    //     printf("vector_nth index out of bounds: %lld (%lld,%lld) \n", i, vec->vec_lower, vec->vec_upper);
    //     exit(1);
    // }
    return (vec->vec_data + (vec->vec_elt_size * (vec->vec_lower + i)));
}

static inline VectorTy* vector_inplace_update(VectorTy *vec, IntTy i, void* elt) {
    void* dst = vector_nth(vec, i);
    memcpy(dst, elt, vec->vec_elt_size);
    return vec;
}

static inline VectorTy* vector_copy(VectorTy *vec) {
    IntTy len = vector_length(vec);
    void *start = vector_nth(vec, 0);
    VectorTy *vec2 = vector_alloc(len, vec->vec_elt_size);
    memcpy(vec2->vec_data, start, len * vec->vec_elt_size);
    return vec2;
}

static inline VectorTy* vector_inplace_sort(VectorTy *vec, int (*compar)(const void *, const void*)) {
    void *start = vector_nth(vec, 0);
    qsort(start, vector_length(vec), vec->vec_elt_size, compar);
    return vec;
}

static inline VectorTy* vector_sort(VectorTy *vec, int (*compar)(const void *, const void*)) {
    VectorTy *vec2 = vector_copy(vec);
    vector_inplace_sort(vec2, compar);
    return vec2;
}

static inline VectorTy* vector_concat(VectorTy *vec) {
    // Length of the input vector.
    IntTy len = vector_length(vec);
    // Length of the concatenated vector.
    IntTy result_len = 0;
    // Size of each element in the concatenated vector.
    IntTy result_elt_size = 0;
    VectorTy **elt_ref, *elt;
    for (IntTy i = 0; i < len; i++) {
        elt_ref = vector_nth(vec, i);
        elt = *elt_ref;
        result_elt_size = elt->vec_elt_size;
        result_len += vector_length(elt);
    }

    // Concatenated vector.
    VectorTy *result = vector_alloc(result_len, result_elt_size);
    IntTy elt_len;
    // A counter that tracks the index of elements in 'result'.
    IntTy k = 0;
    for (IntTy i = 0; i < len; i++) {
        elt_ref = vector_nth(vec, i);
        elt = *elt_ref;
        elt_len = vector_length(elt);

        for (IntTy j = 0; j < elt_len; j++) {
            void* k_elt = vector_nth(elt, j);
            vector_inplace_update(result, k, k_elt);
            k++;
        }
    }

    return result;
}

static inline void vector_free(VectorTy *vec) {
    free(vec->vec_data);
    free(vec);
    return;
}

static inline VectorTy* vector_merge(VectorTy *vec1, VectorTy *vec2) {
    if (vec1->vec_upper != vec2->vec_lower) {
        printf("vector_merge: non-contiguous slices, (%lld,%lld), (%lld,%lld).",
               vec1->vec_lower, vec1->vec_upper, vec2->vec_lower, vec2->vec_upper);
        exit(1);
    }
    VectorTy *merged = ALLOC(sizeof(VectorTy));
    if (merged == NULL) {
        printf("vector_merge: malloc failed: %ld", sizeof(VectorTy));
        exit(1);
    }
    merged->vec_lower = vec1->vec_lower;
    merged->vec_upper = vec2->vec_upper;
    merged->vec_elt_size = vec1->vec_elt_size;
    merged->vec_data = vec1->vec_data;
    return merged;
}

void print_timing_array(VectorTy *times) {
    printf("TIMES: [");
    double *d;
    IntTy n = vector_length(times);
    for(int i = 0; i < n; i++) {
        d = vector_nth(times, i);
        if (i == (n-1)) {
            printf("%f",*d);
        }
        else {
            printf("%f, ",*d);
        }
    }
    printf("]\n");
}

double sum_timing_array(VectorTy *times) {
    double *d;
    double acc = 0;
    for(int i = 0; i < vector_length(times); i++) {
        d = vector_nth(times, i);
        acc += *d;
    }
    return acc;
}

// -------------------------------------
// Linked lists
// -------------------------------------

typedef struct ListTy_struct {
    IntTy ll_data_size;
    void* ll_data;
    struct ListTy_struct* ll_next;
} ListTy;

static inline ListTy* list_alloc(IntTy data_size) {
    // ListTy *ls = ALLOC(sizeof(ListTy));
    ListTy *ls = BUMPALLOC(sizeof(ListTy));
    ls->ll_data_size = data_size;
    ls->ll_data = NULL;
    ls->ll_next = NULL;
    return ls;
}

static inline BoolTy list_is_empty(ListTy *ls) {
    return ls->ll_next == NULL;
}

static inline ListTy* list_cons(void* elt, ListTy *ls) {
    // void* data = ALLOC(ls->data_size);
    void* data = BUMPALLOC(ls->ll_data_size);
    if (data == NULL) {
        printf("list_cons: malloc failed: %lld", ls->ll_data_size);
        exit(1);
    }
    memcpy(data, elt, ls->ll_data_size);
    // ListTy *res = ALLOC(sizeof(ListTy));
    ListTy *res = BUMPALLOC(sizeof(ListTy));
    res->ll_data_size = ls->ll_data_size;
    res->ll_data = data;
    res->ll_next = (ListTy*) ls;
    return res;
}

static inline void* list_head(ListTy *ls) {
    return ls->ll_data;
}

static inline ListTy* list_tail(ListTy *ls) {
    return ls->ll_next;
}

static inline void list_free(ListTy *ls) {
    free(ls->ll_data);
    free(ls);
    return;
}

static inline ListTy* list_copy(ListTy *ls) {
    ListTy *ls2 = list_alloc(ls->ll_data_size);
    if (ls->ll_data != NULL) {
        void* data = BUMPALLOC(ls->ll_data_size);
        memcpy(data, ls->ll_data, ls->ll_data_size);
        ls2->ll_data = data;
    }
    ls2->ll_next = ls->ll_next;
    return ls2;
}

// -------------------------------------
// Ppm Images
// -------------------------------------

typedef struct __Pixel_struct {
    IntTy field0;
    IntTy field1;
    IntTy field2;
} __Pixel;

void writePpm(char* filename, IntTy width, IntTy height, VectorTy *pixels);
void writePpm_loop(FILE *fp, IntTy idx, IntTy end, VectorTy *pixels);

// Example: writePpm("gibbon_rgb_1000.ppm", 1000, 1000, pixels);
void writePpm(char* filename, IntTy width, IntTy height, VectorTy *pixels)
{
    FILE *fp;
    fp = fopen(filename, "w+");
    fprintf(fp, "P3\n");
    fprintf(fp, "%lld %lld\n255\n", width, height);
    IntTy len = vector_length(pixels);
    writePpm_loop(fp, 0, len, pixels);
    fclose(fp);
    return;
}

void writePpm_loop(FILE *fp, IntTy idx, IntTy end, VectorTy *pixels)
{
    BoolTy fltIf_5768_6575 = idx == end;

    if (fltIf_5768_6575) {
        return;
    } else {
        __Pixel *tmp_112;
        tmp_112 = (__Pixel *) vector_nth(pixels, idx);
        __Pixel tup = *tmp_112;
        IntTy x = tup.field0;
        IntTy y = tup.field1;
        IntTy z = tup.field2;
        // write to file.
        fprintf(fp, "%lld %lld %lld\n", x, y, z);
        writePpm_loop(fp, (idx+1), end, pixels);
    }
}

/* -------------------------------------------------------------------------------- */

int main(int argc, char** argv)
{
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

    // lim.rlim_cur = 1024LU * 1024LU * 1024LU; // 1GB stack.
    lim.rlim_cur = 512LU * 1024LU * 1024LU; // 500MB stack.
    // lim.rlim_max = lim.rlim_cur; // Normal users may only be able to decrease this.

    // WARNING: Haven't yet figured out why this doesn't work on MacOS...
#ifndef __APPLE__
    code = setrlimit(RLIMIT_STACK, &lim);
    while (code) {
      fprintf(stderr, " [gibbon rts] Failed to set stack size to %llu, code %d\n", (unsigned long long)lim.rlim_cur, code);
      lim.rlim_cur /= 2;
      // lim.rlim_max /= 2;
      if(lim.rlim_cur < 100 * 1024) {
        fprintf(stderr, " [gibbon rts] Failed setrlimit stack size to something reasonable; giving up.\n");
        break; // abort();
      }
      int code = setrlimit(RLIMIT_STACK, &lim);
    }
#endif

    int got_numargs = 0; // How many numeric arguments have we got.

    int i;
    for (i = 1; i < argc; ++i)
    {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
          show_usage(argv);
          exit(0);
        }
        else if (strcmp(argv[i], "--biginf-buffer-size") == 0 && i < argc - 1)
        {
            global_init_biginf_buf_size = atoll(argv[i + 1]);
            i++;
        }
        else if (strcmp(argv[i], "--inf-buffer-size") == 0 && i < argc - 1)
        {
            global_init_inf_buf_size = atoll(argv[i + 1]);
            i++;
        }
        else if ((strcmp(argv[i], "--bench-input") == 0)) {
          if (i+1 >= argc) {
            fprintf(stderr, "Not enough arguments after --bench-input, expected <file>.\n");
            show_usage(argv);
            exit(1);
          }
          global_benchfile_param = argv[i+1];
          i++;
        }
        else if ((strcmp(argv[i], "--array-input") == 0)) {
          if (i+1 >= argc) {
            fprintf(stderr, "Not enough arguments after --array-input, expected <file>.\n");
            show_usage(argv);
            exit(1);
          }
          global_arrayfile_param = argv[i+1];
          i++;
        }
        else if (strcmp(argv[i], "--array-input-length") == 0 && i < argc - 1) {
            global_arrayfile_length_param = atoll(argv[i+1]);
            i++;
        }
        else if (strcmp(argv[i], "--bench-prog") == 0 && i < argc - 1) {
            int len = strlen(argv[i+1]);
            global_bench_prog_param = (char*) malloc((len+1)*sizeof(char));
            strncpy(global_bench_prog_param,argv[i+1],len);
            i++;
        }
        // If present, we expect the two arguments to be <size> <iters>
        else if (got_numargs >= 2) {
            fprintf(stderr, "Extra arguments left over: ");
            for(; i < argc; i++) fprintf(stderr, "%s ", argv[i]);
            show_usage(argv);
            exit(1);
        } else {
          if (got_numargs == 0) {
            global_size_param  = atoll(argv[i]);
            got_numargs ++;
          } else {
            global_iters_param = atoll(argv[i]);
          }
        }
    }

    // Initialize global_bench_prog_param to an empty string in case
    // the runtime argument --bench-prog isn't passed.
    if (global_bench_prog_param == NULL) {
        global_bench_prog_param = (char*) malloc(1*sizeof(char));
        *global_bench_prog_param = '\n';
    }

    __main_expr();

    return 0;
}

// -----------------------------------------------------------------------------
// Program starts here
// -----------------------------------------------------------------------------

typedef struct Prod_struct { } Prod;
typedef struct Int64Prod_struct {
            IntTy field0;
        } Int64Prod;
typedef struct Float32Prod_struct {
            FloatTy field0;
        } Float32Prod;
typedef struct Float32CursorProd_struct {
            FloatTy field0;
            CursorTy field1;
        } Float32CursorProd;
typedef struct BoolProd_struct {
            BoolTy field0;
        } BoolProd;
typedef struct TagCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
        } TagCursorProd;
typedef struct CursorProd_struct {
            CursorTy field0;
        } CursorProd;
typedef struct CursorInt64Prod_struct {
            CursorTy field0;
            IntTy field1;
        } CursorInt64Prod;
typedef struct CursorCursorProd_struct {
            CursorTy field0;
            CursorTy field1;
        } CursorCursorProd;
typedef struct CursorCursorCursorProd_struct {
            CursorTy field0;
            CursorTy field1;
            CursorTy field2;
        } CursorCursorCursorProd;
typedef struct CursorCursorCursorCursorProd_struct {
            CursorTy field0;
            CursorTy field1;
            CursorTy field2;
            CursorTy field3;
        } CursorCursorCursorCursorProd;
CursorInt64Prod size(CursorTy end_r_2433, CursorTy ls_236_846_1178);
unsigned char bench_psc();
unsigned char bench_psb();
unsigned char bench_ts();
CursorCursorCursorProd psB(CursorTy end_r_2435, CursorTy loc_2434,
                           IntTy n_245_855_1194);
CursorCursorCursorProd psC(CursorTy end_r_2437, CursorTy loc_2436,
                           IntTy n_246_856_1204);
CursorCursorCursorCursorProd toList(CursorTy end_r_2440, CursorTy end_r_2441,
                                    CursorTy loc_2439,
                                    CursorTy ps_247_857_1218);
CursorCursorCursorProd sinx(CursorTy end_r_2443, CursorTy loc_2442,
                            IntTy n_262_865_1222);
CursorCursorCursorProd cosx(CursorTy end_r_2445, CursorTy loc_2444,
                            IntTy n_263_866_1226);
CursorCursorCursorProd psSqrt(CursorTy end_r_2448, CursorTy end_r_2449,
                              CursorTy loc_2447, IntTy n_264_867_1233,
                              CursorTy a_265_868_1234);
CursorCursorCursorProd getQs(CursorTy end_r_2452, CursorTy end_r_2453,
                             CursorTy loc_2451, IntTy n_270_871_1238,
                             CursorTy fs_271_872_1239);
CursorCursorCursorCursorProd integral(CursorTy end_r_2456, CursorTy end_r_2457,
                                      CursorTy loc_2455,
                                      CursorTy fs_272_873_1250);
CursorCursorCursorCursorProd int1(CursorTy end_r_2460, CursorTy end_r_2461,
                                  CursorTy loc_2459, CursorTy a_273_874_1252,
                                  IntTy n_274_875_1253);
CursorCursorCursorCursorProd deriv(CursorTy end_r_2464, CursorTy end_r_2465,
                                   CursorTy loc_2463, CursorTy a_277_878_1260);
CursorCursorCursorCursorProd deriv1(CursorTy end_r_2468, CursorTy end_r_2469,
                                    CursorTy loc_2467, CursorTy a_280_881_1263,
                                    IntTy n_281_882_1264);
CursorCursorCursorProd revert(CursorTy end_r_2472, CursorTy end_r_2473,
                              CursorTy loc_2471, IntTy n_284_885_1271,
                              CursorTy a_285_886_1272);
CursorCursorCursorProd getRs(CursorTy end_r_2476, CursorTy end_r_2477,
                             CursorTy loc_2475, IntTy n_290_889_1276,
                             CursorTy fs_291_890_1277);
CursorCursorCursorProd compose(CursorTy end_r_2481, CursorTy end_r_2482,
                               CursorTy end_r_2483, CursorTy loc_2480,
                               CursorTy a_292_891_1285,
                               CursorTy b_293_892_1286);
CursorCursorCursorProd ts(CursorTy end_r_2485, CursorTy loc_2484,
                          IntTy n_299_896_1289);
CursorCursorCursorProd takePs(CursorTy end_r_2488, CursorTy end_r_2489,
                              CursorTy loc_2487, IntTy n_300_897_1298,
                              CursorTy fs_301_898_1299);
CursorCursorCursorProd psDiv(CursorTy end_r_2493, CursorTy end_r_2494,
                             CursorTy end_r_2495, CursorTy loc_2492,
                             IntTy n_304_899_1301, CursorTy a_305_900_1302,
                             CursorTy b_306_901_1303);
CursorCursorCursorProd psMult(CursorTy end_r_2499, CursorTy end_r_2500,
                              CursorTy end_r_2501, CursorTy loc_2498,
                              CursorTy a_314_902_1305, CursorTy b_315_903_1306);
CursorCursorCursorProd psAdd(CursorTy end_r_2505, CursorTy end_r_2506,
                             CursorTy end_r_2507, CursorTy loc_2504,
                             CursorTy a_320_906_1309, CursorTy b_321_907_1310);
CursorCursorCursorCursorProd psNeg(CursorTy end_r_2510, CursorTy end_r_2511,
                                   CursorTy loc_2509, CursorTy a_326_910_1313);
CursorCursorCursorProd psX(CursorTy end_r_2513, CursorTy loc_2512);
CursorCursorCursorCursorProd dot(CursorTy end_r_2516, CursorTy end_r_2517,
                                 CursorTy loc_2515, FloatTy c_329_913_1320,
                                 CursorTy b_330_914_1321);
CursorCursorCursorProd pone(CursorTy end_r_2519, CursorTy loc_2518);
unsigned char print_check(BoolTy b_333_917_1327);
CursorCursorCursorCursorProd _copy_Ps(CursorTy end_r_2522, CursorTy end_r_2523,
                                      CursorTy loc_2521,
                                      CursorTy arg_743_935_1330);
CursorCursorCursorCursorProd _copy_without_ptrs_Ps(CursorTy end_r_2526,
                                                   CursorTy end_r_2527,
                                                   CursorTy loc_2525,
                                                   CursorTy arg_748_940_1335);
CursorProd _traverse_Ps(CursorTy end_r_2529, CursorTy arg_753_945_1340);
CursorProd _print_Ps(CursorTy end_r_2531, CursorTy arg_758_949_1344);
CursorCursorCursorCursorProd _copy_PList1(CursorTy end_r_2534,
                                          CursorTy end_r_2535,
                                          CursorTy loc_2533,
                                          CursorTy arg_771_962_1357);
CursorCursorCursorCursorProd _copy_without_ptrs_PList1(CursorTy end_r_2538,
                                                       CursorTy end_r_2539,
                                                       CursorTy loc_2537,
                                                       CursorTy arg_776_967_1362);
CursorProd _traverse_PList1(CursorTy end_r_2541, CursorTy arg_781_972_1367);
CursorProd _print_PList1(CursorTy end_r_2543, CursorTy arg_786_976_1371);
CursorCursorCursorProd caseFn_807(CursorTy end_r_2546, CursorTy end_r_2547,
                                  CursorTy loc_2545, IntTy n_264_808_1001_1384,
                                  CursorTy fs_267_809_1002_1385);
CursorCursorCursorCursorProd caseFn_810(CursorTy end_r_2550,
                                        CursorTy end_r_2551, CursorTy loc_2549,
                                        FloatTy f_286_811_1005_1391,
                                        CursorTy fs__289_812_1006_1392,
                                        FloatTy f__288_813_1007_1393);
CursorCursorCursorCursorProd caseFn_814(CursorTy end_r_2554,
                                        CursorTy end_r_2555, CursorTy loc_2553,
                                        FloatTy f_286_815_1008_1399,
                                        CursorTy fs_287_816_1009_1400);
CursorCursorCursorProd caseFn_817(CursorTy end_r_2559, CursorTy end_r_2560,
                                  CursorTy end_r_2561, CursorTy loc_2558,
                                  CursorTy b_293_818_1012_1403,
                                  FloatTy f_294_819_1013_1404,
                                  CursorTy fs_295_820_1014_1405);
CursorCursorCursorProd caseFn_821(CursorTy end_r_2564, CursorTy end_r_2565,
                                  CursorTy loc_2563, IntTy n_300_822_1017_1417,
                                  CursorTy fs_301_823_1018_1418);
CursorCursorCursorProd caseFn_824(CursorTy end_r_2568, CursorTy end_r_2569,
                                  CursorTy loc_2567, IntTy n_304_825_1021_1423,
                                  CursorTy b_306_826_1022_1424);
CursorCursorCursorProd caseFn_827(CursorTy end_r_2573, CursorTy end_r_2574,
                                  CursorTy end_r_2575, CursorTy loc_2572,
                                  IntTy n_304_828_1025_1429,
                                  CursorTy b_306_829_1026_1430,
                                  FloatTy f_309_830_1027_1431,
                                  CursorTy fs_310_831_1028_1432);
CursorCursorCursorProd caseFn_832(CursorTy end_r_2579, CursorTy end_r_2580,
                                  CursorTy end_r_2581, CursorTy loc_2578,
                                  IntTy n_304_833_1032_1444,
                                  CursorTy a_305_834_1033_1445,
                                  CursorTy b_306_835_1034_1446);
CursorCursorCursorCursorProd caseFn_836(CursorTy end_r_2585,
                                        CursorTy end_r_2586,
                                        CursorTy end_r_2587, CursorTy loc_2584,
                                        CursorTy b_315_837_1037_1449,
                                        FloatTy f_316_838_1038_1450,
                                        CursorTy fs_317_839_1039_1451);
CursorCursorCursorProd caseFn_840(CursorTy end_r_2592, CursorTy end_r_2593,
                                  CursorTy end_r_2594, CursorTy end_r_2595,
                                  CursorTy loc_2591,
                                  CursorTy a_320_841_1042_1462,
                                  CursorTy b_321_842_1043_1463,
                                  FloatTy f_322_843_1044_1464,
                                  CursorTy fs_323_844_1045_1465);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Ps(CursorTy end_r_2598,
                                                          CursorTy end_r_2599,
                                                          CursorTy loc_2597,
                                                          CursorTy arg_2420);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_PList1(CursorTy end_r_2602, CursorTy end_r_2603,
                                 CursorTy loc_2601, CursorTy arg_2425);
CursorInt64Prod size(CursorTy end_r_2433, CursorTy ls_236_846_1178)
{
    TagTyPacked tmpval_6091 = *(TagTyPacked *) ls_236_846_1178;
    CursorTy tmpcur_6092 = ls_236_846_1178 + 1;


  switch_6105:
    ;
    switch (tmpval_6091) {

      case 0:
        {
            CursorTy jump_3417 = ls_236_846_1178 + 1;

            return (CursorInt64Prod) {jump_3417, 0};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6093 = *(FloatTy *) tmpcur_6092;
            CursorTy tmpcur_6094 = tmpcur_6092 + sizeof(FloatTy);
            CursorTy jump_3418 = tmpcur_6092 + 4;
            CursorInt64Prod tmp_struct_0 =  size(end_r_2433, tmpcur_6094);
            CursorTy pvrtmp_6095 = tmp_struct_0.field0;
            IntTy pvrtmp_6096 = tmp_struct_0.field1;
            IntTy tailprim_3420 = 1 + pvrtmp_6096;

            return (CursorInt64Prod) {pvrtmp_6095, tailprim_3420};
            break;
        }

      case 2:
        {
            CursorTy jump_3421 = ls_236_846_1178 + 1;
            IntTy tailprim_3422 = 0 - 1;

            return (CursorInt64Prod) {jump_3421, tailprim_3422};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6097 = *(CursorTy *) tmpcur_6092;
            CursorTy tmpaftercur_6098 = tmpcur_6092 + 8;
            CursorTy jump_3676 = tmpcur_6092 + 8;
            CursorInt64Prod tmp_struct_1 =  size(end_r_2433, tmpcur_6097);
            CursorTy pvrtmp_6099 = tmp_struct_1.field0;
            IntTy pvrtmp_6100 = tmp_struct_1.field1;

            return (CursorInt64Prod) {jump_3676, pvrtmp_6100};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6101 = *(CursorTy *) tmpcur_6092;
            CursorTy tmpaftercur_6102 = tmpcur_6092 + 8;
            CursorInt64Prod tmp_struct_2 =  size(end_r_2433, tmpcur_6101);
            CursorTy pvrtmp_6103 = tmp_struct_2.field0;
            IntTy pvrtmp_6104 = tmp_struct_2.field1;

            return (CursorInt64Prod) {pvrtmp_6103, pvrtmp_6104};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6091");
            exit(1);
        }
    }
}
unsigned char bench_psc()
{
    RegionTy *region_6106 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2621 = region_6106->reg_heap;
    IntTy sizeof_end_r_2621_6107 = global_init_inf_buf_size;
    CursorTy end_r_2621 = r_2621 + sizeof_end_r_2621_6107;
    RegionTy *region_6108 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2620 = region_6108->reg_heap;
    IntTy sizeof_end_r_2620_6109 = global_init_inf_buf_size;
    CursorTy end_r_2620 = r_2620 + sizeof_end_r_2620_6109;
    CursorTy pvrtmp_6119;
    CursorTy pvrtmp_6120;
    CursorTy pvrtmp_6121;
    VectorTy *times_7 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6119;
    struct timespec end_pvrtmp_6119;

    for (long long iters_pvrtmp_6119 = 0; iters_pvrtmp_6119 <
         global_iters_param; iters_pvrtmp_6119++) {
        if (iters_pvrtmp_6119 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6119);

        CursorCursorCursorProd tmp_struct_3 =  psC(end_r_2621, r_2621, 5);
        CursorTy pvrtmp_6110 = tmp_struct_3.field0;
        CursorTy pvrtmp_6111 = tmp_struct_3.field1;
        CursorTy pvrtmp_6112 = tmp_struct_3.field2;

        pvrtmp_6119 = pvrtmp_6110;
        pvrtmp_6120 = pvrtmp_6111;
        pvrtmp_6121 = pvrtmp_6112;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6119);
        if (iters_pvrtmp_6119 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_4 = difftimespecs(&begin_pvrtmp_6119, &end_pvrtmp_6119);

        vector_inplace_update(times_7, iters_pvrtmp_6119, &itertime_4);
    }
    vector_inplace_sort(times_7, compare_doubles);

    double *tmp_8 = (double *) vector_nth(times_7, global_iters_param / 2);
    double selftimed_6 = *tmp_8;
    double batchtime_5 = sum_timing_array(times_7);

    print_timing_array(times_7);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_5);
    printf("SELFTIMED: %e\n", selftimed_6);

    CursorCursorCursorCursorProd tmp_struct_9 =
                                  toList(end_r_2621, end_r_2620, r_2620, pvrtmp_6120);
    CursorTy pvrtmp_6129 = tmp_struct_9.field0;
    CursorTy pvrtmp_6130 = tmp_struct_9.field1;
    CursorTy pvrtmp_6131 = tmp_struct_9.field2;
    CursorTy pvrtmp_6132 = tmp_struct_9.field3;
    CursorInt64Prod tmp_struct_10 =  size(pvrtmp_6129, pvrtmp_6131);
    CursorTy pvrtmp_6137 = tmp_struct_10.field0;
    IntTy pvrtmp_6138 = tmp_struct_10.field1;
    BoolTy fltAppE_1053_1185 = pvrtmp_6138 == 5;
    unsigned char tailapp_3426 =  print_check(fltAppE_1053_1185);

    free_region(end_r_2620);
    free_region(end_r_2621);
    return tailapp_3426;
}
unsigned char bench_psb()
{
    RegionTy *region_6139 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2633 = region_6139->reg_heap;
    IntTy sizeof_end_r_2633_6140 = global_init_inf_buf_size;
    CursorTy end_r_2633 = r_2633 + sizeof_end_r_2633_6140;
    RegionTy *region_6141 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2632 = region_6141->reg_heap;
    IntTy sizeof_end_r_2632_6142 = global_init_inf_buf_size;
    CursorTy end_r_2632 = r_2632 + sizeof_end_r_2632_6142;
    CursorTy pvrtmp_6152;
    CursorTy pvrtmp_6153;
    CursorTy pvrtmp_6154;
    VectorTy *times_15 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6152;
    struct timespec end_pvrtmp_6152;

    for (long long iters_pvrtmp_6152 = 0; iters_pvrtmp_6152 <
         global_iters_param; iters_pvrtmp_6152++) {
        if (iters_pvrtmp_6152 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6152);

        CursorCursorCursorProd tmp_struct_11 =  psB(end_r_2633, r_2633, 50);
        CursorTy pvrtmp_6143 = tmp_struct_11.field0;
        CursorTy pvrtmp_6144 = tmp_struct_11.field1;
        CursorTy pvrtmp_6145 = tmp_struct_11.field2;

        pvrtmp_6152 = pvrtmp_6143;
        pvrtmp_6153 = pvrtmp_6144;
        pvrtmp_6154 = pvrtmp_6145;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6152);
        if (iters_pvrtmp_6152 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_12 = difftimespecs(&begin_pvrtmp_6152,
                                           &end_pvrtmp_6152);

        vector_inplace_update(times_15, iters_pvrtmp_6152, &itertime_12);
    }
    vector_inplace_sort(times_15, compare_doubles);

    double *tmp_16 = (double *) vector_nth(times_15, global_iters_param / 2);
    double selftimed_14 = *tmp_16;
    double batchtime_13 = sum_timing_array(times_15);

    print_timing_array(times_15);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_13);
    printf("SELFTIMED: %e\n", selftimed_14);

    CursorCursorCursorCursorProd tmp_struct_17 =
                                  toList(end_r_2633, end_r_2632, r_2632, pvrtmp_6153);
    CursorTy pvrtmp_6162 = tmp_struct_17.field0;
    CursorTy pvrtmp_6163 = tmp_struct_17.field1;
    CursorTy pvrtmp_6164 = tmp_struct_17.field2;
    CursorTy pvrtmp_6165 = tmp_struct_17.field3;
    CursorInt64Prod tmp_struct_18 =  size(pvrtmp_6162, pvrtmp_6164);
    CursorTy pvrtmp_6170 = tmp_struct_18.field0;
    IntTy pvrtmp_6171 = tmp_struct_18.field1;
    BoolTy fltAppE_1055_1189 = pvrtmp_6171 == 90;
    unsigned char tailapp_3430 =  print_check(fltAppE_1055_1189);

    free_region(end_r_2632);
    free_region(end_r_2633);
    return tailapp_3430;
}
unsigned char bench_ts()
{
    RegionTy *region_6172 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2645 = region_6172->reg_heap;
    IntTy sizeof_end_r_2645_6173 = global_init_inf_buf_size;
    CursorTy end_r_2645 = r_2645 + sizeof_end_r_2645_6173;
    RegionTy *region_6174 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2644 = region_6174->reg_heap;
    IntTy sizeof_end_r_2644_6175 = global_init_inf_buf_size;
    CursorTy end_r_2644 = r_2644 + sizeof_end_r_2644_6175;
    CursorTy pvrtmp_6185;
    CursorTy pvrtmp_6186;
    CursorTy pvrtmp_6187;
    VectorTy *times_23 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6185;
    struct timespec end_pvrtmp_6185;

    long long N = global_size_param;

    for (long long iters_pvrtmp_6185 = 0; iters_pvrtmp_6185 <
         global_iters_param; iters_pvrtmp_6185++) {
        if (iters_pvrtmp_6185 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6185);

        CursorCursorCursorProd tmp_struct_19 =  ts(end_r_2645, r_2645, N);
        CursorTy pvrtmp_6176 = tmp_struct_19.field0;
        CursorTy pvrtmp_6177 = tmp_struct_19.field1;
        CursorTy pvrtmp_6178 = tmp_struct_19.field2;

        pvrtmp_6185 = pvrtmp_6176;
        pvrtmp_6186 = pvrtmp_6177;
        pvrtmp_6187 = pvrtmp_6178;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6185);
        if (iters_pvrtmp_6185 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_20 = difftimespecs(&begin_pvrtmp_6185,
                                           &end_pvrtmp_6185);

        vector_inplace_update(times_23, iters_pvrtmp_6185, &itertime_20);
    }
    vector_inplace_sort(times_23, compare_doubles);

    double *tmp_24 = (double *) vector_nth(times_23, global_iters_param / 2);
    double selftimed_22 = *tmp_24;
    double batchtime_21 = sum_timing_array(times_23);

    print_timing_array(times_23);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_21);
    printf("SELFTIMED: %e\n", selftimed_22);

    CursorCursorCursorCursorProd tmp_struct_25 =
                                  toList(end_r_2645, end_r_2644, r_2644, pvrtmp_6186);
    CursorTy pvrtmp_6195 = tmp_struct_25.field0;
    CursorTy pvrtmp_6196 = tmp_struct_25.field1;
    CursorTy pvrtmp_6197 = tmp_struct_25.field2;
    CursorTy pvrtmp_6198 = tmp_struct_25.field3;
    CursorInt64Prod tmp_struct_26 =  size(pvrtmp_6195, pvrtmp_6197);
    CursorTy pvrtmp_6203 = tmp_struct_26.field0;
    IntTy pvrtmp_6204 = tmp_struct_26.field1;
    BoolTy fltAppE_1057_1193 = pvrtmp_6204 == N;
    unsigned char tailapp_3434 =  print_check(fltAppE_1057_1193);

    free_region(end_r_2644);
    free_region(end_r_2645);
    return tailapp_3434;
}
CursorCursorCursorProd psB(CursorTy end_r_2435, CursorTy loc_2434,
                           IntTy n_245_855_1194)
{
    RegionTy *region_6205 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2692 = region_6205->reg_heap;
    IntTy sizeof_end_r_2692_6206 = global_init_inf_buf_size;
    CursorTy end_r_2692 = r_2692 + sizeof_end_r_2692_6206;
    RegionTy *region_6207 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2691 = region_6207->reg_heap;
    IntTy sizeof_end_r_2691_6208 = global_init_inf_buf_size;
    CursorTy end_r_2691 = r_2691 + sizeof_end_r_2691_6208;
    RegionTy *region_6209 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2690 = region_6209->reg_heap;
    IntTy sizeof_end_r_2690_6210 = global_init_inf_buf_size;
    CursorTy end_r_2690 = r_2690 + sizeof_end_r_2690_6210;
    RegionTy *region_6211 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2689 = region_6211->reg_heap;
    IntTy sizeof_end_r_2689_6212 = global_init_inf_buf_size;
    CursorTy end_r_2689 = r_2689 + sizeof_end_r_2689_6212;
    RegionTy *region_6213 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2688 = region_6213->reg_heap;
    IntTy sizeof_end_r_2688_6214 = global_init_inf_buf_size;
    CursorTy end_r_2688 = r_2688 + sizeof_end_r_2688_6214;
    RegionTy *region_6215 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2687 = region_6215->reg_heap;
    IntTy sizeof_end_r_2687_6216 = global_init_inf_buf_size;
    CursorTy end_r_2687 = r_2687 + sizeof_end_r_2687_6216;
    RegionTy *region_6217 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2686 = region_6217->reg_heap;
    IntTy sizeof_end_r_2686_6218 = global_init_inf_buf_size;
    CursorTy end_r_2686 = r_2686 + sizeof_end_r_2686_6218;
    RegionTy *region_6219 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2685 = region_6219->reg_heap;
    IntTy sizeof_end_r_2685_6220 = global_init_inf_buf_size;
    CursorTy end_r_2685 = r_2685 + sizeof_end_r_2685_6220;
    RegionTy *region_6221 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2684 = region_6221->reg_heap;
    IntTy sizeof_end_r_2684_6222 = global_init_inf_buf_size;
    CursorTy end_r_2684 = r_2684 + sizeof_end_r_2684_6222;

    if (loc_2434 + 32 > end_r_2435) {
        ChunkTy new_chunk_37 = alloc_chunk(end_r_2435);
        CursorTy chunk_start_38 = new_chunk_37.chunk_start;
        CursorTy chunk_end_39 = new_chunk_37.chunk_end;

        end_r_2435 = chunk_end_39;
        *(TagTyPacked *) loc_2434 = 255;

        CursorTy redir = loc_2434 + 1;

        *(CursorTy *) redir = chunk_start_38;
        loc_2434 = chunk_start_38;
    }

    CursorCursorCursorProd tmp_struct_27 =
                            sinx(end_r_2692, r_2692, n_245_855_1194);
    CursorTy pvrtmp_6223 = tmp_struct_27.field0;
    CursorTy pvrtmp_6224 = tmp_struct_27.field1;
    CursorTy pvrtmp_6225 = tmp_struct_27.field2;
    CursorCursorCursorProd tmp_struct_28 =  pone(end_r_2691, r_2691);
    CursorTy pvrtmp_6230 = tmp_struct_28.field0;
    CursorTy pvrtmp_6231 = tmp_struct_28.field1;
    CursorTy pvrtmp_6232 = tmp_struct_28.field2;
    CursorCursorCursorProd tmp_struct_29 =
                            cosx(end_r_2690, r_2690, n_245_855_1194);
    CursorTy pvrtmp_6237 = tmp_struct_29.field0;
    CursorTy pvrtmp_6238 = tmp_struct_29.field1;
    CursorTy pvrtmp_6239 = tmp_struct_29.field2;
    CursorCursorCursorProd tmp_struct_30 =
                            cosx(end_r_2689, r_2689, n_245_855_1194);
    CursorTy pvrtmp_6244 = tmp_struct_30.field0;
    CursorTy pvrtmp_6245 = tmp_struct_30.field1;
    CursorTy pvrtmp_6246 = tmp_struct_30.field2;
    CursorCursorCursorProd tmp_struct_31 =
                            psMult(pvrtmp_6237, pvrtmp_6244, end_r_2688, r_2688, pvrtmp_6238, pvrtmp_6245);
    CursorTy pvrtmp_6251 = tmp_struct_31.field0;
    CursorTy pvrtmp_6252 = tmp_struct_31.field1;
    CursorTy pvrtmp_6253 = tmp_struct_31.field2;
    CursorCursorCursorCursorProd tmp_struct_32 =
                                  psNeg(pvrtmp_6251, end_r_2687, r_2687, pvrtmp_6252);
    CursorTy pvrtmp_6258 = tmp_struct_32.field0;
    CursorTy pvrtmp_6259 = tmp_struct_32.field1;
    CursorTy pvrtmp_6260 = tmp_struct_32.field2;
    CursorTy pvrtmp_6261 = tmp_struct_32.field3;
    CursorCursorCursorProd tmp_struct_33 =
                            psAdd(pvrtmp_6230, pvrtmp_6258, end_r_2686, r_2686, pvrtmp_6231, pvrtmp_6260);
    CursorTy pvrtmp_6266 = tmp_struct_33.field0;
    CursorTy pvrtmp_6267 = tmp_struct_33.field1;
    CursorTy pvrtmp_6268 = tmp_struct_33.field2;
    CursorCursorCursorProd tmp_struct_34 =
                            psSqrt(pvrtmp_6266, end_r_2685, r_2685, n_245_855_1194, pvrtmp_6267);
    CursorTy pvrtmp_6273 = tmp_struct_34.field0;
    CursorTy pvrtmp_6274 = tmp_struct_34.field1;
    CursorTy pvrtmp_6275 = tmp_struct_34.field2;
    CursorCursorCursorCursorProd tmp_struct_35 =
                                  psNeg(pvrtmp_6273, end_r_2684, r_2684, pvrtmp_6274);
    CursorTy pvrtmp_6280 = tmp_struct_35.field0;
    CursorTy pvrtmp_6281 = tmp_struct_35.field1;
    CursorTy pvrtmp_6282 = tmp_struct_35.field2;
    CursorTy pvrtmp_6283 = tmp_struct_35.field3;
    CursorCursorCursorProd tmp_struct_36 =
                            psAdd(pvrtmp_6223, pvrtmp_6280, end_r_2435, loc_2434, pvrtmp_6224, pvrtmp_6282);
    CursorTy pvrtmp_6288 = tmp_struct_36.field0;
    CursorTy pvrtmp_6289 = tmp_struct_36.field1;
    CursorTy pvrtmp_6290 = tmp_struct_36.field2;

    free_region(end_r_2684);
    free_region(end_r_2685);
    free_region(end_r_2686);
    free_region(end_r_2687);
    free_region(end_r_2688);
    free_region(end_r_2689);
    free_region(end_r_2690);
    free_region(end_r_2691);
    free_region(end_r_2692);
    return (CursorCursorCursorProd) {pvrtmp_6288, pvrtmp_6289, pvrtmp_6290};
}
CursorCursorCursorProd psC(CursorTy end_r_2437, CursorTy loc_2436,
                           IntTy n_246_856_1204)
{
    RegionTy *region_6297 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2759 = region_6297->reg_heap;
    IntTy sizeof_end_r_2759_6298 = global_init_inf_buf_size;
    CursorTy end_r_2759 = r_2759 + sizeof_end_r_2759_6298;
    RegionTy *region_6299 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2758 = region_6299->reg_heap;
    IntTy sizeof_end_r_2758_6300 = global_init_inf_buf_size;
    CursorTy end_r_2758 = r_2758 + sizeof_end_r_2758_6300;
    RegionTy *region_6301 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2757 = region_6301->reg_heap;
    IntTy sizeof_end_r_2757_6302 = global_init_inf_buf_size;
    CursorTy end_r_2757 = r_2757 + sizeof_end_r_2757_6302;
    RegionTy *region_6303 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2756 = region_6303->reg_heap;
    IntTy sizeof_end_r_2756_6304 = global_init_inf_buf_size;
    CursorTy end_r_2756 = r_2756 + sizeof_end_r_2756_6304;
    RegionTy *region_6305 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2755 = region_6305->reg_heap;
    IntTy sizeof_end_r_2755_6306 = global_init_inf_buf_size;
    CursorTy end_r_2755 = r_2755 + sizeof_end_r_2755_6306;
    RegionTy *region_6307 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2754 = region_6307->reg_heap;
    IntTy sizeof_end_r_2754_6308 = global_init_inf_buf_size;
    CursorTy end_r_2754 = r_2754 + sizeof_end_r_2754_6308;
    RegionTy *region_6309 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2753 = region_6309->reg_heap;
    IntTy sizeof_end_r_2753_6310 = global_init_inf_buf_size;
    CursorTy end_r_2753 = r_2753 + sizeof_end_r_2753_6310;
    RegionTy *region_6311 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2752 = region_6311->reg_heap;
    IntTy sizeof_end_r_2752_6312 = global_init_inf_buf_size;
    CursorTy end_r_2752 = r_2752 + sizeof_end_r_2752_6312;
    RegionTy *region_6313 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2751 = region_6313->reg_heap;
    IntTy sizeof_end_r_2751_6314 = global_init_inf_buf_size;
    CursorTy end_r_2751 = r_2751 + sizeof_end_r_2751_6314;
    RegionTy *region_6315 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2750 = region_6315->reg_heap;
    IntTy sizeof_end_r_2750_6316 = global_init_inf_buf_size;
    CursorTy end_r_2750 = r_2750 + sizeof_end_r_2750_6316;
    RegionTy *region_6317 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2749 = region_6317->reg_heap;
    IntTy sizeof_end_r_2749_6318 = global_init_inf_buf_size;
    CursorTy end_r_2749 = r_2749 + sizeof_end_r_2749_6318;
    RegionTy *region_6319 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2748 = region_6319->reg_heap;
    IntTy sizeof_end_r_2748_6320 = global_init_inf_buf_size;
    CursorTy end_r_2748 = r_2748 + sizeof_end_r_2748_6320;
    RegionTy *region_6321 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2747 = region_6321->reg_heap;
    IntTy sizeof_end_r_2747_6322 = global_init_inf_buf_size;
    CursorTy end_r_2747 = r_2747 + sizeof_end_r_2747_6322;

    if (loc_2436 + 32 > end_r_2437) {
        ChunkTy new_chunk_54 = alloc_chunk(end_r_2437);
        CursorTy chunk_start_55 = new_chunk_54.chunk_start;
        CursorTy chunk_end_56 = new_chunk_54.chunk_end;

        end_r_2437 = chunk_end_56;
        *(TagTyPacked *) loc_2436 = 255;

        CursorTy redir = loc_2436 + 1;

        *(CursorTy *) redir = chunk_start_55;
        loc_2436 = chunk_start_55;
    }

    CursorCursorCursorProd tmp_struct_40 =
                            sinx(end_r_2759, r_2759, n_246_856_1204);
    CursorTy pvrtmp_6323 = tmp_struct_40.field0;
    CursorTy pvrtmp_6324 = tmp_struct_40.field1;
    CursorTy pvrtmp_6325 = tmp_struct_40.field2;
    CursorCursorCursorProd tmp_struct_41 =
                            cosx(end_r_2758, r_2758, n_246_856_1204);
    CursorTy pvrtmp_6330 = tmp_struct_41.field0;
    CursorTy pvrtmp_6331 = tmp_struct_41.field1;
    CursorTy pvrtmp_6332 = tmp_struct_41.field2;
    CursorCursorCursorProd tmp_struct_42 =
                            psDiv(pvrtmp_6323, pvrtmp_6330, end_r_2757, r_2757, n_246_856_1204, pvrtmp_6324, pvrtmp_6331);
    CursorTy pvrtmp_6337 = tmp_struct_42.field0;
    CursorTy pvrtmp_6338 = tmp_struct_42.field1;
    CursorTy pvrtmp_6339 = tmp_struct_42.field2;
    CursorCursorCursorProd tmp_struct_43 =  pone(end_r_2756, r_2756);
    CursorTy pvrtmp_6344 = tmp_struct_43.field0;
    CursorTy pvrtmp_6345 = tmp_struct_43.field1;
    CursorTy pvrtmp_6346 = tmp_struct_43.field2;
    CursorCursorCursorProd tmp_struct_44 =  pone(end_r_2755, r_2755);
    CursorTy pvrtmp_6351 = tmp_struct_44.field0;
    CursorTy pvrtmp_6352 = tmp_struct_44.field1;
    CursorTy pvrtmp_6353 = tmp_struct_44.field2;
    CursorCursorCursorProd tmp_struct_45 =  psX(end_r_2754, r_2754);
    CursorTy pvrtmp_6358 = tmp_struct_45.field0;
    CursorTy pvrtmp_6359 = tmp_struct_45.field1;
    CursorTy pvrtmp_6360 = tmp_struct_45.field2;
    CursorCursorCursorProd tmp_struct_46 =  psX(end_r_2753, r_2753);
    CursorTy pvrtmp_6365 = tmp_struct_46.field0;
    CursorTy pvrtmp_6366 = tmp_struct_46.field1;
    CursorTy pvrtmp_6367 = tmp_struct_46.field2;
    CursorCursorCursorProd tmp_struct_47 =
                            psMult(pvrtmp_6358, pvrtmp_6365, end_r_2752, r_2752, pvrtmp_6359, pvrtmp_6366);
    CursorTy pvrtmp_6372 = tmp_struct_47.field0;
    CursorTy pvrtmp_6373 = tmp_struct_47.field1;
    CursorTy pvrtmp_6374 = tmp_struct_47.field2;
    CursorCursorCursorProd tmp_struct_48 =
                            psAdd(pvrtmp_6351, pvrtmp_6372, end_r_2751, r_2751, pvrtmp_6352, pvrtmp_6373);
    CursorTy pvrtmp_6379 = tmp_struct_48.field0;
    CursorTy pvrtmp_6380 = tmp_struct_48.field1;
    CursorTy pvrtmp_6381 = tmp_struct_48.field2;
    CursorCursorCursorProd tmp_struct_49 =
                            psDiv(pvrtmp_6344, pvrtmp_6379, end_r_2750, r_2750, n_246_856_1204, pvrtmp_6345, pvrtmp_6380);
    CursorTy pvrtmp_6386 = tmp_struct_49.field0;
    CursorTy pvrtmp_6387 = tmp_struct_49.field1;
    CursorTy pvrtmp_6388 = tmp_struct_49.field2;
    CursorCursorCursorCursorProd tmp_struct_50 =
                                  integral(pvrtmp_6386, end_r_2749, r_2749, pvrtmp_6387);
    CursorTy pvrtmp_6393 = tmp_struct_50.field0;
    CursorTy pvrtmp_6394 = tmp_struct_50.field1;
    CursorTy pvrtmp_6395 = tmp_struct_50.field2;
    CursorTy pvrtmp_6396 = tmp_struct_50.field3;
    CursorCursorCursorProd tmp_struct_51 =
                            revert(pvrtmp_6393, end_r_2748, r_2748, n_246_856_1204, pvrtmp_6395);
    CursorTy pvrtmp_6401 = tmp_struct_51.field0;
    CursorTy pvrtmp_6402 = tmp_struct_51.field1;
    CursorTy pvrtmp_6403 = tmp_struct_51.field2;
    CursorCursorCursorCursorProd tmp_struct_52 =
                                  psNeg(pvrtmp_6401, end_r_2747, r_2747, pvrtmp_6402);
    CursorTy pvrtmp_6408 = tmp_struct_52.field0;
    CursorTy pvrtmp_6409 = tmp_struct_52.field1;
    CursorTy pvrtmp_6410 = tmp_struct_52.field2;
    CursorTy pvrtmp_6411 = tmp_struct_52.field3;
    CursorCursorCursorProd tmp_struct_53 =
                            psAdd(pvrtmp_6337, pvrtmp_6408, end_r_2437, loc_2436, pvrtmp_6338, pvrtmp_6410);
    CursorTy pvrtmp_6416 = tmp_struct_53.field0;
    CursorTy pvrtmp_6417 = tmp_struct_53.field1;
    CursorTy pvrtmp_6418 = tmp_struct_53.field2;

    free_region(end_r_2747);
    free_region(end_r_2748);
    free_region(end_r_2749);
    free_region(end_r_2750);
    free_region(end_r_2751);
    free_region(end_r_2752);
    free_region(end_r_2753);
    free_region(end_r_2754);
    free_region(end_r_2755);
    free_region(end_r_2756);
    free_region(end_r_2757);
    free_region(end_r_2758);
    free_region(end_r_2759);
    return (CursorCursorCursorProd) {pvrtmp_6416, pvrtmp_6417, pvrtmp_6418};
}
CursorCursorCursorCursorProd toList(CursorTy end_r_2440, CursorTy end_r_2441,
                                    CursorTy loc_2439, CursorTy ps_247_857_1218)
{
    if (loc_2439 + 32 > end_r_2441) {
        ChunkTy new_chunk_60 = alloc_chunk(end_r_2441);
        CursorTy chunk_start_61 = new_chunk_60.chunk_start;
        CursorTy chunk_end_62 = new_chunk_60.chunk_end;

        end_r_2441 = chunk_end_62;
        *(TagTyPacked *) loc_2439 = 255;

        CursorTy redir = loc_2439 + 1;

        *(CursorTy *) redir = chunk_start_61;
        loc_2439 = chunk_start_61;
    }

    TagTyPacked tmpval_6425 = *(TagTyPacked *) ps_247_857_1218;
    CursorTy tmpcur_6426 = ps_247_857_1218 + 1;


  switch_6469:
    ;
    switch (tmpval_6425) {

      case 0:
        {
            CursorTy jump_3441 = ps_247_857_1218 + 1;

            *(TagTyPacked *) loc_2439 = 0;

            CursorTy writetag_4054 = loc_2439 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2441, jump_3441,
                                                   loc_2439, writetag_4054};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6431 = *(FloatTy *) tmpcur_6426;
            CursorTy tmpcur_6432 = tmpcur_6426 + sizeof(FloatTy);
            CursorTy jump_3443 = tmpcur_6426 + 4;
            CursorTy loc_2768 = loc_2439 + 1;
            CursorTy loc_2769 = loc_2768 + 4;
            CursorCursorCursorCursorProd tmp_struct_57 =
                                          toList(end_r_2440, end_r_2441, loc_2769, tmpcur_6432);
            CursorTy pvrtmp_6433 = tmp_struct_57.field0;
            CursorTy pvrtmp_6434 = tmp_struct_57.field1;
            CursorTy pvrtmp_6435 = tmp_struct_57.field2;
            CursorTy pvrtmp_6436 = tmp_struct_57.field3;

            *(TagTyPacked *) loc_2439 = 1;

            CursorTy writetag_4059 = loc_2439 + 1;

            *(FloatTy *) writetag_4059 = tmpval_6431;

            CursorTy writecur_4060 = writetag_4059 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_6433, pvrtmp_6434,
                                                   loc_2439, pvrtmp_6436};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6445 = *(CursorTy *) tmpcur_6426;
            CursorTy tmpaftercur_6446 = tmpcur_6426 + 8;
            CursorTy jump_3682 = tmpcur_6426 + 8;
            CursorCursorCursorCursorProd tmp_struct_58 =
                                          toList(end_r_2440, end_r_2441, loc_2439, tmpcur_6445);
            CursorTy pvrtmp_6447 = tmp_struct_58.field0;
            CursorTy pvrtmp_6448 = tmp_struct_58.field1;
            CursorTy pvrtmp_6449 = tmp_struct_58.field2;
            CursorTy pvrtmp_6450 = tmp_struct_58.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6447, jump_3682,
                                                   pvrtmp_6449, pvrtmp_6450};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6457 = *(CursorTy *) tmpcur_6426;
            CursorTy tmpaftercur_6458 = tmpcur_6426 + 8;
            CursorCursorCursorCursorProd tmp_struct_59 =
                                          toList(end_r_2440, end_r_2441, loc_2439, tmpcur_6457);
            CursorTy pvrtmp_6459 = tmp_struct_59.field0;
            CursorTy pvrtmp_6460 = tmp_struct_59.field1;
            CursorTy pvrtmp_6461 = tmp_struct_59.field2;
            CursorTy pvrtmp_6462 = tmp_struct_59.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6459, pvrtmp_6460,
                                                   pvrtmp_6461, pvrtmp_6462};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6425");
            exit(1);
        }
    }
}
CursorCursorCursorProd sinx(CursorTy end_r_2443, CursorTy loc_2442,
                            IntTy n_262_865_1222)
{
    if (loc_2442 + 32 > end_r_2443) {
        ChunkTy new_chunk_65 = alloc_chunk(end_r_2443);
        CursorTy chunk_start_66 = new_chunk_65.chunk_start;
        CursorTy chunk_end_67 = new_chunk_65.chunk_end;

        end_r_2443 = chunk_end_67;
        *(TagTyPacked *) loc_2442 = 255;

        CursorTy redir = loc_2442 + 1;

        *(CursorTy *) redir = chunk_start_66;
        loc_2442 = chunk_start_66;
    }

    BoolTy fltIf_1081_1223 = n_262_865_1222 == 0;

    if (fltIf_1081_1223) {
        *(TagTyPacked *) loc_2442 = 0;

        CursorTy writetag_4069 = loc_2442 + 1;

        return (CursorCursorCursorProd) {end_r_2443, loc_2442, writetag_4069};
    } else {
        RegionTy *region_6474 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2780 = region_6474->reg_heap;
        IntTy sizeof_end_r_2780_6475 = global_init_inf_buf_size;
        CursorTy end_r_2780 = r_2780 + sizeof_end_r_2780_6475;
        IntTy fltAppE_1083_1224 = n_262_865_1222 - 1;
        CursorCursorCursorProd tmp_struct_63 =
                                cosx(end_r_2780, r_2780, fltAppE_1083_1224);
        CursorTy pvrtmp_6476 = tmp_struct_63.field0;
        CursorTy pvrtmp_6477 = tmp_struct_63.field1;
        CursorTy pvrtmp_6478 = tmp_struct_63.field2;
        CursorCursorCursorCursorProd tmp_struct_64 =
                                      integral(pvrtmp_6476, end_r_2443, loc_2442, pvrtmp_6477);
        CursorTy pvrtmp_6483 = tmp_struct_64.field0;
        CursorTy pvrtmp_6484 = tmp_struct_64.field1;
        CursorTy pvrtmp_6485 = tmp_struct_64.field2;
        CursorTy pvrtmp_6486 = tmp_struct_64.field3;

        free_region(end_r_2780);
        return (CursorCursorCursorProd) {pvrtmp_6483, pvrtmp_6485, pvrtmp_6486};
    }
}
CursorCursorCursorProd cosx(CursorTy end_r_2445, CursorTy loc_2444,
                            IntTy n_263_866_1226)
{
    if (loc_2444 + 32 > end_r_2445) {
        ChunkTy new_chunk_73 = alloc_chunk(end_r_2445);
        CursorTy chunk_start_74 = new_chunk_73.chunk_start;
        CursorTy chunk_end_75 = new_chunk_73.chunk_end;

        end_r_2445 = chunk_end_75;
        *(TagTyPacked *) loc_2444 = 255;

        CursorTy redir = loc_2444 + 1;

        *(CursorTy *) redir = chunk_start_74;
        loc_2444 = chunk_start_74;
    }

    BoolTy fltIf_1084_1227 = n_263_866_1226 == 0;

    if (fltIf_1084_1227) {
        *(TagTyPacked *) loc_2444 = 0;

        CursorTy writetag_4073 = loc_2444 + 1;

        return (CursorCursorCursorProd) {end_r_2445, loc_2444, writetag_4073};
    } else {
        RegionTy *region_6497 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2803 = region_6497->reg_heap;
        IntTy sizeof_end_r_2803_6498 = global_init_inf_buf_size;
        CursorTy end_r_2803 = r_2803 + sizeof_end_r_2803_6498;
        RegionTy *region_6499 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2802 = region_6499->reg_heap;
        IntTy sizeof_end_r_2802_6500 = global_init_inf_buf_size;
        CursorTy end_r_2802 = r_2802 + sizeof_end_r_2802_6500;
        RegionTy *region_6501 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2801 = region_6501->reg_heap;
        IntTy sizeof_end_r_2801_6502 = global_init_inf_buf_size;
        CursorTy end_r_2801 = r_2801 + sizeof_end_r_2801_6502;
        RegionTy *region_6503 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2800 = region_6503->reg_heap;
        IntTy sizeof_end_r_2800_6504 = global_init_inf_buf_size;
        CursorTy end_r_2800 = r_2800 + sizeof_end_r_2800_6504;
        CursorCursorCursorProd tmp_struct_68 =  pone(end_r_2803, r_2803);
        CursorTy pvrtmp_6505 = tmp_struct_68.field0;
        CursorTy pvrtmp_6506 = tmp_struct_68.field1;
        CursorTy pvrtmp_6507 = tmp_struct_68.field2;
        IntTy fltAppE_1089_1229 = n_263_866_1226 - 1;
        CursorCursorCursorProd tmp_struct_69 =
                                sinx(end_r_2802, r_2802, fltAppE_1089_1229);
        CursorTy pvrtmp_6512 = tmp_struct_69.field0;
        CursorTy pvrtmp_6513 = tmp_struct_69.field1;
        CursorTy pvrtmp_6514 = tmp_struct_69.field2;
        CursorCursorCursorCursorProd tmp_struct_70 =
                                      integral(pvrtmp_6512, end_r_2801, r_2801, pvrtmp_6513);
        CursorTy pvrtmp_6519 = tmp_struct_70.field0;
        CursorTy pvrtmp_6520 = tmp_struct_70.field1;
        CursorTy pvrtmp_6521 = tmp_struct_70.field2;
        CursorTy pvrtmp_6522 = tmp_struct_70.field3;
        CursorCursorCursorCursorProd tmp_struct_71 =
                                      psNeg(pvrtmp_6519, end_r_2800, r_2800, pvrtmp_6521);
        CursorTy pvrtmp_6527 = tmp_struct_71.field0;
        CursorTy pvrtmp_6528 = tmp_struct_71.field1;
        CursorTy pvrtmp_6529 = tmp_struct_71.field2;
        CursorTy pvrtmp_6530 = tmp_struct_71.field3;
        CursorCursorCursorProd tmp_struct_72 =
                                psAdd(pvrtmp_6505, pvrtmp_6527, end_r_2445, loc_2444, pvrtmp_6506, pvrtmp_6529);
        CursorTy pvrtmp_6535 = tmp_struct_72.field0;
        CursorTy pvrtmp_6536 = tmp_struct_72.field1;
        CursorTy pvrtmp_6537 = tmp_struct_72.field2;

        free_region(end_r_2800);
        free_region(end_r_2801);
        free_region(end_r_2802);
        free_region(end_r_2803);
        return (CursorCursorCursorProd) {pvrtmp_6535, pvrtmp_6536, pvrtmp_6537};
    }
}
CursorCursorCursorProd psSqrt(CursorTy end_r_2448, CursorTy end_r_2449,
                              CursorTy loc_2447, IntTy n_264_867_1233,
                              CursorTy a_265_868_1234)
{
    if (loc_2447 + 32 > end_r_2449) {
        ChunkTy new_chunk_80 = alloc_chunk(end_r_2449);
        CursorTy chunk_start_81 = new_chunk_80.chunk_start;
        CursorTy chunk_end_82 = new_chunk_80.chunk_end;

        end_r_2449 = chunk_end_82;
        *(TagTyPacked *) loc_2447 = 255;

        CursorTy redir = loc_2447 + 1;

        *(CursorTy *) redir = chunk_start_81;
        loc_2447 = chunk_start_81;
    }

    TagTyPacked tmpval_6544 = *(TagTyPacked *) a_265_868_1234;
    CursorTy tmpcur_6545 = a_265_868_1234 + 1;


  switch_6596:
    ;
    switch (tmpval_6544) {

      case 0:
        {
            CursorTy jump_3453 = a_265_868_1234 + 1;

            *(TagTyPacked *) loc_2447 = 0;

            CursorTy writetag_4081 = loc_2447 + 1;

            return (CursorCursorCursorProd) {end_r_2449, loc_2447,
                                             writetag_4081};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6550 = *(FloatTy *) tmpcur_6545;
            CursorTy tmpcur_6551 = tmpcur_6545 + sizeof(FloatTy);
            CursorTy jump_3455 = tmpcur_6545 + 4;
            BoolTy fltIf_1090_1237 = tmpval_6550 == 1.0;

            if (fltIf_1090_1237) {
                CursorCursorCursorProd tmp_struct_76 =
                                        getQs(end_r_2448, end_r_2449, loc_2447, n_264_867_1233, tmpcur_6551);
                CursorTy pvrtmp_6552 = tmp_struct_76.field0;
                CursorTy pvrtmp_6553 = tmp_struct_76.field1;
                CursorTy pvrtmp_6554 = tmp_struct_76.field2;

                return (CursorCursorCursorProd) {pvrtmp_6552, pvrtmp_6553,
                                                 pvrtmp_6554};
            } else {
                CursorCursorCursorProd tmp_struct_77 =
                                        caseFn_807(end_r_2448, end_r_2449, loc_2447, n_264_867_1233, tmpcur_6551);
                CursorTy pvrtmp_6561 = tmp_struct_77.field0;
                CursorTy pvrtmp_6562 = tmp_struct_77.field1;
                CursorTy pvrtmp_6563 = tmp_struct_77.field2;

                return (CursorCursorCursorProd) {pvrtmp_6561, pvrtmp_6562,
                                                 pvrtmp_6563};
            }
            break;
        }

      case 2:
        {
            CursorTy jump_3458 = a_265_868_1234 + 1;

            *(TagTyPacked *) loc_2447 = 2;

            CursorTy writetag_4088 = loc_2447 + 1;

            return (CursorCursorCursorProd) {end_r_2449, loc_2447,
                                             writetag_4088};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6574 = *(CursorTy *) tmpcur_6545;
            CursorTy tmpaftercur_6575 = tmpcur_6545 + 8;
            CursorTy jump_3688 = tmpcur_6545 + 8;
            CursorCursorCursorProd tmp_struct_78 =
                                    psSqrt(end_r_2448, end_r_2449, loc_2447, n_264_867_1233, tmpcur_6574);
            CursorTy pvrtmp_6576 = tmp_struct_78.field0;
            CursorTy pvrtmp_6577 = tmp_struct_78.field1;
            CursorTy pvrtmp_6578 = tmp_struct_78.field2;

            return (CursorCursorCursorProd) {pvrtmp_6576, pvrtmp_6577,
                                             pvrtmp_6578};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6585 = *(CursorTy *) tmpcur_6545;
            CursorTy tmpaftercur_6586 = tmpcur_6545 + 8;
            CursorCursorCursorProd tmp_struct_79 =
                                    psSqrt(end_r_2448, end_r_2449, loc_2447, n_264_867_1233, tmpcur_6585);
            CursorTy pvrtmp_6587 = tmp_struct_79.field0;
            CursorTy pvrtmp_6588 = tmp_struct_79.field1;
            CursorTy pvrtmp_6589 = tmp_struct_79.field2;

            return (CursorCursorCursorProd) {pvrtmp_6587, pvrtmp_6588,
                                             pvrtmp_6589};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6544");
            exit(1);
        }
    }
}
CursorCursorCursorProd getQs(CursorTy end_r_2452, CursorTy end_r_2453,
                             CursorTy loc_2451, IntTy n_270_871_1238,
                             CursorTy fs_271_872_1239)
{
    if (loc_2451 + 32 > end_r_2453) {
        ChunkTy new_chunk_90 = alloc_chunk(end_r_2453);
        CursorTy chunk_start_91 = new_chunk_90.chunk_start;
        CursorTy chunk_end_92 = new_chunk_90.chunk_end;

        end_r_2453 = chunk_end_92;
        *(TagTyPacked *) loc_2451 = 255;

        CursorTy redir = loc_2451 + 1;

        *(CursorTy *) redir = chunk_start_91;
        loc_2451 = chunk_start_91;
    }

    BoolTy fltIf_1091_1240 = n_270_871_1238 <= 0;

    if (fltIf_1091_1240) {
        *(TagTyPacked *) loc_2451 = 0;

        CursorTy writetag_4096 = loc_2451 + 1;

        return (CursorCursorCursorProd) {end_r_2453, loc_2451, writetag_4096};
    } else {
        RegionTy *region_6601 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2860 = region_6601->reg_heap;
        IntTy sizeof_end_r_2860_6602 = global_init_inf_buf_size;
        CursorTy end_r_2860 = r_2860 + sizeof_end_r_2860_6602;
        RegionTy *region_6603 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2859 = region_6603->reg_heap;
        IntTy sizeof_end_r_2859_6604 = global_init_inf_buf_size;
        CursorTy end_r_2859 = r_2859 + sizeof_end_r_2859_6604;
        RegionTy *region_6605 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2858 = region_6605->reg_heap;
        IntTy sizeof_end_r_2858_6606 = global_init_inf_buf_size;
        CursorTy end_r_2858 = r_2858 + sizeof_end_r_2858_6606;
        RegionTy *region_6607 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2857 = region_6607->reg_heap;
        IntTy sizeof_end_r_2857_6608 = global_init_inf_buf_size;
        CursorTy end_r_2857 = r_2857 + sizeof_end_r_2857_6608;
        RegionTy *region_6609 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2856 = region_6609->reg_heap;
        IntTy sizeof_end_r_2856_6610 = global_init_inf_buf_size;
        CursorTy end_r_2856 = r_2856 + sizeof_end_r_2856_6610;
        RegionTy *region_6611 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2855 = region_6611->reg_heap;
        IntTy sizeof_end_r_2855_6612 = global_init_inf_buf_size;
        CursorTy end_r_2855 = r_2855 + sizeof_end_r_2855_6612;
        RegionTy *region_6613 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2854 = region_6613->reg_heap;
        IntTy sizeof_end_r_2854_6614 = global_init_inf_buf_size;
        CursorTy end_r_2854 = r_2854 + sizeof_end_r_2854_6614;
        CursorCursorCursorProd tmp_struct_83 =  pone(end_r_2860, r_2860);
        CursorTy pvrtmp_6615 = tmp_struct_83.field0;
        CursorTy pvrtmp_6616 = tmp_struct_83.field1;
        CursorTy pvrtmp_6617 = tmp_struct_83.field2;
        IntTy fltAppE_1095_1242 = n_270_871_1238 - 1;
        CursorTy loc_2821 = r_2859 + 1;
        CursorTy loc_2822 = loc_2821 + 4;

        bump_ref_count(end_r_2859, end_r_2452);
        *(TagTyPacked *) loc_2822 = 254;

        CursorTy writetag_4099 = loc_2822 + 1;

        *(CursorTy *) writetag_4099 = fs_271_872_1239;

        CursorTy writecur_4100 = writetag_4099 + 8;

        *(TagTyPacked *) r_2859 = 1;

        CursorTy writetag_4102 = r_2859 + 1;

        *(FloatTy *) writetag_4102 = 1.0;

        CursorTy writecur_4103 = writetag_4102 + sizeof(FloatTy);
        CursorCursorCursorCursorProd tmp_struct_84 =
                                      deriv(end_r_2859, end_r_2858, r_2858, r_2859);
        CursorTy pvrtmp_6626 = tmp_struct_84.field0;
        CursorTy pvrtmp_6627 = tmp_struct_84.field1;
        CursorTy pvrtmp_6628 = tmp_struct_84.field2;
        CursorTy pvrtmp_6629 = tmp_struct_84.field3;
        IntTy fltAppE_1100_1245 = n_270_871_1238 - 1;
        CursorCursorCursorProd tmp_struct_85 =
                                getQs(end_r_2452, end_r_2857, r_2857, fltAppE_1100_1245, fs_271_872_1239);
        CursorTy pvrtmp_6634 = tmp_struct_85.field0;
        CursorTy pvrtmp_6635 = tmp_struct_85.field1;
        CursorTy pvrtmp_6636 = tmp_struct_85.field2;
        CursorCursorCursorCursorProd tmp_struct_86 =
                                      dot(pvrtmp_6634, end_r_2856, r_2856, 2.0, pvrtmp_6635);
        CursorTy pvrtmp_6641 = tmp_struct_86.field0;
        CursorTy pvrtmp_6642 = tmp_struct_86.field1;
        CursorTy pvrtmp_6643 = tmp_struct_86.field2;
        CursorTy pvrtmp_6644 = tmp_struct_86.field3;
        CursorCursorCursorProd tmp_struct_87 =
                                psDiv(pvrtmp_6626, pvrtmp_6641, end_r_2855, r_2855, fltAppE_1095_1242, pvrtmp_6628, pvrtmp_6643);
        CursorTy pvrtmp_6649 = tmp_struct_87.field0;
        CursorTy pvrtmp_6650 = tmp_struct_87.field1;
        CursorTy pvrtmp_6651 = tmp_struct_87.field2;
        CursorCursorCursorCursorProd tmp_struct_88 =
                                      integral(pvrtmp_6649, end_r_2854, r_2854, pvrtmp_6650);
        CursorTy pvrtmp_6656 = tmp_struct_88.field0;
        CursorTy pvrtmp_6657 = tmp_struct_88.field1;
        CursorTy pvrtmp_6658 = tmp_struct_88.field2;
        CursorTy pvrtmp_6659 = tmp_struct_88.field3;
        CursorCursorCursorProd tmp_struct_89 =
                                psAdd(pvrtmp_6615, pvrtmp_6656, end_r_2453, loc_2451, pvrtmp_6616, pvrtmp_6658);
        CursorTy pvrtmp_6664 = tmp_struct_89.field0;
        CursorTy pvrtmp_6665 = tmp_struct_89.field1;
        CursorTy pvrtmp_6666 = tmp_struct_89.field2;

        free_region(end_r_2854);
        free_region(end_r_2855);
        free_region(end_r_2856);
        free_region(end_r_2857);
        free_region(end_r_2858);
        free_region(end_r_2859);
        free_region(end_r_2860);
        return (CursorCursorCursorProd) {pvrtmp_6664, pvrtmp_6665, pvrtmp_6666};
    }
}
CursorCursorCursorCursorProd integral(CursorTy end_r_2456, CursorTy end_r_2457,
                                      CursorTy loc_2455,
                                      CursorTy fs_272_873_1250)
{
    if (loc_2455 + 32 > end_r_2457) {
        ChunkTy new_chunk_94 = alloc_chunk(end_r_2457);
        CursorTy chunk_start_95 = new_chunk_94.chunk_start;
        CursorTy chunk_end_96 = new_chunk_94.chunk_end;

        end_r_2457 = chunk_end_96;
        *(TagTyPacked *) loc_2455 = 255;

        CursorTy redir = loc_2455 + 1;

        *(CursorTy *) redir = chunk_start_95;
        loc_2455 = chunk_start_95;
    }

    CursorTy loc_2864 = loc_2455 + 1;
    CursorTy loc_2865 = loc_2864 + 4;
    CursorCursorCursorCursorProd tmp_struct_93 =
                                  int1(end_r_2456, end_r_2457, loc_2865, fs_272_873_1250, 1);
    CursorTy pvrtmp_6673 = tmp_struct_93.field0;
    CursorTy pvrtmp_6674 = tmp_struct_93.field1;
    CursorTy pvrtmp_6675 = tmp_struct_93.field2;
    CursorTy pvrtmp_6676 = tmp_struct_93.field3;

    *(TagTyPacked *) loc_2455 = 1;

    CursorTy writetag_4113 = loc_2455 + 1;

    *(FloatTy *) writetag_4113 = 0.0;

    CursorTy writecur_4114 = writetag_4113 + sizeof(FloatTy);

    return (CursorCursorCursorCursorProd) {pvrtmp_6673, pvrtmp_6674, loc_2455,
                                           pvrtmp_6676};
}
CursorCursorCursorCursorProd int1(CursorTy end_r_2460, CursorTy end_r_2461,
                                  CursorTy loc_2459, CursorTy a_273_874_1252,
                                  IntTy n_274_875_1253)
{
    if (loc_2459 + 32 > end_r_2461) {
        ChunkTy new_chunk_100 = alloc_chunk(end_r_2461);
        CursorTy chunk_start_101 = new_chunk_100.chunk_start;
        CursorTy chunk_end_102 = new_chunk_100.chunk_end;

        end_r_2461 = chunk_end_102;
        *(TagTyPacked *) loc_2459 = 255;

        CursorTy redir = loc_2459 + 1;

        *(CursorTy *) redir = chunk_start_101;
        loc_2459 = chunk_start_101;
    }

    TagTyPacked tmpval_6685 = *(TagTyPacked *) a_273_874_1252;
    CursorTy tmpcur_6686 = a_273_874_1252 + 1;


  switch_6733:
    ;
    switch (tmpval_6685) {

      case 0:
        {
            CursorTy jump_3467 = a_273_874_1252 + 1;

            *(TagTyPacked *) loc_2459 = 0;

            CursorTy writetag_4118 = loc_2459 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2461, jump_3467,
                                                   loc_2459, writetag_4118};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6691 = *(FloatTy *) tmpcur_6686;
            CursorTy tmpcur_6692 = tmpcur_6686 + sizeof(FloatTy);
            CursorTy jump_3469 = tmpcur_6686 + 4;
            FloatTy fltPrm_1103_1256 = (FloatTy) n_274_875_1253;
            FloatTy fltPkd_1102_1257 = tmpval_6691 / fltPrm_1103_1256;
            IntTy fltAppE_1105_1258 = n_274_875_1253 + 1;
            CursorTy loc_2875 = loc_2459 + 1;
            CursorTy loc_2876 = loc_2875 + 4;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          int1(end_r_2460, end_r_2461, loc_2876, tmpcur_6692, fltAppE_1105_1258);
            CursorTy pvrtmp_6693 = tmp_struct_97.field0;
            CursorTy pvrtmp_6694 = tmp_struct_97.field1;
            CursorTy pvrtmp_6695 = tmp_struct_97.field2;
            CursorTy pvrtmp_6696 = tmp_struct_97.field3;

            *(TagTyPacked *) loc_2459 = 1;

            CursorTy writetag_4123 = loc_2459 + 1;

            *(FloatTy *) writetag_4123 = fltPkd_1102_1257;

            CursorTy writecur_4124 = writetag_4123 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_6693, pvrtmp_6694,
                                                   loc_2459, pvrtmp_6696};
            break;
        }

      case 2:
        {
            CursorTy jump_3472 = a_273_874_1252 + 1;

            *(TagTyPacked *) loc_2459 = 2;

            CursorTy writetag_4128 = loc_2459 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2461, jump_3472,
                                                   loc_2459, writetag_4128};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6709 = *(CursorTy *) tmpcur_6686;
            CursorTy tmpaftercur_6710 = tmpcur_6686 + 8;
            CursorTy jump_3693 = tmpcur_6686 + 8;
            CursorCursorCursorCursorProd tmp_struct_98 =
                                          int1(end_r_2460, end_r_2461, loc_2459, tmpcur_6709, n_274_875_1253);
            CursorTy pvrtmp_6711 = tmp_struct_98.field0;
            CursorTy pvrtmp_6712 = tmp_struct_98.field1;
            CursorTy pvrtmp_6713 = tmp_struct_98.field2;
            CursorTy pvrtmp_6714 = tmp_struct_98.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6711, jump_3693,
                                                   pvrtmp_6713, pvrtmp_6714};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6721 = *(CursorTy *) tmpcur_6686;
            CursorTy tmpaftercur_6722 = tmpcur_6686 + 8;
            CursorCursorCursorCursorProd tmp_struct_99 =
                                          int1(end_r_2460, end_r_2461, loc_2459, tmpcur_6721, n_274_875_1253);
            CursorTy pvrtmp_6723 = tmp_struct_99.field0;
            CursorTy pvrtmp_6724 = tmp_struct_99.field1;
            CursorTy pvrtmp_6725 = tmp_struct_99.field2;
            CursorTy pvrtmp_6726 = tmp_struct_99.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6723, pvrtmp_6724,
                                                   pvrtmp_6725, pvrtmp_6726};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6685");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd deriv(CursorTy end_r_2464, CursorTy end_r_2465,
                                   CursorTy loc_2463, CursorTy a_277_878_1260)
{
    if (loc_2463 + 32 > end_r_2465) {
        ChunkTy new_chunk_106 = alloc_chunk(end_r_2465);
        CursorTy chunk_start_107 = new_chunk_106.chunk_start;
        CursorTy chunk_end_108 = new_chunk_106.chunk_end;

        end_r_2465 = chunk_end_108;
        *(TagTyPacked *) loc_2463 = 255;

        CursorTy redir = loc_2463 + 1;

        *(CursorTy *) redir = chunk_start_107;
        loc_2463 = chunk_start_107;
    }

    TagTyPacked tmpval_6734 = *(TagTyPacked *) a_277_878_1260;
    CursorTy tmpcur_6735 = a_277_878_1260 + 1;


  switch_6780:
    ;
    switch (tmpval_6734) {

      case 0:
        {
            CursorTy jump_3474 = a_277_878_1260 + 1;

            *(TagTyPacked *) loc_2463 = 0;

            CursorTy writetag_4137 = loc_2463 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2465, jump_3474,
                                                   loc_2463, writetag_4137};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6740 = *(FloatTy *) tmpcur_6735;
            CursorTy tmpcur_6741 = tmpcur_6735 + sizeof(FloatTy);
            CursorTy jump_3476 = tmpcur_6735 + 4;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          deriv1(end_r_2464, end_r_2465, loc_2463, tmpcur_6741, 1);
            CursorTy pvrtmp_6742 = tmp_struct_103.field0;
            CursorTy pvrtmp_6743 = tmp_struct_103.field1;
            CursorTy pvrtmp_6744 = tmp_struct_103.field2;
            CursorTy pvrtmp_6745 = tmp_struct_103.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6742, pvrtmp_6743,
                                                   pvrtmp_6744, pvrtmp_6745};
            break;
        }

      case 2:
        {
            CursorTy jump_3479 = a_277_878_1260 + 1;

            *(TagTyPacked *) loc_2463 = 2;

            CursorTy writetag_4143 = loc_2463 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2465, jump_3479,
                                                   loc_2463, writetag_4143};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6756 = *(CursorTy *) tmpcur_6735;
            CursorTy tmpaftercur_6757 = tmpcur_6735 + 8;
            CursorTy jump_3699 = tmpcur_6735 + 8;
            CursorCursorCursorCursorProd tmp_struct_104 =
                                          deriv(end_r_2464, end_r_2465, loc_2463, tmpcur_6756);
            CursorTy pvrtmp_6758 = tmp_struct_104.field0;
            CursorTy pvrtmp_6759 = tmp_struct_104.field1;
            CursorTy pvrtmp_6760 = tmp_struct_104.field2;
            CursorTy pvrtmp_6761 = tmp_struct_104.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6758, jump_3699,
                                                   pvrtmp_6760, pvrtmp_6761};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6768 = *(CursorTy *) tmpcur_6735;
            CursorTy tmpaftercur_6769 = tmpcur_6735 + 8;
            CursorCursorCursorCursorProd tmp_struct_105 =
                                          deriv(end_r_2464, end_r_2465, loc_2463, tmpcur_6768);
            CursorTy pvrtmp_6770 = tmp_struct_105.field0;
            CursorTy pvrtmp_6771 = tmp_struct_105.field1;
            CursorTy pvrtmp_6772 = tmp_struct_105.field2;
            CursorTy pvrtmp_6773 = tmp_struct_105.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6770, pvrtmp_6771,
                                                   pvrtmp_6772, pvrtmp_6773};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6734");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd deriv1(CursorTy end_r_2468, CursorTy end_r_2469,
                                    CursorTy loc_2467, CursorTy a_280_881_1263,
                                    IntTy n_281_882_1264)
{
    if (loc_2467 + 32 > end_r_2469) {
        ChunkTy new_chunk_112 = alloc_chunk(end_r_2469);
        CursorTy chunk_start_113 = new_chunk_112.chunk_start;
        CursorTy chunk_end_114 = new_chunk_112.chunk_end;

        end_r_2469 = chunk_end_114;
        *(TagTyPacked *) loc_2467 = 255;

        CursorTy redir = loc_2467 + 1;

        *(CursorTy *) redir = chunk_start_113;
        loc_2467 = chunk_start_113;
    }

    TagTyPacked tmpval_6781 = *(TagTyPacked *) a_280_881_1263;
    CursorTy tmpcur_6782 = a_280_881_1263 + 1;


  switch_6829:
    ;
    switch (tmpval_6781) {

      case 0:
        {
            CursorTy jump_3481 = a_280_881_1263 + 1;

            *(TagTyPacked *) loc_2467 = 0;

            CursorTy writetag_4152 = loc_2467 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2469, jump_3481,
                                                   loc_2467, writetag_4152};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6787 = *(FloatTy *) tmpcur_6782;
            CursorTy tmpcur_6788 = tmpcur_6782 + sizeof(FloatTy);
            CursorTy jump_3483 = tmpcur_6782 + 4;
            FloatTy fltPrm_1107_1267 = (FloatTy) n_281_882_1264;
            FloatTy fltPkd_1106_1268 = fltPrm_1107_1267 * tmpval_6787;
            IntTy fltAppE_1109_1269 = n_281_882_1264 + 1;
            CursorTy loc_2899 = loc_2467 + 1;
            CursorTy loc_2900 = loc_2899 + 4;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          deriv1(end_r_2468, end_r_2469, loc_2900, tmpcur_6788, fltAppE_1109_1269);
            CursorTy pvrtmp_6789 = tmp_struct_109.field0;
            CursorTy pvrtmp_6790 = tmp_struct_109.field1;
            CursorTy pvrtmp_6791 = tmp_struct_109.field2;
            CursorTy pvrtmp_6792 = tmp_struct_109.field3;

            *(TagTyPacked *) loc_2467 = 1;

            CursorTy writetag_4157 = loc_2467 + 1;

            *(FloatTy *) writetag_4157 = fltPkd_1106_1268;

            CursorTy writecur_4158 = writetag_4157 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_6789, pvrtmp_6790,
                                                   loc_2467, pvrtmp_6792};
            break;
        }

      case 2:
        {
            CursorTy jump_3486 = a_280_881_1263 + 1;

            *(TagTyPacked *) loc_2467 = 2;

            CursorTy writetag_4162 = loc_2467 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2469, jump_3486,
                                                   loc_2467, writetag_4162};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6805 = *(CursorTy *) tmpcur_6782;
            CursorTy tmpaftercur_6806 = tmpcur_6782 + 8;
            CursorTy jump_3705 = tmpcur_6782 + 8;
            CursorCursorCursorCursorProd tmp_struct_110 =
                                          deriv1(end_r_2468, end_r_2469, loc_2467, tmpcur_6805, n_281_882_1264);
            CursorTy pvrtmp_6807 = tmp_struct_110.field0;
            CursorTy pvrtmp_6808 = tmp_struct_110.field1;
            CursorTy pvrtmp_6809 = tmp_struct_110.field2;
            CursorTy pvrtmp_6810 = tmp_struct_110.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6807, jump_3705,
                                                   pvrtmp_6809, pvrtmp_6810};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6817 = *(CursorTy *) tmpcur_6782;
            CursorTy tmpaftercur_6818 = tmpcur_6782 + 8;
            CursorCursorCursorCursorProd tmp_struct_111 =
                                          deriv1(end_r_2468, end_r_2469, loc_2467, tmpcur_6817, n_281_882_1264);
            CursorTy pvrtmp_6819 = tmp_struct_111.field0;
            CursorTy pvrtmp_6820 = tmp_struct_111.field1;
            CursorTy pvrtmp_6821 = tmp_struct_111.field2;
            CursorTy pvrtmp_6822 = tmp_struct_111.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6819, pvrtmp_6820,
                                                   pvrtmp_6821, pvrtmp_6822};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6781");
            exit(1);
        }
    }
}
CursorCursorCursorProd revert(CursorTy end_r_2472, CursorTy end_r_2473,
                              CursorTy loc_2471, IntTy n_284_885_1271,
                              CursorTy a_285_886_1272)
{
    if (loc_2471 + 32 > end_r_2473) {
        ChunkTy new_chunk_119 = alloc_chunk(end_r_2473);
        CursorTy chunk_start_120 = new_chunk_119.chunk_start;
        CursorTy chunk_end_121 = new_chunk_119.chunk_end;

        end_r_2473 = chunk_end_121;
        *(TagTyPacked *) loc_2471 = 255;

        CursorTy redir = loc_2471 + 1;

        *(CursorTy *) redir = chunk_start_120;
        loc_2471 = chunk_start_120;
    }

    TagTyPacked tmpval_6830 = *(TagTyPacked *) a_285_886_1272;
    CursorTy tmpcur_6831 = a_285_886_1272 + 1;


  switch_6879:
    ;
    switch (tmpval_6830) {

      case 0:
        {
            CursorTy jump_3488 = a_285_886_1272 + 1;

            *(TagTyPacked *) loc_2471 = 2;

            CursorTy writetag_4171 = loc_2471 + 1;

            return (CursorCursorCursorProd) {end_r_2473, loc_2471,
                                             writetag_4171};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6836 = *(FloatTy *) tmpcur_6831;
            CursorTy tmpcur_6837 = tmpcur_6831 + sizeof(FloatTy);
            CursorTy jump_3490 = tmpcur_6831 + 4;
            BoolTy fltIf_1110_1275 = tmpval_6836 == 0.0;

            if (fltIf_1110_1275) {
                CursorCursorCursorProd tmp_struct_115 =
                                        getRs(end_r_2472, end_r_2473, loc_2471, n_284_885_1271, tmpcur_6837);
                CursorTy pvrtmp_6838 = tmp_struct_115.field0;
                CursorTy pvrtmp_6839 = tmp_struct_115.field1;
                CursorTy pvrtmp_6840 = tmp_struct_115.field2;

                return (CursorCursorCursorProd) {pvrtmp_6838, pvrtmp_6839,
                                                 pvrtmp_6840};
            } else {
                CursorCursorCursorCursorProd tmp_struct_116 =
                                              caseFn_814(end_r_2472, end_r_2473, loc_2471, tmpval_6836, tmpcur_6837);
                CursorTy pvrtmp_6847 = tmp_struct_116.field0;
                CursorTy pvrtmp_6848 = tmp_struct_116.field1;
                CursorTy pvrtmp_6849 = tmp_struct_116.field2;
                CursorTy pvrtmp_6850 = tmp_struct_116.field3;

                return (CursorCursorCursorProd) {pvrtmp_6847, pvrtmp_6849,
                                                 pvrtmp_6850};
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6857 = *(CursorTy *) tmpcur_6831;
            CursorTy tmpaftercur_6858 = tmpcur_6831 + 8;
            CursorTy jump_3711 = tmpcur_6831 + 8;
            CursorCursorCursorProd tmp_struct_117 =
                                    revert(end_r_2472, end_r_2473, loc_2471, n_284_885_1271, tmpcur_6857);
            CursorTy pvrtmp_6859 = tmp_struct_117.field0;
            CursorTy pvrtmp_6860 = tmp_struct_117.field1;
            CursorTy pvrtmp_6861 = tmp_struct_117.field2;

            return (CursorCursorCursorProd) {pvrtmp_6859, pvrtmp_6860,
                                             pvrtmp_6861};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6868 = *(CursorTy *) tmpcur_6831;
            CursorTy tmpaftercur_6869 = tmpcur_6831 + 8;
            CursorCursorCursorProd tmp_struct_118 =
                                    revert(end_r_2472, end_r_2473, loc_2471, n_284_885_1271, tmpcur_6868);
            CursorTy pvrtmp_6870 = tmp_struct_118.field0;
            CursorTy pvrtmp_6871 = tmp_struct_118.field1;
            CursorTy pvrtmp_6872 = tmp_struct_118.field2;

            return (CursorCursorCursorProd) {pvrtmp_6870, pvrtmp_6871,
                                             pvrtmp_6872};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6830");
            exit(1);
        }
    }
}
CursorCursorCursorProd getRs(CursorTy end_r_2476, CursorTy end_r_2477,
                             CursorTy loc_2475, IntTy n_290_889_1276,
                             CursorTy fs_291_890_1277)
{
    if (loc_2475 + 32 > end_r_2477) {
        ChunkTy new_chunk_126 = alloc_chunk(end_r_2477);
        CursorTy chunk_start_127 = new_chunk_126.chunk_start;
        CursorTy chunk_end_128 = new_chunk_126.chunk_end;

        end_r_2477 = chunk_end_128;
        *(TagTyPacked *) loc_2475 = 255;

        CursorTy redir = loc_2475 + 1;

        *(CursorTy *) redir = chunk_start_127;
        loc_2475 = chunk_start_127;
    }

    BoolTy fltIf_1111_1278 = n_290_889_1276 == 0;

    if (fltIf_1111_1278) {
        *(TagTyPacked *) loc_2475 = 0;

        CursorTy writetag_4183 = loc_2475 + 1;

        return (CursorCursorCursorProd) {end_r_2477, loc_2475, writetag_4183};
    } else {
        RegionTy *region_6884 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2941 = region_6884->reg_heap;
        IntTy sizeof_end_r_2941_6885 = global_init_inf_buf_size;
        CursorTy end_r_2941 = r_2941 + sizeof_end_r_2941_6885;
        RegionTy *region_6886 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2940 = region_6886->reg_heap;
        IntTy sizeof_end_r_2940_6887 = global_init_inf_buf_size;
        CursorTy end_r_2940 = r_2940 + sizeof_end_r_2940_6887;
        RegionTy *region_6888 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2939 = region_6888->reg_heap;
        IntTy sizeof_end_r_2939_6889 = global_init_inf_buf_size;
        CursorTy end_r_2939 = r_2939 + sizeof_end_r_2939_6889;
        IntTy fltAppE_1113_1279 = n_290_889_1276 - 1;
        CursorCursorCursorProd tmp_struct_122 =  pone(end_r_2941, r_2941);
        CursorTy pvrtmp_6890 = tmp_struct_122.field0;
        CursorTy pvrtmp_6891 = tmp_struct_122.field1;
        CursorTy pvrtmp_6892 = tmp_struct_122.field2;
        IntTy fltAppE_1117_1281 = n_290_889_1276 - 1;
        CursorCursorCursorProd tmp_struct_123 =
                                getRs(end_r_2476, end_r_2940, r_2940, fltAppE_1117_1281, fs_291_890_1277);
        CursorTy pvrtmp_6897 = tmp_struct_123.field0;
        CursorTy pvrtmp_6898 = tmp_struct_123.field1;
        CursorTy pvrtmp_6899 = tmp_struct_123.field2;
        CursorCursorCursorProd tmp_struct_124 =
                                compose(end_r_2476, pvrtmp_6897, end_r_2939, r_2939, fs_291_890_1277, pvrtmp_6898);
        CursorTy pvrtmp_6904 = tmp_struct_124.field0;
        CursorTy pvrtmp_6905 = tmp_struct_124.field1;
        CursorTy pvrtmp_6906 = tmp_struct_124.field2;
        CursorTy loc_2936 = loc_2475 + 1;
        CursorTy loc_2937 = loc_2936 + 4;
        CursorCursorCursorProd tmp_struct_125 =
                                psDiv(pvrtmp_6890, pvrtmp_6904, end_r_2477, loc_2937, fltAppE_1113_1279, pvrtmp_6891, pvrtmp_6905);
        CursorTy pvrtmp_6911 = tmp_struct_125.field0;
        CursorTy pvrtmp_6912 = tmp_struct_125.field1;
        CursorTy pvrtmp_6913 = tmp_struct_125.field2;

        *(TagTyPacked *) loc_2475 = 1;

        CursorTy writetag_4189 = loc_2475 + 1;

        *(FloatTy *) writetag_4189 = 0.0;

        CursorTy writecur_4190 = writetag_4189 + sizeof(FloatTy);

        free_region(end_r_2939);
        free_region(end_r_2940);
        free_region(end_r_2941);
        return (CursorCursorCursorProd) {pvrtmp_6911, loc_2475, pvrtmp_6913};
    }
}
CursorCursorCursorProd compose(CursorTy end_r_2481, CursorTy end_r_2482,
                               CursorTy end_r_2483, CursorTy loc_2480,
                               CursorTy a_292_891_1285, CursorTy b_293_892_1286)
{
    if (loc_2480 + 32 > end_r_2483) {
        ChunkTy new_chunk_132 = alloc_chunk(end_r_2483);
        CursorTy chunk_start_133 = new_chunk_132.chunk_start;
        CursorTy chunk_end_134 = new_chunk_132.chunk_end;

        end_r_2483 = chunk_end_134;
        *(TagTyPacked *) loc_2480 = 255;

        CursorTy redir = loc_2480 + 1;

        *(CursorTy *) redir = chunk_start_133;
        loc_2480 = chunk_start_133;
    }

    TagTyPacked tmpval_6922 = *(TagTyPacked *) a_292_891_1285;
    CursorTy tmpcur_6923 = a_292_891_1285 + 1;


  switch_6965:
    ;
    switch (tmpval_6922) {

      case 0:
        {
            CursorTy jump_3496 = a_292_891_1285 + 1;

            *(TagTyPacked *) loc_2480 = 0;

            CursorTy writetag_4194 = loc_2480 + 1;

            return (CursorCursorCursorProd) {end_r_2483, loc_2480,
                                             writetag_4194};
            break;
        }

      case 1:
        {
            FloatTy tmpval_6928 = *(FloatTy *) tmpcur_6923;
            CursorTy tmpcur_6929 = tmpcur_6923 + sizeof(FloatTy);
            CursorTy jump_3498 = tmpcur_6923 + 4;
            CursorCursorCursorProd tmp_struct_129 =
                                    caseFn_817(end_r_2482, end_r_2481, end_r_2483, loc_2480, b_293_892_1286, tmpval_6928, tmpcur_6929);
            CursorTy pvrtmp_6930 = tmp_struct_129.field0;
            CursorTy pvrtmp_6931 = tmp_struct_129.field1;
            CursorTy pvrtmp_6932 = tmp_struct_129.field2;

            return (CursorCursorCursorProd) {pvrtmp_6930, pvrtmp_6931,
                                             pvrtmp_6932};
            break;
        }

      case 2:
        {
            CursorTy jump_3500 = a_292_891_1285 + 1;

            *(TagTyPacked *) loc_2480 = 2;

            CursorTy writetag_4200 = loc_2480 + 1;

            return (CursorCursorCursorProd) {end_r_2483, loc_2480,
                                             writetag_4200};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6943 = *(CursorTy *) tmpcur_6923;
            CursorTy tmpaftercur_6944 = tmpcur_6923 + 8;
            CursorTy jump_3716 = tmpcur_6923 + 8;
            CursorCursorCursorProd tmp_struct_130 =
                                    compose(end_r_2481, end_r_2482, end_r_2483, loc_2480, tmpcur_6943, b_293_892_1286);
            CursorTy pvrtmp_6945 = tmp_struct_130.field0;
            CursorTy pvrtmp_6946 = tmp_struct_130.field1;
            CursorTy pvrtmp_6947 = tmp_struct_130.field2;

            return (CursorCursorCursorProd) {pvrtmp_6945, pvrtmp_6946,
                                             pvrtmp_6947};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6954 = *(CursorTy *) tmpcur_6923;
            CursorTy tmpaftercur_6955 = tmpcur_6923 + 8;
            CursorCursorCursorProd tmp_struct_131 =
                                    compose(end_r_2481, end_r_2482, end_r_2483, loc_2480, tmpcur_6954, b_293_892_1286);
            CursorTy pvrtmp_6956 = tmp_struct_131.field0;
            CursorTy pvrtmp_6957 = tmp_struct_131.field1;
            CursorTy pvrtmp_6958 = tmp_struct_131.field2;

            return (CursorCursorCursorProd) {pvrtmp_6956, pvrtmp_6957,
                                             pvrtmp_6958};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6922");
            exit(1);
        }
    }
}
CursorCursorCursorProd ts(CursorTy end_r_2485, CursorTy loc_2484,
                          IntTy n_299_896_1289)
{
    if (loc_2484 + 32 > end_r_2485) {
        ChunkTy new_chunk_139 = alloc_chunk(end_r_2485);
        CursorTy chunk_start_140 = new_chunk_139.chunk_start;
        CursorTy chunk_end_141 = new_chunk_139.chunk_end;

        end_r_2485 = chunk_end_141;
        *(TagTyPacked *) loc_2484 = 255;

        CursorTy redir = loc_2484 + 1;

        *(CursorTy *) redir = chunk_start_140;
        loc_2484 = chunk_start_140;
    }

    BoolTy fltIf_1118_1290 = n_299_896_1289 == 0;

    if (fltIf_1118_1290) {
        *(TagTyPacked *) loc_2484 = 0;

        CursorTy writetag_4208 = loc_2484 + 1;

        return (CursorCursorCursorProd) {end_r_2485, loc_2484, writetag_4208};
    } else {
        RegionTy *region_6970 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2973 = region_6970->reg_heap;
        IntTy sizeof_end_r_2973_6971 = global_init_inf_buf_size;
        CursorTy end_r_2973 = r_2973 + sizeof_end_r_2973_6971;
        RegionTy *region_6972 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2972 = region_6972->reg_heap;
        IntTy sizeof_end_r_2972_6973 = global_init_inf_buf_size;
        CursorTy end_r_2972 = r_2972 + sizeof_end_r_2972_6973;
        RegionTy *region_6974 = alloc_region(global_init_inf_buf_size);
        CursorTy r_2971 = region_6974->reg_heap;
        IntTy sizeof_end_r_2971_6975 = global_init_inf_buf_size;
        CursorTy end_r_2971 = r_2971 + sizeof_end_r_2971_6975;
        IntTy fltAppE_1120_1291 = n_299_896_1289 - 1;
        IntTy fltAppE_1123_1292 = n_299_896_1289 - 1;
        CursorCursorCursorProd tmp_struct_135 =
                                ts(end_r_2973, r_2973, fltAppE_1123_1292);
        CursorTy pvrtmp_6976 = tmp_struct_135.field0;
        CursorTy pvrtmp_6977 = tmp_struct_135.field1;
        CursorTy pvrtmp_6978 = tmp_struct_135.field2;
        IntTy fltAppE_1125_1294 = n_299_896_1289 - 1;
        CursorCursorCursorProd tmp_struct_136 =
                                ts(end_r_2972, r_2972, fltAppE_1125_1294);
        CursorTy pvrtmp_6983 = tmp_struct_136.field0;
        CursorTy pvrtmp_6984 = tmp_struct_136.field1;
        CursorTy pvrtmp_6985 = tmp_struct_136.field2;
        CursorCursorCursorProd tmp_struct_137 =
                                psMult(pvrtmp_6976, pvrtmp_6983, end_r_2971, r_2971, pvrtmp_6977, pvrtmp_6984);
        CursorTy pvrtmp_6990 = tmp_struct_137.field0;
        CursorTy pvrtmp_6991 = tmp_struct_137.field1;
        CursorTy pvrtmp_6992 = tmp_struct_137.field2;
        CursorTy loc_2968 = loc_2484 + 1;
        CursorTy loc_2969 = loc_2968 + 4;
        CursorCursorCursorProd tmp_struct_138 =
                                takePs(pvrtmp_6990, end_r_2485, loc_2969, fltAppE_1120_1291, pvrtmp_6991);
        CursorTy pvrtmp_6997 = tmp_struct_138.field0;
        CursorTy pvrtmp_6998 = tmp_struct_138.field1;
        CursorTy pvrtmp_6999 = tmp_struct_138.field2;

        *(TagTyPacked *) loc_2484 = 1;

        CursorTy writetag_4214 = loc_2484 + 1;

        *(FloatTy *) writetag_4214 = 1.0;

        CursorTy writecur_4215 = writetag_4214 + sizeof(FloatTy);

        free_region(end_r_2971);
        free_region(end_r_2972);
        free_region(end_r_2973);
        return (CursorCursorCursorProd) {pvrtmp_6997, loc_2484, pvrtmp_6999};
    }
}
CursorCursorCursorProd takePs(CursorTy end_r_2488, CursorTy end_r_2489,
                              CursorTy loc_2487, IntTy n_300_897_1298,
                              CursorTy fs_301_898_1299)
{
    if (loc_2487 + 32 > end_r_2489) {
        ChunkTy new_chunk_143 = alloc_chunk(end_r_2489);
        CursorTy chunk_start_144 = new_chunk_143.chunk_start;
        CursorTy chunk_end_145 = new_chunk_143.chunk_end;

        end_r_2489 = chunk_end_145;
        *(TagTyPacked *) loc_2487 = 255;

        CursorTy redir = loc_2487 + 1;

        *(CursorTy *) redir = chunk_start_144;
        loc_2487 = chunk_start_144;
    }

    BoolTy fltIf_1126_1300 = n_300_897_1298 == 0;

    if (fltIf_1126_1300) {
        *(TagTyPacked *) loc_2487 = 0;

        CursorTy writetag_4218 = loc_2487 + 1;

        return (CursorCursorCursorProd) {end_r_2489, loc_2487, writetag_4218};
    } else {
        CursorCursorCursorProd tmp_struct_142 =
                                caseFn_821(end_r_2488, end_r_2489, loc_2487, n_300_897_1298, fs_301_898_1299);
        CursorTy pvrtmp_7012 = tmp_struct_142.field0;
        CursorTy pvrtmp_7013 = tmp_struct_142.field1;
        CursorTy pvrtmp_7014 = tmp_struct_142.field2;

        return (CursorCursorCursorProd) {pvrtmp_7012, pvrtmp_7013, pvrtmp_7014};
    }
}
CursorCursorCursorProd psDiv(CursorTy end_r_2493, CursorTy end_r_2494,
                             CursorTy end_r_2495, CursorTy loc_2492,
                             IntTy n_304_899_1301, CursorTy a_305_900_1302,
                             CursorTy b_306_901_1303)
{
    if (loc_2492 + 32 > end_r_2495) {
        ChunkTy new_chunk_147 = alloc_chunk(end_r_2495);
        CursorTy chunk_start_148 = new_chunk_147.chunk_start;
        CursorTy chunk_end_149 = new_chunk_147.chunk_end;

        end_r_2495 = chunk_end_149;
        *(TagTyPacked *) loc_2492 = 255;

        CursorTy redir = loc_2492 + 1;

        *(CursorTy *) redir = chunk_start_148;
        loc_2492 = chunk_start_148;
    }

    BoolTy fltIf_1127_1304 = n_304_899_1301 == 0;

    if (fltIf_1127_1304) {
        *(TagTyPacked *) loc_2492 = 0;

        CursorTy writetag_4221 = loc_2492 + 1;

        return (CursorCursorCursorProd) {end_r_2495, loc_2492, writetag_4221};
    } else {
        CursorCursorCursorProd tmp_struct_146 =
                                caseFn_832(end_r_2493, end_r_2494, end_r_2495, loc_2492, n_304_899_1301, a_305_900_1302, b_306_901_1303);
        CursorTy pvrtmp_7025 = tmp_struct_146.field0;
        CursorTy pvrtmp_7026 = tmp_struct_146.field1;
        CursorTy pvrtmp_7027 = tmp_struct_146.field2;

        return (CursorCursorCursorProd) {pvrtmp_7025, pvrtmp_7026, pvrtmp_7027};
    }
}
CursorCursorCursorProd psMult(CursorTy end_r_2499, CursorTy end_r_2500,
                              CursorTy end_r_2501, CursorTy loc_2498,
                              CursorTy a_314_902_1305, CursorTy b_315_903_1306)
{
    if (loc_2498 + 32 > end_r_2501) {
        ChunkTy new_chunk_153 = alloc_chunk(end_r_2501);
        CursorTy chunk_start_154 = new_chunk_153.chunk_start;
        CursorTy chunk_end_155 = new_chunk_153.chunk_end;

        end_r_2501 = chunk_end_155;
        *(TagTyPacked *) loc_2498 = 255;

        CursorTy redir = loc_2498 + 1;

        *(CursorTy *) redir = chunk_start_154;
        loc_2498 = chunk_start_154;
    }

    TagTyPacked tmpval_7034 = *(TagTyPacked *) a_314_902_1305;
    CursorTy tmpcur_7035 = a_314_902_1305 + 1;


  switch_7078:
    ;
    switch (tmpval_7034) {

      case 0:
        {
            CursorTy jump_3508 = a_314_902_1305 + 1;

            *(TagTyPacked *) loc_2498 = 0;

            CursorTy writetag_4225 = loc_2498 + 1;

            return (CursorCursorCursorProd) {end_r_2501, loc_2498,
                                             writetag_4225};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7040 = *(FloatTy *) tmpcur_7035;
            CursorTy tmpcur_7041 = tmpcur_7035 + sizeof(FloatTy);
            CursorTy jump_3510 = tmpcur_7035 + 4;
            CursorCursorCursorCursorProd tmp_struct_150 =
                                          caseFn_836(end_r_2500, end_r_2499, end_r_2501, loc_2498, b_315_903_1306, tmpval_7040, tmpcur_7041);
            CursorTy pvrtmp_7042 = tmp_struct_150.field0;
            CursorTy pvrtmp_7043 = tmp_struct_150.field1;
            CursorTy pvrtmp_7044 = tmp_struct_150.field2;
            CursorTy pvrtmp_7045 = tmp_struct_150.field3;

            return (CursorCursorCursorProd) {pvrtmp_7042, pvrtmp_7044,
                                             pvrtmp_7045};
            break;
        }

      case 2:
        {
            CursorTy jump_3513 = a_314_902_1305 + 1;

            *(TagTyPacked *) loc_2498 = 2;

            CursorTy writetag_4231 = loc_2498 + 1;

            return (CursorCursorCursorProd) {end_r_2501, loc_2498,
                                             writetag_4231};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7056 = *(CursorTy *) tmpcur_7035;
            CursorTy tmpaftercur_7057 = tmpcur_7035 + 8;
            CursorTy jump_3721 = tmpcur_7035 + 8;
            CursorCursorCursorProd tmp_struct_151 =
                                    psMult(end_r_2499, end_r_2500, end_r_2501, loc_2498, tmpcur_7056, b_315_903_1306);
            CursorTy pvrtmp_7058 = tmp_struct_151.field0;
            CursorTy pvrtmp_7059 = tmp_struct_151.field1;
            CursorTy pvrtmp_7060 = tmp_struct_151.field2;

            return (CursorCursorCursorProd) {pvrtmp_7058, pvrtmp_7059,
                                             pvrtmp_7060};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7067 = *(CursorTy *) tmpcur_7035;
            CursorTy tmpaftercur_7068 = tmpcur_7035 + 8;
            CursorCursorCursorProd tmp_struct_152 =
                                    psMult(end_r_2499, end_r_2500, end_r_2501, loc_2498, tmpcur_7067, b_315_903_1306);
            CursorTy pvrtmp_7069 = tmp_struct_152.field0;
            CursorTy pvrtmp_7070 = tmp_struct_152.field1;
            CursorTy pvrtmp_7071 = tmp_struct_152.field2;

            return (CursorCursorCursorProd) {pvrtmp_7069, pvrtmp_7070,
                                             pvrtmp_7071};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7034");
            exit(1);
        }
    }
}
CursorCursorCursorProd psAdd(CursorTy end_r_2505, CursorTy end_r_2506,
                             CursorTy end_r_2507, CursorTy loc_2504,
                             CursorTy a_320_906_1309, CursorTy b_321_907_1310)
{
    if (loc_2504 + 32 > end_r_2507) {
        ChunkTy new_chunk_159 = alloc_chunk(end_r_2507);
        CursorTy chunk_start_160 = new_chunk_159.chunk_start;
        CursorTy chunk_end_161 = new_chunk_159.chunk_end;

        end_r_2507 = chunk_end_161;
        *(TagTyPacked *) loc_2504 = 255;

        CursorTy redir = loc_2504 + 1;

        *(CursorTy *) redir = chunk_start_160;
        loc_2504 = chunk_start_160;
    }

    TagTyPacked tmpval_7079 = *(TagTyPacked *) a_320_906_1309;
    CursorTy tmpcur_7080 = a_320_906_1309 + 1;


  switch_7122:
    ;
    switch (tmpval_7079) {

      case 0:
        {
            CursorTy jump_3515 = a_320_906_1309 + 1;

            bump_ref_count(end_r_2507, end_r_2506);
            *(TagTyPacked *) loc_2504 = 254;

            CursorTy writetag_4240 = loc_2504 + 1;

            *(CursorTy *) writetag_4240 = b_321_907_1310;

            CursorTy writecur_4241 = writetag_4240 + 8;

            return (CursorCursorCursorProd) {end_r_2507, loc_2504,
                                             writecur_4241};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7085 = *(FloatTy *) tmpcur_7080;
            CursorTy tmpcur_7086 = tmpcur_7080 + sizeof(FloatTy);
            CursorTy jump_3516 = tmpcur_7080 + 4;
            CursorCursorCursorProd tmp_struct_156 =
                                    caseFn_840(end_r_2505, end_r_2506, end_r_2505, end_r_2507, loc_2504, a_320_906_1309, b_321_907_1310, tmpval_7085, tmpcur_7086);
            CursorTy pvrtmp_7087 = tmp_struct_156.field0;
            CursorTy pvrtmp_7088 = tmp_struct_156.field1;
            CursorTy pvrtmp_7089 = tmp_struct_156.field2;

            return (CursorCursorCursorProd) {pvrtmp_7087, pvrtmp_7088,
                                             pvrtmp_7089};
            break;
        }

      case 2:
        {
            CursorTy jump_3518 = a_320_906_1309 + 1;

            *(TagTyPacked *) loc_2504 = 2;

            CursorTy writetag_4247 = loc_2504 + 1;

            return (CursorCursorCursorProd) {end_r_2507, loc_2504,
                                             writetag_4247};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7100 = *(CursorTy *) tmpcur_7080;
            CursorTy tmpaftercur_7101 = tmpcur_7080 + 8;
            CursorTy jump_3726 = tmpcur_7080 + 8;
            CursorCursorCursorProd tmp_struct_157 =
                                    psAdd(end_r_2505, end_r_2506, end_r_2507, loc_2504, tmpcur_7100, b_321_907_1310);
            CursorTy pvrtmp_7102 = tmp_struct_157.field0;
            CursorTy pvrtmp_7103 = tmp_struct_157.field1;
            CursorTy pvrtmp_7104 = tmp_struct_157.field2;

            return (CursorCursorCursorProd) {pvrtmp_7102, pvrtmp_7103,
                                             pvrtmp_7104};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7111 = *(CursorTy *) tmpcur_7080;
            CursorTy tmpaftercur_7112 = tmpcur_7080 + 8;
            CursorCursorCursorProd tmp_struct_158 =
                                    psAdd(end_r_2505, end_r_2506, end_r_2507, loc_2504, tmpcur_7111, b_321_907_1310);
            CursorTy pvrtmp_7113 = tmp_struct_158.field0;
            CursorTy pvrtmp_7114 = tmp_struct_158.field1;
            CursorTy pvrtmp_7115 = tmp_struct_158.field2;

            return (CursorCursorCursorProd) {pvrtmp_7113, pvrtmp_7114,
                                             pvrtmp_7115};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7079");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd psNeg(CursorTy end_r_2510, CursorTy end_r_2511,
                                   CursorTy loc_2509, CursorTy a_326_910_1313)
{
    if (loc_2509 + 32 > end_r_2511) {
        ChunkTy new_chunk_165 = alloc_chunk(end_r_2511);
        CursorTy chunk_start_166 = new_chunk_165.chunk_start;
        CursorTy chunk_end_167 = new_chunk_165.chunk_end;

        end_r_2511 = chunk_end_167;
        *(TagTyPacked *) loc_2509 = 255;

        CursorTy redir = loc_2509 + 1;

        *(CursorTy *) redir = chunk_start_166;
        loc_2509 = chunk_start_166;
    }

    TagTyPacked tmpval_7123 = *(TagTyPacked *) a_326_910_1313;
    CursorTy tmpcur_7124 = a_326_910_1313 + 1;


  switch_7171:
    ;
    switch (tmpval_7123) {

      case 0:
        {
            CursorTy jump_3520 = a_326_910_1313 + 1;

            *(TagTyPacked *) loc_2509 = 0;

            CursorTy writetag_4256 = loc_2509 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2511, jump_3520,
                                                   loc_2509, writetag_4256};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7129 = *(FloatTy *) tmpcur_7124;
            CursorTy tmpcur_7130 = tmpcur_7124 + sizeof(FloatTy);
            CursorTy jump_3522 = tmpcur_7124 + 4;
            FloatTy fltPkd_1128_1316 = 0.0 - tmpval_7129;
            CursorTy loc_3019 = loc_2509 + 1;
            CursorTy loc_3020 = loc_3019 + 4;
            CursorCursorCursorCursorProd tmp_struct_162 =
                                          psNeg(end_r_2510, end_r_2511, loc_3020, tmpcur_7130);
            CursorTy pvrtmp_7131 = tmp_struct_162.field0;
            CursorTy pvrtmp_7132 = tmp_struct_162.field1;
            CursorTy pvrtmp_7133 = tmp_struct_162.field2;
            CursorTy pvrtmp_7134 = tmp_struct_162.field3;

            *(TagTyPacked *) loc_2509 = 1;

            CursorTy writetag_4261 = loc_2509 + 1;

            *(FloatTy *) writetag_4261 = fltPkd_1128_1316;

            CursorTy writecur_4262 = writetag_4261 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_7131, pvrtmp_7132,
                                                   loc_2509, pvrtmp_7134};
            break;
        }

      case 2:
        {
            CursorTy jump_3525 = a_326_910_1313 + 1;

            *(TagTyPacked *) loc_2509 = 2;

            CursorTy writetag_4266 = loc_2509 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2511, jump_3525,
                                                   loc_2509, writetag_4266};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7147 = *(CursorTy *) tmpcur_7124;
            CursorTy tmpaftercur_7148 = tmpcur_7124 + 8;
            CursorTy jump_3731 = tmpcur_7124 + 8;
            CursorCursorCursorCursorProd tmp_struct_163 =
                                          psNeg(end_r_2510, end_r_2511, loc_2509, tmpcur_7147);
            CursorTy pvrtmp_7149 = tmp_struct_163.field0;
            CursorTy pvrtmp_7150 = tmp_struct_163.field1;
            CursorTy pvrtmp_7151 = tmp_struct_163.field2;
            CursorTy pvrtmp_7152 = tmp_struct_163.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7149, jump_3731,
                                                   pvrtmp_7151, pvrtmp_7152};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7159 = *(CursorTy *) tmpcur_7124;
            CursorTy tmpaftercur_7160 = tmpcur_7124 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          psNeg(end_r_2510, end_r_2511, loc_2509, tmpcur_7159);
            CursorTy pvrtmp_7161 = tmp_struct_164.field0;
            CursorTy pvrtmp_7162 = tmp_struct_164.field1;
            CursorTy pvrtmp_7163 = tmp_struct_164.field2;
            CursorTy pvrtmp_7164 = tmp_struct_164.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7161, pvrtmp_7162,
                                                   pvrtmp_7163, pvrtmp_7164};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7123");
            exit(1);
        }
    }
}
CursorCursorCursorProd psX(CursorTy end_r_2513, CursorTy loc_2512)
{
    if (loc_2512 + 32 > end_r_2513) {
        ChunkTy new_chunk_168 = alloc_chunk(end_r_2513);
        CursorTy chunk_start_169 = new_chunk_168.chunk_start;
        CursorTy chunk_end_170 = new_chunk_168.chunk_end;

        end_r_2513 = chunk_end_170;
        *(TagTyPacked *) loc_2512 = 255;

        CursorTy redir = loc_2512 + 1;

        *(CursorTy *) redir = chunk_start_169;
        loc_2512 = chunk_start_169;
    }

    CursorTy loc_3031 = loc_2512 + 1;
    CursorTy loc_3032 = loc_3031 + 4;
    CursorTy loc_3028 = loc_3032 + 1;
    CursorTy loc_3029 = loc_3028 + 4;

    *(TagTyPacked *) loc_3029 = 0;

    CursorTy writetag_4274 = loc_3029 + 1;

    *(TagTyPacked *) loc_3032 = 1;

    CursorTy writetag_4276 = loc_3032 + 1;

    *(FloatTy *) writetag_4276 = 1.0;

    CursorTy writecur_4277 = writetag_4276 + sizeof(FloatTy);

    *(TagTyPacked *) loc_2512 = 1;

    CursorTy writetag_4280 = loc_2512 + 1;

    *(FloatTy *) writetag_4280 = 0.0;

    CursorTy writecur_4281 = writetag_4280 + sizeof(FloatTy);

    return (CursorCursorCursorProd) {end_r_2513, loc_2512, writetag_4274};
}
CursorCursorCursorCursorProd dot(CursorTy end_r_2516, CursorTy end_r_2517,
                                 CursorTy loc_2515, FloatTy c_329_913_1320,
                                 CursorTy b_330_914_1321)
{
    if (loc_2515 + 32 > end_r_2517) {
        ChunkTy new_chunk_174 = alloc_chunk(end_r_2517);
        CursorTy chunk_start_175 = new_chunk_174.chunk_start;
        CursorTy chunk_end_176 = new_chunk_174.chunk_end;

        end_r_2517 = chunk_end_176;
        *(TagTyPacked *) loc_2515 = 255;

        CursorTy redir = loc_2515 + 1;

        *(CursorTy *) redir = chunk_start_175;
        loc_2515 = chunk_start_175;
    }

    TagTyPacked tmpval_7180 = *(TagTyPacked *) b_330_914_1321;
    CursorTy tmpcur_7181 = b_330_914_1321 + 1;


  switch_7228:
    ;
    switch (tmpval_7180) {

      case 0:
        {
            CursorTy jump_3528 = b_330_914_1321 + 1;

            *(TagTyPacked *) loc_2515 = 0;

            CursorTy writetag_4285 = loc_2515 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2517, jump_3528,
                                                   loc_2515, writetag_4285};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7186 = *(FloatTy *) tmpcur_7181;
            CursorTy tmpcur_7187 = tmpcur_7181 + sizeof(FloatTy);
            CursorTy jump_3530 = tmpcur_7181 + 4;
            FloatTy fltPkd_1132_1324 = c_329_913_1320 * tmpval_7186;
            CursorTy loc_3042 = loc_2515 + 1;
            CursorTy loc_3043 = loc_3042 + 4;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          dot(end_r_2516, end_r_2517, loc_3043, c_329_913_1320, tmpcur_7187);
            CursorTy pvrtmp_7188 = tmp_struct_171.field0;
            CursorTy pvrtmp_7189 = tmp_struct_171.field1;
            CursorTy pvrtmp_7190 = tmp_struct_171.field2;
            CursorTy pvrtmp_7191 = tmp_struct_171.field3;

            *(TagTyPacked *) loc_2515 = 1;

            CursorTy writetag_4290 = loc_2515 + 1;

            *(FloatTy *) writetag_4290 = fltPkd_1132_1324;

            CursorTy writecur_4291 = writetag_4290 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_7188, pvrtmp_7189,
                                                   loc_2515, pvrtmp_7191};
            break;
        }

      case 2:
        {
            CursorTy jump_3533 = b_330_914_1321 + 1;

            *(TagTyPacked *) loc_2515 = 2;

            CursorTy writetag_4295 = loc_2515 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2517, jump_3533,
                                                   loc_2515, writetag_4295};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7204 = *(CursorTy *) tmpcur_7181;
            CursorTy tmpaftercur_7205 = tmpcur_7181 + 8;
            CursorTy jump_3737 = tmpcur_7181 + 8;
            CursorCursorCursorCursorProd tmp_struct_172 =
                                          dot(end_r_2516, end_r_2517, loc_2515, c_329_913_1320, tmpcur_7204);
            CursorTy pvrtmp_7206 = tmp_struct_172.field0;
            CursorTy pvrtmp_7207 = tmp_struct_172.field1;
            CursorTy pvrtmp_7208 = tmp_struct_172.field2;
            CursorTy pvrtmp_7209 = tmp_struct_172.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7206, jump_3737,
                                                   pvrtmp_7208, pvrtmp_7209};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7216 = *(CursorTy *) tmpcur_7181;
            CursorTy tmpaftercur_7217 = tmpcur_7181 + 8;
            CursorCursorCursorCursorProd tmp_struct_173 =
                                          dot(end_r_2516, end_r_2517, loc_2515, c_329_913_1320, tmpcur_7216);
            CursorTy pvrtmp_7218 = tmp_struct_173.field0;
            CursorTy pvrtmp_7219 = tmp_struct_173.field1;
            CursorTy pvrtmp_7220 = tmp_struct_173.field2;
            CursorTy pvrtmp_7221 = tmp_struct_173.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7218, pvrtmp_7219,
                                                   pvrtmp_7220, pvrtmp_7221};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7180");
            exit(1);
        }
    }
}
CursorCursorCursorProd pone(CursorTy end_r_2519, CursorTy loc_2518)
{
    if (loc_2518 + 32 > end_r_2519) {
        ChunkTy new_chunk_177 = alloc_chunk(end_r_2519);
        CursorTy chunk_start_178 = new_chunk_177.chunk_start;
        CursorTy chunk_end_179 = new_chunk_177.chunk_end;

        end_r_2519 = chunk_end_179;
        *(TagTyPacked *) loc_2518 = 255;

        CursorTy redir = loc_2518 + 1;

        *(CursorTy *) redir = chunk_start_178;
        loc_2518 = chunk_start_178;
    }

    CursorTy loc_3050 = loc_2518 + 1;
    CursorTy loc_3051 = loc_3050 + 4;

    *(TagTyPacked *) loc_3051 = 0;

    CursorTy writetag_4303 = loc_3051 + 1;

    *(TagTyPacked *) loc_2518 = 1;

    CursorTy writetag_4305 = loc_2518 + 1;

    *(FloatTy *) writetag_4305 = 1.0;

    CursorTy writecur_4306 = writetag_4305 + sizeof(FloatTy);

    return (CursorCursorCursorProd) {end_r_2519, loc_2518, writetag_4303};
}
unsigned char print_check(BoolTy b_333_917_1327)
{
    if (b_333_917_1327) {
        unsigned char wildcard__14_334_918_1328 = print_symbol(6079);

        return 0;
    } else {
        unsigned char wildcard__16_335_919_1329 = print_symbol(6080);

        return 0;
    }
}
CursorCursorCursorCursorProd _copy_Ps(CursorTy end_r_2522, CursorTy end_r_2523,
                                      CursorTy loc_2521,
                                      CursorTy arg_743_935_1330)
{
    if (loc_2521 + 32 > end_r_2523) {
        ChunkTy new_chunk_183 = alloc_chunk(end_r_2523);
        CursorTy chunk_start_184 = new_chunk_183.chunk_start;
        CursorTy chunk_end_185 = new_chunk_183.chunk_end;

        end_r_2523 = chunk_end_185;
        *(TagTyPacked *) loc_2521 = 255;

        CursorTy redir = loc_2521 + 1;

        *(CursorTy *) redir = chunk_start_184;
        loc_2521 = chunk_start_184;
    }

    TagTyPacked tmpval_7235 = *(TagTyPacked *) arg_743_935_1330;
    CursorTy tmpcur_7236 = arg_743_935_1330 + 1;


  switch_7283:
    ;
    switch (tmpval_7235) {

      case 0:
        {
            CursorTy jump_3538 = arg_743_935_1330 + 1;

            *(TagTyPacked *) loc_2521 = 0;

            CursorTy writetag_4310 = loc_2521 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2523, jump_3538,
                                                   loc_2521, writetag_4310};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7241 = *(FloatTy *) tmpcur_7236;
            CursorTy tmpcur_7242 = tmpcur_7236 + sizeof(FloatTy);
            CursorTy jump_3540 = tmpcur_7236 + 4;
            CursorTy loc_3061 = loc_2521 + 1;
            CursorTy loc_3062 = loc_3061 + 4;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _copy_Ps(end_r_2522, end_r_2523, loc_3062, tmpcur_7242);
            CursorTy pvrtmp_7243 = tmp_struct_180.field0;
            CursorTy pvrtmp_7244 = tmp_struct_180.field1;
            CursorTy pvrtmp_7245 = tmp_struct_180.field2;
            CursorTy pvrtmp_7246 = tmp_struct_180.field3;

            *(TagTyPacked *) loc_2521 = 1;

            CursorTy writetag_4315 = loc_2521 + 1;

            *(FloatTy *) writetag_4315 = tmpval_7241;

            CursorTy writecur_4316 = writetag_4315 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_7243, pvrtmp_7244,
                                                   loc_2521, pvrtmp_7246};
            break;
        }

      case 2:
        {
            CursorTy jump_3543 = arg_743_935_1330 + 1;

            *(TagTyPacked *) loc_2521 = 2;

            CursorTy writetag_4320 = loc_2521 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2523, jump_3543,
                                                   loc_2521, writetag_4320};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7259 = *(CursorTy *) tmpcur_7236;
            CursorTy tmpaftercur_7260 = tmpcur_7236 + 8;
            CursorTy jump_3743 = tmpcur_7236 + 8;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _copy_Ps(end_r_2522, end_r_2523, loc_2521, tmpcur_7259);
            CursorTy pvrtmp_7261 = tmp_struct_181.field0;
            CursorTy pvrtmp_7262 = tmp_struct_181.field1;
            CursorTy pvrtmp_7263 = tmp_struct_181.field2;
            CursorTy pvrtmp_7264 = tmp_struct_181.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7261, jump_3743,
                                                   pvrtmp_7263, pvrtmp_7264};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7271 = *(CursorTy *) tmpcur_7236;
            CursorTy tmpaftercur_7272 = tmpcur_7236 + 8;
            CursorCursorCursorCursorProd tmp_struct_182 =
                                          _copy_Ps(end_r_2522, end_r_2523, loc_2521, tmpcur_7271);
            CursorTy pvrtmp_7273 = tmp_struct_182.field0;
            CursorTy pvrtmp_7274 = tmp_struct_182.field1;
            CursorTy pvrtmp_7275 = tmp_struct_182.field2;
            CursorTy pvrtmp_7276 = tmp_struct_182.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7273, pvrtmp_7274,
                                                   pvrtmp_7275, pvrtmp_7276};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7235");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Ps(CursorTy end_r_2526,
                                                   CursorTy end_r_2527,
                                                   CursorTy loc_2525,
                                                   CursorTy arg_748_940_1335)
{
    TagTyPacked tmpval_7284 = *(TagTyPacked *) arg_748_940_1335;
    CursorTy tmpcur_7285 = arg_748_940_1335 + 1;


  switch_7332:
    ;
    switch (tmpval_7284) {

      case 0:
        {
            CursorTy jump_3545 = arg_748_940_1335 + 1;

            *(TagTyPacked *) loc_2525 = 0;

            CursorTy writetag_4329 = loc_2525 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2527, jump_3545,
                                                   loc_2525, writetag_4329};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7290 = *(FloatTy *) tmpcur_7285;
            CursorTy tmpcur_7291 = tmpcur_7285 + sizeof(FloatTy);
            CursorTy jump_3547 = tmpcur_7285 + 4;
            CursorTy loc_3075 = loc_2525 + 1;
            CursorTy loc_3076 = loc_3075 + 4;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _copy_without_ptrs_Ps(end_r_2526, end_r_2527, loc_3076, tmpcur_7291);
            CursorTy pvrtmp_7292 = tmp_struct_186.field0;
            CursorTy pvrtmp_7293 = tmp_struct_186.field1;
            CursorTy pvrtmp_7294 = tmp_struct_186.field2;
            CursorTy pvrtmp_7295 = tmp_struct_186.field3;

            *(TagTyPacked *) loc_2525 = 1;

            CursorTy writetag_4334 = loc_2525 + 1;

            *(FloatTy *) writetag_4334 = tmpval_7290;

            CursorTy writecur_4335 = writetag_4334 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_7292, pvrtmp_7293,
                                                   loc_2525, pvrtmp_7295};
            break;
        }

      case 2:
        {
            CursorTy jump_3550 = arg_748_940_1335 + 1;

            *(TagTyPacked *) loc_2525 = 2;

            CursorTy writetag_4339 = loc_2525 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2527, jump_3550,
                                                   loc_2525, writetag_4339};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7308 = *(CursorTy *) tmpcur_7285;
            CursorTy tmpaftercur_7309 = tmpcur_7285 + 8;
            CursorTy jump_3749 = tmpcur_7285 + 8;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _copy_without_ptrs_Ps(end_r_2526, end_r_2527, loc_2525, tmpcur_7308);
            CursorTy pvrtmp_7310 = tmp_struct_187.field0;
            CursorTy pvrtmp_7311 = tmp_struct_187.field1;
            CursorTy pvrtmp_7312 = tmp_struct_187.field2;
            CursorTy pvrtmp_7313 = tmp_struct_187.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7310, jump_3749,
                                                   pvrtmp_7312, pvrtmp_7313};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7320 = *(CursorTy *) tmpcur_7285;
            CursorTy tmpaftercur_7321 = tmpcur_7285 + 8;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _copy_without_ptrs_Ps(end_r_2526, end_r_2527, loc_2525, tmpcur_7320);
            CursorTy pvrtmp_7322 = tmp_struct_188.field0;
            CursorTy pvrtmp_7323 = tmp_struct_188.field1;
            CursorTy pvrtmp_7324 = tmp_struct_188.field2;
            CursorTy pvrtmp_7325 = tmp_struct_188.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7322, pvrtmp_7323,
                                                   pvrtmp_7324, pvrtmp_7325};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7284");
            exit(1);
        }
    }
}
CursorProd _traverse_Ps(CursorTy end_r_2529, CursorTy arg_753_945_1340)
{
    TagTyPacked tmpval_7333 = *(TagTyPacked *) arg_753_945_1340;
    CursorTy tmpcur_7334 = arg_753_945_1340 + 1;


  switch_7344:
    ;
    switch (tmpval_7333) {

      case 0:
        {
            CursorTy jump_3552 = arg_753_945_1340 + 1;

            return (CursorProd) {jump_3552};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7335 = *(FloatTy *) tmpcur_7334;
            CursorTy tmpcur_7336 = tmpcur_7334 + sizeof(FloatTy);
            CursorTy jump_3554 = tmpcur_7334 + 4;
            CursorProd tmp_struct_189 =  _traverse_Ps(end_r_2529, tmpcur_7336);
            CursorTy pvrtmp_7337 = tmp_struct_189.field0;

            return (CursorProd) {pvrtmp_7337};
            break;
        }

      case 2:
        {
            CursorTy jump_3557 = arg_753_945_1340 + 1;

            return (CursorProd) {jump_3557};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7338 = *(CursorTy *) tmpcur_7334;
            CursorTy tmpaftercur_7339 = tmpcur_7334 + 8;
            CursorTy jump_3755 = tmpcur_7334 + 8;
            CursorProd tmp_struct_190 =  _traverse_Ps(end_r_2529, tmpcur_7338);
            CursorTy pvrtmp_7340 = tmp_struct_190.field0;

            return (CursorProd) {jump_3755};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7341 = *(CursorTy *) tmpcur_7334;
            CursorTy tmpaftercur_7342 = tmpcur_7334 + 8;
            CursorProd tmp_struct_191 =  _traverse_Ps(end_r_2529, tmpcur_7341);
            CursorTy pvrtmp_7343 = tmp_struct_191.field0;

            return (CursorProd) {pvrtmp_7343};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7333");
            exit(1);
        }
    }
}
CursorProd _print_Ps(CursorTy end_r_2531, CursorTy arg_758_949_1344)
{
    TagTyPacked tmpval_7345 = *(TagTyPacked *) arg_758_949_1344;
    CursorTy tmpcur_7346 = arg_758_949_1344 + 1;


  switch_7356:
    ;
    switch (tmpval_7345) {

      case 0:
        {
            CursorTy jump_3559 = arg_758_949_1344 + 1;
            unsigned char wildcard_759_950_1345 = print_symbol(6082);
            unsigned char wildcard_760_951_1346 = print_symbol(6081);

            return (CursorProd) {jump_3559};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7347 = *(FloatTy *) tmpcur_7346;
            CursorTy tmpcur_7348 = tmpcur_7346 + sizeof(FloatTy);
            CursorTy jump_3561 = tmpcur_7346 + 4;
            unsigned char wildcard_765_954_1349 = print_symbol(6083);
            unsigned char wildcard_768_955_1350 = print_symbol(6090);
            unsigned char y_763_956_1351 = printf("%.2f", tmpval_7347);
            unsigned char wildcard_767_957_1352 = print_symbol(6090);
            CursorProd tmp_struct_192 =  _print_Ps(end_r_2531, tmpcur_7348);
            CursorTy pvrtmp_7349 = tmp_struct_192.field0;
            unsigned char wildcard_766_959_1354 = print_symbol(6081);

            return (CursorProd) {pvrtmp_7349};
            break;
        }

      case 2:
        {
            CursorTy jump_3564 = arg_758_949_1344 + 1;
            unsigned char wildcard_769_960_1355 = print_symbol(6086);
            unsigned char wildcard_770_961_1356 = print_symbol(6081);

            return (CursorProd) {jump_3564};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7350 = *(CursorTy *) tmpcur_7346;
            CursorTy tmpaftercur_7351 = tmpcur_7346 + 8;
            CursorTy jump_3761 = tmpcur_7346 + 8;
            unsigned char wildcard_3764 = print_symbol(6089);
            CursorProd tmp_struct_193 =  _print_Ps(end_r_2531, tmpcur_7350);
            CursorTy pvrtmp_7352 = tmp_struct_193.field0;

            return (CursorProd) {jump_3761};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7353 = *(CursorTy *) tmpcur_7346;
            CursorTy tmpaftercur_7354 = tmpcur_7346 + 8;
            unsigned char wildcard_3764 = print_symbol(6088);
            CursorProd tmp_struct_194 =  _print_Ps(end_r_2531, tmpcur_7353);
            CursorTy pvrtmp_7355 = tmp_struct_194.field0;

            return (CursorProd) {pvrtmp_7355};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7345");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_PList1(CursorTy end_r_2534,
                                          CursorTy end_r_2535,
                                          CursorTy loc_2533,
                                          CursorTy arg_771_962_1357)
{
    if (loc_2533 + 32 > end_r_2535) {
        ChunkTy new_chunk_198 = alloc_chunk(end_r_2535);
        CursorTy chunk_start_199 = new_chunk_198.chunk_start;
        CursorTy chunk_end_200 = new_chunk_198.chunk_end;

        end_r_2535 = chunk_end_200;
        *(TagTyPacked *) loc_2533 = 255;

        CursorTy redir = loc_2533 + 1;

        *(CursorTy *) redir = chunk_start_199;
        loc_2533 = chunk_start_199;
    }

    TagTyPacked tmpval_7357 = *(TagTyPacked *) arg_771_962_1357;
    CursorTy tmpcur_7358 = arg_771_962_1357 + 1;


  switch_7405:
    ;
    switch (tmpval_7357) {

      case 0:
        {
            CursorTy jump_3566 = arg_771_962_1357 + 1;

            *(TagTyPacked *) loc_2533 = 0;

            CursorTy writetag_4370 = loc_2533 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2535, jump_3566,
                                                   loc_2533, writetag_4370};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7363 = *(FloatTy *) tmpcur_7358;
            CursorTy tmpcur_7364 = tmpcur_7358 + sizeof(FloatTy);
            CursorTy jump_3568 = tmpcur_7358 + 4;
            CursorTy loc_3101 = loc_2533 + 1;
            CursorTy loc_3102 = loc_3101 + 4;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _copy_PList1(end_r_2534, end_r_2535, loc_3102, tmpcur_7364);
            CursorTy pvrtmp_7365 = tmp_struct_195.field0;
            CursorTy pvrtmp_7366 = tmp_struct_195.field1;
            CursorTy pvrtmp_7367 = tmp_struct_195.field2;
            CursorTy pvrtmp_7368 = tmp_struct_195.field3;

            *(TagTyPacked *) loc_2533 = 1;

            CursorTy writetag_4375 = loc_2533 + 1;

            *(FloatTy *) writetag_4375 = tmpval_7363;

            CursorTy writecur_4376 = writetag_4375 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_7365, pvrtmp_7366,
                                                   loc_2533, pvrtmp_7368};
            break;
        }

      case 2:
        {
            CursorTy jump_3571 = arg_771_962_1357 + 1;

            *(TagTyPacked *) loc_2533 = 2;

            CursorTy writetag_4380 = loc_2533 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2535, jump_3571,
                                                   loc_2533, writetag_4380};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7381 = *(CursorTy *) tmpcur_7358;
            CursorTy tmpaftercur_7382 = tmpcur_7358 + 8;
            CursorTy jump_3767 = tmpcur_7358 + 8;
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _copy_PList1(end_r_2534, end_r_2535, loc_2533, tmpcur_7381);
            CursorTy pvrtmp_7383 = tmp_struct_196.field0;
            CursorTy pvrtmp_7384 = tmp_struct_196.field1;
            CursorTy pvrtmp_7385 = tmp_struct_196.field2;
            CursorTy pvrtmp_7386 = tmp_struct_196.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7383, jump_3767,
                                                   pvrtmp_7385, pvrtmp_7386};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7393 = *(CursorTy *) tmpcur_7358;
            CursorTy tmpaftercur_7394 = tmpcur_7358 + 8;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _copy_PList1(end_r_2534, end_r_2535, loc_2533, tmpcur_7393);
            CursorTy pvrtmp_7395 = tmp_struct_197.field0;
            CursorTy pvrtmp_7396 = tmp_struct_197.field1;
            CursorTy pvrtmp_7397 = tmp_struct_197.field2;
            CursorTy pvrtmp_7398 = tmp_struct_197.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7395, pvrtmp_7396,
                                                   pvrtmp_7397, pvrtmp_7398};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7357");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_PList1(CursorTy end_r_2538,
                                                       CursorTy end_r_2539,
                                                       CursorTy loc_2537,
                                                       CursorTy arg_776_967_1362)
{
    TagTyPacked tmpval_7406 = *(TagTyPacked *) arg_776_967_1362;
    CursorTy tmpcur_7407 = arg_776_967_1362 + 1;


  switch_7454:
    ;
    switch (tmpval_7406) {

      case 0:
        {
            CursorTy jump_3573 = arg_776_967_1362 + 1;

            *(TagTyPacked *) loc_2537 = 0;

            CursorTy writetag_4389 = loc_2537 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2539, jump_3573,
                                                   loc_2537, writetag_4389};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7412 = *(FloatTy *) tmpcur_7407;
            CursorTy tmpcur_7413 = tmpcur_7407 + sizeof(FloatTy);
            CursorTy jump_3575 = tmpcur_7407 + 4;
            CursorTy loc_3115 = loc_2537 + 1;
            CursorTy loc_3116 = loc_3115 + 4;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _copy_without_ptrs_PList1(end_r_2538, end_r_2539, loc_3116, tmpcur_7413);
            CursorTy pvrtmp_7414 = tmp_struct_201.field0;
            CursorTy pvrtmp_7415 = tmp_struct_201.field1;
            CursorTy pvrtmp_7416 = tmp_struct_201.field2;
            CursorTy pvrtmp_7417 = tmp_struct_201.field3;

            *(TagTyPacked *) loc_2537 = 1;

            CursorTy writetag_4394 = loc_2537 + 1;

            *(FloatTy *) writetag_4394 = tmpval_7412;

            CursorTy writecur_4395 = writetag_4394 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_7414, pvrtmp_7415,
                                                   loc_2537, pvrtmp_7417};
            break;
        }

      case 2:
        {
            CursorTy jump_3578 = arg_776_967_1362 + 1;

            *(TagTyPacked *) loc_2537 = 2;

            CursorTy writetag_4399 = loc_2537 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2539, jump_3578,
                                                   loc_2537, writetag_4399};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7430 = *(CursorTy *) tmpcur_7407;
            CursorTy tmpaftercur_7431 = tmpcur_7407 + 8;
            CursorTy jump_3773 = tmpcur_7407 + 8;
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _copy_without_ptrs_PList1(end_r_2538, end_r_2539, loc_2537, tmpcur_7430);
            CursorTy pvrtmp_7432 = tmp_struct_202.field0;
            CursorTy pvrtmp_7433 = tmp_struct_202.field1;
            CursorTy pvrtmp_7434 = tmp_struct_202.field2;
            CursorTy pvrtmp_7435 = tmp_struct_202.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7432, jump_3773,
                                                   pvrtmp_7434, pvrtmp_7435};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7442 = *(CursorTy *) tmpcur_7407;
            CursorTy tmpaftercur_7443 = tmpcur_7407 + 8;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _copy_without_ptrs_PList1(end_r_2538, end_r_2539, loc_2537, tmpcur_7442);
            CursorTy pvrtmp_7444 = tmp_struct_203.field0;
            CursorTy pvrtmp_7445 = tmp_struct_203.field1;
            CursorTy pvrtmp_7446 = tmp_struct_203.field2;
            CursorTy pvrtmp_7447 = tmp_struct_203.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7444, pvrtmp_7445,
                                                   pvrtmp_7446, pvrtmp_7447};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7406");
            exit(1);
        }
    }
}
CursorProd _traverse_PList1(CursorTy end_r_2541, CursorTy arg_781_972_1367)
{
    TagTyPacked tmpval_7455 = *(TagTyPacked *) arg_781_972_1367;
    CursorTy tmpcur_7456 = arg_781_972_1367 + 1;


  switch_7466:
    ;
    switch (tmpval_7455) {

      case 0:
        {
            CursorTy jump_3580 = arg_781_972_1367 + 1;

            return (CursorProd) {jump_3580};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7457 = *(FloatTy *) tmpcur_7456;
            CursorTy tmpcur_7458 = tmpcur_7456 + sizeof(FloatTy);
            CursorTy jump_3582 = tmpcur_7456 + 4;
            CursorProd tmp_struct_204 =
                        _traverse_PList1(end_r_2541, tmpcur_7458);
            CursorTy pvrtmp_7459 = tmp_struct_204.field0;

            return (CursorProd) {pvrtmp_7459};
            break;
        }

      case 2:
        {
            CursorTy jump_3585 = arg_781_972_1367 + 1;

            return (CursorProd) {jump_3585};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7460 = *(CursorTy *) tmpcur_7456;
            CursorTy tmpaftercur_7461 = tmpcur_7456 + 8;
            CursorTy jump_3779 = tmpcur_7456 + 8;
            CursorProd tmp_struct_205 =
                        _traverse_PList1(end_r_2541, tmpcur_7460);
            CursorTy pvrtmp_7462 = tmp_struct_205.field0;

            return (CursorProd) {jump_3779};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7463 = *(CursorTy *) tmpcur_7456;
            CursorTy tmpaftercur_7464 = tmpcur_7456 + 8;
            CursorProd tmp_struct_206 =
                        _traverse_PList1(end_r_2541, tmpcur_7463);
            CursorTy pvrtmp_7465 = tmp_struct_206.field0;

            return (CursorProd) {pvrtmp_7465};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7455");
            exit(1);
        }
    }
}
CursorProd _print_PList1(CursorTy end_r_2543, CursorTy arg_786_976_1371)
{
    TagTyPacked tmpval_7467 = *(TagTyPacked *) arg_786_976_1371;
    CursorTy tmpcur_7468 = arg_786_976_1371 + 1;


  switch_7478:
    ;
    switch (tmpval_7467) {

      case 0:
        {
            CursorTy jump_3587 = arg_786_976_1371 + 1;
            unsigned char wildcard_787_977_1372 = print_symbol(6084);
            unsigned char wildcard_788_978_1373 = print_symbol(6081);

            return (CursorProd) {jump_3587};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7469 = *(FloatTy *) tmpcur_7468;
            CursorTy tmpcur_7470 = tmpcur_7468 + sizeof(FloatTy);
            CursorTy jump_3589 = tmpcur_7468 + 4;
            unsigned char wildcard_793_981_1376 = print_symbol(6087);
            unsigned char wildcard_796_982_1377 = print_symbol(6090);
            unsigned char y_791_983_1378 = printf("%.2f", tmpval_7469);
            unsigned char wildcard_795_984_1379 = print_symbol(6090);
            CursorProd tmp_struct_207 =  _print_PList1(end_r_2543, tmpcur_7470);
            CursorTy pvrtmp_7471 = tmp_struct_207.field0;
            unsigned char wildcard_794_986_1381 = print_symbol(6081);

            return (CursorProd) {pvrtmp_7471};
            break;
        }

      case 2:
        {
            CursorTy jump_3592 = arg_786_976_1371 + 1;
            unsigned char wildcard_797_987_1382 = print_symbol(6085);
            unsigned char wildcard_798_988_1383 = print_symbol(6081);

            return (CursorProd) {jump_3592};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7472 = *(CursorTy *) tmpcur_7468;
            CursorTy tmpaftercur_7473 = tmpcur_7468 + 8;
            CursorTy jump_3785 = tmpcur_7468 + 8;
            unsigned char wildcard_3788 = print_symbol(6089);
            CursorProd tmp_struct_208 =  _print_PList1(end_r_2543, tmpcur_7472);
            CursorTy pvrtmp_7474 = tmp_struct_208.field0;

            return (CursorProd) {jump_3785};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7475 = *(CursorTy *) tmpcur_7468;
            CursorTy tmpaftercur_7476 = tmpcur_7468 + 8;
            unsigned char wildcard_3788 = print_symbol(6088);
            CursorProd tmp_struct_209 =  _print_PList1(end_r_2543, tmpcur_7475);
            CursorTy pvrtmp_7477 = tmp_struct_209.field0;

            return (CursorProd) {pvrtmp_7477};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7467");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_807(CursorTy end_r_2546, CursorTy end_r_2547,
                                  CursorTy loc_2545, IntTy n_264_808_1001_1384,
                                  CursorTy fs_267_809_1002_1385)
{
    if (loc_2545 + 32 > end_r_2547) {
        ChunkTy new_chunk_213 = alloc_chunk(end_r_2547);
        CursorTy chunk_start_214 = new_chunk_213.chunk_start;
        CursorTy chunk_end_215 = new_chunk_213.chunk_end;

        end_r_2547 = chunk_end_215;
        *(TagTyPacked *) loc_2545 = 255;

        CursorTy redir = loc_2545 + 1;

        *(CursorTy *) redir = chunk_start_214;
        loc_2545 = chunk_start_214;
    }

    TagTyPacked tmpval_7479 = *(TagTyPacked *) fs_267_809_1002_1385;
    CursorTy tmpcur_7480 = fs_267_809_1002_1385 + 1;


  switch_7528:
    ;
    switch (tmpval_7479) {

      case 0:
        {
            CursorTy jump_3594 = fs_267_809_1002_1385 + 1;

            *(TagTyPacked *) loc_2545 = 2;

            CursorTy writetag_4430 = loc_2545 + 1;

            return (CursorCursorCursorProd) {end_r_2547, loc_2545,
                                             writetag_4430};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7485 = *(FloatTy *) tmpcur_7480;
            CursorTy tmpcur_7486 = tmpcur_7480 + sizeof(FloatTy);
            CursorTy jump_3596 = tmpcur_7480 + 4;
            BoolTy fltIf_1135_1388 = tmpval_7485 == 0.0;

            if (fltIf_1135_1388) {
                IntTy fltAppE_1137_1389 = n_264_808_1001_1384 - 1;
                CursorTy loc_3141 = loc_2545 + 1;
                CursorTy loc_3142 = loc_3141 + 4;
                CursorCursorCursorProd tmp_struct_210 =
                                        psSqrt(end_r_2546, end_r_2547, loc_3142, fltAppE_1137_1389, tmpcur_7486);
                CursorTy pvrtmp_7487 = tmp_struct_210.field0;
                CursorTy pvrtmp_7488 = tmp_struct_210.field1;
                CursorTy pvrtmp_7489 = tmp_struct_210.field2;

                *(TagTyPacked *) loc_2545 = 1;

                CursorTy writetag_4435 = loc_2545 + 1;

                *(FloatTy *) writetag_4435 = 0.0;

                CursorTy writecur_4436 = writetag_4435 + sizeof(FloatTy);

                return (CursorCursorCursorProd) {pvrtmp_7487, loc_2545,
                                                 pvrtmp_7489};
            } else {
                *(TagTyPacked *) loc_2545 = 2;

                CursorTy writetag_4439 = loc_2545 + 1;

                return (CursorCursorCursorProd) {end_r_2547, loc_2545,
                                                 writetag_4439};
            }
            break;
        }

      case 2:
        {
            CursorTy jump_3599 = fs_267_809_1002_1385 + 1;

            *(TagTyPacked *) loc_2545 = 2;

            CursorTy writetag_4442 = loc_2545 + 1;

            return (CursorCursorCursorProd) {end_r_2547, loc_2545,
                                             writetag_4442};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7506 = *(CursorTy *) tmpcur_7480;
            CursorTy tmpaftercur_7507 = tmpcur_7480 + 8;
            CursorTy jump_3791 = tmpcur_7480 + 8;
            CursorCursorCursorProd tmp_struct_211 =
                                    caseFn_807(end_r_2546, end_r_2547, loc_2545, n_264_808_1001_1384, tmpcur_7506);
            CursorTy pvrtmp_7508 = tmp_struct_211.field0;
            CursorTy pvrtmp_7509 = tmp_struct_211.field1;
            CursorTy pvrtmp_7510 = tmp_struct_211.field2;

            return (CursorCursorCursorProd) {pvrtmp_7508, pvrtmp_7509,
                                             pvrtmp_7510};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7517 = *(CursorTy *) tmpcur_7480;
            CursorTy tmpaftercur_7518 = tmpcur_7480 + 8;
            CursorCursorCursorProd tmp_struct_212 =
                                    caseFn_807(end_r_2546, end_r_2547, loc_2545, n_264_808_1001_1384, tmpcur_7517);
            CursorTy pvrtmp_7519 = tmp_struct_212.field0;
            CursorTy pvrtmp_7520 = tmp_struct_212.field1;
            CursorTy pvrtmp_7521 = tmp_struct_212.field2;

            return (CursorCursorCursorProd) {pvrtmp_7519, pvrtmp_7520,
                                             pvrtmp_7521};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7479");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd caseFn_810(CursorTy end_r_2550,
                                        CursorTy end_r_2551, CursorTy loc_2549,
                                        FloatTy f_286_811_1005_1391,
                                        CursorTy fs__289_812_1006_1392,
                                        FloatTy f__288_813_1007_1393)
{
    if (loc_2549 + 32 > end_r_2551) {
        ChunkTy new_chunk_218 = alloc_chunk(end_r_2551);
        CursorTy chunk_start_219 = new_chunk_218.chunk_start;
        CursorTy chunk_end_220 = new_chunk_218.chunk_end;

        end_r_2551 = chunk_end_220;
        *(TagTyPacked *) loc_2549 = 255;

        CursorTy redir = loc_2549 + 1;

        *(CursorTy *) redir = chunk_start_219;
        loc_2549 = chunk_start_219;
    }

    TagTyPacked tmpval_7529 = *(TagTyPacked *) fs__289_812_1006_1392;
    CursorTy tmpcur_7530 = fs__289_812_1006_1392 + 1;


  switch_7563:
    ;
    switch (tmpval_7529) {

      case 0:
        {
            CursorTy jump_3601 = fs__289_812_1006_1392 + 1;
            FloatTy fltPkd_1138_1394 = f_286_811_1005_1391 /
                    f__288_813_1007_1393;
            FloatTy fltPrm_1141_1395 = 0.0 - 1.0;
            FloatTy fltPkd_1140_1396 = fltPrm_1141_1395 / f__288_813_1007_1393;
            CursorTy loc_3156 = loc_2549 + 1;
            CursorTy loc_3157 = loc_3156 + 4;
            CursorTy loc_3151 = loc_3157 + 1;
            CursorTy loc_3152 = loc_3151 + 4;

            *(TagTyPacked *) loc_3152 = 0;

            CursorTy writetag_4451 = loc_3152 + 1;

            *(TagTyPacked *) loc_3157 = 1;

            CursorTy writetag_4453 = loc_3157 + 1;

            *(FloatTy *) writetag_4453 = fltPkd_1140_1396;

            CursorTy writecur_4454 = writetag_4453 + sizeof(FloatTy);

            *(TagTyPacked *) loc_2549 = 1;

            CursorTy writetag_4457 = loc_2549 + 1;

            *(FloatTy *) writetag_4457 = fltPkd_1138_1394;

            CursorTy writecur_4458 = writetag_4457 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_2551, jump_3601,
                                                   loc_2549, writetag_4451};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7539 = *(CursorTy *) tmpcur_7530;
            CursorTy tmpaftercur_7540 = tmpcur_7530 + 8;
            CursorTy jump_3796 = tmpcur_7530 + 8;
            CursorCursorCursorCursorProd tmp_struct_216 =
                                          caseFn_810(end_r_2550, end_r_2551, loc_2549, f_286_811_1005_1391, tmpcur_7539, f__288_813_1007_1393);
            CursorTy pvrtmp_7541 = tmp_struct_216.field0;
            CursorTy pvrtmp_7542 = tmp_struct_216.field1;
            CursorTy pvrtmp_7543 = tmp_struct_216.field2;
            CursorTy pvrtmp_7544 = tmp_struct_216.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7541, jump_3796,
                                                   pvrtmp_7543, pvrtmp_7544};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7551 = *(CursorTy *) tmpcur_7530;
            CursorTy tmpaftercur_7552 = tmpcur_7530 + 8;
            CursorCursorCursorCursorProd tmp_struct_217 =
                                          caseFn_810(end_r_2550, end_r_2551, loc_2549, f_286_811_1005_1391, tmpcur_7551, f__288_813_1007_1393);
            CursorTy pvrtmp_7553 = tmp_struct_217.field0;
            CursorTy pvrtmp_7554 = tmp_struct_217.field1;
            CursorTy pvrtmp_7555 = tmp_struct_217.field2;
            CursorTy pvrtmp_7556 = tmp_struct_217.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7553, pvrtmp_7554,
                                                   pvrtmp_7555, pvrtmp_7556};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7529");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd caseFn_814(CursorTy end_r_2554,
                                        CursorTy end_r_2555, CursorTy loc_2553,
                                        FloatTy f_286_815_1008_1399,
                                        CursorTy fs_287_816_1009_1400)
{
    if (loc_2553 + 32 > end_r_2555) {
        ChunkTy new_chunk_224 = alloc_chunk(end_r_2555);
        CursorTy chunk_start_225 = new_chunk_224.chunk_start;
        CursorTy chunk_end_226 = new_chunk_224.chunk_end;

        end_r_2555 = chunk_end_226;
        *(TagTyPacked *) loc_2553 = 255;

        CursorTy redir = loc_2553 + 1;

        *(CursorTy *) redir = chunk_start_225;
        loc_2553 = chunk_start_225;
    }

    TagTyPacked tmpval_7564 = *(TagTyPacked *) fs_287_816_1009_1400;
    CursorTy tmpcur_7565 = fs_287_816_1009_1400 + 1;


  switch_7602:
    ;
    switch (tmpval_7564) {

      case 1:
        {
            FloatTy tmpval_7566 = *(FloatTy *) tmpcur_7565;
            CursorTy tmpcur_7567 = tmpcur_7565 + sizeof(FloatTy);
            CursorTy jump_3603 = tmpcur_7565 + 4;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          caseFn_810(end_r_2554, end_r_2555, loc_2553, f_286_815_1008_1399, tmpcur_7567, tmpval_7566);
            CursorTy pvrtmp_7568 = tmp_struct_221.field0;
            CursorTy pvrtmp_7569 = tmp_struct_221.field1;
            CursorTy pvrtmp_7570 = tmp_struct_221.field2;
            CursorTy pvrtmp_7571 = tmp_struct_221.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7568, pvrtmp_7569,
                                                   pvrtmp_7570, pvrtmp_7571};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7578 = *(CursorTy *) tmpcur_7565;
            CursorTy tmpaftercur_7579 = tmpcur_7565 + 8;
            CursorTy jump_3802 = tmpcur_7565 + 8;
            CursorCursorCursorCursorProd tmp_struct_222 =
                                          caseFn_814(end_r_2554, end_r_2555, loc_2553, f_286_815_1008_1399, tmpcur_7578);
            CursorTy pvrtmp_7580 = tmp_struct_222.field0;
            CursorTy pvrtmp_7581 = tmp_struct_222.field1;
            CursorTy pvrtmp_7582 = tmp_struct_222.field2;
            CursorTy pvrtmp_7583 = tmp_struct_222.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7580, jump_3802,
                                                   pvrtmp_7582, pvrtmp_7583};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7590 = *(CursorTy *) tmpcur_7565;
            CursorTy tmpaftercur_7591 = tmpcur_7565 + 8;
            CursorCursorCursorCursorProd tmp_struct_223 =
                                          caseFn_814(end_r_2554, end_r_2555, loc_2553, f_286_815_1008_1399, tmpcur_7590);
            CursorTy pvrtmp_7592 = tmp_struct_223.field0;
            CursorTy pvrtmp_7593 = tmp_struct_223.field1;
            CursorTy pvrtmp_7594 = tmp_struct_223.field2;
            CursorTy pvrtmp_7595 = tmp_struct_223.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_7592, pvrtmp_7593,
                                                   pvrtmp_7594, pvrtmp_7595};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7564");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_817(CursorTy end_r_2559, CursorTy end_r_2560,
                                  CursorTy end_r_2561, CursorTy loc_2558,
                                  CursorTy b_293_818_1012_1403,
                                  FloatTy f_294_819_1013_1404,
                                  CursorTy fs_295_820_1014_1405)
{
    if (loc_2558 + 32 > end_r_2561) {
        ChunkTy new_chunk_234 = alloc_chunk(end_r_2561);
        CursorTy chunk_start_235 = new_chunk_234.chunk_start;
        CursorTy chunk_end_236 = new_chunk_234.chunk_end;

        end_r_2561 = chunk_end_236;
        *(TagTyPacked *) loc_2558 = 255;

        CursorTy redir = loc_2558 + 1;

        *(CursorTy *) redir = chunk_start_235;
        loc_2558 = chunk_start_235;
    }

    TagTyPacked tmpval_7603 = *(TagTyPacked *) b_293_818_1012_1403;
    CursorTy tmpcur_7604 = b_293_818_1012_1403 + 1;


  switch_7698:
    ;
    switch (tmpval_7603) {

      case 0:
        {
            CursorTy jump_3606 = b_293_818_1012_1403 + 1;
            CursorTy loc_3173 = loc_2558 + 1;
            CursorTy loc_3174 = loc_3173 + 4;

            *(TagTyPacked *) loc_3174 = 0;

            CursorTy writetag_4477 = loc_3174 + 1;

            *(TagTyPacked *) loc_2558 = 1;

            CursorTy writetag_4479 = loc_2558 + 1;

            *(FloatTy *) writetag_4479 = f_294_819_1013_1404;

            CursorTy writecur_4480 = writetag_4479 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {end_r_2561, loc_2558,
                                             writetag_4477};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7611 = *(FloatTy *) tmpcur_7604;
            CursorTy tmpcur_7612 = tmpcur_7604 + sizeof(FloatTy);
            CursorTy jump_3608 = tmpcur_7604 + 4;
            BoolTy fltIf_1144_1409 = tmpval_7611 == 0.0;

            if (fltIf_1144_1409) {
                RegionTy *region_7613 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3202 = region_7613->reg_heap;
                IntTy sizeof_end_r_3202_7614 = global_init_inf_buf_size;
                CursorTy end_r_3202 = r_3202 + sizeof_end_r_3202_7614;
                RegionTy *region_7615 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3201 = region_7615->reg_heap;
                IntTy sizeof_end_r_3201_7616 = global_init_inf_buf_size;
                CursorTy end_r_3201 = r_3201 + sizeof_end_r_3201_7616;
                CursorTy loc_3181 = r_3202 + 1;
                CursorTy loc_3182 = loc_3181 + 4;

                bump_ref_count(end_r_3202, end_r_2559);
                *(TagTyPacked *) loc_3182 = 254;

                CursorTy writetag_4485 = loc_3182 + 1;

                *(CursorTy *) writetag_4485 = tmpcur_7612;

                CursorTy writecur_4486 = writetag_4485 + 8;

                *(TagTyPacked *) r_3202 = 1;

                CursorTy writetag_4488 = r_3202 + 1;

                *(FloatTy *) writetag_4488 = 0.0;

                CursorTy writecur_4489 = writetag_4488 + sizeof(FloatTy);
                CursorCursorCursorProd tmp_struct_227 =
                                        compose(end_r_2560, end_r_3202, end_r_3201, r_3201, fs_295_820_1014_1405, r_3202);
                CursorTy pvrtmp_7621 = tmp_struct_227.field0;
                CursorTy pvrtmp_7622 = tmp_struct_227.field1;
                CursorTy pvrtmp_7623 = tmp_struct_227.field2;
                CursorTy loc_3173 = loc_2558 + 1;
                CursorTy loc_3174 = loc_3173 + 4;
                CursorCursorCursorProd tmp_struct_228 =
                                        psMult(end_r_2559, pvrtmp_7621, end_r_2561, loc_3174, tmpcur_7612, pvrtmp_7622);
                CursorTy pvrtmp_7628 = tmp_struct_228.field0;
                CursorTy pvrtmp_7629 = tmp_struct_228.field1;
                CursorTy pvrtmp_7630 = tmp_struct_228.field2;

                *(TagTyPacked *) loc_2558 = 1;

                CursorTy writetag_4494 = loc_2558 + 1;

                *(FloatTy *) writetag_4494 = f_294_819_1013_1404;

                CursorTy writecur_4495 = writetag_4494 + sizeof(FloatTy);

                free_region(end_r_3201);
                free_region(end_r_3202);
                return (CursorCursorCursorProd) {pvrtmp_7628, loc_2558,
                                                 pvrtmp_7630};
            } else {
                RegionTy *region_7639 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3232 = region_7639->reg_heap;
                IntTy sizeof_end_r_3232_7640 = global_init_inf_buf_size;
                CursorTy end_r_3232 = r_3232 + sizeof_end_r_3232_7640;
                RegionTy *region_7641 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3231 = region_7641->reg_heap;
                IntTy sizeof_end_r_3231_7642 = global_init_inf_buf_size;
                CursorTy end_r_3231 = r_3231 + sizeof_end_r_3231_7642;
                RegionTy *region_7643 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3230 = region_7643->reg_heap;
                IntTy sizeof_end_r_3230_7644 = global_init_inf_buf_size;
                CursorTy end_r_3230 = r_3230 + sizeof_end_r_3230_7644;
                CursorTy loc_3206 = r_3232 + 1;
                CursorTy loc_3207 = loc_3206 + 4;

                *(TagTyPacked *) loc_3207 = 0;

                CursorTy writetag_4498 = loc_3207 + 1;

                *(TagTyPacked *) r_3232 = 1;

                CursorTy writetag_4500 = r_3232 + 1;

                *(FloatTy *) writetag_4500 = f_294_819_1013_1404;

                CursorTy writecur_4501 = writetag_4500 + sizeof(FloatTy);
                CursorCursorCursorProd tmp_struct_229 =
                                        compose(end_r_2560, end_r_2559, end_r_3231, r_3231, fs_295_820_1014_1405, b_293_818_1012_1403);
                CursorTy pvrtmp_7649 = tmp_struct_229.field0;
                CursorTy pvrtmp_7650 = tmp_struct_229.field1;
                CursorTy pvrtmp_7651 = tmp_struct_229.field2;
                CursorCursorCursorProd tmp_struct_230 =
                                        psMult(end_r_2559, pvrtmp_7649, end_r_3230, r_3230, b_293_818_1012_1403, pvrtmp_7650);
                CursorTy pvrtmp_7656 = tmp_struct_230.field0;
                CursorTy pvrtmp_7657 = tmp_struct_230.field1;
                CursorTy pvrtmp_7658 = tmp_struct_230.field2;
                CursorCursorCursorProd tmp_struct_231 =
                                        psAdd(end_r_3232, pvrtmp_7656, end_r_2561, loc_2558, r_3232, pvrtmp_7657);
                CursorTy pvrtmp_7663 = tmp_struct_231.field0;
                CursorTy pvrtmp_7664 = tmp_struct_231.field1;
                CursorTy pvrtmp_7665 = tmp_struct_231.field2;

                free_region(end_r_3230);
                free_region(end_r_3231);
                free_region(end_r_3232);
                return (CursorCursorCursorProd) {pvrtmp_7663, pvrtmp_7664,
                                                 pvrtmp_7665};
            }
            break;
        }

      case 2:
        {
            CursorTy jump_3611 = b_293_818_1012_1403 + 1;

            *(TagTyPacked *) loc_2558 = 2;

            CursorTy writetag_4508 = loc_2558 + 1;

            return (CursorCursorCursorProd) {end_r_2561, loc_2558,
                                             writetag_4508};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7676 = *(CursorTy *) tmpcur_7604;
            CursorTy tmpaftercur_7677 = tmpcur_7604 + 8;
            CursorTy jump_3808 = tmpcur_7604 + 8;
            CursorCursorCursorProd tmp_struct_232 =
                                    caseFn_817(end_r_2559, end_r_2560, end_r_2561, loc_2558, tmpcur_7676, f_294_819_1013_1404, fs_295_820_1014_1405);
            CursorTy pvrtmp_7678 = tmp_struct_232.field0;
            CursorTy pvrtmp_7679 = tmp_struct_232.field1;
            CursorTy pvrtmp_7680 = tmp_struct_232.field2;

            return (CursorCursorCursorProd) {pvrtmp_7678, pvrtmp_7679,
                                             pvrtmp_7680};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7687 = *(CursorTy *) tmpcur_7604;
            CursorTy tmpaftercur_7688 = tmpcur_7604 + 8;
            CursorCursorCursorProd tmp_struct_233 =
                                    caseFn_817(end_r_2559, end_r_2560, end_r_2561, loc_2558, tmpcur_7687, f_294_819_1013_1404, fs_295_820_1014_1405);
            CursorTy pvrtmp_7689 = tmp_struct_233.field0;
            CursorTy pvrtmp_7690 = tmp_struct_233.field1;
            CursorTy pvrtmp_7691 = tmp_struct_233.field2;

            return (CursorCursorCursorProd) {pvrtmp_7689, pvrtmp_7690,
                                             pvrtmp_7691};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7603");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_821(CursorTy end_r_2564, CursorTy end_r_2565,
                                  CursorTy loc_2563, IntTy n_300_822_1017_1417,
                                  CursorTy fs_301_823_1018_1418)
{
    if (loc_2563 + 32 > end_r_2565) {
        ChunkTy new_chunk_240 = alloc_chunk(end_r_2565);
        CursorTy chunk_start_241 = new_chunk_240.chunk_start;
        CursorTy chunk_end_242 = new_chunk_240.chunk_end;

        end_r_2565 = chunk_end_242;
        *(TagTyPacked *) loc_2563 = 255;

        CursorTy redir = loc_2563 + 1;

        *(CursorTy *) redir = chunk_start_241;
        loc_2563 = chunk_start_241;
    }

    TagTyPacked tmpval_7699 = *(TagTyPacked *) fs_301_823_1018_1418;
    CursorTy tmpcur_7700 = fs_301_823_1018_1418 + 1;


  switch_7744:
    ;
    switch (tmpval_7699) {

      case 0:
        {
            CursorTy jump_3613 = fs_301_823_1018_1418 + 1;

            *(TagTyPacked *) loc_2563 = 0;

            CursorTy writetag_4517 = loc_2563 + 1;

            return (CursorCursorCursorProd) {end_r_2565, loc_2563,
                                             writetag_4517};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7705 = *(FloatTy *) tmpcur_7700;
            CursorTy tmpcur_7706 = tmpcur_7700 + sizeof(FloatTy);
            CursorTy jump_3615 = tmpcur_7700 + 4;
            IntTy fltAppE_1153_1421 = n_300_822_1017_1417 - 1;
            CursorTy loc_3242 = loc_2563 + 1;
            CursorTy loc_3243 = loc_3242 + 4;
            CursorCursorCursorProd tmp_struct_237 =
                                    takePs(end_r_2564, end_r_2565, loc_3243, fltAppE_1153_1421, tmpcur_7706);
            CursorTy pvrtmp_7707 = tmp_struct_237.field0;
            CursorTy pvrtmp_7708 = tmp_struct_237.field1;
            CursorTy pvrtmp_7709 = tmp_struct_237.field2;

            *(TagTyPacked *) loc_2563 = 1;

            CursorTy writetag_4522 = loc_2563 + 1;

            *(FloatTy *) writetag_4522 = tmpval_7705;

            CursorTy writecur_4523 = writetag_4522 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {pvrtmp_7707, loc_2563,
                                             pvrtmp_7709};
            break;
        }

      case 2:
        {
            CursorTy jump_3617 = fs_301_823_1018_1418 + 1;

            *(TagTyPacked *) loc_2563 = 2;

            CursorTy writetag_4527 = loc_2563 + 1;

            return (CursorCursorCursorProd) {end_r_2565, loc_2563,
                                             writetag_4527};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7722 = *(CursorTy *) tmpcur_7700;
            CursorTy tmpaftercur_7723 = tmpcur_7700 + 8;
            CursorTy jump_3813 = tmpcur_7700 + 8;
            CursorCursorCursorProd tmp_struct_238 =
                                    caseFn_821(end_r_2564, end_r_2565, loc_2563, n_300_822_1017_1417, tmpcur_7722);
            CursorTy pvrtmp_7724 = tmp_struct_238.field0;
            CursorTy pvrtmp_7725 = tmp_struct_238.field1;
            CursorTy pvrtmp_7726 = tmp_struct_238.field2;

            return (CursorCursorCursorProd) {pvrtmp_7724, pvrtmp_7725,
                                             pvrtmp_7726};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7733 = *(CursorTy *) tmpcur_7700;
            CursorTy tmpaftercur_7734 = tmpcur_7700 + 8;
            CursorCursorCursorProd tmp_struct_239 =
                                    caseFn_821(end_r_2564, end_r_2565, loc_2563, n_300_822_1017_1417, tmpcur_7733);
            CursorTy pvrtmp_7735 = tmp_struct_239.field0;
            CursorTy pvrtmp_7736 = tmp_struct_239.field1;
            CursorTy pvrtmp_7737 = tmp_struct_239.field2;

            return (CursorCursorCursorProd) {pvrtmp_7735, pvrtmp_7736,
                                             pvrtmp_7737};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7699");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_824(CursorTy end_r_2568, CursorTy end_r_2569,
                                  CursorTy loc_2567, IntTy n_304_825_1021_1423,
                                  CursorTy b_306_826_1022_1424)
{
    if (loc_2567 + 32 > end_r_2569) {
        ChunkTy new_chunk_246 = alloc_chunk(end_r_2569);
        CursorTy chunk_start_247 = new_chunk_246.chunk_start;
        CursorTy chunk_end_248 = new_chunk_246.chunk_end;

        end_r_2569 = chunk_end_248;
        *(TagTyPacked *) loc_2567 = 255;

        CursorTy redir = loc_2567 + 1;

        *(CursorTy *) redir = chunk_start_247;
        loc_2567 = chunk_start_247;
    }

    TagTyPacked tmpval_7745 = *(TagTyPacked *) b_306_826_1022_1424;
    CursorTy tmpcur_7746 = b_306_826_1022_1424 + 1;


  switch_7796:
    ;
    switch (tmpval_7745) {

      case 0:
        {
            CursorTy jump_3619 = b_306_826_1022_1424 + 1;

            *(TagTyPacked *) loc_2567 = 2;

            CursorTy writetag_4536 = loc_2567 + 1;

            return (CursorCursorCursorProd) {end_r_2569, loc_2567,
                                             writetag_4536};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7751 = *(FloatTy *) tmpcur_7746;
            CursorTy tmpcur_7752 = tmpcur_7746 + sizeof(FloatTy);
            CursorTy jump_3621 = tmpcur_7746 + 4;
            BoolTy fltIf_1154_1427 = tmpval_7751 == 0.0;

            if (fltIf_1154_1427) {
                RegionTy *region_7753 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3262 = region_7753->reg_heap;
                IntTy sizeof_end_r_3262_7754 = global_init_inf_buf_size;
                CursorTy end_r_3262 = r_3262 + sizeof_end_r_3262_7754;

                *(TagTyPacked *) r_3262 = 0;

                CursorTy writetag_4540 = r_3262 + 1;
                CursorCursorCursorProd tmp_struct_243 =
                                        psDiv(end_r_3262, end_r_2568, end_r_2569, loc_2567, n_304_825_1021_1423, r_3262, tmpcur_7752);
                CursorTy pvrtmp_7757 = tmp_struct_243.field0;
                CursorTy pvrtmp_7758 = tmp_struct_243.field1;
                CursorTy pvrtmp_7759 = tmp_struct_243.field2;

                free_region(end_r_3262);
                return (CursorCursorCursorProd) {pvrtmp_7757, pvrtmp_7758,
                                                 pvrtmp_7759};
            } else {
                *(TagTyPacked *) loc_2567 = 0;

                CursorTy writetag_4543 = loc_2567 + 1;

                return (CursorCursorCursorProd) {end_r_2569, loc_2567,
                                                 writetag_4543};
            }
            break;
        }

      case 2:
        {
            CursorTy jump_3624 = b_306_826_1022_1424 + 1;

            *(TagTyPacked *) loc_2567 = 2;

            CursorTy writetag_4546 = loc_2567 + 1;

            return (CursorCursorCursorProd) {end_r_2569, loc_2567,
                                             writetag_4546};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7774 = *(CursorTy *) tmpcur_7746;
            CursorTy tmpaftercur_7775 = tmpcur_7746 + 8;
            CursorTy jump_3818 = tmpcur_7746 + 8;
            CursorCursorCursorProd tmp_struct_244 =
                                    caseFn_824(end_r_2568, end_r_2569, loc_2567, n_304_825_1021_1423, tmpcur_7774);
            CursorTy pvrtmp_7776 = tmp_struct_244.field0;
            CursorTy pvrtmp_7777 = tmp_struct_244.field1;
            CursorTy pvrtmp_7778 = tmp_struct_244.field2;

            return (CursorCursorCursorProd) {pvrtmp_7776, pvrtmp_7777,
                                             pvrtmp_7778};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7785 = *(CursorTy *) tmpcur_7746;
            CursorTy tmpaftercur_7786 = tmpcur_7746 + 8;
            CursorCursorCursorProd tmp_struct_245 =
                                    caseFn_824(end_r_2568, end_r_2569, loc_2567, n_304_825_1021_1423, tmpcur_7785);
            CursorTy pvrtmp_7787 = tmp_struct_245.field0;
            CursorTy pvrtmp_7788 = tmp_struct_245.field1;
            CursorTy pvrtmp_7789 = tmp_struct_245.field2;

            return (CursorCursorCursorProd) {pvrtmp_7787, pvrtmp_7788,
                                             pvrtmp_7789};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7745");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_827(CursorTy end_r_2573, CursorTy end_r_2574,
                                  CursorTy end_r_2575, CursorTy loc_2572,
                                  IntTy n_304_828_1025_1429,
                                  CursorTy b_306_829_1026_1430,
                                  FloatTy f_309_830_1027_1431,
                                  CursorTy fs_310_831_1028_1432)
{
    if (loc_2572 + 32 > end_r_2575) {
        ChunkTy new_chunk_256 = alloc_chunk(end_r_2575);
        CursorTy chunk_start_257 = new_chunk_256.chunk_start;
        CursorTy chunk_end_258 = new_chunk_256.chunk_end;

        end_r_2575 = chunk_end_258;
        *(TagTyPacked *) loc_2572 = 255;

        CursorTy redir = loc_2572 + 1;

        *(CursorTy *) redir = chunk_start_257;
        loc_2572 = chunk_start_257;
    }

    TagTyPacked tmpval_7797 = *(TagTyPacked *) b_306_829_1026_1430;
    CursorTy tmpcur_7798 = b_306_829_1026_1430 + 1;


  switch_7880:
    ;
    switch (tmpval_7797) {

      case 0:
        {
            CursorTy jump_3626 = b_306_829_1026_1430 + 1;

            *(TagTyPacked *) loc_2572 = 2;

            CursorTy writetag_4555 = loc_2572 + 1;

            return (CursorCursorCursorProd) {end_r_2575, loc_2572,
                                             writetag_4555};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7803 = *(FloatTy *) tmpcur_7798;
            CursorTy tmpcur_7804 = tmpcur_7798 + sizeof(FloatTy);
            CursorTy jump_3628 = tmpcur_7798 + 4;
            BoolTy fltPrm_1157_1435 = f_309_830_1027_1431 == 0.0;
            BoolTy fltPrm_1158_1436 = tmpval_7803 == 0.0;
            BoolTy fltIf_1156_1437 = fltPrm_1157_1435 && fltPrm_1158_1436;

            if (fltIf_1156_1437) {
                CursorCursorCursorProd tmp_struct_249 =
                                        psDiv(end_r_2574, end_r_2573, end_r_2575, loc_2572, n_304_828_1025_1429, fs_310_831_1028_1432, tmpcur_7804);
                CursorTy pvrtmp_7805 = tmp_struct_249.field0;
                CursorTy pvrtmp_7806 = tmp_struct_249.field1;
                CursorTy pvrtmp_7807 = tmp_struct_249.field2;

                return (CursorCursorCursorProd) {pvrtmp_7805, pvrtmp_7806,
                                                 pvrtmp_7807};
            } else {
                RegionTy *region_7814 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3302 = region_7814->reg_heap;
                IntTy sizeof_end_r_3302_7815 = global_init_inf_buf_size;
                CursorTy end_r_3302 = r_3302 + sizeof_end_r_3302_7815;
                RegionTy *region_7816 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3301 = region_7816->reg_heap;
                IntTy sizeof_end_r_3301_7817 = global_init_inf_buf_size;
                CursorTy end_r_3301 = r_3301 + sizeof_end_r_3301_7817;
                RegionTy *region_7818 = alloc_region(global_init_inf_buf_size);
                CursorTy r_3300 = region_7818->reg_heap;
                IntTy sizeof_end_r_3300_7819 = global_init_inf_buf_size;
                CursorTy end_r_3300 = r_3300 + sizeof_end_r_3300_7819;
                FloatTy q_313_1031_1438 = f_309_830_1027_1431 / tmpval_7803;
                IntTy fltAppE_1160_1439 = n_304_828_1025_1429 - 1;
                CursorCursorCursorCursorProd tmp_struct_250 =
                                              dot(end_r_2573, end_r_3302, r_3302, q_313_1031_1438, tmpcur_7804);
                CursorTy pvrtmp_7820 = tmp_struct_250.field0;
                CursorTy pvrtmp_7821 = tmp_struct_250.field1;
                CursorTy pvrtmp_7822 = tmp_struct_250.field2;
                CursorTy pvrtmp_7823 = tmp_struct_250.field3;
                CursorCursorCursorCursorProd tmp_struct_251 =
                                              psNeg(pvrtmp_7820, end_r_3301, r_3301, pvrtmp_7822);
                CursorTy pvrtmp_7828 = tmp_struct_251.field0;
                CursorTy pvrtmp_7829 = tmp_struct_251.field1;
                CursorTy pvrtmp_7830 = tmp_struct_251.field2;
                CursorTy pvrtmp_7831 = tmp_struct_251.field3;
                CursorCursorCursorProd tmp_struct_252 =
                                        psAdd(end_r_2574, pvrtmp_7828, end_r_3300, r_3300, fs_310_831_1028_1432, pvrtmp_7830);
                CursorTy pvrtmp_7836 = tmp_struct_252.field0;
                CursorTy pvrtmp_7837 = tmp_struct_252.field1;
                CursorTy pvrtmp_7838 = tmp_struct_252.field2;
                CursorTy loc_3295 = loc_2572 + 1;
                CursorTy loc_3296 = loc_3295 + 4;
                CursorCursorCursorProd tmp_struct_253 =
                                        psDiv(pvrtmp_7836, end_r_2573, end_r_2575, loc_3296, fltAppE_1160_1439, pvrtmp_7837, b_306_829_1026_1430);
                CursorTy pvrtmp_7843 = tmp_struct_253.field0;
                CursorTy pvrtmp_7844 = tmp_struct_253.field1;
                CursorTy pvrtmp_7845 = tmp_struct_253.field2;

                *(TagTyPacked *) loc_2572 = 1;

                CursorTy writetag_4564 = loc_2572 + 1;

                *(FloatTy *) writetag_4564 = q_313_1031_1438;

                CursorTy writecur_4565 = writetag_4564 + sizeof(FloatTy);

                free_region(end_r_3300);
                free_region(end_r_3301);
                free_region(end_r_3302);
                return (CursorCursorCursorProd) {pvrtmp_7843, loc_2572,
                                                 pvrtmp_7845};
            }
            break;
        }

      case 2:
        {
            CursorTy jump_3633 = b_306_829_1026_1430 + 1;

            *(TagTyPacked *) loc_2572 = 2;

            CursorTy writetag_4569 = loc_2572 + 1;

            return (CursorCursorCursorProd) {end_r_2575, loc_2572,
                                             writetag_4569};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7858 = *(CursorTy *) tmpcur_7798;
            CursorTy tmpaftercur_7859 = tmpcur_7798 + 8;
            CursorTy jump_3823 = tmpcur_7798 + 8;
            CursorCursorCursorProd tmp_struct_254 =
                                    caseFn_827(end_r_2573, end_r_2574, end_r_2575, loc_2572, n_304_828_1025_1429, tmpcur_7858, f_309_830_1027_1431, fs_310_831_1028_1432);
            CursorTy pvrtmp_7860 = tmp_struct_254.field0;
            CursorTy pvrtmp_7861 = tmp_struct_254.field1;
            CursorTy pvrtmp_7862 = tmp_struct_254.field2;

            return (CursorCursorCursorProd) {pvrtmp_7860, pvrtmp_7861,
                                             pvrtmp_7862};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7869 = *(CursorTy *) tmpcur_7798;
            CursorTy tmpaftercur_7870 = tmpcur_7798 + 8;
            CursorCursorCursorProd tmp_struct_255 =
                                    caseFn_827(end_r_2573, end_r_2574, end_r_2575, loc_2572, n_304_828_1025_1429, tmpcur_7869, f_309_830_1027_1431, fs_310_831_1028_1432);
            CursorTy pvrtmp_7871 = tmp_struct_255.field0;
            CursorTy pvrtmp_7872 = tmp_struct_255.field1;
            CursorTy pvrtmp_7873 = tmp_struct_255.field2;

            return (CursorCursorCursorProd) {pvrtmp_7871, pvrtmp_7872,
                                             pvrtmp_7873};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7797");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_832(CursorTy end_r_2579, CursorTy end_r_2580,
                                  CursorTy end_r_2581, CursorTy loc_2578,
                                  IntTy n_304_833_1032_1444,
                                  CursorTy a_305_834_1033_1445,
                                  CursorTy b_306_835_1034_1446)
{
    if (loc_2578 + 32 > end_r_2581) {
        ChunkTy new_chunk_263 = alloc_chunk(end_r_2581);
        CursorTy chunk_start_264 = new_chunk_263.chunk_start;
        CursorTy chunk_end_265 = new_chunk_263.chunk_end;

        end_r_2581 = chunk_end_265;
        *(TagTyPacked *) loc_2578 = 255;

        CursorTy redir = loc_2578 + 1;

        *(CursorTy *) redir = chunk_start_264;
        loc_2578 = chunk_start_264;
    }

    TagTyPacked tmpval_7881 = *(TagTyPacked *) a_305_834_1033_1445;
    CursorTy tmpcur_7882 = a_305_834_1033_1445 + 1;


  switch_7929:
    ;
    switch (tmpval_7881) {

      case 0:
        {
            CursorTy jump_3635 = a_305_834_1033_1445 + 1;
            CursorCursorCursorProd tmp_struct_259 =
                                    caseFn_824(end_r_2580, end_r_2581, loc_2578, n_304_833_1032_1444, b_306_835_1034_1446);
            CursorTy pvrtmp_7883 = tmp_struct_259.field0;
            CursorTy pvrtmp_7884 = tmp_struct_259.field1;
            CursorTy pvrtmp_7885 = tmp_struct_259.field2;

            return (CursorCursorCursorProd) {pvrtmp_7883, pvrtmp_7884,
                                             pvrtmp_7885};
            break;
        }

      case 1:
        {
            FloatTy tmpval_7892 = *(FloatTy *) tmpcur_7882;
            CursorTy tmpcur_7893 = tmpcur_7882 + sizeof(FloatTy);
            CursorTy jump_3637 = tmpcur_7882 + 4;
            CursorCursorCursorProd tmp_struct_260 =
                                    caseFn_827(end_r_2580, end_r_2579, end_r_2581, loc_2578, n_304_833_1032_1444, b_306_835_1034_1446, tmpval_7892, tmpcur_7893);
            CursorTy pvrtmp_7894 = tmp_struct_260.field0;
            CursorTy pvrtmp_7895 = tmp_struct_260.field1;
            CursorTy pvrtmp_7896 = tmp_struct_260.field2;

            return (CursorCursorCursorProd) {pvrtmp_7894, pvrtmp_7895,
                                             pvrtmp_7896};
            break;
        }

      case 2:
        {
            CursorTy jump_3639 = a_305_834_1033_1445 + 1;

            *(TagTyPacked *) loc_2578 = 2;

            CursorTy writetag_4583 = loc_2578 + 1;

            return (CursorCursorCursorProd) {end_r_2581, loc_2578,
                                             writetag_4583};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7907 = *(CursorTy *) tmpcur_7882;
            CursorTy tmpaftercur_7908 = tmpcur_7882 + 8;
            CursorTy jump_3828 = tmpcur_7882 + 8;
            CursorCursorCursorProd tmp_struct_261 =
                                    caseFn_832(end_r_2579, end_r_2580, end_r_2581, loc_2578, n_304_833_1032_1444, tmpcur_7907, b_306_835_1034_1446);
            CursorTy pvrtmp_7909 = tmp_struct_261.field0;
            CursorTy pvrtmp_7910 = tmp_struct_261.field1;
            CursorTy pvrtmp_7911 = tmp_struct_261.field2;

            return (CursorCursorCursorProd) {pvrtmp_7909, pvrtmp_7910,
                                             pvrtmp_7911};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7918 = *(CursorTy *) tmpcur_7882;
            CursorTy tmpaftercur_7919 = tmpcur_7882 + 8;
            CursorCursorCursorProd tmp_struct_262 =
                                    caseFn_832(end_r_2579, end_r_2580, end_r_2581, loc_2578, n_304_833_1032_1444, tmpcur_7918, b_306_835_1034_1446);
            CursorTy pvrtmp_7920 = tmp_struct_262.field0;
            CursorTy pvrtmp_7921 = tmp_struct_262.field1;
            CursorTy pvrtmp_7922 = tmp_struct_262.field2;

            return (CursorCursorCursorProd) {pvrtmp_7920, pvrtmp_7921,
                                             pvrtmp_7922};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7881");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd caseFn_836(CursorTy end_r_2585,
                                        CursorTy end_r_2586,
                                        CursorTy end_r_2587, CursorTy loc_2584,
                                        CursorTy b_315_837_1037_1449,
                                        FloatTy f_316_838_1038_1450,
                                        CursorTy fs_317_839_1039_1451)
{
    if (loc_2584 + 32 > end_r_2587) {
        ChunkTy new_chunk_275 = alloc_chunk(end_r_2587);
        CursorTy chunk_start_276 = new_chunk_275.chunk_start;
        CursorTy chunk_end_277 = new_chunk_275.chunk_end;

        end_r_2587 = chunk_end_277;
        *(TagTyPacked *) loc_2584 = 255;

        CursorTy redir = loc_2584 + 1;

        *(CursorTy *) redir = chunk_start_276;
        loc_2584 = chunk_start_276;
    }

    TagTyPacked tmpval_7930 = *(TagTyPacked *) b_315_837_1037_1449;
    CursorTy tmpcur_7931 = b_315_837_1037_1449 + 1;


  switch_8033:
    ;
    switch (tmpval_7930) {

      case 0:
        {
            CursorTy jump_3641 = b_315_837_1037_1449 + 1;

            *(TagTyPacked *) loc_2584 = 0;

            CursorTy writetag_4592 = loc_2584 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2587, jump_3641,
                                                   loc_2584, writetag_4592};
            break;
        }

      case 1:
        {
            RegionTy *region_7936 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3367 = region_7936->reg_heap;
            IntTy sizeof_end_r_3367_7937 = global_init_inf_buf_size;
            CursorTy end_r_3367 = r_3367 + sizeof_end_r_3367_7937;
            RegionTy *region_7938 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3366 = region_7938->reg_heap;
            IntTy sizeof_end_r_3366_7939 = global_init_inf_buf_size;
            CursorTy end_r_3366 = r_3366 + sizeof_end_r_3366_7939;
            RegionTy *region_7940 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3365 = region_7940->reg_heap;
            IntTy sizeof_end_r_3365_7941 = global_init_inf_buf_size;
            CursorTy end_r_3365 = r_3365 + sizeof_end_r_3365_7941;
            RegionTy *region_7942 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3364 = region_7942->reg_heap;
            IntTy sizeof_end_r_3364_7943 = global_init_inf_buf_size;
            CursorTy end_r_3364 = r_3364 + sizeof_end_r_3364_7943;
            RegionTy *region_7944 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3363 = region_7944->reg_heap;
            IntTy sizeof_end_r_3363_7945 = global_init_inf_buf_size;
            CursorTy end_r_3363 = r_3363 + sizeof_end_r_3363_7945;
            RegionTy *region_7946 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3362 = region_7946->reg_heap;
            IntTy sizeof_end_r_3362_7947 = global_init_inf_buf_size;
            CursorTy end_r_3362 = r_3362 + sizeof_end_r_3362_7947;
            FloatTy tmpval_7948 = *(FloatTy *) tmpcur_7931;
            CursorTy tmpcur_7949 = tmpcur_7931 + sizeof(FloatTy);
            CursorTy jump_3643 = tmpcur_7931 + 4;
            FloatTy fltPkd_1164_1454 = f_316_838_1038_1450 * tmpval_7948;
            CursorCursorCursorCursorProd tmp_struct_266 =
                                          dot(end_r_2585, end_r_3367, r_3367, f_316_838_1038_1450, tmpcur_7949);
            CursorTy pvrtmp_7950 = tmp_struct_266.field0;
            CursorTy pvrtmp_7951 = tmp_struct_266.field1;
            CursorTy pvrtmp_7952 = tmp_struct_266.field2;
            CursorTy pvrtmp_7953 = tmp_struct_266.field3;
            CursorCursorCursorCursorProd tmp_struct_267 =
                                          dot(end_r_2586, end_r_3366, r_3366, tmpval_7948, fs_317_839_1039_1451);
            CursorTy pvrtmp_7958 = tmp_struct_267.field0;
            CursorTy pvrtmp_7959 = tmp_struct_267.field1;
            CursorTy pvrtmp_7960 = tmp_struct_267.field2;
            CursorTy pvrtmp_7961 = tmp_struct_267.field3;
            CursorCursorCursorProd tmp_struct_268 =  psX(end_r_3365, r_3365);
            CursorTy pvrtmp_7966 = tmp_struct_268.field0;
            CursorTy pvrtmp_7967 = tmp_struct_268.field1;
            CursorTy pvrtmp_7968 = tmp_struct_268.field2;
            CursorCursorCursorProd tmp_struct_269 =
                                    psMult(end_r_2586, end_r_2585, end_r_3364, r_3364, fs_317_839_1039_1451, tmpcur_7949);
            CursorTy pvrtmp_7973 = tmp_struct_269.field0;
            CursorTy pvrtmp_7974 = tmp_struct_269.field1;
            CursorTy pvrtmp_7975 = tmp_struct_269.field2;
            CursorCursorCursorProd tmp_struct_270 =
                                    psMult(pvrtmp_7966, pvrtmp_7973, end_r_3363, r_3363, pvrtmp_7967, pvrtmp_7974);
            CursorTy pvrtmp_7980 = tmp_struct_270.field0;
            CursorTy pvrtmp_7981 = tmp_struct_270.field1;
            CursorTy pvrtmp_7982 = tmp_struct_270.field2;
            CursorCursorCursorProd tmp_struct_271 =
                                    psAdd(pvrtmp_7958, pvrtmp_7980, end_r_3362, r_3362, pvrtmp_7960, pvrtmp_7981);
            CursorTy pvrtmp_7987 = tmp_struct_271.field0;
            CursorTy pvrtmp_7988 = tmp_struct_271.field1;
            CursorTy pvrtmp_7989 = tmp_struct_271.field2;
            CursorTy loc_3357 = loc_2584 + 1;
            CursorTy loc_3358 = loc_3357 + 4;
            CursorCursorCursorProd tmp_struct_272 =
                                    psAdd(pvrtmp_7950, pvrtmp_7987, end_r_2587, loc_3358, pvrtmp_7952, pvrtmp_7988);
            CursorTy pvrtmp_7994 = tmp_struct_272.field0;
            CursorTy pvrtmp_7995 = tmp_struct_272.field1;
            CursorTy pvrtmp_7996 = tmp_struct_272.field2;

            *(TagTyPacked *) loc_2584 = 1;

            CursorTy writetag_4603 = loc_2584 + 1;

            *(FloatTy *) writetag_4603 = fltPkd_1164_1454;

            CursorTy writecur_4604 = writetag_4603 + sizeof(FloatTy);

            free_region(end_r_3362);
            free_region(end_r_3363);
            free_region(end_r_3364);
            free_region(end_r_3365);
            free_region(end_r_3366);
            free_region(end_r_3367);
            return (CursorCursorCursorCursorProd) {pvrtmp_7994, pvrtmp_7951,
                                                   loc_2584, pvrtmp_7996};
            break;
        }

      case 2:
        {
            CursorTy jump_3647 = b_315_837_1037_1449 + 1;

            *(TagTyPacked *) loc_2584 = 2;

            CursorTy writetag_4608 = loc_2584 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2587, jump_3647,
                                                   loc_2584, writetag_4608};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_8009 = *(CursorTy *) tmpcur_7931;
            CursorTy tmpaftercur_8010 = tmpcur_7931 + 8;
            CursorTy jump_3833 = tmpcur_7931 + 8;
            CursorCursorCursorCursorProd tmp_struct_273 =
                                          caseFn_836(end_r_2585, end_r_2586, end_r_2587, loc_2584, tmpcur_8009, f_316_838_1038_1450, fs_317_839_1039_1451);
            CursorTy pvrtmp_8011 = tmp_struct_273.field0;
            CursorTy pvrtmp_8012 = tmp_struct_273.field1;
            CursorTy pvrtmp_8013 = tmp_struct_273.field2;
            CursorTy pvrtmp_8014 = tmp_struct_273.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_8011, jump_3833,
                                                   pvrtmp_8013, pvrtmp_8014};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_8021 = *(CursorTy *) tmpcur_7931;
            CursorTy tmpaftercur_8022 = tmpcur_7931 + 8;
            CursorCursorCursorCursorProd tmp_struct_274 =
                                          caseFn_836(end_r_2585, end_r_2586, end_r_2587, loc_2584, tmpcur_8021, f_316_838_1038_1450, fs_317_839_1039_1451);
            CursorTy pvrtmp_8023 = tmp_struct_274.field0;
            CursorTy pvrtmp_8024 = tmp_struct_274.field1;
            CursorTy pvrtmp_8025 = tmp_struct_274.field2;
            CursorTy pvrtmp_8026 = tmp_struct_274.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_8023, pvrtmp_8024,
                                                   pvrtmp_8025, pvrtmp_8026};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7930");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_840(CursorTy end_r_2592, CursorTy end_r_2593,
                                  CursorTy end_r_2594, CursorTy end_r_2595,
                                  CursorTy loc_2591,
                                  CursorTy a_320_841_1042_1462,
                                  CursorTy b_321_842_1043_1463,
                                  FloatTy f_322_843_1044_1464,
                                  CursorTy fs_323_844_1045_1465)
{
    if (loc_2591 + 32 > end_r_2595) {
        ChunkTy new_chunk_281 = alloc_chunk(end_r_2595);
        CursorTy chunk_start_282 = new_chunk_281.chunk_start;
        CursorTy chunk_end_283 = new_chunk_281.chunk_end;

        end_r_2595 = chunk_end_283;
        *(TagTyPacked *) loc_2591 = 255;

        CursorTy redir = loc_2591 + 1;

        *(CursorTy *) redir = chunk_start_282;
        loc_2591 = chunk_start_282;
    }

    TagTyPacked tmpval_8034 = *(TagTyPacked *) b_321_842_1043_1463;
    CursorTy tmpcur_8035 = b_321_842_1043_1463 + 1;


  switch_8079:
    ;
    switch (tmpval_8034) {

      case 0:
        {
            CursorTy jump_3649 = b_321_842_1043_1463 + 1;

            bump_ref_count(end_r_2595, end_r_2592);
            *(TagTyPacked *) loc_2591 = 254;

            CursorTy writetag_4617 = loc_2591 + 1;

            *(CursorTy *) writetag_4617 = a_320_841_1042_1462;

            CursorTy writecur_4618 = writetag_4617 + 8;

            return (CursorCursorCursorProd) {end_r_2595, loc_2591,
                                             writecur_4618};
            break;
        }

      case 1:
        {
            FloatTy tmpval_8040 = *(FloatTy *) tmpcur_8035;
            CursorTy tmpcur_8041 = tmpcur_8035 + sizeof(FloatTy);
            CursorTy jump_3650 = tmpcur_8035 + 4;
            FloatTy fltPkd_1172_1468 = f_322_843_1044_1464 + tmpval_8040;
            CursorTy loc_3378 = loc_2591 + 1;
            CursorTy loc_3379 = loc_3378 + 4;
            CursorCursorCursorProd tmp_struct_278 =
                                    psAdd(end_r_2594, end_r_2593, end_r_2595, loc_3379, fs_323_844_1045_1465, tmpcur_8041);
            CursorTy pvrtmp_8042 = tmp_struct_278.field0;
            CursorTy pvrtmp_8043 = tmp_struct_278.field1;
            CursorTy pvrtmp_8044 = tmp_struct_278.field2;

            *(TagTyPacked *) loc_2591 = 1;

            CursorTy writetag_4623 = loc_2591 + 1;

            *(FloatTy *) writetag_4623 = fltPkd_1172_1468;

            CursorTy writecur_4624 = writetag_4623 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {pvrtmp_8042, loc_2591,
                                             pvrtmp_8044};
            break;
        }

      case 2:
        {
            CursorTy jump_3652 = b_321_842_1043_1463 + 1;

            *(TagTyPacked *) loc_2591 = 2;

            CursorTy writetag_4628 = loc_2591 + 1;

            return (CursorCursorCursorProd) {end_r_2595, loc_2591,
                                             writetag_4628};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_8057 = *(CursorTy *) tmpcur_8035;
            CursorTy tmpaftercur_8058 = tmpcur_8035 + 8;
            CursorTy jump_3839 = tmpcur_8035 + 8;
            CursorCursorCursorProd tmp_struct_279 =
                                    caseFn_840(end_r_2592, end_r_2593, end_r_2594, end_r_2595, loc_2591, a_320_841_1042_1462, tmpcur_8057, f_322_843_1044_1464, fs_323_844_1045_1465);
            CursorTy pvrtmp_8059 = tmp_struct_279.field0;
            CursorTy pvrtmp_8060 = tmp_struct_279.field1;
            CursorTy pvrtmp_8061 = tmp_struct_279.field2;

            return (CursorCursorCursorProd) {pvrtmp_8059, pvrtmp_8060,
                                             pvrtmp_8061};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_8068 = *(CursorTy *) tmpcur_8035;
            CursorTy tmpaftercur_8069 = tmpcur_8035 + 8;
            CursorCursorCursorProd tmp_struct_280 =
                                    caseFn_840(end_r_2592, end_r_2593, end_r_2594, end_r_2595, loc_2591, a_320_841_1042_1462, tmpcur_8068, f_322_843_1044_1464, fs_323_844_1045_1465);
            CursorTy pvrtmp_8070 = tmp_struct_280.field0;
            CursorTy pvrtmp_8071 = tmp_struct_280.field1;
            CursorTy pvrtmp_8072 = tmp_struct_280.field2;

            return (CursorCursorCursorProd) {pvrtmp_8070, pvrtmp_8071,
                                             pvrtmp_8072};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_8034");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Ps(CursorTy end_r_2598,
                                                          CursorTy end_r_2599,
                                                          CursorTy loc_2597,
                                                          CursorTy arg_2420)
{
    if (loc_2597 + 32 > end_r_2599) {
        ChunkTy new_chunk_287 = alloc_chunk(end_r_2599);
        CursorTy chunk_start_288 = new_chunk_287.chunk_start;
        CursorTy chunk_end_289 = new_chunk_287.chunk_end;

        end_r_2599 = chunk_end_289;
        *(TagTyPacked *) loc_2597 = 255;

        CursorTy redir = loc_2597 + 1;

        *(CursorTy *) redir = chunk_start_288;
        loc_2597 = chunk_start_288;
    }

    TagTyPacked tmpval_8080 = *(TagTyPacked *) arg_2420;
    CursorTy tmpcur_8081 = arg_2420 + 1;


  switch_8128:
    ;
    switch (tmpval_8080) {

      case 0:
        {
            CursorTy jump_3654 = arg_2420 + 1;

            *(TagTyPacked *) loc_2597 = 0;

            CursorTy writetag_4637 = loc_2597 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2599, jump_3654,
                                                   loc_2597, writetag_4637};
            break;
        }

      case 1:
        {
            FloatTy tmpval_8086 = *(FloatTy *) tmpcur_8081;
            CursorTy tmpcur_8087 = tmpcur_8081 + sizeof(FloatTy);
            CursorTy jump_3656 = tmpcur_8081 + 4;
            CursorTy loc_3392 = loc_2597 + 1;
            CursorTy loc_3393 = loc_3392 + 4;
            CursorCursorCursorCursorProd tmp_struct_284 =
                                          _add_size_and_rel_offsets_Ps(end_r_2598, end_r_2599, loc_3393, tmpcur_8087);
            CursorTy pvrtmp_8088 = tmp_struct_284.field0;
            CursorTy pvrtmp_8089 = tmp_struct_284.field1;
            CursorTy pvrtmp_8090 = tmp_struct_284.field2;
            CursorTy pvrtmp_8091 = tmp_struct_284.field3;

            *(TagTyPacked *) loc_2597 = 1;

            CursorTy writetag_4642 = loc_2597 + 1;

            *(FloatTy *) writetag_4642 = tmpval_8086;

            CursorTy writecur_4643 = writetag_4642 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_8088, pvrtmp_8089,
                                                   loc_2597, pvrtmp_8091};
            break;
        }

      case 2:
        {
            CursorTy jump_3659 = arg_2420 + 1;

            *(TagTyPacked *) loc_2597 = 2;

            CursorTy writetag_4647 = loc_2597 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2599, jump_3659,
                                                   loc_2597, writetag_4647};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_8104 = *(CursorTy *) tmpcur_8081;
            CursorTy tmpaftercur_8105 = tmpcur_8081 + 8;
            CursorTy jump_3844 = tmpcur_8081 + 8;
            CursorCursorCursorCursorProd tmp_struct_285 =
                                          _add_size_and_rel_offsets_Ps(end_r_2598, end_r_2599, loc_2597, tmpcur_8104);
            CursorTy pvrtmp_8106 = tmp_struct_285.field0;
            CursorTy pvrtmp_8107 = tmp_struct_285.field1;
            CursorTy pvrtmp_8108 = tmp_struct_285.field2;
            CursorTy pvrtmp_8109 = tmp_struct_285.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_8106, jump_3844,
                                                   pvrtmp_8108, pvrtmp_8109};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_8116 = *(CursorTy *) tmpcur_8081;
            CursorTy tmpaftercur_8117 = tmpcur_8081 + 8;
            CursorCursorCursorCursorProd tmp_struct_286 =
                                          _add_size_and_rel_offsets_Ps(end_r_2598, end_r_2599, loc_2597, tmpcur_8116);
            CursorTy pvrtmp_8118 = tmp_struct_286.field0;
            CursorTy pvrtmp_8119 = tmp_struct_286.field1;
            CursorTy pvrtmp_8120 = tmp_struct_286.field2;
            CursorTy pvrtmp_8121 = tmp_struct_286.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_8118, pvrtmp_8119,
                                                   pvrtmp_8120, pvrtmp_8121};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_8080");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_PList1(CursorTy end_r_2602,
                                                              CursorTy end_r_2603,
                                                              CursorTy loc_2601,
                                                              CursorTy arg_2425)
{
    if (loc_2601 + 32 > end_r_2603) {
        ChunkTy new_chunk_293 = alloc_chunk(end_r_2603);
        CursorTy chunk_start_294 = new_chunk_293.chunk_start;
        CursorTy chunk_end_295 = new_chunk_293.chunk_end;

        end_r_2603 = chunk_end_295;
        *(TagTyPacked *) loc_2601 = 255;

        CursorTy redir = loc_2601 + 1;

        *(CursorTy *) redir = chunk_start_294;
        loc_2601 = chunk_start_294;
    }

    TagTyPacked tmpval_8129 = *(TagTyPacked *) arg_2425;
    CursorTy tmpcur_8130 = arg_2425 + 1;


  switch_8177:
    ;
    switch (tmpval_8129) {

      case 0:
        {
            CursorTy jump_3661 = arg_2425 + 1;

            *(TagTyPacked *) loc_2601 = 0;

            CursorTy writetag_4656 = loc_2601 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2603, jump_3661,
                                                   loc_2601, writetag_4656};
            break;
        }

      case 1:
        {
            FloatTy tmpval_8135 = *(FloatTy *) tmpcur_8130;
            CursorTy tmpcur_8136 = tmpcur_8130 + sizeof(FloatTy);
            CursorTy jump_3663 = tmpcur_8130 + 4;
            CursorTy loc_3406 = loc_2601 + 1;
            CursorTy loc_3407 = loc_3406 + 4;
            CursorCursorCursorCursorProd tmp_struct_290 =
                                          _add_size_and_rel_offsets_PList1(end_r_2602, end_r_2603, loc_3407, tmpcur_8136);
            CursorTy pvrtmp_8137 = tmp_struct_290.field0;
            CursorTy pvrtmp_8138 = tmp_struct_290.field1;
            CursorTy pvrtmp_8139 = tmp_struct_290.field2;
            CursorTy pvrtmp_8140 = tmp_struct_290.field3;

            *(TagTyPacked *) loc_2601 = 1;

            CursorTy writetag_4661 = loc_2601 + 1;

            *(FloatTy *) writetag_4661 = tmpval_8135;

            CursorTy writecur_4662 = writetag_4661 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_8137, pvrtmp_8138,
                                                   loc_2601, pvrtmp_8140};
            break;
        }

      case 2:
        {
            CursorTy jump_3666 = arg_2425 + 1;

            *(TagTyPacked *) loc_2601 = 2;

            CursorTy writetag_4666 = loc_2601 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2603, jump_3666,
                                                   loc_2601, writetag_4666};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_8153 = *(CursorTy *) tmpcur_8130;
            CursorTy tmpaftercur_8154 = tmpcur_8130 + 8;
            CursorTy jump_3850 = tmpcur_8130 + 8;
            CursorCursorCursorCursorProd tmp_struct_291 =
                                          _add_size_and_rel_offsets_PList1(end_r_2602, end_r_2603, loc_2601, tmpcur_8153);
            CursorTy pvrtmp_8155 = tmp_struct_291.field0;
            CursorTy pvrtmp_8156 = tmp_struct_291.field1;
            CursorTy pvrtmp_8157 = tmp_struct_291.field2;
            CursorTy pvrtmp_8158 = tmp_struct_291.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_8155, jump_3850,
                                                   pvrtmp_8157, pvrtmp_8158};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_8165 = *(CursorTy *) tmpcur_8130;
            CursorTy tmpaftercur_8166 = tmpcur_8130 + 8;
            CursorCursorCursorCursorProd tmp_struct_292 =
                                          _add_size_and_rel_offsets_PList1(end_r_2602, end_r_2603, loc_2601, tmpcur_8165);
            CursorTy pvrtmp_8167 = tmp_struct_292.field0;
            CursorTy pvrtmp_8168 = tmp_struct_292.field1;
            CursorTy pvrtmp_8169 = tmp_struct_292.field2;
            CursorTy pvrtmp_8170 = tmp_struct_292.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_8167, pvrtmp_8168,
                                                   pvrtmp_8169, pvrtmp_8170};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_8129");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(6078,
               "benchrunner: select benchmark to run with --bench-prog\n");
    add_symbol(6079, "OK\n");
    add_symbol(6080, "Err\n");
    add_symbol(6081, ")");
    add_symbol(6082, "(Pz");
    add_symbol(6083, "(OpP");
    add_symbol(6084, "(Nil1");
    add_symbol(6085, "(ErrorL");
    add_symbol(6086, "(Error");
    add_symbol(6087, "(Cons1");
    add_symbol(6088, " ->r ");
    add_symbol(6089, " ->i ");
    add_symbol(6090, " ");

    BoolTy fltIf_1048_1174 = strcmp("ts", global_bench_prog_param) == 0;

    if (fltIf_1048_1174) {
        unsigned char tailapp_3668 =  bench_ts();

        printf("'#()");
        printf("\n");
        free_symtable();
        return 0;
    } else {
        BoolTy fltIf_1049_1175 = strcmp("psb", global_bench_prog_param) == 0;

        if (fltIf_1049_1175) {
            unsigned char tailapp_3669 =  bench_psb();

            printf("'#()");
            printf("\n");
            free_symtable();
            return 0;
        } else {
            BoolTy fltIf_1050_1176 = strcmp("psc", global_bench_prog_param) ==
                   0;

            if (fltIf_1050_1176) {
                unsigned char tailapp_3670 =  bench_psc();

                printf("'#()");
                printf("\n");
                free_symtable();
                return 0;
            } else {
                unsigned char wildcard__232_235_845_1177 = print_symbol(6078);

                printf("'#()");
                printf("\n");
                free_symtable();
                return 0;
            }
        }
    }
}
