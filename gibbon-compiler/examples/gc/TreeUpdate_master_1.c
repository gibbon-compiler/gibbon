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
typedef struct Int64CursorProd_struct {
            IntTy field0;
            CursorTy field1;
        } Int64CursorProd;
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
typedef struct VectorProd_struct {
            VectorTy *field0;
        } VectorProd;
CursorCursorCursorProd loop(CursorTy end_r_1445, CursorTy end_r_1446,
                            CursorTy loc_1444, VectorTy *nums_94_781_940,
                            IntTy idx_95_782_941, CursorTy tr_96_783_942,
                            IntTy n_97_784_943);
CursorCursorCursorProd treeDelete(CursorTy end_r_1449, CursorTy end_r_1450,
                                  CursorTy loc_1448, CursorTy tr_100_787_959,
                                  IntTy n_101_788_960);
IntTy minTree(CursorTy end_r_1452, CursorTy tr_107_794_975);
CursorCursorCursorProd treeInsert(CursorTy end_r_1455, CursorTy end_r_1456,
                                  CursorTy loc_1454, CursorTy tr_116_799_980,
                                  IntTy n_117_800_981);
CursorInt64Prod countnodes(CursorTy end_r_1458, CursorTy tr_127_810_1000);
CursorCursorCursorProd helper(CursorTy end_r_1460, CursorTy loc_1459,
                              IntTy s_132_815_1008, IntTy e_133_816_1009);
CursorCursorCursorCursorProd _copy_SearchTree(CursorTy end_r_1463,
                                              CursorTy end_r_1464,
                                              CursorTy loc_1462,
                                              CursorTy arg_723_839_1019);
CursorCursorCursorCursorProd _copy_without_ptrs_SearchTree(CursorTy end_r_1467,
                                                           CursorTy end_r_1468,
                                                           CursorTy loc_1466,
                                                           CursorTy arg_732_848_1028);
CursorProd _traverse_SearchTree(CursorTy end_r_1470, CursorTy arg_741_857_1037);
CursorProd _print_SearchTree(CursorTy end_r_1472, CursorTy arg_750_864_1044);
IntTy caseFn_769(CursorTy end_r_1474, CursorTy l_110_770_883_1063,
                 IntTy n_109_771_884_1064);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_SearchTree(CursorTy end_r_1477, CursorTy end_r_1478,
                                     CursorTy loc_1476, CursorTy arg_1420);
CursorCursorCursorProd loop(CursorTy end_r_1445, CursorTy end_r_1446,
                            CursorTy loc_1444, VectorTy *nums_94_781_940,
                            IntTy idx_95_782_941, CursorTy tr_96_783_942,
                            IntTy n_97_784_943)
{
    if (loc_1444 + 32 > end_r_1446) {
        ChunkTy new_chunk_5 = alloc_chunk(end_r_1446);
        CursorTy chunk_start_6 = new_chunk_5.chunk_start;
        CursorTy chunk_end_7 = new_chunk_5.chunk_end;

        end_r_1446 = chunk_end_7;
        *(TagTyPacked *) loc_1444 = 255;

        CursorTy redir = loc_1444 + 1;

        *(CursorTy *) redir = chunk_start_6;
        loc_1444 = chunk_start_6;
    }

    BoolTy fltIf_892_944 = n_97_784_943 == 0;

    if (fltIf_892_944) {
        bump_ref_count(end_r_1446, end_r_1445);
        *(TagTyPacked *) loc_1444 = 254;

        CursorTy writetag_1992 = loc_1444 + 1;

        *(CursorTy *) writetag_1992 = tr_96_783_942;

        CursorTy writecur_1993 = writetag_1992 + 8;

        return (CursorCursorCursorProd) {end_r_1446, loc_1444, writecur_1993};
    } else {
        IntTy fltPrm_893_945 = idx_95_782_941 + 1;
        IntTy fltPrm_894_947 = vector_length(nums_94_781_940);
        IntTy idx1_98_785_948 = fltPrm_893_945 % fltPrm_894_947;
        IntTy *tmp_4;

        tmp_4 = (IntTy *) vector_nth(nums_94_781_940, idx1_98_785_948);

        IntTy j_99_786_951 = *tmp_4;
        IntTy fltPrm_896_952 = j_99_786_951 % 2;
        BoolTy fltIf_895_953 = fltPrm_896_952 == 0;

        if (fltIf_895_953) {
            RegionTy *region_2614 = alloc_region(global_init_inf_buf_size);
            CursorTy r_1499 = region_2614->reg_heap;
            IntTy sizeof_end_r_1499_2615 = global_init_inf_buf_size;
            CursorTy end_r_1499 = r_1499 + sizeof_end_r_1499_2615;
            CursorCursorCursorProd tmp_struct_0 =
                                    treeInsert(end_r_1445, end_r_1499, r_1499, tr_96_783_942, j_99_786_951);
            CursorTy pvrtmp_2616 = tmp_struct_0.field0;
            CursorTy pvrtmp_2617 = tmp_struct_0.field1;
            CursorTy pvrtmp_2618 = tmp_struct_0.field2;
            IntTy fltAppE_898_955 = n_97_784_943 - 1;
            CursorCursorCursorProd tmp_struct_1 =
                                    loop(pvrtmp_2616, end_r_1446, loc_1444, nums_94_781_940, idx1_98_785_948, pvrtmp_2617, fltAppE_898_955);
            CursorTy pvrtmp_2623 = tmp_struct_1.field0;
            CursorTy pvrtmp_2624 = tmp_struct_1.field1;
            CursorTy pvrtmp_2625 = tmp_struct_1.field2;

            free_region(end_r_1499);
            return (CursorCursorCursorProd) {pvrtmp_2623, pvrtmp_2624,
                                             pvrtmp_2625};
        } else {
            RegionTy *region_2632 = alloc_region(global_init_inf_buf_size);
            CursorTy r_1508 = region_2632->reg_heap;
            IntTy sizeof_end_r_1508_2633 = global_init_inf_buf_size;
            CursorTy end_r_1508 = r_1508 + sizeof_end_r_1508_2633;
            IntTy fltAppE_900_956 = j_99_786_951 - 1;
            CursorCursorCursorProd tmp_struct_2 =
                                    treeDelete(end_r_1445, end_r_1508, r_1508, tr_96_783_942, fltAppE_900_956);
            CursorTy pvrtmp_2634 = tmp_struct_2.field0;
            CursorTy pvrtmp_2635 = tmp_struct_2.field1;
            CursorTy pvrtmp_2636 = tmp_struct_2.field2;
            IntTy fltAppE_901_958 = n_97_784_943 - 1;
            CursorCursorCursorProd tmp_struct_3 =
                                    loop(pvrtmp_2634, end_r_1446, loc_1444, nums_94_781_940, idx1_98_785_948, pvrtmp_2635, fltAppE_901_958);
            CursorTy pvrtmp_2641 = tmp_struct_3.field0;
            CursorTy pvrtmp_2642 = tmp_struct_3.field1;
            CursorTy pvrtmp_2643 = tmp_struct_3.field2;

            free_region(end_r_1508);
            return (CursorCursorCursorProd) {pvrtmp_2641, pvrtmp_2642,
                                             pvrtmp_2643};
        }
    }
}
CursorCursorCursorProd treeDelete(CursorTy end_r_1449, CursorTy end_r_1450,
                                  CursorTy loc_1448, CursorTy tr_100_787_959,
                                  IntTy n_101_788_960)
{
    if (loc_1448 + 32 > end_r_1450) {
        ChunkTy new_chunk_13 = alloc_chunk(end_r_1450);
        CursorTy chunk_start_14 = new_chunk_13.chunk_start;
        CursorTy chunk_end_15 = new_chunk_13.chunk_end;

        end_r_1450 = chunk_end_15;
        *(TagTyPacked *) loc_1448 = 255;

        CursorTy redir = loc_1448 + 1;

        *(CursorTy *) redir = chunk_start_14;
        loc_1448 = chunk_start_14;
    }

    TagTyPacked tmpval_2650 = *(TagTyPacked *) tr_100_787_959;
    CursorTy tmpcur_2651 = tr_100_787_959 + 1;


  switch_2731:
    ;
    switch (tmpval_2650) {

      case 0:
        {
            CursorTy jump_1815 = tr_100_787_959 + 1;

            *(TagTyPacked *) loc_1448 = 0;

            CursorTy writetag_2000 = loc_1448 + 1;

            return (CursorCursorCursorProd) {end_r_1450, loc_1448,
                                             writetag_2000};
            break;
        }

      case 1:
        {
            IntTy tmpval_2656 = *(IntTy *) tmpcur_2651;
            CursorTy tmpcur_2657 = tmpcur_2651 + sizeof(IntTy);
            CursorTy jump_1817 = tmpcur_2651 + 8;
            BoolTy fltIf_902_962 = tmpval_2656 == n_101_788_960;

            if (fltIf_902_962) {
                *(TagTyPacked *) loc_1448 = 0;

                CursorTy writetag_2004 = loc_1448 + 1;

                return (CursorCursorCursorProd) {end_r_1450, loc_1448,
                                                 writetag_2004};
            } else {
                *(TagTyPacked *) loc_1448 = 1;

                CursorTy writetag_2006 = loc_1448 + 1;

                *(IntTy *) writetag_2006 = tmpval_2656;

                CursorTy writecur_2007 = writetag_2006 + sizeof(IntTy);

                return (CursorCursorCursorProd) {end_r_1450, loc_1448,
                                                 writecur_2007};
            }
            break;
        }

      case 3:
        {
            CursorTy tmpcur_2666 = *(CursorTy *) tmpcur_2651;
            CursorTy tmpaftercur_2667 = tmpcur_2651 + 8;
            IntTy tmpval_2668 = *(IntTy *) tmpaftercur_2667;
            CursorTy tmpcur_2669 = tmpaftercur_2667 + sizeof(IntTy);
            CursorTy jump_1821 = tmpaftercur_2667 + 8;
            CursorTy jump_1820 = tmpcur_2651 + 8;
            BoolTy fltIf_903_966 = tmpval_2668 == n_101_788_960;

            if (fltIf_903_966) {
                IntTy k_106_793_967 =  minTree(end_r_1449, tmpcur_2666);
                CursorTy loc_1529 = loc_1448 + 1;
                CursorTy loc_1530 = loc_1529 + 8;
                CursorTy loc_1531 = loc_1530 + 8;

                bump_ref_count(end_r_1450, end_r_1449);
                *(TagTyPacked *) loc_1531 = 254;

                CursorTy writetag_2012 = loc_1531 + 1;

                *(CursorTy *) writetag_2012 = tmpcur_2669;

                CursorTy writecur_2013 = writetag_2012 + 8;
                CursorCursorCursorProd tmp_struct_8 =
                                        treeDelete(end_r_1449, end_r_1450, writecur_2013, tmpcur_2666, k_106_793_967);
                CursorTy pvrtmp_2672 = tmp_struct_8.field0;
                CursorTy pvrtmp_2673 = tmp_struct_8.field1;
                CursorTy pvrtmp_2674 = tmp_struct_8.field2;

                *(TagTyPacked *) loc_1448 = 3;

                CursorTy writetag_2016 = loc_1448 + 1;

                *(CursorTy *) writetag_2016 = writecur_2013;

                CursorTy writecur_2017 = writetag_2016 + 8;

                *(IntTy *) writecur_2017 = k_106_793_967;

                CursorTy writecur_2018 = writecur_2017 + sizeof(IntTy);

                return (CursorCursorCursorProd) {pvrtmp_2672, loc_1448,
                                                 pvrtmp_2674};
            } else {
                BoolTy fltIf_906_970 = tmpval_2668 < n_101_788_960;

                if (fltIf_906_970) {
                    CursorTy loc_1529 = loc_1448 + 1;
                    CursorTy loc_1530 = loc_1529 + 8;
                    CursorTy loc_1531 = loc_1530 + 8;

                    bump_ref_count(end_r_1450, end_r_1449);
                    *(TagTyPacked *) loc_1531 = 254;

                    CursorTy writetag_2022 = loc_1531 + 1;

                    *(CursorTy *) writetag_2022 = tmpcur_2669;

                    CursorTy writecur_2023 = writetag_2022 + 8;
                    CursorCursorCursorProd tmp_struct_9 =
                                            treeDelete(end_r_1449, end_r_1450, writecur_2023, tmpcur_2666, n_101_788_960);
                    CursorTy pvrtmp_2685 = tmp_struct_9.field0;
                    CursorTy pvrtmp_2686 = tmp_struct_9.field1;
                    CursorTy pvrtmp_2687 = tmp_struct_9.field2;

                    *(TagTyPacked *) loc_1448 = 3;

                    CursorTy writetag_2026 = loc_1448 + 1;

                    *(CursorTy *) writetag_2026 = writecur_2023;

                    CursorTy writecur_2027 = writetag_2026 + 8;

                    *(IntTy *) writecur_2027 = tmpval_2668;

                    CursorTy writecur_2028 = writecur_2027 + sizeof(IntTy);

                    return (CursorCursorCursorProd) {pvrtmp_2685, loc_1448,
                                                     pvrtmp_2687};
                } else {
                    CursorTy loc_1529 = loc_1448 + 1;
                    CursorTy loc_1530 = loc_1529 + 8;
                    CursorTy loc_1531 = loc_1530 + 8;
                    CursorCursorCursorProd tmp_struct_10 =
                                            treeDelete(end_r_1449, end_r_1450, loc_1531, tmpcur_2669, n_101_788_960);
                    CursorTy pvrtmp_2696 = tmp_struct_10.field0;
                    CursorTy pvrtmp_2697 = tmp_struct_10.field1;
                    CursorTy pvrtmp_2698 = tmp_struct_10.field2;

                    bump_ref_count(end_r_1450, end_r_1449);
                    *(TagTyPacked *) pvrtmp_2698 = 254;

                    CursorTy writetag_2033 = pvrtmp_2698 + 1;

                    *(CursorTy *) writetag_2033 = tmpcur_2666;

                    CursorTy writecur_2034 = writetag_2033 + 8;

                    *(TagTyPacked *) loc_1448 = 3;

                    CursorTy writetag_2036 = loc_1448 + 1;

                    *(CursorTy *) writetag_2036 = pvrtmp_2698;

                    CursorTy writecur_2037 = writetag_2036 + 8;

                    *(IntTy *) writecur_2037 = tmpval_2668;

                    CursorTy writecur_2038 = writecur_2037 + sizeof(IntTy);

                    return (CursorCursorCursorProd) {pvrtmp_2696, loc_1448,
                                                     writecur_2034};
                }
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2709 = *(CursorTy *) tmpcur_2651;
            CursorTy tmpaftercur_2710 = tmpcur_2651 + 8;
            CursorTy jump_1909 = tmpcur_2651 + 8;
            CursorCursorCursorProd tmp_struct_11 =
                                    treeDelete(end_r_1449, end_r_1450, loc_1448, tmpcur_2709, n_101_788_960);
            CursorTy pvrtmp_2711 = tmp_struct_11.field0;
            CursorTy pvrtmp_2712 = tmp_struct_11.field1;
            CursorTy pvrtmp_2713 = tmp_struct_11.field2;

            return (CursorCursorCursorProd) {pvrtmp_2711, pvrtmp_2712,
                                             pvrtmp_2713};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2720 = *(CursorTy *) tmpcur_2651;
            CursorTy tmpaftercur_2721 = tmpcur_2651 + 8;
            CursorCursorCursorProd tmp_struct_12 =
                                    treeDelete(end_r_1449, end_r_1450, loc_1448, tmpcur_2720, n_101_788_960);
            CursorTy pvrtmp_2722 = tmp_struct_12.field0;
            CursorTy pvrtmp_2723 = tmp_struct_12.field1;
            CursorTy pvrtmp_2724 = tmp_struct_12.field2;

            return (CursorCursorCursorProd) {pvrtmp_2722, pvrtmp_2723,
                                             pvrtmp_2724};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2650");
            exit(1);
        }
    }
}
IntTy minTree(CursorTy end_r_1452, CursorTy tr_107_794_975)
{
    TagTyPacked tmpval_2732 = *(TagTyPacked *) tr_107_794_975;
    CursorTy tmpcur_2733 = tr_107_794_975 + 1;


  switch_2744:
    ;
    switch (tmpval_2732) {

      case 0:
        {
            CursorTy jump_1826 = tr_107_794_975 + 1;

            return 0;
            break;
        }

      case 1:
        {
            IntTy tmpval_2734 = *(IntTy *) tmpcur_2733;
            CursorTy tmpcur_2735 = tmpcur_2733 + sizeof(IntTy);
            CursorTy jump_1827 = tmpcur_2733 + 8;

            return tmpval_2734;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_2736 = *(CursorTy *) tmpcur_2733;
            CursorTy tmpaftercur_2737 = tmpcur_2733 + 8;
            IntTy tmpval_2738 = *(IntTy *) tmpaftercur_2737;
            CursorTy tmpcur_2739 = tmpaftercur_2737 + sizeof(IntTy);
            CursorTy jump_1829 = tmpaftercur_2737 + 8;
            CursorTy jump_1828 = tmpcur_2733 + 8;
            IntTy tailapp_1830 =
                   caseFn_769(end_r_1452, tmpcur_2739, tmpval_2738);

            return tailapp_1830;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2740 = *(CursorTy *) tmpcur_2733;
            CursorTy tmpaftercur_2741 = tmpcur_2733 + 8;
            CursorTy jump_1914 = tmpcur_2733 + 8;
            IntTy call_1915 =  minTree(end_r_1452, tmpcur_2740);

            return call_1915;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2742 = *(CursorTy *) tmpcur_2733;
            CursorTy tmpaftercur_2743 = tmpcur_2733 + 8;
            IntTy call_1915 =  minTree(end_r_1452, tmpcur_2742);

            return call_1915;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2732");
            exit(1);
        }
    }
}
CursorCursorCursorProd treeInsert(CursorTy end_r_1455, CursorTy end_r_1456,
                                  CursorTy loc_1454, CursorTy tr_116_799_980,
                                  IntTy n_117_800_981)
{
    if (loc_1454 + 32 > end_r_1456) {
        ChunkTy new_chunk_20 = alloc_chunk(end_r_1456);
        CursorTy chunk_start_21 = new_chunk_20.chunk_start;
        CursorTy chunk_end_22 = new_chunk_20.chunk_end;

        end_r_1456 = chunk_end_22;
        *(TagTyPacked *) loc_1454 = 255;

        CursorTy redir = loc_1454 + 1;

        *(CursorTy *) redir = chunk_start_21;
        loc_1454 = chunk_start_21;
    }

    TagTyPacked tmpval_2745 = *(TagTyPacked *) tr_116_799_980;
    CursorTy tmpcur_2746 = tr_116_799_980 + 1;


  switch_2833:
    ;
    switch (tmpval_2745) {

      case 0:
        {
            CursorTy jump_1831 = tr_116_799_980 + 1;

            *(TagTyPacked *) loc_1454 = 1;

            CursorTy writetag_2059 = loc_1454 + 1;

            *(IntTy *) writetag_2059 = n_117_800_981;

            CursorTy writecur_2060 = writetag_2059 + sizeof(IntTy);

            return (CursorCursorCursorProd) {end_r_1456, loc_1454,
                                             writecur_2060};
            break;
        }

      case 1:
        {
            IntTy tmpval_2751 = *(IntTy *) tmpcur_2746;
            CursorTy tmpcur_2752 = tmpcur_2746 + sizeof(IntTy);
            CursorTy jump_1833 = tmpcur_2746 + 8;
            BoolTy fltIf_911_983 = n_117_800_981 == tmpval_2751;

            if (fltIf_911_983) {
                *(TagTyPacked *) loc_1454 = 1;

                CursorTy writetag_2064 = loc_1454 + 1;

                *(IntTy *) writetag_2064 = tmpval_2751;

                CursorTy writecur_2065 = writetag_2064 + sizeof(IntTy);

                return (CursorCursorCursorProd) {end_r_1456, loc_1454,
                                                 writecur_2065};
            } else {
                BoolTy fltIf_912_984 = n_117_800_981 < tmpval_2751;

                if (fltIf_912_984) {
                    CursorTy loc_1595 = loc_1454 + 1;
                    CursorTy loc_1596 = loc_1595 + 8;
                    CursorTy loc_1597 = loc_1596 + 8;

                    *(TagTyPacked *) loc_1597 = 1;

                    CursorTy writetag_2067 = loc_1597 + 1;

                    *(IntTy *) writetag_2067 = n_117_800_981;

                    CursorTy writecur_2068 = writetag_2067 + sizeof(IntTy);

                    *(TagTyPacked *) writecur_2068 = 0;

                    CursorTy writetag_2070 = writecur_2068 + 1;

                    *(TagTyPacked *) loc_1454 = 3;

                    CursorTy writetag_2072 = loc_1454 + 1;

                    *(CursorTy *) writetag_2072 = writecur_2068;

                    CursorTy writecur_2073 = writetag_2072 + 8;

                    *(IntTy *) writecur_2073 = tmpval_2751;

                    CursorTy writecur_2074 = writecur_2073 + sizeof(IntTy);

                    return (CursorCursorCursorProd) {end_r_1456, loc_1454,
                                                     writetag_2070};
                } else {
                    CursorTy loc_1595 = loc_1454 + 1;
                    CursorTy loc_1596 = loc_1595 + 8;
                    CursorTy loc_1597 = loc_1596 + 8;

                    *(TagTyPacked *) loc_1597 = 0;

                    CursorTy writetag_2078 = loc_1597 + 1;

                    *(TagTyPacked *) writetag_2078 = 1;

                    CursorTy writetag_2080 = writetag_2078 + 1;

                    *(IntTy *) writetag_2080 = n_117_800_981;

                    CursorTy writecur_2081 = writetag_2080 + sizeof(IntTy);

                    *(TagTyPacked *) loc_1454 = 3;

                    CursorTy writetag_2083 = loc_1454 + 1;

                    *(CursorTy *) writetag_2083 = writetag_2078;

                    CursorTy writecur_2084 = writetag_2083 + 8;

                    *(IntTy *) writecur_2084 = tmpval_2751;

                    CursorTy writecur_2085 = writecur_2084 + sizeof(IntTy);

                    return (CursorCursorCursorProd) {end_r_1456, loc_1454,
                                                     writecur_2081};
                }
            }
            break;
        }

      case 3:
        {
            CursorTy tmpcur_2773 = *(CursorTy *) tmpcur_2746;
            CursorTy tmpaftercur_2774 = tmpcur_2746 + 8;
            IntTy tmpval_2775 = *(IntTy *) tmpaftercur_2774;
            CursorTy tmpcur_2776 = tmpaftercur_2774 + sizeof(IntTy);
            CursorTy jump_1838 = tmpaftercur_2774 + 8;
            CursorTy jump_1837 = tmpcur_2746 + 8;
            BoolTy fltIf_917_992 = tmpval_2775 == n_117_800_981;

            if (fltIf_917_992) {
                CursorTy loc_1595 = loc_1454 + 1;
                CursorTy loc_1596 = loc_1595 + 8;
                CursorTy loc_1597 = loc_1596 + 8;

                bump_ref_count(end_r_1456, end_r_1455);
                *(TagTyPacked *) loc_1597 = 254;

                CursorTy writetag_2092 = loc_1597 + 1;

                *(CursorTy *) writetag_2092 = tmpcur_2776;

                CursorTy writecur_2093 = writetag_2092 + 8;

                bump_ref_count(end_r_1456, end_r_1455);
                *(TagTyPacked *) writecur_2093 = 254;

                CursorTy writetag_2095 = writecur_2093 + 1;

                *(CursorTy *) writetag_2095 = tmpcur_2773;

                CursorTy writecur_2096 = writetag_2095 + 8;

                *(TagTyPacked *) loc_1454 = 3;

                CursorTy writetag_2098 = loc_1454 + 1;

                *(CursorTy *) writetag_2098 = writecur_2093;

                CursorTy writecur_2099 = writetag_2098 + 8;

                *(IntTy *) writecur_2099 = tmpval_2775;

                CursorTy writecur_2100 = writecur_2099 + sizeof(IntTy);

                return (CursorCursorCursorProd) {end_r_1456, loc_1454,
                                                 writecur_2096};
            } else {
                BoolTy fltIf_920_995 = n_117_800_981 < tmpval_2775;

                if (fltIf_920_995) {
                    CursorTy loc_1595 = loc_1454 + 1;
                    CursorTy loc_1596 = loc_1595 + 8;
                    CursorTy loc_1597 = loc_1596 + 8;

                    bump_ref_count(end_r_1456, end_r_1455);
                    *(TagTyPacked *) loc_1597 = 254;

                    CursorTy writetag_2104 = loc_1597 + 1;

                    *(CursorTy *) writetag_2104 = tmpcur_2776;

                    CursorTy writecur_2105 = writetag_2104 + 8;
                    CursorCursorCursorProd tmp_struct_16 =
                                            treeInsert(end_r_1455, end_r_1456, writecur_2105, tmpcur_2773, n_117_800_981);
                    CursorTy pvrtmp_2787 = tmp_struct_16.field0;
                    CursorTy pvrtmp_2788 = tmp_struct_16.field1;
                    CursorTy pvrtmp_2789 = tmp_struct_16.field2;

                    *(TagTyPacked *) loc_1454 = 3;

                    CursorTy writetag_2108 = loc_1454 + 1;

                    *(CursorTy *) writetag_2108 = writecur_2105;

                    CursorTy writecur_2109 = writetag_2108 + 8;

                    *(IntTy *) writecur_2109 = tmpval_2775;

                    CursorTy writecur_2110 = writecur_2109 + sizeof(IntTy);

                    return (CursorCursorCursorProd) {pvrtmp_2787, loc_1454,
                                                     pvrtmp_2789};
                } else {
                    CursorTy loc_1595 = loc_1454 + 1;
                    CursorTy loc_1596 = loc_1595 + 8;
                    CursorTy loc_1597 = loc_1596 + 8;
                    CursorCursorCursorProd tmp_struct_17 =
                                            treeInsert(end_r_1455, end_r_1456, loc_1597, tmpcur_2776, n_117_800_981);
                    CursorTy pvrtmp_2798 = tmp_struct_17.field0;
                    CursorTy pvrtmp_2799 = tmp_struct_17.field1;
                    CursorTy pvrtmp_2800 = tmp_struct_17.field2;

                    bump_ref_count(end_r_1456, end_r_1455);
                    *(TagTyPacked *) pvrtmp_2800 = 254;

                    CursorTy writetag_2115 = pvrtmp_2800 + 1;

                    *(CursorTy *) writetag_2115 = tmpcur_2773;

                    CursorTy writecur_2116 = writetag_2115 + 8;

                    *(TagTyPacked *) loc_1454 = 3;

                    CursorTy writetag_2118 = loc_1454 + 1;

                    *(CursorTy *) writetag_2118 = pvrtmp_2800;

                    CursorTy writecur_2119 = writetag_2118 + 8;

                    *(IntTy *) writecur_2119 = tmpval_2775;

                    CursorTy writecur_2120 = writecur_2119 + sizeof(IntTy);

                    return (CursorCursorCursorProd) {pvrtmp_2798, loc_1454,
                                                     writecur_2116};
                }
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2811 = *(CursorTy *) tmpcur_2746;
            CursorTy tmpaftercur_2812 = tmpcur_2746 + 8;
            CursorTy jump_1919 = tmpcur_2746 + 8;
            CursorCursorCursorProd tmp_struct_18 =
                                    treeInsert(end_r_1455, end_r_1456, loc_1454, tmpcur_2811, n_117_800_981);
            CursorTy pvrtmp_2813 = tmp_struct_18.field0;
            CursorTy pvrtmp_2814 = tmp_struct_18.field1;
            CursorTy pvrtmp_2815 = tmp_struct_18.field2;

            return (CursorCursorCursorProd) {pvrtmp_2813, pvrtmp_2814,
                                             pvrtmp_2815};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2822 = *(CursorTy *) tmpcur_2746;
            CursorTy tmpaftercur_2823 = tmpcur_2746 + 8;
            CursorCursorCursorProd tmp_struct_19 =
                                    treeInsert(end_r_1455, end_r_1456, loc_1454, tmpcur_2822, n_117_800_981);
            CursorTy pvrtmp_2824 = tmp_struct_19.field0;
            CursorTy pvrtmp_2825 = tmp_struct_19.field1;
            CursorTy pvrtmp_2826 = tmp_struct_19.field2;

            return (CursorCursorCursorProd) {pvrtmp_2824, pvrtmp_2825,
                                             pvrtmp_2826};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2745");
            exit(1);
        }
    }
}
CursorInt64Prod countnodes(CursorTy end_r_1458, CursorTy tr_127_810_1000)
{
    TagTyPacked tmpval_2834 = *(TagTyPacked *) tr_127_810_1000;
    CursorTy tmpcur_2835 = tr_127_810_1000 + 1;


  switch_2854:
    ;
    switch (tmpval_2834) {

      case 0:
        {
            CursorTy jump_1844 = tr_127_810_1000 + 1;

            return (CursorInt64Prod) {jump_1844, 0};
            break;
        }

      case 1:
        {
            IntTy tmpval_2836 = *(IntTy *) tmpcur_2835;
            CursorTy tmpcur_2837 = tmpcur_2835 + sizeof(IntTy);
            CursorTy jump_1845 = tmpcur_2835 + 8;

            return (CursorInt64Prod) {jump_1845, 1};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_2838 = *(CursorTy *) tmpcur_2835;
            CursorTy tmpaftercur_2839 = tmpcur_2835 + 8;
            IntTy tmpval_2840 = *(IntTy *) tmpaftercur_2839;
            CursorTy tmpcur_2841 = tmpaftercur_2839 + sizeof(IntTy);
            CursorTy jump_1847 = tmpaftercur_2839 + 8;
            CursorTy jump_1846 = tmpcur_2835 + 8;
            CursorInt64Prod tmp_struct_23 =
                             countnodes(end_r_1458, tmpcur_2841);
            CursorTy pvrtmp_2842 = tmp_struct_23.field0;
            IntTy pvrtmp_2843 = tmp_struct_23.field1;
            IntTy fltPrm_925_1006 = 1 + pvrtmp_2843;
            CursorInt64Prod tmp_struct_24 =
                             countnodes(end_r_1458, tmpcur_2838);
            CursorTy pvrtmp_2844 = tmp_struct_24.field0;
            IntTy pvrtmp_2845 = tmp_struct_24.field1;
            IntTy tailprim_1850 = fltPrm_925_1006 + pvrtmp_2845;

            return (CursorInt64Prod) {pvrtmp_2844, tailprim_1850};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2846 = *(CursorTy *) tmpcur_2835;
            CursorTy tmpaftercur_2847 = tmpcur_2835 + 8;
            CursorTy jump_1924 = tmpcur_2835 + 8;
            CursorInt64Prod tmp_struct_25 =
                             countnodes(end_r_1458, tmpcur_2846);
            CursorTy pvrtmp_2848 = tmp_struct_25.field0;
            IntTy pvrtmp_2849 = tmp_struct_25.field1;

            return (CursorInt64Prod) {jump_1924, pvrtmp_2849};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2850 = *(CursorTy *) tmpcur_2835;
            CursorTy tmpaftercur_2851 = tmpcur_2835 + 8;
            CursorInt64Prod tmp_struct_26 =
                             countnodes(end_r_1458, tmpcur_2850);
            CursorTy pvrtmp_2852 = tmp_struct_26.field0;
            IntTy pvrtmp_2853 = tmp_struct_26.field1;

            return (CursorInt64Prod) {pvrtmp_2852, pvrtmp_2853};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2834");
            exit(1);
        }
    }
}
CursorCursorCursorProd helper(CursorTy end_r_1460, CursorTy loc_1459,
                              IntTy s_132_815_1008, IntTy e_133_816_1009)
{
    if (loc_1459 + 32 > end_r_1460) {
        ChunkTy new_chunk_29 = alloc_chunk(end_r_1460);
        CursorTy chunk_start_30 = new_chunk_29.chunk_start;
        CursorTy chunk_end_31 = new_chunk_29.chunk_end;

        end_r_1460 = chunk_end_31;
        *(TagTyPacked *) loc_1459 = 255;

        CursorTy redir = loc_1459 + 1;

        *(CursorTy *) redir = chunk_start_30;
        loc_1459 = chunk_start_30;
    }

    BoolTy fltIf_928_1010 = e_133_816_1009 < s_132_815_1008;

    if (fltIf_928_1010) {
        *(TagTyPacked *) loc_1459 = 0;

        CursorTy writetag_2144 = loc_1459 + 1;

        return (CursorCursorCursorProd) {end_r_1460, loc_1459, writetag_2144};
    } else {
        BoolTy fltIf_929_1011 = s_132_815_1008 == e_133_816_1009;

        if (fltIf_929_1011) {
            *(TagTyPacked *) loc_1459 = 1;

            CursorTy writetag_2146 = loc_1459 + 1;

            *(IntTy *) writetag_2146 = s_132_815_1008;

            CursorTy writecur_2147 = writetag_2146 + sizeof(IntTy);

            return (CursorCursorCursorProd) {end_r_1460, loc_1459,
                                             writecur_2147};
        } else {
            IntTy fltPrm_931_1012 = e_133_816_1009 - s_132_815_1008;
            IntTy fltPrm_930_1013 = fltPrm_931_1012 / 2;
            IntTy m_134_817_1014 = fltPrm_930_1013 + s_132_815_1008;
            IntTy fltAppE_933_1015 = m_134_817_1014 - 1;
            CursorTy loc_1690 = loc_1459 + 1;
            CursorTy loc_1691 = loc_1690 + 8;
            CursorTy loc_1692 = loc_1691 + 8;
            CursorCursorCursorProd tmp_struct_27 =
                                    helper(end_r_1460, loc_1692, s_132_815_1008, fltAppE_933_1015);
            CursorTy pvrtmp_2863 = tmp_struct_27.field0;
            CursorTy pvrtmp_2864 = tmp_struct_27.field1;
            CursorTy pvrtmp_2865 = tmp_struct_27.field2;
            IntTy fltAppE_935_1017 = m_134_817_1014 + 1;
            CursorCursorCursorProd tmp_struct_28 =
                                    helper(pvrtmp_2863, pvrtmp_2865, fltAppE_935_1017, e_133_816_1009);
            CursorTy pvrtmp_2870 = tmp_struct_28.field0;
            CursorTy pvrtmp_2871 = tmp_struct_28.field1;
            CursorTy pvrtmp_2872 = tmp_struct_28.field2;

            *(TagTyPacked *) loc_1459 = 3;

            CursorTy writetag_2151 = loc_1459 + 1;

            *(CursorTy *) writetag_2151 = pvrtmp_2865;

            CursorTy writecur_2152 = writetag_2151 + 8;

            *(IntTy *) writecur_2152 = m_134_817_1014;

            CursorTy writecur_2153 = writecur_2152 + sizeof(IntTy);

            return (CursorCursorCursorProd) {pvrtmp_2870, loc_1459,
                                             pvrtmp_2872};
        }
    }
}
CursorCursorCursorCursorProd _copy_SearchTree(CursorTy end_r_1463,
                                              CursorTy end_r_1464,
                                              CursorTy loc_1462,
                                              CursorTy arg_723_839_1019)
{
    if (loc_1462 + 32 > end_r_1464) {
        ChunkTy new_chunk_36 = alloc_chunk(end_r_1464);
        CursorTy chunk_start_37 = new_chunk_36.chunk_start;
        CursorTy chunk_end_38 = new_chunk_36.chunk_end;

        end_r_1464 = chunk_end_38;
        *(TagTyPacked *) loc_1462 = 255;

        CursorTy redir = loc_1462 + 1;

        *(CursorTy *) redir = chunk_start_37;
        loc_1462 = chunk_start_37;
    }

    TagTyPacked tmpval_2881 = *(TagTyPacked *) arg_723_839_1019;
    CursorTy tmpcur_2882 = arg_723_839_1019 + 1;


  switch_2941:
    ;
    switch (tmpval_2881) {

      case 0:
        {
            CursorTy jump_1854 = arg_723_839_1019 + 1;

            *(TagTyPacked *) loc_1462 = 0;

            CursorTy writetag_2158 = loc_1462 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1464, jump_1854,
                                                   loc_1462, writetag_2158};
            break;
        }

      case 1:
        {
            IntTy tmpval_2887 = *(IntTy *) tmpcur_2882;
            CursorTy tmpcur_2888 = tmpcur_2882 + sizeof(IntTy);
            CursorTy jump_1856 = tmpcur_2882 + 8;

            *(TagTyPacked *) loc_1462 = 1;

            CursorTy writetag_2162 = loc_1462 + 1;

            *(IntTy *) writetag_2162 = tmpval_2887;

            CursorTy writecur_2163 = writetag_2162 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1464, jump_1856,
                                                   loc_1462, writecur_2163};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_2893 = *(CursorTy *) tmpcur_2882;
            CursorTy tmpaftercur_2894 = tmpcur_2882 + 8;
            IntTy tmpval_2895 = *(IntTy *) tmpaftercur_2894;
            CursorTy tmpcur_2896 = tmpaftercur_2894 + sizeof(IntTy);
            CursorTy jump_1859 = tmpaftercur_2894 + 8;
            CursorTy jump_1858 = tmpcur_2882 + 8;
            CursorTy loc_1717 = loc_1462 + 1;
            CursorTy loc_1718 = loc_1717 + 8;
            CursorTy loc_1719 = loc_1718 + 8;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_SearchTree(end_r_1463, end_r_1464, loc_1719, tmpcur_2896);
            CursorTy pvrtmp_2897 = tmp_struct_32.field0;
            CursorTy pvrtmp_2898 = tmp_struct_32.field1;
            CursorTy pvrtmp_2899 = tmp_struct_32.field2;
            CursorTy pvrtmp_2900 = tmp_struct_32.field3;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_SearchTree(end_r_1463, pvrtmp_2897, pvrtmp_2900, tmpcur_2893);
            CursorTy pvrtmp_2905 = tmp_struct_33.field0;
            CursorTy pvrtmp_2906 = tmp_struct_33.field1;
            CursorTy pvrtmp_2907 = tmp_struct_33.field2;
            CursorTy pvrtmp_2908 = tmp_struct_33.field3;

            *(TagTyPacked *) loc_1462 = 3;

            CursorTy writetag_2170 = loc_1462 + 1;

            *(CursorTy *) writetag_2170 = pvrtmp_2900;

            CursorTy writecur_2171 = writetag_2170 + 8;

            *(IntTy *) writecur_2171 = tmpval_2895;

            CursorTy writecur_2172 = writecur_2171 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_2905, pvrtmp_2906,
                                                   loc_1462, pvrtmp_2908};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2917 = *(CursorTy *) tmpcur_2882;
            CursorTy tmpaftercur_2918 = tmpcur_2882 + 8;
            CursorTy jump_1930 = tmpcur_2882 + 8;
            CursorCursorCursorCursorProd tmp_struct_34 =
                                          _copy_SearchTree(end_r_1463, end_r_1464, loc_1462, tmpcur_2917);
            CursorTy pvrtmp_2919 = tmp_struct_34.field0;
            CursorTy pvrtmp_2920 = tmp_struct_34.field1;
            CursorTy pvrtmp_2921 = tmp_struct_34.field2;
            CursorTy pvrtmp_2922 = tmp_struct_34.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2919, jump_1930,
                                                   pvrtmp_2921, pvrtmp_2922};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2929 = *(CursorTy *) tmpcur_2882;
            CursorTy tmpaftercur_2930 = tmpcur_2882 + 8;
            CursorCursorCursorCursorProd tmp_struct_35 =
                                          _copy_SearchTree(end_r_1463, end_r_1464, loc_1462, tmpcur_2929);
            CursorTy pvrtmp_2931 = tmp_struct_35.field0;
            CursorTy pvrtmp_2932 = tmp_struct_35.field1;
            CursorTy pvrtmp_2933 = tmp_struct_35.field2;
            CursorTy pvrtmp_2934 = tmp_struct_35.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2931, pvrtmp_2932,
                                                   pvrtmp_2933, pvrtmp_2934};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2881");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_SearchTree(CursorTy end_r_1467,
                                                           CursorTy end_r_1468,
                                                           CursorTy loc_1466,
                                                           CursorTy arg_732_848_1028)
{
    TagTyPacked tmpval_2942 = *(TagTyPacked *) arg_732_848_1028;
    CursorTy tmpcur_2943 = arg_732_848_1028 + 1;


  switch_3002:
    ;
    switch (tmpval_2942) {

      case 0:
        {
            CursorTy jump_1863 = arg_732_848_1028 + 1;

            *(TagTyPacked *) loc_1466 = 0;

            CursorTy writetag_2183 = loc_1466 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1468, jump_1863,
                                                   loc_1466, writetag_2183};
            break;
        }

      case 1:
        {
            IntTy tmpval_2948 = *(IntTy *) tmpcur_2943;
            CursorTy tmpcur_2949 = tmpcur_2943 + sizeof(IntTy);
            CursorTy jump_1865 = tmpcur_2943 + 8;

            *(TagTyPacked *) loc_1466 = 1;

            CursorTy writetag_2187 = loc_1466 + 1;

            *(IntTy *) writetag_2187 = tmpval_2948;

            CursorTy writecur_2188 = writetag_2187 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1468, jump_1865,
                                                   loc_1466, writecur_2188};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_2954 = *(CursorTy *) tmpcur_2943;
            CursorTy tmpaftercur_2955 = tmpcur_2943 + 8;
            IntTy tmpval_2956 = *(IntTy *) tmpaftercur_2955;
            CursorTy tmpcur_2957 = tmpaftercur_2955 + sizeof(IntTy);
            CursorTy jump_1868 = tmpaftercur_2955 + 8;
            CursorTy jump_1867 = tmpcur_2943 + 8;
            CursorTy loc_1744 = loc_1466 + 1;
            CursorTy loc_1745 = loc_1744 + 8;
            CursorCursorCursorCursorProd tmp_struct_39 =
                                          _copy_without_ptrs_SearchTree(end_r_1467, end_r_1468, loc_1745, tmpcur_2957);
            CursorTy pvrtmp_2958 = tmp_struct_39.field0;
            CursorTy pvrtmp_2959 = tmp_struct_39.field1;
            CursorTy pvrtmp_2960 = tmp_struct_39.field2;
            CursorTy pvrtmp_2961 = tmp_struct_39.field3;
            CursorCursorCursorCursorProd tmp_struct_40 =
                                          _copy_without_ptrs_SearchTree(end_r_1467, pvrtmp_2958, pvrtmp_2961, tmpcur_2954);
            CursorTy pvrtmp_2966 = tmp_struct_40.field0;
            CursorTy pvrtmp_2967 = tmp_struct_40.field1;
            CursorTy pvrtmp_2968 = tmp_struct_40.field2;
            CursorTy pvrtmp_2969 = tmp_struct_40.field3;

            *(TagTyPacked *) loc_1466 = 2;

            CursorTy writetag_2195 = loc_1466 + 1;

            *(IntTy *) writetag_2195 = tmpval_2956;

            CursorTy writecur_2196 = writetag_2195 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_2966, pvrtmp_2967,
                                                   loc_1466, pvrtmp_2969};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2978 = *(CursorTy *) tmpcur_2943;
            CursorTy tmpaftercur_2979 = tmpcur_2943 + 8;
            CursorTy jump_1936 = tmpcur_2943 + 8;
            CursorCursorCursorCursorProd tmp_struct_41 =
                                          _copy_without_ptrs_SearchTree(end_r_1467, end_r_1468, loc_1466, tmpcur_2978);
            CursorTy pvrtmp_2980 = tmp_struct_41.field0;
            CursorTy pvrtmp_2981 = tmp_struct_41.field1;
            CursorTy pvrtmp_2982 = tmp_struct_41.field2;
            CursorTy pvrtmp_2983 = tmp_struct_41.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2980, jump_1936,
                                                   pvrtmp_2982, pvrtmp_2983};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2990 = *(CursorTy *) tmpcur_2943;
            CursorTy tmpaftercur_2991 = tmpcur_2943 + 8;
            CursorCursorCursorCursorProd tmp_struct_42 =
                                          _copy_without_ptrs_SearchTree(end_r_1467, end_r_1468, loc_1466, tmpcur_2990);
            CursorTy pvrtmp_2992 = tmp_struct_42.field0;
            CursorTy pvrtmp_2993 = tmp_struct_42.field1;
            CursorTy pvrtmp_2994 = tmp_struct_42.field2;
            CursorTy pvrtmp_2995 = tmp_struct_42.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2992, pvrtmp_2993,
                                                   pvrtmp_2994, pvrtmp_2995};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2942");
            exit(1);
        }
    }
}
CursorProd _traverse_SearchTree(CursorTy end_r_1470, CursorTy arg_741_857_1037)
{
    TagTyPacked tmpval_3003 = *(TagTyPacked *) arg_741_857_1037;
    CursorTy tmpcur_3004 = arg_741_857_1037 + 1;


  switch_3019:
    ;
    switch (tmpval_3003) {

      case 0:
        {
            CursorTy jump_1872 = arg_741_857_1037 + 1;

            return (CursorProd) {jump_1872};
            break;
        }

      case 1:
        {
            IntTy tmpval_3005 = *(IntTy *) tmpcur_3004;
            CursorTy tmpcur_3006 = tmpcur_3004 + sizeof(IntTy);
            CursorTy jump_1874 = tmpcur_3004 + 8;

            return (CursorProd) {jump_1874};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_3007 = *(CursorTy *) tmpcur_3004;
            CursorTy tmpaftercur_3008 = tmpcur_3004 + 8;
            IntTy tmpval_3009 = *(IntTy *) tmpaftercur_3008;
            CursorTy tmpcur_3010 = tmpaftercur_3008 + sizeof(IntTy);
            CursorTy jump_1877 = tmpaftercur_3008 + 8;
            CursorTy jump_1876 = tmpcur_3004 + 8;
            CursorProd tmp_struct_43 =
                        _traverse_SearchTree(end_r_1470, tmpcur_3010);
            CursorTy pvrtmp_3011 = tmp_struct_43.field0;
            CursorProd tmp_struct_44 =
                        _traverse_SearchTree(end_r_1470, tmpcur_3007);
            CursorTy pvrtmp_3012 = tmp_struct_44.field0;

            return (CursorProd) {pvrtmp_3012};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3013 = *(CursorTy *) tmpcur_3004;
            CursorTy tmpaftercur_3014 = tmpcur_3004 + 8;
            CursorTy jump_1942 = tmpcur_3004 + 8;
            CursorProd tmp_struct_45 =
                        _traverse_SearchTree(end_r_1470, tmpcur_3013);
            CursorTy pvrtmp_3015 = tmp_struct_45.field0;

            return (CursorProd) {jump_1942};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3016 = *(CursorTy *) tmpcur_3004;
            CursorTy tmpaftercur_3017 = tmpcur_3004 + 8;
            CursorProd tmp_struct_46 =
                        _traverse_SearchTree(end_r_1470, tmpcur_3016);
            CursorTy pvrtmp_3018 = tmp_struct_46.field0;

            return (CursorProd) {pvrtmp_3018};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3003");
            exit(1);
        }
    }
}
CursorProd _print_SearchTree(CursorTy end_r_1472, CursorTy arg_750_864_1044)
{
    TagTyPacked tmpval_3020 = *(TagTyPacked *) arg_750_864_1044;
    CursorTy tmpcur_3021 = arg_750_864_1044 + 1;


  switch_3036:
    ;
    switch (tmpval_3020) {

      case 0:
        {
            CursorTy jump_1881 = arg_750_864_1044 + 1;
            unsigned char wildcard_751_865_1045 = print_symbol(2572);
            unsigned char wildcard_752_866_1046 = print_symbol(2571);

            return (CursorProd) {jump_1881};
            break;
        }

      case 1:
        {
            IntTy tmpval_3022 = *(IntTy *) tmpcur_3021;
            CursorTy tmpcur_3023 = tmpcur_3021 + sizeof(IntTy);
            CursorTy jump_1883 = tmpcur_3021 + 8;
            unsigned char wildcard_755_868_1048 = print_symbol(2574);
            unsigned char wildcard_757_869_1049 = print_symbol(2577);
            unsigned char y_754_870_1050 = printf("%lld", tmpval_3022);
            unsigned char wildcard_756_871_1051 = print_symbol(2571);

            return (CursorProd) {jump_1883};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_3024 = *(CursorTy *) tmpcur_3021;
            CursorTy tmpaftercur_3025 = tmpcur_3021 + 8;
            IntTy tmpval_3026 = *(IntTy *) tmpaftercur_3025;
            CursorTy tmpcur_3027 = tmpaftercur_3025 + sizeof(IntTy);
            CursorTy jump_1886 = tmpaftercur_3025 + 8;
            CursorTy jump_1885 = tmpcur_3021 + 8;
            unsigned char wildcard_764_875_1055 = print_symbol(2573);
            unsigned char wildcard_768_876_1056 = print_symbol(2577);
            unsigned char y_761_877_1057 = printf("%lld", tmpval_3026);
            unsigned char wildcard_767_878_1058 = print_symbol(2577);
            CursorProd tmp_struct_47 =
                        _print_SearchTree(end_r_1472, tmpcur_3027);
            CursorTy pvrtmp_3028 = tmp_struct_47.field0;
            unsigned char wildcard_766_880_1060 = print_symbol(2577);
            CursorProd tmp_struct_48 =
                        _print_SearchTree(end_r_1472, tmpcur_3024);
            CursorTy pvrtmp_3029 = tmp_struct_48.field0;
            unsigned char wildcard_765_882_1062 = print_symbol(2571);

            return (CursorProd) {pvrtmp_3029};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3030 = *(CursorTy *) tmpcur_3021;
            CursorTy tmpaftercur_3031 = tmpcur_3021 + 8;
            CursorTy jump_1948 = tmpcur_3021 + 8;
            unsigned char wildcard_1951 = print_symbol(2576);
            CursorProd tmp_struct_49 =
                        _print_SearchTree(end_r_1472, tmpcur_3030);
            CursorTy pvrtmp_3032 = tmp_struct_49.field0;

            return (CursorProd) {jump_1948};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3033 = *(CursorTy *) tmpcur_3021;
            CursorTy tmpaftercur_3034 = tmpcur_3021 + 8;
            unsigned char wildcard_1951 = print_symbol(2575);
            CursorProd tmp_struct_50 =
                        _print_SearchTree(end_r_1472, tmpcur_3033);
            CursorTy pvrtmp_3035 = tmp_struct_50.field0;

            return (CursorProd) {pvrtmp_3035};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3020");
            exit(1);
        }
    }
}
IntTy caseFn_769(CursorTy end_r_1474, CursorTy l_110_770_883_1063,
                 IntTy n_109_771_884_1064)
{
    TagTyPacked tmpval_3037 = *(TagTyPacked *) l_110_770_883_1063;
    CursorTy tmpcur_3038 = l_110_770_883_1063 + 1;


  switch_3049:
    ;
    switch (tmpval_3037) {

      case 0:
        {
            CursorTy jump_1890 = l_110_770_883_1063 + 1;

            return n_109_771_884_1064;
            break;
        }

      case 1:
        {
            IntTy tmpval_3039 = *(IntTy *) tmpcur_3038;
            CursorTy tmpcur_3040 = tmpcur_3038 + sizeof(IntTy);
            CursorTy jump_1891 = tmpcur_3038 + 8;

            return tmpval_3039;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_3041 = *(CursorTy *) tmpcur_3038;
            CursorTy tmpaftercur_3042 = tmpcur_3038 + 8;
            IntTy tmpval_3043 = *(IntTy *) tmpaftercur_3042;
            CursorTy tmpcur_3044 = tmpaftercur_3042 + sizeof(IntTy);
            CursorTy jump_1893 = tmpaftercur_3042 + 8;
            CursorTy jump_1892 = tmpcur_3038 + 8;
            IntTy tailapp_1894 =  minTree(end_r_1474, tmpcur_3044);

            return tailapp_1894;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3045 = *(CursorTy *) tmpcur_3038;
            CursorTy tmpaftercur_3046 = tmpcur_3038 + 8;
            CursorTy jump_1954 = tmpcur_3038 + 8;
            IntTy call_1955 =
                   caseFn_769(end_r_1474, tmpcur_3045, n_109_771_884_1064);

            return call_1955;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3047 = *(CursorTy *) tmpcur_3038;
            CursorTy tmpaftercur_3048 = tmpcur_3038 + 8;
            IntTy call_1955 =
                   caseFn_769(end_r_1474, tmpcur_3047, n_109_771_884_1064);

            return call_1955;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3037");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_SearchTree(CursorTy end_r_1477,
                                                                  CursorTy end_r_1478,
                                                                  CursorTy loc_1476,
                                                                  CursorTy arg_1420)
{
    if (loc_1476 + 32 > end_r_1478) {
        ChunkTy new_chunk_55 = alloc_chunk(end_r_1478);
        CursorTy chunk_start_56 = new_chunk_55.chunk_start;
        CursorTy chunk_end_57 = new_chunk_55.chunk_end;

        end_r_1478 = chunk_end_57;
        *(TagTyPacked *) loc_1476 = 255;

        CursorTy redir = loc_1476 + 1;

        *(CursorTy *) redir = chunk_start_56;
        loc_1476 = chunk_start_56;
    }

    TagTyPacked tmpval_3050 = *(TagTyPacked *) arg_1420;
    CursorTy tmpcur_3051 = arg_1420 + 1;


  switch_3108:
    ;
    switch (tmpval_3050) {

      case 0:
        {
            CursorTy jump_1895 = arg_1420 + 1;

            *(TagTyPacked *) loc_1476 = 0;

            CursorTy writetag_2245 = loc_1476 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1478, jump_1895,
                                                   loc_1476, writetag_2245};
            break;
        }

      case 1:
        {
            IntTy tmpval_3056 = *(IntTy *) tmpcur_3051;
            CursorTy tmpcur_3057 = tmpcur_3051 + sizeof(IntTy);
            CursorTy jump_1897 = tmpcur_3051 + 8;

            *(TagTyPacked *) loc_1476 = 1;

            CursorTy writetag_2249 = loc_1476 + 1;

            *(IntTy *) writetag_2249 = tmpval_3056;

            CursorTy writecur_2250 = writetag_2249 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1478, jump_1897,
                                                   loc_1476, writecur_2250};
            break;
        }

      case 2:
        {
            IntTy tmpval_3062 = *(IntTy *) tmpcur_3051;
            CursorTy tmpcur_3063 = tmpcur_3051 + sizeof(IntTy);
            CursorTy jump_1899 = tmpcur_3051 + 8;
            CursorTy loc_1798 = loc_1476 + 1;
            CursorTy loc_1799 = loc_1798 + 8;
            CursorTy loc_1800 = loc_1799 + 8;
            CursorTy loc_1801 = loc_1800 + 8;
            CursorCursorCursorCursorProd tmp_struct_51 =
                                          _add_size_and_rel_offsets_SearchTree(end_r_1477, end_r_1478, loc_1801, tmpcur_3063);
            CursorTy pvrtmp_3064 = tmp_struct_51.field0;
            CursorTy pvrtmp_3065 = tmp_struct_51.field1;
            CursorTy pvrtmp_3066 = tmp_struct_51.field2;
            CursorTy pvrtmp_3067 = tmp_struct_51.field3;
            CursorCursorCursorCursorProd tmp_struct_52 =
                                          _add_size_and_rel_offsets_SearchTree(end_r_1477, pvrtmp_3064, pvrtmp_3067, pvrtmp_3065);
            CursorTy pvrtmp_3072 = tmp_struct_52.field0;
            CursorTy pvrtmp_3073 = tmp_struct_52.field1;
            CursorTy pvrtmp_3074 = tmp_struct_52.field2;
            CursorTy pvrtmp_3075 = tmp_struct_52.field3;
            IntTy sizeof_y_1427__1430 = pvrtmp_3067 - pvrtmp_3066;
            IntTy sizeof_y_1428__1431 = pvrtmp_3075 - pvrtmp_3074;
            IntTy fltPrm_1434 = 8 + sizeof_y_1427__1430;
            IntTy offset__1432 = 0 + fltPrm_1434;
            IntTy fltPrm_1436 = sizeof_y_1427__1430 + sizeof_y_1428__1431;
            IntTy fltPrm_1435 = 8 + fltPrm_1436;
            IntTy size_dcon_1433 = 9 + fltPrm_1435;

            *(TagTyPacked *) loc_1476 = 154;

            CursorTy writetag_2256 = loc_1476 + 1;

            *(IntTy *) writetag_2256 = size_dcon_1433;

            CursorTy writecur_2257 = writetag_2256 + sizeof(IntTy);

            *(IntTy *) writecur_2257 = offset__1432;

            CursorTy writecur_2258 = writecur_2257 + sizeof(IntTy);

            *(IntTy *) writecur_2258 = tmpval_3062;

            CursorTy writecur_2259 = writecur_2258 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_3072, pvrtmp_3073,
                                                   loc_1476, pvrtmp_3075};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3084 = *(CursorTy *) tmpcur_3051;
            CursorTy tmpaftercur_3085 = tmpcur_3051 + 8;
            CursorTy jump_1959 = tmpcur_3051 + 8;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _add_size_and_rel_offsets_SearchTree(end_r_1477, end_r_1478, loc_1476, tmpcur_3084);
            CursorTy pvrtmp_3086 = tmp_struct_53.field0;
            CursorTy pvrtmp_3087 = tmp_struct_53.field1;
            CursorTy pvrtmp_3088 = tmp_struct_53.field2;
            CursorTy pvrtmp_3089 = tmp_struct_53.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3086, jump_1959,
                                                   pvrtmp_3088, pvrtmp_3089};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3096 = *(CursorTy *) tmpcur_3051;
            CursorTy tmpaftercur_3097 = tmpcur_3051 + 8;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _add_size_and_rel_offsets_SearchTree(end_r_1477, end_r_1478, loc_1476, tmpcur_3096);
            CursorTy pvrtmp_3098 = tmp_struct_54.field0;
            CursorTy pvrtmp_3099 = tmp_struct_54.field1;
            CursorTy pvrtmp_3100 = tmp_struct_54.field2;
            CursorTy pvrtmp_3101 = tmp_struct_54.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3098, pvrtmp_3099,
                                                   pvrtmp_3100, pvrtmp_3101};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3050");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(2571, ")");
    add_symbol(2572, "(Null");
    add_symbol(2573, "(Node");
    add_symbol(2574, "(Leaf");
    add_symbol(2575, " ->r ");
    add_symbol(2576, " ->i ");
    add_symbol(2577, " ");

    RegionTy *region_2578 = alloc_region(global_init_inf_buf_size);
    CursorTy r_1490 = region_2578->reg_heap;
    IntTy sizeof_end_r_1490_2579 = global_init_inf_buf_size;
    CursorTy end_r_1490 = r_1490 + sizeof_end_r_1490_2579;
    RegionTy *region_2580 = alloc_region(global_init_inf_buf_size);
    CursorTy r_1489 = region_2580->reg_heap;
    IntTy sizeof_end_r_1489_2581 = global_init_inf_buf_size;
    CursorTy end_r_1489 = r_1489 + sizeof_end_r_1489_2581;
    VectorTy *pts_85_772_936 = vector_alloc(read_arrayfile_length_param(),
                                            sizeof(IntTy));
    IntTy arr_elem_66;

    FILE * fp_67;

    char *line_68 = NULL;

    size_t(len_69);
    len_69 = 0;
    ssize_t(read_70);
    fp_67 = fopen(read_arrayfile_param(), "r");
    if (fp_67 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    IntTy tmp_72;
    IntTy i_71 = 0;

    while ((read_70 = getline(&line_68, &len_69, fp_67)) != -1) {
        int xxxx = sscanf(line_68, "%lld", &tmp_72);

        arr_elem_66 = tmp_72;
        vector_inplace_update(pts_85_772_936, i_71, &arr_elem_66);
        i_71++;
    }

    IntTy n_86_773_937 = global_size_param;
    CursorCursorCursorProd tmp_struct_58 =  helper(end_r_1490, r_1490, 0, 3);
    CursorTy pvrtmp_2582 = tmp_struct_58.field0;
    CursorTy pvrtmp_2583 = tmp_struct_58.field1;
    CursorTy pvrtmp_2584 = tmp_struct_58.field2;
    CursorTy pvrtmp_2598;
    CursorTy pvrtmp_2599;
    CursorTy pvrtmp_2600;
    VectorTy *times_63 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_2598;
    struct timespec end_pvrtmp_2598;

    for (long long iters_pvrtmp_2598 = 0; iters_pvrtmp_2598 <
         global_iters_param; iters_pvrtmp_2598++) {
        if (iters_pvrtmp_2598 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2598);

        CursorCursorCursorProd tmp_struct_59 =
                                loop(pvrtmp_2582, end_r_1489, r_1489, pts_85_772_936, 0, pvrtmp_2583, n_86_773_937);
        CursorTy pvrtmp_2589 = tmp_struct_59.field0;
        CursorTy pvrtmp_2590 = tmp_struct_59.field1;
        CursorTy pvrtmp_2591 = tmp_struct_59.field2;

        pvrtmp_2598 = pvrtmp_2589;
        pvrtmp_2599 = pvrtmp_2590;
        pvrtmp_2600 = pvrtmp_2591;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2598);
        if (iters_pvrtmp_2598 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_60 = difftimespecs(&begin_pvrtmp_2598,
                                           &end_pvrtmp_2598);

        vector_inplace_update(times_63, iters_pvrtmp_2598, &itertime_60);
    }
    vector_inplace_sort(times_63, compare_doubles);

    double *tmp_64 = (double *) vector_nth(times_63, global_iters_param / 2);
    double selftimed_62 = *tmp_64;
    double batchtime_61 = sum_timing_array(times_63);

    print_timing_array(times_63);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_61);
    printf("SELFTIMED: %e\n", selftimed_62);

    CursorInt64Prod tmp_struct_65 =  countnodes(end_r_1489, pvrtmp_2599);
    CursorTy pvrtmp_2608 = tmp_struct_65.field0;
    IntTy pvrtmp_2609 = tmp_struct_65.field1;

    printf("%lld", pvrtmp_2609);
    printf("\n");
    free_symtable();
    free_region(end_r_1489);
    free_region(end_r_1490);
    return 0;
}
