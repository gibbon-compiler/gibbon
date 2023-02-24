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
static long long global_init_inf_buf_size = 1 * KB;

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
typedef struct Float32Prod_struct {
            FloatTy field0;
        } Float32Prod;
typedef struct Float32Float32Prod_struct {
            FloatTy field0;
            FloatTy field1;
        } Float32Float32Prod;
typedef struct Float32Float32Float32Prod_struct {
            FloatTy field0;
            FloatTy field1;
            FloatTy field2;
        } Float32Float32Float32Prod;
typedef struct Float32Float32Float32Float32Prod_struct {
            FloatTy field0;
            FloatTy field1;
            FloatTy field2;
            FloatTy field3;
        } Float32Float32Float32Float32Prod;
typedef struct Float32Float32Float32Float32Float32Prod_struct {
            FloatTy field0;
            FloatTy field1;
            FloatTy field2;
            FloatTy field3;
            FloatTy field4;
        } Float32Float32Float32Float32Float32Prod;
typedef struct Float32CursorProd_struct {
            FloatTy field0;
            CursorTy field1;
        } Float32CursorProd;
typedef struct BoolProd_struct {
            BoolTy field0;
        } BoolProd;
typedef struct BoolInt64Prod_struct {
            BoolTy field0;
            IntTy field1;
        } BoolInt64Prod;
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
typedef struct CursorFloat32Prod_struct {
            CursorTy field0;
            FloatTy field1;
        } CursorFloat32Prod;
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
unsigned char bench_seqbuildkdtree();
unsigned char bench_seqfoldconstants();
unsigned char bench_seqbhut();
unsigned char bench_seqbuildquadtree();
unsigned char bench_seqnearest();
unsigned char bench_seqcountcorr();
CursorProd check_buildkdtree(CursorTy end_r_10636, VectorTy *pts_154_4607_7479,
                             CursorTy tr_155_4608_7480);
CursorCursorCursorProd mkKdTree_seq(CursorTy end_r_10638, CursorTy loc_10637,
                                    VectorTy *pts_165_4618_7492);
unsigned char check_countcorr(VectorTy *pts_166_4619_7493,
                              Float32Float32Float32Prod query_167_4620_7494,
                              IntTy actual_168_4621_7495,
                              FloatTy radius_169_4622_7496);
VectorTy *allCountCorr_seq(CursorTy end_r_10640, FloatTy radius_183_4631_7511,
                           CursorTy tr_184_4632_7512,
                           VectorTy *ls_185_4633_7513);
unsigned char check_nearest(VectorTy *pts_191_4634_7518,
                            VectorTy *actual_192_4635_7519);
VectorTy *allNearest_seq(CursorTy end_r_10642, CursorTy tr_207_4642_7537,
                         VectorTy *ls_208_4643_7538);
CursorProd check_buildquadtree(CursorTy end_r_10644,
                               VectorTy *mpts_210_4644_7542,
                               CursorTy bht_211_4645_7543);
CursorCursorCursorProd buildQtree_seq(CursorTy end_r_10646, CursorTy loc_10645,
                                      Float32Float32Float32Float32Prod box_227_4661_7562,
                                      VectorTy *mpts_228_4662_7563);
FloatTy maxFloat(FloatTy a_265_4694_7614, FloatTy b_266_4695_7615);
FloatTy minFloat(FloatTy a_267_4696_7617, FloatTy b_268_4697_7618);
VectorTy *oneStep_seq(CursorTy end_r_10648, CursorTy bht_274_4698_7620,
                      VectorTy *mpts_275_4699_7621, VectorTy *ps_276_4700_7622);
CursorInt64Prod sumExp(CursorTy end_r_10650, CursorTy exp_282_4702_7632);
CursorCursorCursorCursorProd foldConstants2(CursorTy end_r_10653,
                                            CursorTy end_r_10654,
                                            CursorTy loc_10652,
                                            CursorTy exp_286_4706_7638);
CursorCursorCursorProd buildExp(CursorTy end_r_10656, CursorTy loc_10655,
                                IntTy n_298_4718_7664);
FloatTy sumList(VectorTy *ls_317_4737_7672);
CursorFloat32Prod sumKdTree(CursorTy end_r_10658, CursorTy tr_344_4758_7676);
IntTy countCorr_seq(CursorTy end_r_10660,
                    Float32Float32Float32Prod probe_377_4791_7700,
                    FloatTy radius_378_4792_7701, CursorTy tr_379_4793_7702);
Float32Float32Float32Prod
least_dist_point3d(Float32Float32Float32Prod a_414_4828_7767,
                   Float32Float32Float32Prod b_415_4829_7768,
                   Float32Float32Float32Prod c_416_4830_7769);
Float32Float32Float32Prod find_nearest(CursorTy end_r_10663,
                                       CursorTy end_r_10664,
                                       Float32Float32Float32Prod pivot_419_4833_7773,
                                       Float32Float32Float32Prod query_420_4834_7774,
                                       FloatTy tst_pivot_421_4835_7775,
                                       FloatTy tst_query_422_4836_7776,
                                       CursorTy good_side_423_4837_7777,
                                       CursorTy other_side_424_4838_7778);
Float32Float32Float32Prod nearest(CursorTy end_r_10666,
                                  CursorTy tr_430_4844_7787,
                                  Float32Float32Float32Prod query_431_4845_7788);
CursorCursorCursorProd mkKdTreeWithAxis_seq(CursorTy end_r_10668,
                                            CursorTy loc_10667,
                                            IntTy axis_452_4866_7810,
                                            VectorTy *pts_453_4867_7811);
IntTy get_total_points_kdtree(CursorTy end_r_10670, CursorTy tr_532_4946_7871);
FloatTy get_maxz_kdtree(CursorTy end_r_10672, CursorTy tr_550_4964_7889);
FloatTy get_minz_kdtree(CursorTy end_r_10674, CursorTy tr_568_4982_7907);
FloatTy get_maxy_kdtree(CursorTy end_r_10676, CursorTy tr_586_5000_7925);
FloatTy get_miny_kdtree(CursorTy end_r_10678, CursorTy tr_604_5018_7943);
FloatTy get_maxx_kdtree(CursorTy end_r_10680, CursorTy tr_622_5036_7961);
FloatTy get_minx_kdtree(CursorTy end_r_10682, CursorTy tr_640_5054_7979);
FloatTy get_coord_point3d(IntTy axis_701_5115_7997,
                          Float32Float32Float32Prod pt_702_5116_7998);
IntTy getNextAxis_3d(IntTy i_707_5121_8005);
VectorTy *sort_point3d(IntTy axis_708_5122_8007, VectorTy *ls_709_5123_8008);
FloatTy dist_point3d(Float32Float32Float32Prod a_711_5125_8017,
                     Float32Float32Float32Prod b_712_5126_8018);
unsigned char print_check(BoolTy b_726_5138_8034);
FloatTy float_abs(FloatTy f_729_5141_8037);
BoolTy eq_point3d(Float32Float32Float32Prod a_730_5142_8040,
                  Float32Float32Float32Prod b_731_5143_8041);
VectorTy
*masspointsInBox_seq(Float32Float32Float32Float32Prod box_792_5178_8054,
                     VectorTy *mpts_793_5179_8055);
Float32Float32Float32Prod calcCentroid_seq(VectorTy *mpts_808_5190_8063);
Float32Float32Prod calcAccel_seq(CursorTy end_r_10684,
                                 Float32Float32Float32Prod mpt_825_5196_8074,
                                 CursorTy tr_826_5197_8075);
IntTy getTotalPoints_qtree(CursorTy end_r_10686, CursorTy tr_884_5255_8179);
FloatTy sum_mass_points(VectorTy *mpts_951_5322_8192);
CursorInt64Prod countLeavesQtree(CursorTy end_r_10688,
                                 CursorTy tr_958_5323_8196);
CursorFloat32Prod sumQtree(CursorTy end_r_10690, CursorTy tr_971_5336_8215);
CursorProd trav_exp(CursorTy end_r_10692, CursorTy exp_1043_5392_8247);
FloatTy maybeLit(CursorTy end_r_10694, CursorTy exp_1050_5399_8253);
IntTy maxInt(IntTy a_1063_5412_8257, IntTy b_1064_5413_8258);
IntTy cmpz_point3d_original(Float32Float32Float32Prod a_1340_5498_8260,
                            Float32Float32Float32Prod b_1341_5499_8261);
int cmpz_point3d(const void *a_1340_5498_8260, const void *b_1341_5499_8261);
IntTy cmpy_point3d_original(Float32Float32Float32Prod a_1346_5504_8270,
                            Float32Float32Float32Prod b_1347_5505_8271);
int cmpy_point3d(const void *a_1346_5504_8270, const void *b_1347_5505_8271);
IntTy cmpx_point3d_original(Float32Float32Float32Prod a_1352_5510_8280,
                            Float32Float32Float32Prod b_1353_5511_8281);
int cmpx_point3d(const void *a_1352_5510_8280, const void *b_1353_5511_8281);
VectorTy *filter_loop_2379(VectorTy *idxs_1075_5571_8290,
                           IntTy write_at_1076_5572_8291,
                           IntTy start_1077_5573_8292, IntTy end_1078_5574_8293,
                           VectorTy *from_1079_5575_8294,
                           VectorTy *to_1080_5576_8295);
IntTy foldl_loop_2380_3709(IntTy idx_1164_5926_8369, IntTy end_1165_5927_8370,
                           IntTy acc_1167_5928_8371,
                           VectorTy *vec_1168_5929_8372);
VectorTy *generate_loop_2377_3710(CursorTy end_r_10696,
                                  VectorTy *vec_1196_5931_8380,
                                  IntTy idx_1197_5932_8381,
                                  IntTy end_1198_5933_8382,
                                  CursorTy bht_274_5934_8383,
                                  VectorTy *mpts_275_5935_8384,
                                  VectorTy *ps_276_5936_8385);
VectorTy *generate_loop_2376_3711(VectorTy *vec_1196_5938_8397,
                                  IntTy idx_1197_5939_8398,
                                  IntTy end_1198_5940_8399,
                                  VectorTy *vec_1193_5941_8400);
VectorTy *generate_loop_2374_3714(VectorTy *vec_1196_5960_8407,
                                  IntTy idx_1197_5961_8408,
                                  IntTy end_1198_5962_8409);
VectorTy *generate_loop_2374_3717(VectorTy *vec_1196_5974_8415,
                                  IntTy idx_1197_5975_8416,
                                  IntTy end_1198_5976_8417,
                                  VectorTy *vec_1028_5977_8418,
                                  Float32Float32Float32Float32Prod box_792_5978_8419);
VectorTy *generate_loop_2376_3720(CursorTy end_r_10698,
                                  VectorTy *vec_1196_5989_8435,
                                  IntTy idx_1197_5990_8436,
                                  IntTy end_1198_5991_8437,
                                  VectorTy *vec_270_5992_8438,
                                  CursorTy tr_207_5993_8439);
VectorTy *generate_loop_2374_3723(CursorTy end_r_10700,
                                  VectorTy *vec_1196_6006_8455,
                                  IntTy idx_1197_6007_8456,
                                  IntTy end_1198_6008_8457,
                                  VectorTy *vec_270_6009_8458,
                                  FloatTy radius_183_6010_8459,
                                  CursorTy tr_184_6011_8460);
VectorTy *generate_loop_2377_3726(VectorTy *vec_1196_6021_8475,
                                  IntTy idx_1197_6022_8476,
                                  IntTy end_1198_6023_8477,
                                  VectorTy *vec_270_6024_8478);
VectorTy *generate_loop_2377_3729(VectorTy *vec_1196_6034_8491,
                                  IntTy idx_1197_6035_8492,
                                  IntTy end_1198_6036_8493,
                                  VectorTy *vec_270_6037_8494);
VectorTy *generate_loop_2376_3732(VectorTy *vec_1196_6047_8507,
                                  IntTy idx_1197_6048_8508,
                                  IntTy end_1198_6049_8509,
                                  VectorTy *vec_270_6050_8510);
VectorTy *generate_loop_2376_3735(VectorTy *vec_1196_6060_8523,
                                  IntTy idx_1197_6061_8524,
                                  IntTy end_1198_6062_8525,
                                  VectorTy *vec_270_6063_8526);
Float32Float32Float32Prod foldl_loop_2371_3737(IntTy idx_1164_6073_8534,
                                               IntTy end_1165_6074_8535,
                                               Float32Float32Float32Prod acc_1167_6075_8536,
                                               VectorTy *vec_1168_6076_8537);
FloatTy foldl_loop_2370_3738(IntTy idx_1164_6080_8556, IntTy end_1165_6081_8557,
                             FloatTy acc_1167_6082_8558,
                             VectorTy *vec_1168_6083_8559);
FloatTy foldl_loop_2370_3739(IntTy idx_1164_6087_8571, IntTy end_1165_6088_8572,
                             FloatTy acc_1167_6089_8573,
                             VectorTy *vec_1168_6090_8574);
IntTy foldl_loop_2369_3740(IntTy idx_1164_6092_8586, IntTy end_1165_6093_8587,
                           IntTy acc_1167_6094_8588,
                           VectorTy *vec_1168_6095_8589,
                           Float32Float32Float32Prod query_167_6096_8590,
                           FloatTy radius_sq_170_6097_8591);
FloatTy foldl_loop_2368_3741(IntTy idx_1164_6101_8601, IntTy end_1165_6102_8602,
                             FloatTy acc_1167_6103_8603,
                             VectorTy *vec_1168_6104_8604);
FloatTy foldl_loop_2368_3742(IntTy idx_1164_6108_8611, IntTy end_1165_6109_8612,
                             FloatTy acc_1167_6110_8613,
                             VectorTy *vec_1168_6111_8614);
FloatTy foldl_loop_2368_3743(IntTy idx_1164_6115_8621, IntTy end_1165_6116_8622,
                             FloatTy acc_1167_6117_8623,
                             VectorTy *vec_1168_6118_8624);
FloatTy foldl_loop_2368_3744(IntTy idx_1164_6122_8631, IntTy end_1165_6123_8632,
                             FloatTy acc_1167_6124_8633,
                             VectorTy *vec_1168_6125_8634);
FloatTy foldl_loop_2368_3745(IntTy idx_1164_6129_8641, IntTy end_1165_6130_8642,
                             FloatTy acc_1167_6131_8643,
                             VectorTy *vec_1168_6132_8644);
FloatTy foldl_loop_2368_3746(IntTy idx_1164_6136_8651, IntTy end_1165_6137_8652,
                             FloatTy acc_1167_6138_8653,
                             VectorTy *vec_1168_6139_8654);
FloatTy foldl_loop_2368_3747(IntTy idx_1164_6143_8661, IntTy end_1165_6144_8662,
                             FloatTy acc_1167_6145_8663,
                             VectorTy *vec_1168_6146_8664);
FloatTy foldl_loop_2368_3748(IntTy idx_1164_6150_8671, IntTy end_1165_6151_8672,
                             FloatTy acc_1167_6152_8673,
                             VectorTy *vec_1168_6153_8674);
BoolInt64Prod foldl_loop_2367_3749(IntTy idx_1164_6155_8681,
                                   IntTy end_1165_6156_8682,
                                   BoolInt64Prod acc_1167_6157_8683,
                                   VectorTy *vec_1168_6158_8684,
                                   VectorTy *pts_191_6159_8685,
                                   VectorTy *actual_192_6160_8686);
CursorCursorCursorCursorProd _copy_KdTree(CursorTy end_r_10703,
                                          CursorTy end_r_10704,
                                          CursorTy loc_10702,
                                          CursorTy arg_4208_6162_8704);
CursorCursorCursorCursorProd _copy_without_ptrs_KdTree(CursorTy end_r_10707,
                                                       CursorTy end_r_10708,
                                                       CursorTy loc_10706,
                                                       CursorTy arg_4243_6197_8739);
CursorProd _traverse_KdTree(CursorTy end_r_10710, CursorTy arg_4278_6232_8774);
CursorProd _print_KdTree(CursorTy end_r_10712, CursorTy arg_4313_6252_8794);
CursorCursorCursorCursorProd _copy_BH_Tree(CursorTy end_r_10715,
                                           CursorTy end_r_10716,
                                           CursorTy loc_10714,
                                           CursorTy arg_4371_6310_8852);
CursorCursorCursorCursorProd _copy_without_ptrs_BH_Tree(CursorTy end_r_10719,
                                                        CursorTy end_r_10720,
                                                        CursorTy loc_10718,
                                                        CursorTy arg_4396_6335_8877);
CursorProd _traverse_BH_Tree(CursorTy end_r_10722, CursorTy arg_4421_6360_8902);
CursorProd _print_BH_Tree(CursorTy end_r_10724, CursorTy arg_4446_6377_8919);
CursorCursorCursorCursorProd _copy_Exp(CursorTy end_r_10727,
                                       CursorTy end_r_10728, CursorTy loc_10726,
                                       CursorTy arg_4489_6420_8962);
CursorCursorCursorCursorProd _copy_without_ptrs_Exp(CursorTy end_r_10731,
                                                    CursorTy end_r_10732,
                                                    CursorTy loc_10730,
                                                    CursorTy arg_4504_6435_8977);
CursorProd _traverse_Exp(CursorTy end_r_10734, CursorTy arg_4519_6450_8992);
CursorProd _print_Exp(CursorTy end_r_10736, CursorTy arg_4534_6464_9006);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_KdTree(CursorTy end_r_10739, CursorTy end_r_10740,
                                 CursorTy loc_10738, CursorTy arg_10456);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_BH_Tree(CursorTy end_r_10743, CursorTy end_r_10744,
                                  CursorTy loc_10742, CursorTy arg_10507);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Exp(CursorTy end_r_10747,
                                                           CursorTy end_r_10748,
                                                           CursorTy loc_10746,
                                                           CursorTy arg_10545);
unsigned char bench_seqbuildkdtree()
{
    RegionTy *region_14986 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10755 = region_14986->reg_heap;
    IntTy sizeof_end_r_10755_14987 = global_init_inf_buf_size;
    CursorTy end_r_10755 = r_10755 + sizeof_end_r_10755_14987;
    VectorTy *pts_83_4568_7396 = vector_alloc(read_arrayfile_length_param(),
                                              sizeof(Float32Float32Float32Prod));
    Float32Float32Float32Prod arr_elem_7;

    FILE * fp_8;

    char *line_9 = NULL;

    size_t(len_10);
    len_10 = 0;
    ssize_t(read_11);
    fp_8 = fopen(read_arrayfile_param(), "r");
    if (fp_8 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    FloatTy tmp_13;
    FloatTy tmp_14;
    FloatTy tmp_15;
    IntTy i_12 = 0;

    while ((read_11 = getline(&line_9, &len_10, fp_8)) != -1) {
        int xxxx = sscanf(line_9, "%f %f %f", &tmp_13, &tmp_14, &tmp_15);

        arr_elem_7.field0 = tmp_13;
        arr_elem_7.field1 = tmp_14;
        arr_elem_7.field2 = tmp_15;
        vector_inplace_update(pts_83_4568_7396, i_12, &arr_elem_7);
        i_12++;
    }

    IntTy n_84_4569_7397 = global_size_param;
    FloatTy radius_85_4570_7398 = (FloatTy) n_84_4569_7397;
    CursorTy pvrtmp_14997;
    CursorTy pvrtmp_14998;
    CursorTy pvrtmp_14999;
    VectorTy *times_4 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_14997;
    struct timespec end_pvrtmp_14997;

    for (long long iters_pvrtmp_14997 = 0; iters_pvrtmp_14997 <
         global_iters_param; iters_pvrtmp_14997++) {
        if (iters_pvrtmp_14997 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_14997);

        CursorCursorCursorProd tmp_struct_0 =
                                mkKdTree_seq(end_r_10755, r_10755, pts_83_4568_7396);
        CursorTy pvrtmp_14988 = tmp_struct_0.field0;
        CursorTy pvrtmp_14989 = tmp_struct_0.field1;
        CursorTy pvrtmp_14990 = tmp_struct_0.field2;

        pvrtmp_14997 = pvrtmp_14988;
        pvrtmp_14998 = pvrtmp_14989;
        pvrtmp_14999 = pvrtmp_14990;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_14997);
        if (iters_pvrtmp_14997 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_1 = difftimespecs(&begin_pvrtmp_14997,
                                          &end_pvrtmp_14997);

        vector_inplace_update(times_4, iters_pvrtmp_14997, &itertime_1);
    }
    vector_inplace_sort(times_4, compare_doubles);

    double *tmp_5 = (double *) vector_nth(times_4, global_iters_param / 2);
    double selftimed_3 = *tmp_5;
    double batchtime_2 = sum_timing_array(times_4);

    print_timing_array(times_4);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_2);
    printf("SELFTIMED: %e\n", selftimed_3);

    CursorProd tmp_struct_6 =
                check_buildkdtree(end_r_10755, pts_83_4568_7396, pvrtmp_14998);
    CursorTy pvrtmp_15007 = tmp_struct_6.field0;

    free_region(end_r_10755);
    return 0;
}
unsigned char bench_seqfoldconstants()
{
    RegionTy *region_15008 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10767 = region_15008->reg_heap;
    IntTy sizeof_end_r_10767_15009 = global_init_inf_buf_size;
    CursorTy end_r_10767 = r_10767 + sizeof_end_r_10767_15009;
    RegionTy *region_15010 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10766 = region_15010->reg_heap;
    IntTy sizeof_end_r_10766_15011 = global_init_inf_buf_size;
    CursorTy end_r_10766 = r_10766 + sizeof_end_r_10766_15011;
    IntTy fltAppE_7081_7400 = global_size_param;
    CursorCursorCursorProd tmp_struct_16 =
                            buildExp(end_r_10767, r_10767, fltAppE_7081_7400);
    CursorTy pvrtmp_15012 = tmp_struct_16.field0;
    CursorTy pvrtmp_15013 = tmp_struct_16.field1;
    CursorTy pvrtmp_15014 = tmp_struct_16.field2;
    CursorTy pvrtmp_15029;
    CursorTy pvrtmp_15030;
    CursorTy pvrtmp_15031;
    VectorTy *times_21 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_15029;
    struct timespec end_pvrtmp_15029;

    for (long long iters_pvrtmp_15029 = 0; iters_pvrtmp_15029 <
         global_iters_param; iters_pvrtmp_15029++) {
        if (iters_pvrtmp_15029 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_15029);

        CursorCursorCursorCursorProd tmp_struct_17 =
                                      foldConstants2(pvrtmp_15012, end_r_10766, r_10766, pvrtmp_15013);
        CursorTy pvrtmp_15019 = tmp_struct_17.field0;
        CursorTy pvrtmp_15020 = tmp_struct_17.field1;
        CursorTy pvrtmp_15021 = tmp_struct_17.field2;
        CursorTy pvrtmp_15022 = tmp_struct_17.field3;

        pvrtmp_15029 = pvrtmp_15019;
        pvrtmp_15030 = pvrtmp_15021;
        pvrtmp_15031 = pvrtmp_15022;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_15029);
        if (iters_pvrtmp_15029 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_18 = difftimespecs(&begin_pvrtmp_15029,
                                           &end_pvrtmp_15029);

        vector_inplace_update(times_21, iters_pvrtmp_15029, &itertime_18);
    }
    vector_inplace_sort(times_21, compare_doubles);

    double *tmp_22 = (double *) vector_nth(times_21, global_iters_param / 2);
    double selftimed_20 = *tmp_22;
    double batchtime_19 = sum_timing_array(times_21);

    print_timing_array(times_21);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_19);
    printf("SELFTIMED: %e\n", selftimed_20);

    CursorInt64Prod tmp_struct_23 =  sumExp(end_r_10766, pvrtmp_15030);
    CursorTy pvrtmp_15039 = tmp_struct_23.field0;
    IntTy pvrtmp_15040 = tmp_struct_23.field1;
    unsigned char wildcard__76_90_4575_7404 = printf("%lld", pvrtmp_15040);

    free_region(end_r_10766);
    free_region(end_r_10767);
    return 0;
}
unsigned char bench_seqbhut()
{
    RegionTy *region_15041 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10774 = region_15041->reg_heap;
    IntTy sizeof_end_r_10774_15042 = global_init_inf_buf_size;
    CursorTy end_r_10774 = r_10774 + sizeof_end_r_10774_15042;
    VectorTy *pts_91_4576_7405 = vector_alloc(read_arrayfile_length_param(),
                                              sizeof(Float32Float32Prod));
    Float32Float32Prod arr_elem_28;

    FILE * fp_29;

    char *line_30 = NULL;

    size_t(len_31);
    len_31 = 0;
    ssize_t(read_32);
    fp_29 = fopen(read_arrayfile_param(), "r");
    if (fp_29 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    FloatTy tmp_34;
    FloatTy tmp_35;
    IntTy i_33 = 0;

    while ((read_32 = getline(&line_30, &len_31, fp_29)) != -1) {
        int xxxx = sscanf(line_30, "%f %f", &tmp_34, &tmp_35);

        arr_elem_28.field0 = tmp_34;
        arr_elem_28.field1 = tmp_35;
        vector_inplace_update(pts_91_4576_7405, i_33, &arr_elem_28);
        i_33++;
    }

    IntTy fltAppE_7082_7407 = vector_length(pts_91_4576_7405);
    IntTy n__743_6018_8472_9042 =  maxInt(fltAppE_7082_7407, 0);
    IntTy tmp_27 = sizeof(Float32Float32Float32Float32Float32Prod);
    VectorTy *vec_744_6019_8473_9043 = vector_alloc(n__743_6018_8472_9042,
                                                    tmp_27);
    VectorTy *vec1_745_6020_8474_9044 =
              generate_loop_2377_3726(vec_744_6019_8473_9043, 0, n__743_6018_8472_9042, pts_91_4576_7405);
    IntTy fltAppE_7083_7410 = vector_length(pts_91_4576_7405);
    IntTy n__743_6044_8504_9047 =  maxInt(fltAppE_7083_7410, 0);
    IntTy tmp_26 = sizeof(Float32Float32Float32Prod);
    VectorTy *vec_744_6045_8505_9048 = vector_alloc(n__743_6044_8504_9047,
                                                    tmp_26);
    VectorTy *vec1_745_6046_8506_9049 =
              generate_loop_2376_3732(vec_744_6045_8505_9048, 0, n__743_6044_8504_9047, pts_91_4576_7405);
    IntTy fltAppE_7084_7414 = vector_length(pts_91_4576_7405);
    FloatTy llx_104_4579_7415 =
             foldl_loop_2368_3741(0, fltAppE_7084_7414, 100000.0, pts_91_4576_7405);
    IntTy fltAppE_7085_7418 = vector_length(pts_91_4576_7405);
    FloatTy lly_107_4580_7419 =
             foldl_loop_2368_3742(0, fltAppE_7085_7418, 100000.0, pts_91_4576_7405);
    FloatTy fltPrm_7086_7420 = 0.0 - 1.0;
    FloatTy acc_261_6113_6504_7421 = fltPrm_7086_7420 * 100000.0;
    IntTy fltAppE_7087_7423 = vector_length(pts_91_4576_7405);
    FloatTy rux_110_4581_7424 =
             foldl_loop_2368_3743(0, fltAppE_7087_7423, acc_261_6113_6504_7421, pts_91_4576_7405);
    FloatTy fltPrm_7088_7425 = 0.0 - 1.0;
    FloatTy acc_261_6120_6506_7426 = fltPrm_7088_7425 * 100000.0;
    IntTy fltAppE_7089_7428 = vector_length(pts_91_4576_7405);
    FloatTy ruy_113_4582_7429 =
             foldl_loop_2368_3744(0, fltAppE_7089_7428, acc_261_6120_6506_7426, pts_91_4576_7405);
    CursorCursorCursorProd tmp_struct_24 =
                            buildQtree_seq(end_r_10774, r_10774, (Float32Float32Float32Float32Prod) {llx_104_4579_7415, lly_107_4580_7419, rux_110_4581_7424, ruy_113_4582_7429}, vec1_745_6046_8506_9049);
    CursorTy pvrtmp_15051 = tmp_struct_24.field0;
    CursorTy pvrtmp_15052 = tmp_struct_24.field1;
    CursorTy pvrtmp_15053 = tmp_struct_24.field2;
    CursorProd tmp_struct_25 =
                check_buildquadtree(pvrtmp_15051, vec1_745_6046_8506_9049, pvrtmp_15052);
    CursorTy pvrtmp_15058 = tmp_struct_25.field0;
    VectorTy *particles1_117_4586_7433 =
              oneStep_seq(pvrtmp_15051, pvrtmp_15052, vec1_745_6046_8506_9049, vec1_745_6020_8474_9044);

    free_region(end_r_10774);
    return 0;
}
unsigned char bench_seqbuildquadtree()
{
    RegionTy *region_15059 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10781 = region_15059->reg_heap;
    IntTy sizeof_end_r_10781_15060 = global_init_inf_buf_size;
    CursorTy end_r_10781 = r_10781 + sizeof_end_r_10781_15060;
    VectorTy *pts_118_4587_7434 = vector_alloc(read_arrayfile_length_param(),
                                               sizeof(Float32Float32Prod));
    Float32Float32Prod arr_elem_45;

    FILE * fp_46;

    char *line_47 = NULL;

    size_t(len_48);
    len_48 = 0;
    ssize_t(read_49);
    fp_46 = fopen(read_arrayfile_param(), "r");
    if (fp_46 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    FloatTy tmp_51;
    FloatTy tmp_52;
    IntTy i_50 = 0;

    while ((read_49 = getline(&line_47, &len_48, fp_46)) != -1) {
        int xxxx = sscanf(line_47, "%f %f", &tmp_51, &tmp_52);

        arr_elem_45.field0 = tmp_51;
        arr_elem_45.field1 = tmp_52;
        vector_inplace_update(pts_118_4587_7434, i_50, &arr_elem_45);
        i_50++;
    }

    IntTy fltAppE_7090_7436 = vector_length(pts_118_4587_7434);
    IntTy n__743_6031_8488_9052 =  maxInt(fltAppE_7090_7436, 0);
    IntTy tmp_44 = sizeof(Float32Float32Float32Float32Float32Prod);
    VectorTy *vec_744_6032_8489_9053 = vector_alloc(n__743_6031_8488_9052,
                                                    tmp_44);
    VectorTy *vec1_745_6033_8490_9054 =
              generate_loop_2377_3729(vec_744_6032_8489_9053, 0, n__743_6031_8488_9052, pts_118_4587_7434);
    IntTy fltAppE_7091_7439 = vector_length(pts_118_4587_7434);
    IntTy n__743_6057_8520_9057 =  maxInt(fltAppE_7091_7439, 0);
    IntTy tmp_43 = sizeof(Float32Float32Float32Prod);
    VectorTy *vec_744_6058_8521_9058 = vector_alloc(n__743_6057_8520_9057,
                                                    tmp_43);
    VectorTy *vec1_745_6059_8522_9059 =
              generate_loop_2376_3735(vec_744_6058_8521_9058, 0, n__743_6057_8520_9057, pts_118_4587_7434);
    IntTy fltAppE_7092_7443 = vector_length(pts_118_4587_7434);
    FloatTy llx_131_4590_7444 =
             foldl_loop_2368_3745(0, fltAppE_7092_7443, 100000.0, pts_118_4587_7434);
    IntTy fltAppE_7093_7447 = vector_length(pts_118_4587_7434);
    FloatTy lly_134_4591_7448 =
             foldl_loop_2368_3746(0, fltAppE_7093_7447, 100000.0, pts_118_4587_7434);
    FloatTy fltPrm_7094_7449 = 0.0 - 1.0;
    FloatTy acc_261_6141_6514_7450 = fltPrm_7094_7449 * 100000.0;
    IntTy fltAppE_7095_7452 = vector_length(pts_118_4587_7434);
    FloatTy rux_137_4592_7453 =
             foldl_loop_2368_3747(0, fltAppE_7095_7452, acc_261_6141_6514_7450, pts_118_4587_7434);
    FloatTy fltPrm_7096_7454 = 0.0 - 1.0;
    FloatTy acc_261_6148_6516_7455 = fltPrm_7096_7454 * 100000.0;
    IntTy fltAppE_7097_7457 = vector_length(pts_118_4587_7434);
    FloatTy ruy_140_4593_7458 =
             foldl_loop_2368_3748(0, fltAppE_7097_7457, acc_261_6148_6516_7455, pts_118_4587_7434);
    CursorTy pvrtmp_15078;
    CursorTy pvrtmp_15079;
    CursorTy pvrtmp_15080;
    VectorTy *times_40 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_15078;
    struct timespec end_pvrtmp_15078;

    for (long long iters_pvrtmp_15078 = 0; iters_pvrtmp_15078 <
         global_iters_param; iters_pvrtmp_15078++) {
        if (iters_pvrtmp_15078 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_15078);

        CursorCursorCursorProd tmp_struct_36 =
                                buildQtree_seq(end_r_10781, r_10781, (Float32Float32Float32Float32Prod) {llx_131_4590_7444, lly_134_4591_7448, rux_137_4592_7453, ruy_140_4593_7458}, vec1_745_6059_8522_9059);
        CursorTy pvrtmp_15069 = tmp_struct_36.field0;
        CursorTy pvrtmp_15070 = tmp_struct_36.field1;
        CursorTy pvrtmp_15071 = tmp_struct_36.field2;

        pvrtmp_15078 = pvrtmp_15069;
        pvrtmp_15079 = pvrtmp_15070;
        pvrtmp_15080 = pvrtmp_15071;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_15078);
        if (iters_pvrtmp_15078 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_37 = difftimespecs(&begin_pvrtmp_15078,
                                           &end_pvrtmp_15078);

        vector_inplace_update(times_40, iters_pvrtmp_15078, &itertime_37);
    }
    vector_inplace_sort(times_40, compare_doubles);

    double *tmp_41 = (double *) vector_nth(times_40, global_iters_param / 2);
    double selftimed_39 = *tmp_41;
    double batchtime_38 = sum_timing_array(times_40);

    print_timing_array(times_40);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_38);
    printf("SELFTIMED: %e\n", selftimed_39);

    CursorProd tmp_struct_42 =
                check_buildquadtree(end_r_10781, vec1_745_6059_8522_9059, pvrtmp_15079);
    CursorTy pvrtmp_15088 = tmp_struct_42.field0;

    free_region(end_r_10781);
    return 0;
}
unsigned char bench_seqnearest()
{
    RegionTy *region_15089 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10787 = region_15089->reg_heap;
    IntTy sizeof_end_r_10787_15090 = global_init_inf_buf_size;
    CursorTy end_r_10787 = r_10787 + sizeof_end_r_10787_15090;
    VectorTy *pts_143_4596_7461 = vector_alloc(read_arrayfile_length_param(),
                                               sizeof(Float32Float32Float32Prod));
    Float32Float32Float32Prod arr_elem_59;

    FILE * fp_60;

    char *line_61 = NULL;

    size_t(len_62);
    len_62 = 0;
    ssize_t(read_63);
    fp_60 = fopen(read_arrayfile_param(), "r");
    if (fp_60 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    FloatTy tmp_65;
    FloatTy tmp_66;
    FloatTy tmp_67;
    IntTy i_64 = 0;

    while ((read_63 = getline(&line_61, &len_62, fp_60)) != -1) {
        int xxxx = sscanf(line_61, "%f %f %f", &tmp_65, &tmp_66, &tmp_67);

        arr_elem_59.field0 = tmp_65;
        arr_elem_59.field1 = tmp_66;
        arr_elem_59.field2 = tmp_67;
        vector_inplace_update(pts_143_4596_7461, i_64, &arr_elem_59);
        i_64++;
    }

    CursorCursorCursorProd tmp_struct_53 =
                            mkKdTree_seq(end_r_10787, r_10787, pts_143_4596_7461);
    CursorTy pvrtmp_15091 = tmp_struct_53.field0;
    CursorTy pvrtmp_15092 = tmp_struct_53.field1;
    CursorTy pvrtmp_15093 = tmp_struct_53.field2;
    VectorTy *timed_14497;
    VectorTy *times_57 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_timed_14497;
    struct timespec end_timed_14497;

    for (long long iters_timed_14497 = 0; iters_timed_14497 <
         global_iters_param; iters_timed_14497++) {
        if (iters_timed_14497 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_14497);

        VectorTy *tailapp_12078 =
                  allNearest_seq(pvrtmp_15091, pvrtmp_15092, pts_143_4596_7461);

        timed_14497 = tailapp_12078;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_14497);
        if (iters_timed_14497 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_54 = difftimespecs(&begin_timed_14497,
                                           &end_timed_14497);

        vector_inplace_update(times_57, iters_timed_14497, &itertime_54);
    }
    vector_inplace_sort(times_57, compare_doubles);

    double *tmp_58 = (double *) vector_nth(times_57, global_iters_param / 2);
    double selftimed_56 = *tmp_58;
    double batchtime_55 = sum_timing_array(times_57);

    print_timing_array(times_57);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_55);
    printf("SELFTIMED: %e\n", selftimed_56);

    unsigned char tailapp_12079 =
                   check_nearest(pts_143_4596_7461, timed_14497);

    free_region(end_r_10787);
    return tailapp_12079;
}
unsigned char bench_seqcountcorr()
{
    RegionTy *region_15098 = alloc_region(global_init_inf_buf_size);
    CursorTy r_10793 = region_15098->reg_heap;
    IntTy sizeof_end_r_10793_15099 = global_init_inf_buf_size;
    CursorTy end_r_10793 = r_10793 + sizeof_end_r_10793_15099;
    VectorTy *pts_146_4599_7464 = vector_alloc(read_arrayfile_length_param(),
                                               sizeof(Float32Float32Float32Prod));
    Float32Float32Float32Prod arr_elem_76;

    FILE * fp_77;

    char *line_78 = NULL;

    size_t(len_79);
    len_79 = 0;
    ssize_t(read_80);
    fp_77 = fopen(read_arrayfile_param(), "r");
    if (fp_77 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    FloatTy tmp_82;
    FloatTy tmp_83;
    FloatTy tmp_84;
    IntTy i_81 = 0;

    while ((read_80 = getline(&line_78, &len_79, fp_77)) != -1) {
        int xxxx = sscanf(line_78, "%f %f %f", &tmp_82, &tmp_83, &tmp_84);

        arr_elem_76.field0 = tmp_82;
        arr_elem_76.field1 = tmp_83;
        arr_elem_76.field2 = tmp_84;
        vector_inplace_update(pts_146_4599_7464, i_81, &arr_elem_76);
        i_81++;
    }

    IntTy n_147_4600_7465 = global_size_param;
    CursorCursorCursorProd tmp_struct_68 =
                            mkKdTree_seq(end_r_10793, r_10793, pts_146_4599_7464);
    CursorTy pvrtmp_15100 = tmp_struct_68.field0;
    CursorTy pvrtmp_15101 = tmp_struct_68.field1;
    CursorTy pvrtmp_15102 = tmp_struct_68.field2;
    VectorTy *pts__150_4603_7471 = vector_slice(0, n_147_4600_7465,
                                                pts_146_4599_7464);
    VectorTy *timed_14498;
    VectorTy *times_72 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_timed_14498;
    struct timespec end_timed_14498;

    for (long long iters_timed_14498 = 0; iters_timed_14498 <
         global_iters_param; iters_timed_14498++) {
        if (iters_timed_14498 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_14498);

        VectorTy *tailapp_12080 =
                  allCountCorr_seq(pvrtmp_15100, 100.0, pvrtmp_15101, pts__150_4603_7471);

        timed_14498 = tailapp_12080;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_14498);
        if (iters_timed_14498 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_69 = difftimespecs(&begin_timed_14498,
                                           &end_timed_14498);

        vector_inplace_update(times_72, iters_timed_14498, &itertime_69);
    }
    vector_inplace_sort(times_72, compare_doubles);

    double *tmp_73 = (double *) vector_nth(times_72, global_iters_param / 2);
    double selftimed_71 = *tmp_73;
    double batchtime_70 = sum_timing_array(times_72);

    print_timing_array(times_72);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_70);
    printf("SELFTIMED: %e\n", selftimed_71);

    Float32Float32Float32Prod *tmp_75;

    tmp_75 = (Float32Float32Float32Prod *) vector_nth(pts__150_4603_7471, 4);

    Float32Float32Float32Prod query_152_4605_7475 = *tmp_75;
    IntTy *tmp_74;

    tmp_74 = (IntTy *) vector_nth(timed_14498, 4);

    IntTy count_153_4606_7478 = *tmp_74;
    unsigned char tailapp_12081 =
                   check_countcorr(pts__150_4603_7471, (Float32Float32Float32Prod) {query_152_4605_7475.field0, query_152_4605_7475.field1, query_152_4605_7475.field2}, count_153_4606_7478, 100.0);

    free_region(end_r_10793);
    return tailapp_12081;
}
CursorProd check_buildkdtree(CursorTy end_r_10636, VectorTy *pts_154_4607_7479,
                             CursorTy tr_155_4608_7480)
{
    FloatTy expected_156_4609_7481 =  sumList(pts_154_4607_7479);
    CursorFloat32Prod tmp_struct_85 =  sumKdTree(end_r_10636, tr_155_4608_7480);
    CursorTy pvrtmp_15110 = tmp_struct_85.field0;
    FloatTy pvrtmp_15111 = tmp_struct_85.field1;
    FloatTy err_158_4611_7483 = expected_156_4609_7481 - pvrtmp_15111;
    unsigned char wildcard__617_159_4612_7484 = print_symbol(14964);
    unsigned char wildcard__615_160_4613_7485 = printf("%.2f",
                                                       expected_156_4609_7481);
    unsigned char wildcard__613_161_4614_7486 = print_symbol(14985);
    unsigned char wildcard__611_162_4615_7487 = print_symbol(14967);
    unsigned char wildcard__609_163_4616_7488 = printf("%.2f", pvrtmp_15111);
    unsigned char wildcard__607_164_4617_7489 = print_symbol(14985);
    FloatTy fltPrm_7099_7490 =  float_abs(err_158_4611_7483);
    BoolTy fltAppE_7098_7491 = fltPrm_7099_7490 < 0.1;
    unsigned char tailapp_12083 =  print_check(fltAppE_7098_7491);

    return (CursorProd) {pvrtmp_15110};
}
CursorCursorCursorProd mkKdTree_seq(CursorTy end_r_10638, CursorTy loc_10637,
                                    VectorTy *pts_165_4618_7492)
{
    if (loc_10637 + 73 > end_r_10638) {
        ChunkTy new_chunk_87 = alloc_chunk(end_r_10638);
        CursorTy chunk_start_88 = new_chunk_87.chunk_start;
        CursorTy chunk_end_89 = new_chunk_87.chunk_end;

        end_r_10638 = chunk_end_89;
        *(TagTyPacked *) loc_10637 = 255;

        CursorTy redir = loc_10637 + 1;

        *(CursorTy *) redir = chunk_start_88;
        loc_10637 = chunk_start_88;
    }

    CursorCursorCursorProd tmp_struct_86 =
                            mkKdTreeWithAxis_seq(end_r_10638, loc_10637, 0, pts_165_4618_7492);
    CursorTy pvrtmp_15112 = tmp_struct_86.field0;
    CursorTy pvrtmp_15113 = tmp_struct_86.field1;
    CursorTy pvrtmp_15114 = tmp_struct_86.field2;

    return (CursorCursorCursorProd) {pvrtmp_15112, pvrtmp_15113, pvrtmp_15114};
}
unsigned char check_countcorr(VectorTy *pts_166_4619_7493,
                              Float32Float32Float32Prod query_167_4620_7494,
                              IntTy actual_168_4621_7495,
                              FloatTy radius_169_4622_7496)
{
    FloatTy radius_sq_170_4623_7497 = radius_169_4622_7496 *
            radius_169_4622_7496;
    IntTy fltAppE_7100_7502 = vector_length(pts_166_4619_7493);
    IntTy expected_173_4624_7503 =
           foldl_loop_2369_3740(0, fltAppE_7100_7502, 0, pts_166_4619_7493, (Float32Float32Float32Prod) {query_167_4620_7494.field0, query_167_4620_7494.field1, query_167_4620_7494.field2}, radius_sq_170_4623_7497);
    unsigned char wildcard__636_174_4625_7504 = print_symbol(14964);
    unsigned char wildcard__634_175_4626_7505 = printf("%lld",
                                                       expected_173_4624_7503);
    unsigned char wildcard__632_176_4627_7506 = print_symbol(14985);
    unsigned char wildcard__630_177_4628_7507 = print_symbol(14967);
    unsigned char wildcard__628_178_4629_7508 = printf("%lld",
                                                       actual_168_4621_7495);
    unsigned char wildcard__626_179_4630_7509 = print_symbol(14985);
    BoolTy fltAppE_7101_7510 = expected_173_4624_7503 == actual_168_4621_7495;
    unsigned char tailapp_12085 =  print_check(fltAppE_7101_7510);

    return tailapp_12085;
}
VectorTy *allCountCorr_seq(CursorTy end_r_10640, FloatTy radius_183_4631_7511,
                           CursorTy tr_184_4632_7512,
                           VectorTy *ls_185_4633_7513)
{
    IntTy fltAppE_7102_7517 = vector_length(ls_185_4633_7513);
    IntTy n__743_6003_8452_9064 =  maxInt(fltAppE_7102_7517, 0);
    IntTy tmp_90 = sizeof(IntTy);
    VectorTy *vec_744_6004_8453_9065 = vector_alloc(n__743_6003_8452_9064,
                                                    tmp_90);
    VectorTy *vec1_745_6005_8454_9066 =
              generate_loop_2374_3723(end_r_10640, vec_744_6004_8453_9065, 0, n__743_6003_8452_9064, ls_185_4633_7513, radius_183_4631_7511, tr_184_4632_7512);

    return vec1_745_6005_8454_9066;
}
unsigned char check_nearest(VectorTy *pts_191_4634_7518,
                            VectorTy *actual_192_4635_7519)
{
    IntTy n_193_4636_7521 = vector_length(pts_191_4634_7518);
    IntTy n__743_5957_6534_7523 =  maxInt(n_193_4636_7521, 0);
    IntTy tmp_92 = sizeof(IntTy);
    VectorTy *vec_744_5958_6535_7524 = vector_alloc(n__743_5957_6534_7523,
                                                    tmp_92);
    VectorTy *vec1_745_5959_6536_7525 =
              generate_loop_2374_3714(vec_744_5958_6535_7524, 0, n__743_5957_6534_7523);
    IntTy fltAppE_7104_7532 = vector_length(vec1_745_5959_6536_7525);
    BoolInt64Prod tmp_struct_91 =
                   foldl_loop_2367_3749(0, fltAppE_7104_7532, (BoolInt64Prod) {true, 0}, vec1_745_5959_6536_7525, pts_191_4634_7518, actual_192_4635_7519);
    BoolTy pvrtmp_15128 = tmp_struct_91.field0;
    IntTy pvrtmp_15129 = tmp_struct_91.field1;
    unsigned char tailapp_12086 =  print_check(pvrtmp_15128);

    return tailapp_12086;
}
VectorTy *allNearest_seq(CursorTy end_r_10642, CursorTy tr_207_4642_7537,
                         VectorTy *ls_208_4643_7538)
{
    IntTy fltAppE_7105_7541 = vector_length(ls_208_4643_7538);
    IntTy n__743_5986_8432_9070 =  maxInt(fltAppE_7105_7541, 0);
    IntTy tmp_93 = sizeof(Float32Float32Float32Prod);
    VectorTy *vec_744_5987_8433_9071 = vector_alloc(n__743_5986_8432_9070,
                                                    tmp_93);
    VectorTy *vec1_745_5988_8434_9072 =
              generate_loop_2376_3720(end_r_10642, vec_744_5987_8433_9071, 0, n__743_5986_8432_9070, ls_208_4643_7538, tr_207_4642_7537);

    return vec1_745_5988_8434_9072;
}
CursorProd check_buildquadtree(CursorTy end_r_10644,
                               VectorTy *mpts_210_4644_7542,
                               CursorTy bht_211_4645_7543)
{
    FloatTy expected_212_4646_7544 =  sum_mass_points(mpts_210_4644_7542);
    CursorFloat32Prod tmp_struct_94 =  sumQtree(end_r_10644, bht_211_4645_7543);
    CursorTy pvrtmp_15130 = tmp_struct_94.field0;
    FloatTy pvrtmp_15131 = tmp_struct_94.field1;
    CursorInt64Prod tmp_struct_95 =
                     countLeavesQtree(end_r_10644, bht_211_4645_7543);
    CursorTy pvrtmp_15132 = tmp_struct_95.field0;
    IntTy pvrtmp_15133 = tmp_struct_95.field1;
    IntTy count2_215_4649_7547 =
           getTotalPoints_qtree(end_r_10644, bht_211_4645_7543);
    unsigned char wildcard__424_216_4650_7548 = print_symbol(14962);
    unsigned char wildcard__422_217_4651_7549 = printf("%.2f",
                                                       expected_212_4646_7544);
    unsigned char wildcard__420_218_4652_7550 = print_symbol(14968);
    unsigned char wildcard__418_219_4653_7551 = print_symbol(14961);
    unsigned char wildcard__416_220_4654_7552 = printf("%.2f", pvrtmp_15131);
    unsigned char wildcard__414_221_4655_7553 = print_symbol(14985);
    unsigned char wildcard__412_222_4656_7554 = print_symbol(14966);
    unsigned char wildcard__410_223_4657_7555 = printf("%lld", pvrtmp_15133);
    unsigned char wildcard__408_224_4658_7556 = print_symbol(14968);
    unsigned char wildcard__406_225_4659_7557 = printf("%lld",
                                                       count2_215_4649_7547);
    unsigned char wildcard__404_226_4660_7558 = print_symbol(14985);
    FloatTy fltAppE_7108_7559 = expected_212_4646_7544 - pvrtmp_15131;
    FloatTy fltPrm_7107_7560 =  float_abs(fltAppE_7108_7559);
    BoolTy fltAppE_7106_7561 = fltPrm_7107_7560 < 1.0e-2;
    unsigned char tailapp_12089 =  print_check(fltAppE_7106_7561);

    return (CursorProd) {pvrtmp_15132};
}
CursorCursorCursorProd buildQtree_seq(CursorTy end_r_10646, CursorTy loc_10645,
                                      Float32Float32Float32Float32Prod box_227_4661_7562,
                                      VectorTy *mpts_228_4662_7563)
{
    if (loc_10645 + 57 > end_r_10646) {
        ChunkTy new_chunk_102 = alloc_chunk(end_r_10646);
        CursorTy chunk_start_103 = new_chunk_102.chunk_start;
        CursorTy chunk_end_104 = new_chunk_102.chunk_end;

        end_r_10646 = chunk_end_104;
        *(TagTyPacked *) loc_10645 = 255;

        CursorTy redir = loc_10645 + 1;

        *(CursorTy *) redir = chunk_start_103;
        loc_10645 = chunk_start_103;
    }

    CursorTy loc_10834 = loc_10645 + 1;
    CursorTy loc_10835 = loc_10834 + 8;
    CursorTy loc_10836 = loc_10835 + 8;
    CursorTy loc_10837 = loc_10836 + 8;
    CursorTy loc_10838 = loc_10837 + 4;
    CursorTy loc_10839 = loc_10838 + 4;
    CursorTy loc_10840 = loc_10839 + 4;
    CursorTy loc_10841 = loc_10840 + 8;
    CursorTy loc_10842 = loc_10841 + 4;
    IntTy len_229_4663_7565 = vector_length(mpts_228_4662_7563);
    BoolTy fltIf_7109_7571 = len_229_4663_7565 == 0;

    if (fltIf_7109_7571) {
        *(TagTyPacked *) loc_10645 = 0;

        CursorTy writetag_13005 = loc_10645 + 1;

        return (CursorCursorCursorProd) {end_r_10646, loc_10645,
                                         writetag_13005};
    } else {
        BoolTy fltIf_7110_7572 = len_229_4663_7565 == 1;

        if (fltIf_7110_7572) {
            Float32Float32Float32Prod tmp_struct_96 =
                                       calcCentroid_seq(mpts_228_4662_7563);
            FloatTy pvrtmp_15138 = tmp_struct_96.field0;
            FloatTy pvrtmp_15139 = tmp_struct_96.field1;
            FloatTy pvrtmp_15140 = tmp_struct_96.field2;

            *(TagTyPacked *) loc_10645 = 1;

            CursorTy writetag_13007 = loc_10645 + 1;

            *(FloatTy *) writetag_13007 = pvrtmp_15138;

            CursorTy writecur_13008 = writetag_13007 + sizeof(FloatTy);

            *(FloatTy *) writecur_13008 = pvrtmp_15139;

            CursorTy writecur_13009 = writecur_13008 + sizeof(FloatTy);

            *(FloatTy *) writecur_13009 = pvrtmp_15140;

            CursorTy writecur_13010 = writecur_13009 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {end_r_10646, loc_10645,
                                             writecur_13010};
        } else {
            Float32Float32Float32Prod tmp_struct_97 =
                                       calcCentroid_seq(mpts_228_4662_7563);
            FloatTy pvrtmp_15145 = tmp_struct_97.field0;
            FloatTy pvrtmp_15146 = tmp_struct_97.field1;
            FloatTy pvrtmp_15147 = tmp_struct_97.field2;
            FloatTy fltPrm_7111_7578 = box_227_4661_7562.field0 +
                    box_227_4661_7562.field2;
            FloatTy midx_240_4674_7579 = fltPrm_7111_7578 / 2.0;
            FloatTy fltPrm_7112_7580 = box_227_4661_7562.field1 +
                    box_227_4661_7562.field3;
            FloatTy midy_241_4675_7581 = fltPrm_7112_7580 / 2.0;
            VectorTy *p1_246_4680_7586 =
                      masspointsInBox_seq((Float32Float32Float32Float32Prod) {box_227_4661_7562.field0, box_227_4661_7562.field1, midx_240_4674_7579, midy_241_4675_7581}, mpts_228_4662_7563);
            CursorCursorCursorProd tmp_struct_98 =
                                    buildQtree_seq(end_r_10646, loc_10842, (Float32Float32Float32Float32Prod) {box_227_4661_7562.field0, box_227_4661_7562.field1, midx_240_4674_7579, midy_241_4675_7581}, p1_246_4680_7586);
            CursorTy pvrtmp_15172 = tmp_struct_98.field0;
            CursorTy pvrtmp_15173 = tmp_struct_98.field1;
            CursorTy pvrtmp_15174 = tmp_struct_98.field2;
            VectorTy *p2_248_4682_7588 =
                      masspointsInBox_seq((Float32Float32Float32Float32Prod) {box_227_4661_7562.field0, midy_241_4675_7581, midx_240_4674_7579, box_227_4661_7562.field3}, mpts_228_4662_7563);
            CursorCursorCursorProd tmp_struct_99 =
                                    buildQtree_seq(pvrtmp_15172, pvrtmp_15174, (Float32Float32Float32Float32Prod) {box_227_4661_7562.field0, midy_241_4675_7581, midx_240_4674_7579, box_227_4661_7562.field3}, p2_248_4682_7588);
            CursorTy pvrtmp_15187 = tmp_struct_99.field0;
            CursorTy pvrtmp_15188 = tmp_struct_99.field1;
            CursorTy pvrtmp_15189 = tmp_struct_99.field2;
            VectorTy *p3_250_4684_7590 =
                      masspointsInBox_seq((Float32Float32Float32Float32Prod) {midx_240_4674_7579, midy_241_4675_7581, box_227_4661_7562.field2, box_227_4661_7562.field3}, mpts_228_4662_7563);
            CursorCursorCursorProd tmp_struct_100 =
                                    buildQtree_seq(pvrtmp_15187, pvrtmp_15189, (Float32Float32Float32Float32Prod) {midx_240_4674_7579, midy_241_4675_7581, box_227_4661_7562.field2, box_227_4661_7562.field3}, p3_250_4684_7590);
            CursorTy pvrtmp_15202 = tmp_struct_100.field0;
            CursorTy pvrtmp_15203 = tmp_struct_100.field1;
            CursorTy pvrtmp_15204 = tmp_struct_100.field2;
            VectorTy *p4_252_4686_7592 =
                      masspointsInBox_seq((Float32Float32Float32Float32Prod) {midx_240_4674_7579, box_227_4661_7562.field1, box_227_4661_7562.field2, midy_241_4675_7581}, mpts_228_4662_7563);
            CursorCursorCursorProd tmp_struct_101 =
                                    buildQtree_seq(pvrtmp_15202, pvrtmp_15204, (Float32Float32Float32Float32Prod) {midx_240_4674_7579, box_227_4661_7562.field1, box_227_4661_7562.field2, midy_241_4675_7581}, p4_252_4686_7592);
            CursorTy pvrtmp_15217 = tmp_struct_101.field0;
            CursorTy pvrtmp_15218 = tmp_struct_101.field1;
            CursorTy pvrtmp_15219 = tmp_struct_101.field2;
            IntTy fltPrm_7115_7594 =
                   getTotalPoints_qtree(pvrtmp_15217, pvrtmp_15173);
            IntTy fltPrm_7116_7595 =
                   getTotalPoints_qtree(pvrtmp_15217, pvrtmp_15188);
            IntTy fltPrm_7114_7596 = fltPrm_7115_7594 + fltPrm_7116_7595;
            IntTy fltPrm_7117_7597 =
                   getTotalPoints_qtree(pvrtmp_15217, pvrtmp_15203);
            IntTy fltPrm_7113_7598 = fltPrm_7114_7596 + fltPrm_7117_7597;
            IntTy fltPrm_7118_7599 =
                   getTotalPoints_qtree(pvrtmp_15217, pvrtmp_15218);
            IntTy total_points_254_4688_7600 = fltPrm_7113_7598 +
                  fltPrm_7118_7599;
            FloatTy fltAppE_7119_7607 = box_227_4661_7562.field2 -
                    box_227_4661_7562.field0;
            FloatTy fltAppE_7120_7608 = box_227_4661_7562.field3 -
                    box_227_4661_7562.field1;
            FloatTy width_255_4689_7609 =
                     maxFloat(fltAppE_7119_7607, fltAppE_7120_7608);

            *(TagTyPacked *) loc_10645 = 3;

            CursorTy writetag_13016 = loc_10645 + 1;

            *(CursorTy *) writetag_13016 = pvrtmp_15174;

            CursorTy writecur_13017 = writetag_13016 + 8;

            *(CursorTy *) writecur_13017 = pvrtmp_15189;

            CursorTy writecur_13018 = writecur_13017 + 8;

            *(CursorTy *) writecur_13018 = pvrtmp_15204;

            CursorTy writecur_13019 = writecur_13018 + 8;

            *(FloatTy *) writecur_13019 = pvrtmp_15145;

            CursorTy writecur_13020 = writecur_13019 + sizeof(FloatTy);

            *(FloatTy *) writecur_13020 = pvrtmp_15146;

            CursorTy writecur_13021 = writecur_13020 + sizeof(FloatTy);

            *(FloatTy *) writecur_13021 = pvrtmp_15147;

            CursorTy writecur_13022 = writecur_13021 + sizeof(FloatTy);

            *(IntTy *) writecur_13022 = total_points_254_4688_7600;

            CursorTy writecur_13023 = writecur_13022 + sizeof(IntTy);

            *(FloatTy *) writecur_13023 = width_255_4689_7609;

            CursorTy writecur_13024 = writecur_13023 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {pvrtmp_15217, loc_10645,
                                             pvrtmp_15219};
        }
    }
}
FloatTy maxFloat(FloatTy a_265_4694_7614, FloatTy b_266_4695_7615)
{
    BoolTy fltIf_7121_7616 = a_265_4694_7614 > b_266_4695_7615;

    if (fltIf_7121_7616) {
        return a_265_4694_7614;
    } else {
        return b_266_4695_7615;
    }
}
FloatTy minFloat(FloatTy a_267_4696_7617, FloatTy b_268_4697_7618)
{
    BoolTy fltIf_7122_7619 = a_267_4696_7617 < b_268_4697_7618;

    if (fltIf_7122_7619) {
        return a_267_4696_7617;
    } else {
        return b_268_4697_7618;
    }
}
VectorTy *oneStep_seq(CursorTy end_r_10648, CursorTy bht_274_4698_7620,
                      VectorTy *mpts_275_4699_7621, VectorTy *ps_276_4700_7622)
{
    VectorTy *timed_14499;
    VectorTy *times_109 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_timed_14499;
    struct timespec end_timed_14499;

    for (long long iters_timed_14499 = 0; iters_timed_14499 <
         global_iters_param; iters_timed_14499++) {
        if (iters_timed_14499 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_14499);

        IntTy n_740_5662_6551_7624 = vector_length(ps_276_4700_7622);
        IntTy n__743_5666_6555_7628 =  maxInt(n_740_5662_6551_7624, 0);
        IntTy tmp_105 = sizeof(Float32Float32Float32Float32Float32Prod);
        VectorTy *vec_744_5667_6556_7629 = vector_alloc(n__743_5666_6555_7628,
                                                        tmp_105);
        VectorTy *vec1_745_5668_6557_7630 =
                  generate_loop_2377_3710(end_r_10648, vec_744_5667_6556_7629, 0, n__743_5666_6555_7628, bht_274_4698_7620, mpts_275_4699_7621, ps_276_4700_7622);

        timed_14499 = vec1_745_5668_6557_7630;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_14499);
        if (iters_timed_14499 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_106 = difftimespecs(&begin_timed_14499,
                                            &end_timed_14499);

        vector_inplace_update(times_109, iters_timed_14499, &itertime_106);
    }
    vector_inplace_sort(times_109, compare_doubles);

    double *tmp_110 = (double *) vector_nth(times_109, global_iters_param / 2);
    double selftimed_108 = *tmp_110;
    double batchtime_107 = sum_timing_array(times_109);

    print_timing_array(times_109);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_107);
    printf("SELFTIMED: %e\n", selftimed_108);
    return timed_14499;
}
CursorInt64Prod sumExp(CursorTy end_r_10650, CursorTy exp_282_4702_7632)
{
    TagTyPacked tmpval_15228 = *(TagTyPacked *) exp_282_4702_7632;
    CursorTy tmpcur_15229 = exp_282_4702_7632 + 1;


  switch_15244:
    ;
    switch (tmpval_15228) {

      case 0:
        {
            IntTy tmpval_15230 = *(IntTy *) tmpcur_15229;
            CursorTy tmpcur_15231 = tmpcur_15229 + sizeof(IntTy);
            CursorTy jump_12093 = tmpcur_15229 + 8;

            return (CursorInt64Prod) {jump_12093, tmpval_15230};
            break;
        }

      case 3:
        {
            CursorInt64Prod tmp_struct_111 =  sumExp(end_r_10650, tmpcur_15229);
            CursorTy pvrtmp_15232 = tmp_struct_111.field0;
            IntTy pvrtmp_15233 = tmp_struct_111.field1;
            CursorInt64Prod tmp_struct_112 =  sumExp(end_r_10650, pvrtmp_15232);
            CursorTy pvrtmp_15234 = tmp_struct_112.field0;
            IntTy pvrtmp_15235 = tmp_struct_112.field1;
            IntTy tailprim_12096 = pvrtmp_15233 + pvrtmp_15235;

            return (CursorInt64Prod) {pvrtmp_15234, tailprim_12096};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15236 = *(CursorTy *) tmpcur_15229;
            CursorTy tmpaftercur_15237 = tmpcur_15229 + 8;
            CursorTy jump_12728 = tmpcur_15229 + 8;
            CursorInt64Prod tmp_struct_113 =  sumExp(end_r_10650, tmpcur_15236);
            CursorTy pvrtmp_15238 = tmp_struct_113.field0;
            IntTy pvrtmp_15239 = tmp_struct_113.field1;

            return (CursorInt64Prod) {jump_12728, pvrtmp_15239};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15240 = *(CursorTy *) tmpcur_15229;
            CursorTy tmpaftercur_15241 = tmpcur_15229 + 8;
            CursorInt64Prod tmp_struct_114 =  sumExp(end_r_10650, tmpcur_15240);
            CursorTy pvrtmp_15242 = tmp_struct_114.field0;
            IntTy pvrtmp_15243 = tmp_struct_114.field1;

            return (CursorInt64Prod) {pvrtmp_15242, pvrtmp_15243};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15228");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd foldConstants2(CursorTy end_r_10653,
                                            CursorTy end_r_10654,
                                            CursorTy loc_10652,
                                            CursorTy exp_286_4706_7638)
{
    if (loc_10652 + 32 > end_r_10654) {
        ChunkTy new_chunk_122 = alloc_chunk(end_r_10654);
        CursorTy chunk_start_123 = new_chunk_122.chunk_start;
        CursorTy chunk_end_124 = new_chunk_122.chunk_end;

        end_r_10654 = chunk_end_124;
        *(TagTyPacked *) loc_10652 = 255;

        CursorTy redir = loc_10652 + 1;

        *(CursorTy *) redir = chunk_start_123;
        loc_10652 = chunk_start_123;
    }

    CursorTy loc_10902 = loc_10652 + 1;
    TagTyPacked tmpval_15245 = *(TagTyPacked *) exp_286_4706_7638;
    CursorTy tmpcur_15246 = exp_286_4706_7638 + 1;


  switch_15329:
    ;
    switch (tmpval_15245) {

      case 0:
        {
            IntTy tmpval_15247 = *(IntTy *) tmpcur_15246;
            CursorTy tmpcur_15248 = tmpcur_15246 + sizeof(IntTy);
            CursorTy jump_12097 = tmpcur_15246 + 8;

            *(TagTyPacked *) loc_10652 = 0;

            CursorTy writetag_13043 = loc_10652 + 1;

            *(IntTy *) writetag_13043 = tmpval_15247;

            CursorTy writecur_13044 = writetag_13043 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_10654, jump_12097,
                                                   loc_10652, writecur_13044};
            break;
        }

      case 1:
        {
            CursorTy jump_12099 = exp_286_4706_7638 + 1;

            *(TagTyPacked *) loc_10652 = 1;

            CursorTy writetag_13047 = loc_10652 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10654, jump_12099,
                                                   loc_10652, writetag_13047};
            break;
        }

      case 2:
        {
            CursorTy jump_12101 = exp_286_4706_7638 + 1;

            *(TagTyPacked *) loc_10652 = 2;

            CursorTy writetag_13050 = loc_10652 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10654, jump_12101,
                                                   loc_10652, writetag_13050};
            break;
        }

      case 3:
        {
            FloatTy maybe_alit_290_4710_7642 =
                     maybeLit(end_r_10653, tmpcur_15246);
            FloatTy fltPrm_7128_7644 = 0.0 - 3.14;
            FloatTy fltPrm_7127_7645 = maybe_alit_290_4710_7642 -
                    fltPrm_7128_7644;
            BoolTy fltIf_7126_7646 = fltPrm_7127_7645 < 1.0e-2;
            BoolTy fltIf_7125_7647;

            if (fltIf_7126_7646) {
                fltIf_7125_7647 = false;
            } else {
                fltIf_7125_7647 = true;
            }
            if (fltIf_7125_7647) {
                CursorProd tmp_struct_115 =
                            trav_exp(end_r_10653, tmpcur_15246);
                CursorTy pvrtmp_15263 = tmp_struct_115.field0;
                FloatTy maybe_blit_292_4712_7649 =
                         maybeLit(end_r_10653, pvrtmp_15263);
                FloatTy fltPrm_7132_7651 = 0.0 - 3.14;
                FloatTy fltPrm_7131_7652 = maybe_blit_292_4712_7649 -
                        fltPrm_7132_7651;
                BoolTy fltIf_7130_7653 = fltPrm_7131_7652 < 1.0e-2;
                BoolTy fltIf_7129_7654;

                if (fltIf_7130_7653) {
                    fltIf_7129_7654 = false;
                } else {
                    fltIf_7129_7654 = true;
                }
                if (fltIf_7129_7654) {
                    CursorProd tmp_struct_116 =
                                trav_exp(end_r_10653, pvrtmp_15263);
                    CursorTy pvrtmp_15266 = tmp_struct_116.field0;
                    IntTy fltPrm_7134_7656 = (IntTy) maybe_alit_290_4710_7642;
                    IntTy fltPrm_7135_7657 = (IntTy) maybe_blit_292_4712_7649;
                    IntTy fltPkd_7133_7658 = fltPrm_7134_7656 +
                          fltPrm_7135_7657;

                    *(TagTyPacked *) loc_10652 = 0;

                    CursorTy writetag_13055 = loc_10652 + 1;

                    *(IntTy *) writetag_13055 = fltPkd_7133_7658;

                    CursorTy writecur_13056 = writetag_13055 + sizeof(IntTy);

                    return (CursorCursorCursorCursorProd) {end_r_10654,
                                                           pvrtmp_15266,
                                                           loc_10652,
                                                           writecur_13056};
                } else {
                    IntTy fltPkd_7136_7659 = (IntTy) maybe_alit_290_4710_7642;

                    *(TagTyPacked *) loc_10902 = 0;

                    CursorTy writetag_13058 = loc_10902 + 1;

                    *(IntTy *) writetag_13058 = fltPkd_7136_7659;

                    CursorTy writecur_13059 = writetag_13058 + sizeof(IntTy);
                    CursorCursorCursorCursorProd tmp_struct_117 =
                                                  foldConstants2(end_r_10653, end_r_10654, writecur_13059, pvrtmp_15263);
                    CursorTy pvrtmp_15273 = tmp_struct_117.field0;
                    CursorTy pvrtmp_15274 = tmp_struct_117.field1;
                    CursorTy pvrtmp_15275 = tmp_struct_117.field2;
                    CursorTy pvrtmp_15276 = tmp_struct_117.field3;

                    *(TagTyPacked *) loc_10652 = 3;

                    CursorTy writetag_13062 = loc_10652 + 1;

                    return (CursorCursorCursorCursorProd) {pvrtmp_15273,
                                                           pvrtmp_15274,
                                                           loc_10652,
                                                           pvrtmp_15276};
                }
            } else {
                CursorCursorCursorCursorProd tmp_struct_118 =
                                              foldConstants2(end_r_10653, end_r_10654, loc_10902, tmpcur_15246);
                CursorTy pvrtmp_15285 = tmp_struct_118.field0;
                CursorTy pvrtmp_15286 = tmp_struct_118.field1;
                CursorTy pvrtmp_15287 = tmp_struct_118.field2;
                CursorTy pvrtmp_15288 = tmp_struct_118.field3;
                CursorCursorCursorCursorProd tmp_struct_119 =
                                              foldConstants2(end_r_10653, pvrtmp_15285, pvrtmp_15288, pvrtmp_15286);
                CursorTy pvrtmp_15293 = tmp_struct_119.field0;
                CursorTy pvrtmp_15294 = tmp_struct_119.field1;
                CursorTy pvrtmp_15295 = tmp_struct_119.field2;
                CursorTy pvrtmp_15296 = tmp_struct_119.field3;

                *(TagTyPacked *) loc_10652 = 3;

                CursorTy writetag_13068 = loc_10652 + 1;

                return (CursorCursorCursorCursorProd) {pvrtmp_15293,
                                                       pvrtmp_15294, loc_10652,
                                                       pvrtmp_15296};
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15305 = *(CursorTy *) tmpcur_15246;
            CursorTy tmpaftercur_15306 = tmpcur_15246 + 8;
            CursorTy jump_12734 = tmpcur_15246 + 8;
            CursorCursorCursorCursorProd tmp_struct_120 =
                                          foldConstants2(end_r_10653, end_r_10654, loc_10652, tmpcur_15305);
            CursorTy pvrtmp_15307 = tmp_struct_120.field0;
            CursorTy pvrtmp_15308 = tmp_struct_120.field1;
            CursorTy pvrtmp_15309 = tmp_struct_120.field2;
            CursorTy pvrtmp_15310 = tmp_struct_120.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_15307, jump_12734,
                                                   pvrtmp_15309, pvrtmp_15310};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15317 = *(CursorTy *) tmpcur_15246;
            CursorTy tmpaftercur_15318 = tmpcur_15246 + 8;
            CursorCursorCursorCursorProd tmp_struct_121 =
                                          foldConstants2(end_r_10653, end_r_10654, loc_10652, tmpcur_15317);
            CursorTy pvrtmp_15319 = tmp_struct_121.field0;
            CursorTy pvrtmp_15320 = tmp_struct_121.field1;
            CursorTy pvrtmp_15321 = tmp_struct_121.field2;
            CursorTy pvrtmp_15322 = tmp_struct_121.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_15319, pvrtmp_15320,
                                                   pvrtmp_15321, pvrtmp_15322};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15245");
            exit(1);
        }
    }
}
CursorCursorCursorProd buildExp(CursorTy end_r_10656, CursorTy loc_10655,
                                IntTy n_298_4718_7664)
{
    if (loc_10655 + 32 > end_r_10656) {
        ChunkTy new_chunk_127 = alloc_chunk(end_r_10656);
        CursorTy chunk_start_128 = new_chunk_127.chunk_start;
        CursorTy chunk_end_129 = new_chunk_127.chunk_end;

        end_r_10656 = chunk_end_129;
        *(TagTyPacked *) loc_10655 = 255;

        CursorTy redir = loc_10655 + 1;

        *(CursorTy *) redir = chunk_start_128;
        loc_10655 = chunk_start_128;
    }

    CursorTy loc_10920 = loc_10655 + 1;
    BoolTy fltIf_7137_7665 = n_298_4718_7664 == 0;

    if (fltIf_7137_7665) {
        *(TagTyPacked *) loc_10920 = 0;

        CursorTy writetag_13078 = loc_10920 + 1;

        *(IntTy *) writetag_13078 = 0;

        CursorTy writecur_13079 = writetag_13078 + sizeof(IntTy);

        *(TagTyPacked *) writecur_13079 = 0;

        CursorTy writetag_13081 = writecur_13079 + 1;

        *(IntTy *) writetag_13081 = 1;

        CursorTy writecur_13082 = writetag_13081 + sizeof(IntTy);

        *(TagTyPacked *) loc_10655 = 3;

        CursorTy writetag_13084 = loc_10655 + 1;

        return (CursorCursorCursorProd) {end_r_10656, loc_10655,
                                         writecur_13082};
    } else {
        IntTy fltAppE_7141_7668 = n_298_4718_7664 - 1;
        CursorCursorCursorProd tmp_struct_125 =
                                buildExp(end_r_10656, loc_10920, fltAppE_7141_7668);
        CursorTy pvrtmp_15338 = tmp_struct_125.field0;
        CursorTy pvrtmp_15339 = tmp_struct_125.field1;
        CursorTy pvrtmp_15340 = tmp_struct_125.field2;
        IntTy fltAppE_7143_7670 = n_298_4718_7664 - 1;
        CursorCursorCursorProd tmp_struct_126 =
                                buildExp(pvrtmp_15338, pvrtmp_15340, fltAppE_7143_7670);
        CursorTy pvrtmp_15345 = tmp_struct_126.field0;
        CursorTy pvrtmp_15346 = tmp_struct_126.field1;
        CursorTy pvrtmp_15347 = tmp_struct_126.field2;

        *(TagTyPacked *) loc_10655 = 3;

        CursorTy writetag_13090 = loc_10655 + 1;

        return (CursorCursorCursorProd) {pvrtmp_15345, loc_10655, pvrtmp_15347};
    }
}
FloatTy sumList(VectorTy *ls_317_4737_7672)
{
    IntTy fltAppE_7144_7675 = vector_length(ls_317_4737_7672);
    FloatTy tailapp_12113 =
             foldl_loop_2370_3738(0, fltAppE_7144_7675, 0.0, ls_317_4737_7672);

    return tailapp_12113;
}
CursorFloat32Prod sumKdTree(CursorTy end_r_10658, CursorTy tr_344_4758_7676)
{
    TagTyPacked tmpval_15356 = *(TagTyPacked *) tr_344_4758_7676;
    CursorTy tmpcur_15357 = tr_344_4758_7676 + 1;


  switch_15402:
    ;
    switch (tmpval_15356) {

      case 2:
        {
            CursorTy jump_12115 = tr_344_4758_7676 + 1;

            return (CursorFloat32Prod) {jump_12115, 0.0};
            break;
        }

      case 0:
        {
            FloatTy tmpval_15358 = *(FloatTy *) tmpcur_15357;
            CursorTy tmpcur_15359 = tmpcur_15357 + sizeof(FloatTy);
            FloatTy tmpval_15360 = *(FloatTy *) tmpcur_15359;
            CursorTy tmpcur_15361 = tmpcur_15359 + sizeof(FloatTy);
            FloatTy tmpval_15362 = *(FloatTy *) tmpcur_15361;
            CursorTy tmpcur_15363 = tmpcur_15361 + sizeof(FloatTy);
            CursorTy jump_12118 = tmpcur_15361 + 4;
            CursorTy jump_12117 = tmpcur_15359 + 4;
            CursorTy jump_12116 = tmpcur_15357 + 4;
            FloatTy fltPrm_7145_7680 = tmpval_15358 + tmpval_15360;
            FloatTy tailprim_12119 = fltPrm_7145_7680 + tmpval_15362;

            return (CursorFloat32Prod) {jump_12118, tailprim_12119};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15364 = *(CursorTy *) tmpcur_15357;
            CursorTy tmpaftercur_15365 = tmpcur_15357 + 8;
            FloatTy tmpval_15366 = *(FloatTy *) tmpaftercur_15365;
            CursorTy tmpcur_15367 = tmpaftercur_15365 + sizeof(FloatTy);
            FloatTy tmpval_15368 = *(FloatTy *) tmpcur_15367;
            CursorTy tmpcur_15369 = tmpcur_15367 + sizeof(FloatTy);
            FloatTy tmpval_15370 = *(FloatTy *) tmpcur_15369;
            CursorTy tmpcur_15371 = tmpcur_15369 + sizeof(FloatTy);
            IntTy tmpval_15372 = *(IntTy *) tmpcur_15371;
            CursorTy tmpcur_15373 = tmpcur_15371 + sizeof(IntTy);
            IntTy tmpval_15374 = *(IntTy *) tmpcur_15373;
            CursorTy tmpcur_15375 = tmpcur_15373 + sizeof(IntTy);
            FloatTy tmpval_15376 = *(FloatTy *) tmpcur_15375;
            CursorTy tmpcur_15377 = tmpcur_15375 + sizeof(FloatTy);
            FloatTy tmpval_15378 = *(FloatTy *) tmpcur_15377;
            CursorTy tmpcur_15379 = tmpcur_15377 + sizeof(FloatTy);
            FloatTy tmpval_15380 = *(FloatTy *) tmpcur_15379;
            CursorTy tmpcur_15381 = tmpcur_15379 + sizeof(FloatTy);
            FloatTy tmpval_15382 = *(FloatTy *) tmpcur_15381;
            CursorTy tmpcur_15383 = tmpcur_15381 + sizeof(FloatTy);
            FloatTy tmpval_15384 = *(FloatTy *) tmpcur_15383;
            CursorTy tmpcur_15385 = tmpcur_15383 + sizeof(FloatTy);
            FloatTy tmpval_15386 = *(FloatTy *) tmpcur_15385;
            CursorTy tmpcur_15387 = tmpcur_15385 + sizeof(FloatTy);
            FloatTy tmpval_15388 = *(FloatTy *) tmpcur_15387;
            CursorTy tmpcur_15389 = tmpcur_15387 + sizeof(FloatTy);
            CursorTy jump_12132 = tmpcur_15387 + 4;
            CursorTy jump_12131 = tmpcur_15385 + 4;
            CursorTy jump_12130 = tmpcur_15383 + 4;
            CursorTy jump_12129 = tmpcur_15381 + 4;
            CursorTy jump_12128 = tmpcur_15379 + 4;
            CursorTy jump_12127 = tmpcur_15377 + 4;
            CursorTy jump_12126 = tmpcur_15375 + 4;
            CursorTy jump_12125 = tmpcur_15373 + 8;
            CursorTy jump_12124 = tmpcur_15371 + 8;
            CursorTy jump_12123 = tmpcur_15369 + 4;
            CursorTy jump_12122 = tmpcur_15367 + 4;
            CursorTy jump_12121 = tmpaftercur_15365 + 4;
            CursorTy jump_12120 = tmpcur_15357 + 8;
            CursorFloat32Prod tmp_struct_130 =
                               sumKdTree(end_r_10658, tmpcur_15389);
            CursorTy pvrtmp_15390 = tmp_struct_130.field0;
            FloatTy pvrtmp_15391 = tmp_struct_130.field1;
            CursorFloat32Prod tmp_struct_131 =
                               sumKdTree(end_r_10658, tmpcur_15364);
            CursorTy pvrtmp_15392 = tmp_struct_131.field0;
            FloatTy pvrtmp_15393 = tmp_struct_131.field1;
            FloatTy fltPrm_7148_7697 = tmpval_15366 + tmpval_15368;
            FloatTy fltPrm_7147_7698 = fltPrm_7148_7697 + tmpval_15370;
            FloatTy fltPrm_7146_7699 = fltPrm_7147_7698 + pvrtmp_15391;
            FloatTy tailprim_12135 = fltPrm_7146_7699 + pvrtmp_15393;

            return (CursorFloat32Prod) {pvrtmp_15392, tailprim_12135};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15394 = *(CursorTy *) tmpcur_15357;
            CursorTy tmpaftercur_15395 = tmpcur_15357 + 8;
            CursorTy jump_12740 = tmpcur_15357 + 8;
            CursorFloat32Prod tmp_struct_132 =
                               sumKdTree(end_r_10658, tmpcur_15394);
            CursorTy pvrtmp_15396 = tmp_struct_132.field0;
            FloatTy pvrtmp_15397 = tmp_struct_132.field1;

            return (CursorFloat32Prod) {jump_12740, pvrtmp_15397};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15398 = *(CursorTy *) tmpcur_15357;
            CursorTy tmpaftercur_15399 = tmpcur_15357 + 8;
            CursorFloat32Prod tmp_struct_133 =
                               sumKdTree(end_r_10658, tmpcur_15398);
            CursorTy pvrtmp_15400 = tmp_struct_133.field0;
            FloatTy pvrtmp_15401 = tmp_struct_133.field1;

            return (CursorFloat32Prod) {pvrtmp_15400, pvrtmp_15401};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15356");
            exit(1);
        }
    }
}
IntTy countCorr_seq(CursorTy end_r_10660,
                    Float32Float32Float32Prod probe_377_4791_7700,
                    FloatTy radius_378_4792_7701, CursorTy tr_379_4793_7702)
{
    TagTyPacked tmpval_15403 = *(TagTyPacked *) tr_379_4793_7702;
    CursorTy tmpcur_15404 = tr_379_4793_7702 + 1;


  switch_15480:
    ;
    switch (tmpval_15403) {

      case 2:
        {
            CursorTy jump_12141 = tr_379_4793_7702 + 1;

            return 0;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15405 = *(FloatTy *) tmpcur_15404;
            CursorTy tmpcur_15406 = tmpcur_15404 + sizeof(FloatTy);
            FloatTy tmpval_15407 = *(FloatTy *) tmpcur_15406;
            CursorTy tmpcur_15408 = tmpcur_15406 + sizeof(FloatTy);
            FloatTy tmpval_15409 = *(FloatTy *) tmpcur_15408;
            CursorTy tmpcur_15410 = tmpcur_15408 + sizeof(FloatTy);
            CursorTy jump_12144 = tmpcur_15408 + 4;
            CursorTy jump_12143 = tmpcur_15406 + 4;
            CursorTy jump_12142 = tmpcur_15404 + 4;
            FloatTy fltPrm_7150_7707 =
                     dist_point3d((Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, (Float32Float32Float32Prod) {tmpval_15405, tmpval_15407, tmpval_15409});
            FloatTy fltPrm_7152_7708 = radius_378_4792_7701 *
                    radius_378_4792_7701;
            BoolTy fltIf_7149_7709 = fltPrm_7150_7707 < fltPrm_7152_7708;

            if (fltIf_7149_7709) {
                return 1;
            } else {
                return 0;
            }
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15420 = *(CursorTy *) tmpcur_15404;
            CursorTy tmpaftercur_15421 = tmpcur_15404 + 8;
            FloatTy tmpval_15422 = *(FloatTy *) tmpaftercur_15421;
            CursorTy tmpcur_15423 = tmpaftercur_15421 + sizeof(FloatTy);
            FloatTy tmpval_15424 = *(FloatTy *) tmpcur_15423;
            CursorTy tmpcur_15425 = tmpcur_15423 + sizeof(FloatTy);
            FloatTy tmpval_15426 = *(FloatTy *) tmpcur_15425;
            CursorTy tmpcur_15427 = tmpcur_15425 + sizeof(FloatTy);
            IntTy tmpval_15428 = *(IntTy *) tmpcur_15427;
            CursorTy tmpcur_15429 = tmpcur_15427 + sizeof(IntTy);
            IntTy tmpval_15430 = *(IntTy *) tmpcur_15429;
            CursorTy tmpcur_15431 = tmpcur_15429 + sizeof(IntTy);
            FloatTy tmpval_15432 = *(FloatTy *) tmpcur_15431;
            CursorTy tmpcur_15433 = tmpcur_15431 + sizeof(FloatTy);
            FloatTy tmpval_15434 = *(FloatTy *) tmpcur_15433;
            CursorTy tmpcur_15435 = tmpcur_15433 + sizeof(FloatTy);
            FloatTy tmpval_15436 = *(FloatTy *) tmpcur_15435;
            CursorTy tmpcur_15437 = tmpcur_15435 + sizeof(FloatTy);
            FloatTy tmpval_15438 = *(FloatTy *) tmpcur_15437;
            CursorTy tmpcur_15439 = tmpcur_15437 + sizeof(FloatTy);
            FloatTy tmpval_15440 = *(FloatTy *) tmpcur_15439;
            CursorTy tmpcur_15441 = tmpcur_15439 + sizeof(FloatTy);
            FloatTy tmpval_15442 = *(FloatTy *) tmpcur_15441;
            CursorTy tmpcur_15443 = tmpcur_15441 + sizeof(FloatTy);
            FloatTy tmpval_15444 = *(FloatTy *) tmpcur_15443;
            CursorTy tmpcur_15445 = tmpcur_15443 + sizeof(FloatTy);
            CursorTy jump_12157 = tmpcur_15443 + 4;
            CursorTy jump_12156 = tmpcur_15441 + 4;
            CursorTy jump_12155 = tmpcur_15439 + 4;
            CursorTy jump_12154 = tmpcur_15437 + 4;
            CursorTy jump_12153 = tmpcur_15435 + 4;
            CursorTy jump_12152 = tmpcur_15433 + 4;
            CursorTy jump_12151 = tmpcur_15431 + 4;
            CursorTy jump_12150 = tmpcur_15429 + 8;
            CursorTy jump_12149 = tmpcur_15427 + 8;
            CursorTy jump_12148 = tmpcur_15425 + 4;
            CursorTy jump_12147 = tmpcur_15423 + 4;
            CursorTy jump_12146 = tmpaftercur_15421 + 4;
            CursorTy jump_12145 = tmpcur_15404 + 8;
            FloatTy fltPrm_7153_7724 = tmpval_15434 + tmpval_15436;
            FloatTy center_x_397_4811_7725 = fltPrm_7153_7724 / 2.0;
            FloatTy fltPrm_7154_7726 = tmpval_15438 + tmpval_15440;
            FloatTy center_y_398_4812_7727 = fltPrm_7154_7726 / 2.0;
            FloatTy fltPrm_7155_7728 = tmpval_15442 + tmpval_15444;
            FloatTy center_z_399_4813_7729 = fltPrm_7155_7728 / 2.0;
            FloatTy d_x_404_4818_7734 = probe_377_4791_7700.field0 -
                    center_x_397_4811_7725;
            FloatTy d_y_405_4819_7735 = probe_377_4791_7700.field1 -
                    center_y_398_4812_7727;
            FloatTy d_z_406_4820_7736 = probe_377_4791_7700.field2 -
                    center_z_399_4813_7729;
            FloatTy fltPrm_7156_7737 = tmpval_15436 - tmpval_15434;
            FloatTy boxdist_x_407_4821_7738 = fltPrm_7156_7737 / 2.0;
            FloatTy fltPrm_7157_7739 = tmpval_15440 - tmpval_15438;
            FloatTy boxdist_y_408_4822_7740 = fltPrm_7157_7739 / 2.0;
            FloatTy fltPrm_7158_7741 = tmpval_15444 - tmpval_15442;
            FloatTy boxdist_z_409_4823_7742 = fltPrm_7158_7741 / 2.0;
            FloatTy fltPrm_7160_7743 = d_x_404_4818_7734 * d_x_404_4818_7734;
            FloatTy fltPrm_7161_7744 = d_y_405_4819_7735 * d_y_405_4819_7735;
            FloatTy fltPrm_7159_7745 = fltPrm_7160_7743 + fltPrm_7161_7744;
            FloatTy fltPrm_7162_7746 = d_z_406_4820_7736 * d_z_406_4820_7736;
            FloatTy sum_410_4824_7747 = fltPrm_7159_7745 + fltPrm_7162_7746;
            FloatTy fltPrm_7164_7748 = boxdist_x_407_4821_7738 *
                    boxdist_x_407_4821_7738;
            FloatTy fltPrm_7165_7749 = boxdist_y_408_4822_7740 *
                    boxdist_y_408_4822_7740;
            FloatTy fltPrm_7163_7750 = fltPrm_7164_7748 + fltPrm_7165_7749;
            FloatTy fltPrm_7166_7751 = boxdist_z_409_4823_7742 *
                    boxdist_z_409_4823_7742;
            FloatTy boxsum_411_4825_7752 = fltPrm_7163_7750 + fltPrm_7166_7751;
            FloatTy fltPrm_7168_7753 = sum_410_4824_7747 - boxsum_411_4825_7752;
            FloatTy fltPrm_7169_7754 = radius_378_4792_7701 *
                    radius_378_4792_7701;
            BoolTy fltIf_7167_7755 = fltPrm_7168_7753 < fltPrm_7169_7754;

            if (fltIf_7167_7755) {
                IntTy n1_412_4826_7756 =
                       countCorr_seq(end_r_10660, (Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, radius_378_4792_7701, tmpcur_15445);
                IntTy n2_413_4827_7757 =
                       countCorr_seq(end_r_10660, (Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, radius_378_4792_7701, tmpcur_15420);
                FloatTy fltPrm_7171_7759 =
                         dist_point3d((Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, (Float32Float32Float32Prod) {tmpval_15422, tmpval_15424, tmpval_15426});
                FloatTy fltPrm_7173_7760 = radius_378_4792_7701 *
                        radius_378_4792_7701;
                BoolTy fltIf_7170_7761 = fltPrm_7171_7759 < fltPrm_7173_7760;

                if (fltIf_7170_7761) {
                    IntTy fltPrm_7174_7762 = n1_412_4826_7756 +
                          n2_413_4827_7757;
                    IntTy tailprim_12158 = fltPrm_7174_7762 + 1;

                    return tailprim_12158;
                } else {
                    IntTy tailprim_12159 = n1_412_4826_7756 + n2_413_4827_7757;

                    return tailprim_12159;
                }
            } else {
                FloatTy fltPrm_7176_7764 =
                         dist_point3d((Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, (Float32Float32Float32Prod) {tmpval_15422, tmpval_15424, tmpval_15426});
                FloatTy fltPrm_7178_7765 = radius_378_4792_7701 *
                        radius_378_4792_7701;
                BoolTy fltIf_7175_7766 = fltPrm_7176_7764 < fltPrm_7178_7765;

                if (fltIf_7175_7766) {
                    return 1;
                } else {
                    return 0;
                }
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15470 = *(CursorTy *) tmpcur_15404;
            CursorTy tmpaftercur_15471 = tmpcur_15404 + 8;
            CursorTy jump_12746 = tmpcur_15404 + 8;
            IntTy call_12747 =
                   countCorr_seq(end_r_10660, (Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, radius_378_4792_7701, tmpcur_15470);

            return call_12747;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15475 = *(CursorTy *) tmpcur_15404;
            CursorTy tmpaftercur_15476 = tmpcur_15404 + 8;
            IntTy call_12747 =
                   countCorr_seq(end_r_10660, (Float32Float32Float32Prod) {probe_377_4791_7700.field0, probe_377_4791_7700.field1, probe_377_4791_7700.field2}, radius_378_4792_7701, tmpcur_15475);

            return call_12747;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15403");
            exit(1);
        }
    }
}
Float32Float32Float32Prod least_dist_point3d(Float32Float32Float32Prod a_414_4828_7767,
                                             Float32Float32Float32Prod b_415_4829_7768,
                                             Float32Float32Float32Prod c_416_4830_7769)
{
    FloatTy d1_417_4831_7770 =
             dist_point3d((Float32Float32Float32Prod) {a_414_4828_7767.field0, a_414_4828_7767.field1, a_414_4828_7767.field2}, (Float32Float32Float32Prod) {b_415_4829_7768.field0, b_415_4829_7768.field1, b_415_4829_7768.field2});
    FloatTy d2_418_4832_7771 =
             dist_point3d((Float32Float32Float32Prod) {a_414_4828_7767.field0, a_414_4828_7767.field1, a_414_4828_7767.field2}, (Float32Float32Float32Prod) {c_416_4830_7769.field0, c_416_4830_7769.field1, c_416_4830_7769.field2});
    BoolTy fltIf_7179_7772 = d1_417_4831_7770 < d2_418_4832_7771;

    if (fltIf_7179_7772) {
        return b_415_4829_7768;
    } else {
        return c_416_4830_7769;
    }
}
Float32Float32Float32Prod find_nearest(CursorTy end_r_10663,
                                       CursorTy end_r_10664,
                                       Float32Float32Float32Prod pivot_419_4833_7773,
                                       Float32Float32Float32Prod query_420_4834_7774,
                                       FloatTy tst_pivot_421_4835_7775,
                                       FloatTy tst_query_422_4836_7776,
                                       CursorTy good_side_423_4837_7777,
                                       CursorTy other_side_424_4838_7778)
{
    Float32Float32Float32Prod tmp_struct_134 =
                               nearest(end_r_10663, good_side_423_4837_7777, (Float32Float32Float32Prod) {query_420_4834_7774.field0, query_420_4834_7774.field1, query_420_4834_7774.field2});
    FloatTy pvrtmp_15496 = tmp_struct_134.field0;
    FloatTy pvrtmp_15497 = tmp_struct_134.field1;
    FloatTy pvrtmp_15498 = tmp_struct_134.field2;
    Float32Float32Float32Prod tmp_struct_135 =
                               least_dist_point3d((Float32Float32Float32Prod) {query_420_4834_7774.field0, query_420_4834_7774.field1, query_420_4834_7774.field2}, (Float32Float32Float32Prod) {pvrtmp_15496, pvrtmp_15497, pvrtmp_15498}, (Float32Float32Float32Prod) {pivot_419_4833_7773.field0, pivot_419_4833_7773.field1, pivot_419_4833_7773.field2});
    FloatTy pvrtmp_15508 = tmp_struct_135.field0;
    FloatTy pvrtmp_15509 = tmp_struct_135.field1;
    FloatTy pvrtmp_15510 = tmp_struct_135.field2;
    FloatTy nearest_other_side_427_4841_7781 = tst_query_422_4836_7776 -
            tst_pivot_421_4835_7775;
    FloatTy fltPrm_7181_7782 = nearest_other_side_427_4841_7781 *
            nearest_other_side_427_4841_7781;
    FloatTy fltPrm_7182_7783 =
             dist_point3d((Float32Float32Float32Prod) {query_420_4834_7774.field0, query_420_4834_7774.field1, query_420_4834_7774.field2}, (Float32Float32Float32Prod) {pvrtmp_15508, pvrtmp_15509, pvrtmp_15510});
    BoolTy fltIf_7180_7784 = fltPrm_7181_7782 <= fltPrm_7182_7783;

    if (fltIf_7180_7784) {
        Float32Float32Float32Prod tmp_struct_136 =
                                   nearest(end_r_10664, other_side_424_4838_7778, (Float32Float32Float32Prod) {query_420_4834_7774.field0, query_420_4834_7774.field1, query_420_4834_7774.field2});
        FloatTy pvrtmp_15520 = tmp_struct_136.field0;
        FloatTy pvrtmp_15521 = tmp_struct_136.field1;
        FloatTy pvrtmp_15522 = tmp_struct_136.field2;
        Float32Float32Float32Prod tmp_struct_137 =
                                   least_dist_point3d((Float32Float32Float32Prod) {query_420_4834_7774.field0, query_420_4834_7774.field1, query_420_4834_7774.field2}, (Float32Float32Float32Prod) {pvrtmp_15508, pvrtmp_15509, pvrtmp_15510}, (Float32Float32Float32Prod) {pvrtmp_15520, pvrtmp_15521, pvrtmp_15522});
        FloatTy pvrtmp_15532 = tmp_struct_137.field0;
        FloatTy pvrtmp_15533 = tmp_struct_137.field1;
        FloatTy pvrtmp_15534 = tmp_struct_137.field2;

        return (Float32Float32Float32Prod) {pvrtmp_15532, pvrtmp_15533,
                                            pvrtmp_15534};
    } else {
        return (Float32Float32Float32Prod) {pvrtmp_15508, pvrtmp_15509,
                                            pvrtmp_15510};
    }
}
Float32Float32Float32Prod nearest(CursorTy end_r_10666,
                                  CursorTy tr_430_4844_7787,
                                  Float32Float32Float32Prod query_431_4845_7788)
{
    TagTyPacked tmpval_15535 = *(TagTyPacked *) tr_430_4844_7787;
    CursorTy tmpcur_15536 = tr_430_4844_7787 + 1;


  switch_15618:
    ;
    switch (tmpval_15535) {

      case 2:
        {
            CursorTy jump_12160 = tr_430_4844_7787 + 1;

            return (Float32Float32Float32Prod) {0.0, 0.0, 0.0};
            break;
        }

      case 0:
        {
            FloatTy tmpval_15540 = *(FloatTy *) tmpcur_15536;
            CursorTy tmpcur_15541 = tmpcur_15536 + sizeof(FloatTy);
            FloatTy tmpval_15542 = *(FloatTy *) tmpcur_15541;
            CursorTy tmpcur_15543 = tmpcur_15541 + sizeof(FloatTy);
            FloatTy tmpval_15544 = *(FloatTy *) tmpcur_15543;
            CursorTy tmpcur_15545 = tmpcur_15543 + sizeof(FloatTy);
            CursorTy jump_12164 = tmpcur_15543 + 4;
            CursorTy jump_12163 = tmpcur_15541 + 4;
            CursorTy jump_12162 = tmpcur_15536 + 4;

            return (Float32Float32Float32Prod) {tmpval_15540, tmpval_15542,
                                                tmpval_15544};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15549 = *(CursorTy *) tmpcur_15536;
            CursorTy tmpaftercur_15550 = tmpcur_15536 + 8;
            FloatTy tmpval_15551 = *(FloatTy *) tmpaftercur_15550;
            CursorTy tmpcur_15552 = tmpaftercur_15550 + sizeof(FloatTy);
            FloatTy tmpval_15553 = *(FloatTy *) tmpcur_15552;
            CursorTy tmpcur_15554 = tmpcur_15552 + sizeof(FloatTy);
            FloatTy tmpval_15555 = *(FloatTy *) tmpcur_15554;
            CursorTy tmpcur_15556 = tmpcur_15554 + sizeof(FloatTy);
            IntTy tmpval_15557 = *(IntTy *) tmpcur_15556;
            CursorTy tmpcur_15558 = tmpcur_15556 + sizeof(IntTy);
            IntTy tmpval_15559 = *(IntTy *) tmpcur_15558;
            CursorTy tmpcur_15560 = tmpcur_15558 + sizeof(IntTy);
            FloatTy tmpval_15561 = *(FloatTy *) tmpcur_15560;
            CursorTy tmpcur_15562 = tmpcur_15560 + sizeof(FloatTy);
            FloatTy tmpval_15563 = *(FloatTy *) tmpcur_15562;
            CursorTy tmpcur_15564 = tmpcur_15562 + sizeof(FloatTy);
            FloatTy tmpval_15565 = *(FloatTy *) tmpcur_15564;
            CursorTy tmpcur_15566 = tmpcur_15564 + sizeof(FloatTy);
            FloatTy tmpval_15567 = *(FloatTy *) tmpcur_15566;
            CursorTy tmpcur_15568 = tmpcur_15566 + sizeof(FloatTy);
            FloatTy tmpval_15569 = *(FloatTy *) tmpcur_15568;
            CursorTy tmpcur_15570 = tmpcur_15568 + sizeof(FloatTy);
            FloatTy tmpval_15571 = *(FloatTy *) tmpcur_15570;
            CursorTy tmpcur_15572 = tmpcur_15570 + sizeof(FloatTy);
            FloatTy tmpval_15573 = *(FloatTy *) tmpcur_15572;
            CursorTy tmpcur_15574 = tmpcur_15572 + sizeof(FloatTy);
            CursorTy jump_12178 = tmpcur_15572 + 4;
            CursorTy jump_12177 = tmpcur_15570 + 4;
            CursorTy jump_12176 = tmpcur_15568 + 4;
            CursorTy jump_12175 = tmpcur_15566 + 4;
            CursorTy jump_12174 = tmpcur_15564 + 4;
            CursorTy jump_12173 = tmpcur_15562 + 4;
            CursorTy jump_12172 = tmpcur_15560 + 4;
            CursorTy jump_12171 = tmpcur_15558 + 8;
            CursorTy jump_12170 = tmpcur_15556 + 8;
            CursorTy jump_12169 = tmpcur_15554 + 4;
            CursorTy jump_12168 = tmpcur_15552 + 4;
            CursorTy jump_12167 = tmpaftercur_15550 + 4;
            CursorTy jump_12166 = tmpcur_15536 + 8;
            FloatTy tst_query_450_4864_7807 =
                     get_coord_point3d(tmpval_15559, (Float32Float32Float32Prod) {query_431_4845_7788.field0, query_431_4845_7788.field1, query_431_4845_7788.field2});
            FloatTy tst_pivot_451_4865_7808 =
                     get_coord_point3d(tmpval_15559, (Float32Float32Float32Prod) {tmpval_15551, tmpval_15553, tmpval_15555});
            BoolTy fltIf_7183_7809 = tst_query_450_4864_7807 <
                   tst_pivot_451_4865_7808;

            if (fltIf_7183_7809) {
                Float32Float32Float32Prod tmp_struct_138 =
                                           find_nearest(end_r_10666, end_r_10666, (Float32Float32Float32Prod) {tmpval_15551, tmpval_15553, tmpval_15555}, (Float32Float32Float32Prod) {query_431_4845_7788.field0, query_431_4845_7788.field1, query_431_4845_7788.field2}, tst_pivot_451_4865_7808, tst_query_450_4864_7807, tmpcur_15574, tmpcur_15549);
                FloatTy pvrtmp_15590 = tmp_struct_138.field0;
                FloatTy pvrtmp_15591 = tmp_struct_138.field1;
                FloatTy pvrtmp_15592 = tmp_struct_138.field2;

                return (Float32Float32Float32Prod) {pvrtmp_15590, pvrtmp_15591,
                                                    pvrtmp_15592};
            } else {
                Float32Float32Float32Prod tmp_struct_139 =
                                           find_nearest(end_r_10666, end_r_10666, (Float32Float32Float32Prod) {tmpval_15551, tmpval_15553, tmpval_15555}, (Float32Float32Float32Prod) {query_431_4845_7788.field0, query_431_4845_7788.field1, query_431_4845_7788.field2}, tst_pivot_451_4865_7808, tst_query_450_4864_7807, tmpcur_15549, tmpcur_15574);
                FloatTy pvrtmp_15599 = tmp_struct_139.field0;
                FloatTy pvrtmp_15600 = tmp_struct_139.field1;
                FloatTy pvrtmp_15601 = tmp_struct_139.field2;

                return (Float32Float32Float32Prod) {pvrtmp_15599, pvrtmp_15600,
                                                    pvrtmp_15601};
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15602 = *(CursorTy *) tmpcur_15536;
            CursorTy tmpaftercur_15603 = tmpcur_15536 + 8;
            CursorTy jump_12751 = tmpcur_15536 + 8;
            Float32Float32Float32Prod tmp_struct_140 =
                                       nearest(end_r_10666, tmpcur_15602, (Float32Float32Float32Prod) {query_431_4845_7788.field0, query_431_4845_7788.field1, query_431_4845_7788.field2});
            FloatTy pvrtmp_15607 = tmp_struct_140.field0;
            FloatTy pvrtmp_15608 = tmp_struct_140.field1;
            FloatTy pvrtmp_15609 = tmp_struct_140.field2;

            return (Float32Float32Float32Prod) {pvrtmp_15607, pvrtmp_15608,
                                                pvrtmp_15609};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15610 = *(CursorTy *) tmpcur_15536;
            CursorTy tmpaftercur_15611 = tmpcur_15536 + 8;
            Float32Float32Float32Prod tmp_struct_141 =
                                       nearest(end_r_10666, tmpcur_15610, (Float32Float32Float32Prod) {query_431_4845_7788.field0, query_431_4845_7788.field1, query_431_4845_7788.field2});
            FloatTy pvrtmp_15615 = tmp_struct_141.field0;
            FloatTy pvrtmp_15616 = tmp_struct_141.field1;
            FloatTy pvrtmp_15617 = tmp_struct_141.field2;

            return (Float32Float32Float32Prod) {pvrtmp_15615, pvrtmp_15616,
                                                pvrtmp_15617};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15535");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkKdTreeWithAxis_seq(CursorTy end_r_10668,
                                            CursorTy loc_10667,
                                            IntTy axis_452_4866_7810,
                                            VectorTy *pts_453_4867_7811)
{
    if (loc_10667 + 73 > end_r_10668) {
        ChunkTy new_chunk_146 = alloc_chunk(end_r_10668);
        CursorTy chunk_start_147 = new_chunk_146.chunk_start;
        CursorTy chunk_end_148 = new_chunk_146.chunk_end;

        end_r_10668 = chunk_end_148;
        *(TagTyPacked *) loc_10667 = 255;

        CursorTy redir = loc_10667 + 1;

        *(CursorTy *) redir = chunk_start_147;
        loc_10667 = chunk_start_147;
    }

    CursorTy loc_11052 = loc_10667 + 1;
    CursorTy loc_11053 = loc_11052 + 8;
    CursorTy loc_11054 = loc_11053 + 4;
    CursorTy loc_11055 = loc_11054 + 4;
    CursorTy loc_11056 = loc_11055 + 4;
    CursorTy loc_11057 = loc_11056 + 8;
    CursorTy loc_11058 = loc_11057 + 8;
    CursorTy loc_11059 = loc_11058 + 4;
    CursorTy loc_11060 = loc_11059 + 4;
    CursorTy loc_11061 = loc_11060 + 4;
    CursorTy loc_11062 = loc_11061 + 4;
    CursorTy loc_11063 = loc_11062 + 4;
    CursorTy loc_11064 = loc_11063 + 4;
    CursorTy loc_11065 = loc_11064 + 4;
    IntTy len_454_4868_7812 = vector_length(pts_453_4867_7811);
    BoolTy fltIf_7184_7813 = len_454_4868_7812 == 0;

    if (fltIf_7184_7813) {
        *(TagTyPacked *) loc_10667 = 2;

        CursorTy writetag_13167 = loc_10667 + 1;

        return (CursorCursorCursorProd) {end_r_10668, loc_10667,
                                         writetag_13167};
    } else {
        BoolTy fltIf_7185_7814 = len_454_4868_7812 == 1;

        if (fltIf_7185_7814) {
            Float32Float32Float32Prod *tmp_142;

            tmp_142 =
                (Float32Float32Float32Prod *) vector_nth(pts_453_4867_7811, 0);

            Float32Float32Float32Prod tup_407_455_4869_7817 = *tmp_142;

            *(TagTyPacked *) loc_10667 = 0;

            CursorTy writetag_13169 = loc_10667 + 1;

            *(FloatTy *) writetag_13169 = tup_407_455_4869_7817.field0;

            CursorTy writecur_13170 = writetag_13169 + sizeof(FloatTy);

            *(FloatTy *) writecur_13170 = tup_407_455_4869_7817.field1;

            CursorTy writecur_13171 = writecur_13170 + sizeof(FloatTy);

            *(FloatTy *) writecur_13171 = tup_407_455_4869_7817.field2;

            CursorTy writecur_13172 = writecur_13171 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {end_r_10668, loc_10667,
                                             writecur_13172};
        } else {
            VectorTy *sorted_pts_459_4873_7821 =
                      sort_point3d(axis_452_4866_7810, pts_453_4867_7811);
            IntTy pivot_idx_460_4874_7822 = len_454_4868_7812 / 2;
            Float32Float32Float32Prod *tmp_145;

            tmp_145 =
                (Float32Float32Float32Prod *) vector_nth(sorted_pts_459_4873_7821,
                                                         pivot_idx_460_4874_7822);

            Float32Float32Float32Prod pivot_461_4875_7825 = *tmp_145;
            VectorTy *left_pts_466_4880_7833 = vector_slice(0,
                                                            pivot_idx_460_4874_7822,
                                                            sorted_pts_459_4873_7821);
            IntTy i_187_5582_6572_7834 = pivot_idx_460_4874_7822 + 1;
            IntTy fltPrm_7186_7835 = len_454_4868_7812 -
                  pivot_idx_460_4874_7822;
            IntTy n_188_5583_6573_7836 = fltPrm_7186_7835 - 1;
            VectorTy *right_pts_467_4881_7838 =
                     vector_slice(i_187_5582_6572_7834, n_188_5583_6573_7836,
                                  sorted_pts_459_4873_7821);
            IntTy next_axis_468_4882_7839 =  getNextAxis_3d(axis_452_4866_7810);
            CursorCursorCursorProd tmp_struct_143 =
                                    mkKdTreeWithAxis_seq(end_r_10668, loc_11065, next_axis_468_4882_7839, left_pts_466_4880_7833);
            CursorTy pvrtmp_15627 = tmp_struct_143.field0;
            CursorTy pvrtmp_15628 = tmp_struct_143.field1;
            CursorTy pvrtmp_15629 = tmp_struct_143.field2;
            CursorCursorCursorProd tmp_struct_144 =
                                    mkKdTreeWithAxis_seq(pvrtmp_15627, pvrtmp_15629, next_axis_468_4882_7839, right_pts_467_4881_7838);
            CursorTy pvrtmp_15634 = tmp_struct_144.field0;
            CursorTy pvrtmp_15635 = tmp_struct_144.field1;
            CursorTy pvrtmp_15636 = tmp_struct_144.field2;
            FloatTy fltAppE_7188_7842 =
                     get_minx_kdtree(pvrtmp_15634, pvrtmp_15628);
            FloatTy fltAppE_7189_7843 =
                     get_minx_kdtree(pvrtmp_15634, pvrtmp_15635);
            FloatTy fltAppE_7187_7844 =
                     minFloat(fltAppE_7188_7842, fltAppE_7189_7843);
            FloatTy min_x_471_4885_7845 =
                     minFloat(pivot_461_4875_7825.field0, fltAppE_7187_7844);
            FloatTy fltAppE_7191_7846 =
                     get_maxx_kdtree(pvrtmp_15634, pvrtmp_15628);
            FloatTy fltAppE_7192_7847 =
                     get_maxx_kdtree(pvrtmp_15634, pvrtmp_15635);
            FloatTy fltAppE_7190_7848 =
                     maxFloat(fltAppE_7191_7846, fltAppE_7192_7847);
            FloatTy max_x_472_4886_7849 =
                     maxFloat(pivot_461_4875_7825.field0, fltAppE_7190_7848);
            FloatTy fltAppE_7194_7850 =
                     get_miny_kdtree(pvrtmp_15634, pvrtmp_15628);
            FloatTy fltAppE_7195_7851 =
                     get_miny_kdtree(pvrtmp_15634, pvrtmp_15635);
            FloatTy fltAppE_7193_7852 =
                     minFloat(fltAppE_7194_7850, fltAppE_7195_7851);
            FloatTy min_y_473_4887_7853 =
                     minFloat(pivot_461_4875_7825.field1, fltAppE_7193_7852);
            FloatTy fltAppE_7197_7854 =
                     get_maxy_kdtree(pvrtmp_15634, pvrtmp_15628);
            FloatTy fltAppE_7198_7855 =
                     get_maxy_kdtree(pvrtmp_15634, pvrtmp_15635);
            FloatTy fltAppE_7196_7856 =
                     maxFloat(fltAppE_7197_7854, fltAppE_7198_7855);
            FloatTy max_y_474_4888_7857 =
                     maxFloat(pivot_461_4875_7825.field1, fltAppE_7196_7856);
            FloatTy fltAppE_7200_7858 =
                     get_minz_kdtree(pvrtmp_15634, pvrtmp_15628);
            FloatTy fltAppE_7201_7859 =
                     get_minz_kdtree(pvrtmp_15634, pvrtmp_15635);
            FloatTy fltAppE_7199_7860 =
                     minFloat(fltAppE_7200_7858, fltAppE_7201_7859);
            FloatTy min_z_475_4889_7861 =
                     minFloat(pivot_461_4875_7825.field2, fltAppE_7199_7860);
            FloatTy fltAppE_7203_7862 =
                     get_maxz_kdtree(pvrtmp_15634, pvrtmp_15628);
            FloatTy fltAppE_7204_7863 =
                     get_maxz_kdtree(pvrtmp_15634, pvrtmp_15635);
            FloatTy fltAppE_7202_7864 =
                     maxFloat(fltAppE_7203_7862, fltAppE_7204_7863);
            FloatTy max_z_476_4890_7865 =
                     maxFloat(pivot_461_4875_7825.field2, fltAppE_7202_7864);
            IntTy fltPrm_7206_7866 =
                   get_total_points_kdtree(pvrtmp_15634, pvrtmp_15628);
            IntTy fltPrm_7207_7867 =
                   get_total_points_kdtree(pvrtmp_15634, pvrtmp_15635);
            IntTy fltPrm_7205_7868 = fltPrm_7206_7866 + fltPrm_7207_7867;
            IntTy total_points_477_4891_7869 = fltPrm_7205_7868 + 1;
            FloatTy fltPkd_7208_7870 =
                     get_coord_point3d(axis_452_4866_7810, (Float32Float32Float32Prod) {pivot_461_4875_7825.field0, pivot_461_4875_7825.field1, pivot_461_4875_7825.field2});

            *(TagTyPacked *) loc_10667 = 3;

            CursorTy writetag_13176 = loc_10667 + 1;

            *(CursorTy *) writetag_13176 = pvrtmp_15629;

            CursorTy writecur_13177 = writetag_13176 + 8;

            *(FloatTy *) writecur_13177 = pivot_461_4875_7825.field0;

            CursorTy writecur_13178 = writecur_13177 + sizeof(FloatTy);

            *(FloatTy *) writecur_13178 = pivot_461_4875_7825.field1;

            CursorTy writecur_13179 = writecur_13178 + sizeof(FloatTy);

            *(FloatTy *) writecur_13179 = pivot_461_4875_7825.field2;

            CursorTy writecur_13180 = writecur_13179 + sizeof(FloatTy);

            *(IntTy *) writecur_13180 = total_points_477_4891_7869;

            CursorTy writecur_13181 = writecur_13180 + sizeof(IntTy);

            *(IntTy *) writecur_13181 = axis_452_4866_7810;

            CursorTy writecur_13182 = writecur_13181 + sizeof(IntTy);

            *(FloatTy *) writecur_13182 = fltPkd_7208_7870;

            CursorTy writecur_13183 = writecur_13182 + sizeof(FloatTy);

            *(FloatTy *) writecur_13183 = min_x_471_4885_7845;

            CursorTy writecur_13184 = writecur_13183 + sizeof(FloatTy);

            *(FloatTy *) writecur_13184 = max_x_472_4886_7849;

            CursorTy writecur_13185 = writecur_13184 + sizeof(FloatTy);

            *(FloatTy *) writecur_13185 = min_y_473_4887_7853;

            CursorTy writecur_13186 = writecur_13185 + sizeof(FloatTy);

            *(FloatTy *) writecur_13186 = max_y_474_4888_7857;

            CursorTy writecur_13187 = writecur_13186 + sizeof(FloatTy);

            *(FloatTy *) writecur_13187 = min_z_475_4889_7861;

            CursorTy writecur_13188 = writecur_13187 + sizeof(FloatTy);

            *(FloatTy *) writecur_13188 = max_z_476_4890_7865;

            CursorTy writecur_13189 = writecur_13188 + sizeof(FloatTy);

            return (CursorCursorCursorProd) {pvrtmp_15634, loc_10667,
                                             pvrtmp_15636};
        }
    }
}
IntTy get_total_points_kdtree(CursorTy end_r_10670, CursorTy tr_532_4946_7871)
{
    TagTyPacked tmpval_15648 = *(TagTyPacked *) tr_532_4946_7871;
    CursorTy tmpcur_15649 = tr_532_4946_7871 + 1;


  switch_15686:
    ;
    switch (tmpval_15648) {

      case 2:
        {
            CursorTy jump_12186 = tr_532_4946_7871 + 1;

            return 0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15650 = *(CursorTy *) tmpcur_15649;
            CursorTy tmpaftercur_15651 = tmpcur_15649 + 8;
            FloatTy tmpval_15652 = *(FloatTy *) tmpaftercur_15651;
            CursorTy tmpcur_15653 = tmpaftercur_15651 + sizeof(FloatTy);
            FloatTy tmpval_15654 = *(FloatTy *) tmpcur_15653;
            CursorTy tmpcur_15655 = tmpcur_15653 + sizeof(FloatTy);
            FloatTy tmpval_15656 = *(FloatTy *) tmpcur_15655;
            CursorTy tmpcur_15657 = tmpcur_15655 + sizeof(FloatTy);
            IntTy tmpval_15658 = *(IntTy *) tmpcur_15657;
            CursorTy tmpcur_15659 = tmpcur_15657 + sizeof(IntTy);
            IntTy tmpval_15660 = *(IntTy *) tmpcur_15659;
            CursorTy tmpcur_15661 = tmpcur_15659 + sizeof(IntTy);
            FloatTy tmpval_15662 = *(FloatTy *) tmpcur_15661;
            CursorTy tmpcur_15663 = tmpcur_15661 + sizeof(FloatTy);
            FloatTy tmpval_15664 = *(FloatTy *) tmpcur_15663;
            CursorTy tmpcur_15665 = tmpcur_15663 + sizeof(FloatTy);
            FloatTy tmpval_15666 = *(FloatTy *) tmpcur_15665;
            CursorTy tmpcur_15667 = tmpcur_15665 + sizeof(FloatTy);
            FloatTy tmpval_15668 = *(FloatTy *) tmpcur_15667;
            CursorTy tmpcur_15669 = tmpcur_15667 + sizeof(FloatTy);
            FloatTy tmpval_15670 = *(FloatTy *) tmpcur_15669;
            CursorTy tmpcur_15671 = tmpcur_15669 + sizeof(FloatTy);
            FloatTy tmpval_15672 = *(FloatTy *) tmpcur_15671;
            CursorTy tmpcur_15673 = tmpcur_15671 + sizeof(FloatTy);
            FloatTy tmpval_15674 = *(FloatTy *) tmpcur_15673;
            CursorTy tmpcur_15675 = tmpcur_15673 + sizeof(FloatTy);
            CursorTy jump_12199 = tmpcur_15673 + 4;
            CursorTy jump_12198 = tmpcur_15671 + 4;
            CursorTy jump_12197 = tmpcur_15669 + 4;
            CursorTy jump_12196 = tmpcur_15667 + 4;
            CursorTy jump_12195 = tmpcur_15665 + 4;
            CursorTy jump_12194 = tmpcur_15663 + 4;
            CursorTy jump_12193 = tmpcur_15661 + 4;
            CursorTy jump_12192 = tmpcur_15659 + 8;
            CursorTy jump_12191 = tmpcur_15657 + 8;
            CursorTy jump_12190 = tmpcur_15655 + 4;
            CursorTy jump_12189 = tmpcur_15653 + 4;
            CursorTy jump_12188 = tmpaftercur_15651 + 4;
            CursorTy jump_12187 = tmpcur_15649 + 8;

            return tmpval_15658;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15676 = *(FloatTy *) tmpcur_15649;
            CursorTy tmpcur_15677 = tmpcur_15649 + sizeof(FloatTy);
            FloatTy tmpval_15678 = *(FloatTy *) tmpcur_15677;
            CursorTy tmpcur_15679 = tmpcur_15677 + sizeof(FloatTy);
            FloatTy tmpval_15680 = *(FloatTy *) tmpcur_15679;
            CursorTy tmpcur_15681 = tmpcur_15679 + sizeof(FloatTy);
            CursorTy jump_12202 = tmpcur_15679 + 4;
            CursorTy jump_12201 = tmpcur_15677 + 4;
            CursorTy jump_12200 = tmpcur_15649 + 4;

            return 1;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15682 = *(CursorTy *) tmpcur_15649;
            CursorTy tmpaftercur_15683 = tmpcur_15649 + 8;
            CursorTy jump_12756 = tmpcur_15649 + 8;
            IntTy call_12757 =
                   get_total_points_kdtree(end_r_10670, tmpcur_15682);

            return call_12757;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15684 = *(CursorTy *) tmpcur_15649;
            CursorTy tmpaftercur_15685 = tmpcur_15649 + 8;
            IntTy call_12757 =
                   get_total_points_kdtree(end_r_10670, tmpcur_15684);

            return call_12757;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15648");
            exit(1);
        }
    }
}
FloatTy get_maxz_kdtree(CursorTy end_r_10672, CursorTy tr_550_4964_7889)
{
    TagTyPacked tmpval_15687 = *(TagTyPacked *) tr_550_4964_7889;
    CursorTy tmpcur_15688 = tr_550_4964_7889 + 1;


  switch_15725:
    ;
    switch (tmpval_15687) {

      case 2:
        {
            CursorTy jump_12204 = tr_550_4964_7889 + 1;

            return 0.0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15689 = *(CursorTy *) tmpcur_15688;
            CursorTy tmpaftercur_15690 = tmpcur_15688 + 8;
            FloatTy tmpval_15691 = *(FloatTy *) tmpaftercur_15690;
            CursorTy tmpcur_15692 = tmpaftercur_15690 + sizeof(FloatTy);
            FloatTy tmpval_15693 = *(FloatTy *) tmpcur_15692;
            CursorTy tmpcur_15694 = tmpcur_15692 + sizeof(FloatTy);
            FloatTy tmpval_15695 = *(FloatTy *) tmpcur_15694;
            CursorTy tmpcur_15696 = tmpcur_15694 + sizeof(FloatTy);
            IntTy tmpval_15697 = *(IntTy *) tmpcur_15696;
            CursorTy tmpcur_15698 = tmpcur_15696 + sizeof(IntTy);
            IntTy tmpval_15699 = *(IntTy *) tmpcur_15698;
            CursorTy tmpcur_15700 = tmpcur_15698 + sizeof(IntTy);
            FloatTy tmpval_15701 = *(FloatTy *) tmpcur_15700;
            CursorTy tmpcur_15702 = tmpcur_15700 + sizeof(FloatTy);
            FloatTy tmpval_15703 = *(FloatTy *) tmpcur_15702;
            CursorTy tmpcur_15704 = tmpcur_15702 + sizeof(FloatTy);
            FloatTy tmpval_15705 = *(FloatTy *) tmpcur_15704;
            CursorTy tmpcur_15706 = tmpcur_15704 + sizeof(FloatTy);
            FloatTy tmpval_15707 = *(FloatTy *) tmpcur_15706;
            CursorTy tmpcur_15708 = tmpcur_15706 + sizeof(FloatTy);
            FloatTy tmpval_15709 = *(FloatTy *) tmpcur_15708;
            CursorTy tmpcur_15710 = tmpcur_15708 + sizeof(FloatTy);
            FloatTy tmpval_15711 = *(FloatTy *) tmpcur_15710;
            CursorTy tmpcur_15712 = tmpcur_15710 + sizeof(FloatTy);
            FloatTy tmpval_15713 = *(FloatTy *) tmpcur_15712;
            CursorTy tmpcur_15714 = tmpcur_15712 + sizeof(FloatTy);
            CursorTy jump_12217 = tmpcur_15712 + 4;
            CursorTy jump_12216 = tmpcur_15710 + 4;
            CursorTy jump_12215 = tmpcur_15708 + 4;
            CursorTy jump_12214 = tmpcur_15706 + 4;
            CursorTy jump_12213 = tmpcur_15704 + 4;
            CursorTy jump_12212 = tmpcur_15702 + 4;
            CursorTy jump_12211 = tmpcur_15700 + 4;
            CursorTy jump_12210 = tmpcur_15698 + 8;
            CursorTy jump_12209 = tmpcur_15696 + 8;
            CursorTy jump_12208 = tmpcur_15694 + 4;
            CursorTy jump_12207 = tmpcur_15692 + 4;
            CursorTy jump_12206 = tmpaftercur_15690 + 4;
            CursorTy jump_12205 = tmpcur_15688 + 8;

            return tmpval_15713;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15715 = *(FloatTy *) tmpcur_15688;
            CursorTy tmpcur_15716 = tmpcur_15688 + sizeof(FloatTy);
            FloatTy tmpval_15717 = *(FloatTy *) tmpcur_15716;
            CursorTy tmpcur_15718 = tmpcur_15716 + sizeof(FloatTy);
            FloatTy tmpval_15719 = *(FloatTy *) tmpcur_15718;
            CursorTy tmpcur_15720 = tmpcur_15718 + sizeof(FloatTy);
            CursorTy jump_12220 = tmpcur_15718 + 4;
            CursorTy jump_12219 = tmpcur_15716 + 4;
            CursorTy jump_12218 = tmpcur_15688 + 4;

            return tmpval_15719;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15721 = *(CursorTy *) tmpcur_15688;
            CursorTy tmpaftercur_15722 = tmpcur_15688 + 8;
            CursorTy jump_12761 = tmpcur_15688 + 8;
            FloatTy call_12762 =  get_maxz_kdtree(end_r_10672, tmpcur_15721);

            return call_12762;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15723 = *(CursorTy *) tmpcur_15688;
            CursorTy tmpaftercur_15724 = tmpcur_15688 + 8;
            FloatTy call_12762 =  get_maxz_kdtree(end_r_10672, tmpcur_15723);

            return call_12762;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15687");
            exit(1);
        }
    }
}
FloatTy get_minz_kdtree(CursorTy end_r_10674, CursorTy tr_568_4982_7907)
{
    TagTyPacked tmpval_15726 = *(TagTyPacked *) tr_568_4982_7907;
    CursorTy tmpcur_15727 = tr_568_4982_7907 + 1;


  switch_15764:
    ;
    switch (tmpval_15726) {

      case 2:
        {
            CursorTy jump_12222 = tr_568_4982_7907 + 1;

            return 0.0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15728 = *(CursorTy *) tmpcur_15727;
            CursorTy tmpaftercur_15729 = tmpcur_15727 + 8;
            FloatTy tmpval_15730 = *(FloatTy *) tmpaftercur_15729;
            CursorTy tmpcur_15731 = tmpaftercur_15729 + sizeof(FloatTy);
            FloatTy tmpval_15732 = *(FloatTy *) tmpcur_15731;
            CursorTy tmpcur_15733 = tmpcur_15731 + sizeof(FloatTy);
            FloatTy tmpval_15734 = *(FloatTy *) tmpcur_15733;
            CursorTy tmpcur_15735 = tmpcur_15733 + sizeof(FloatTy);
            IntTy tmpval_15736 = *(IntTy *) tmpcur_15735;
            CursorTy tmpcur_15737 = tmpcur_15735 + sizeof(IntTy);
            IntTy tmpval_15738 = *(IntTy *) tmpcur_15737;
            CursorTy tmpcur_15739 = tmpcur_15737 + sizeof(IntTy);
            FloatTy tmpval_15740 = *(FloatTy *) tmpcur_15739;
            CursorTy tmpcur_15741 = tmpcur_15739 + sizeof(FloatTy);
            FloatTy tmpval_15742 = *(FloatTy *) tmpcur_15741;
            CursorTy tmpcur_15743 = tmpcur_15741 + sizeof(FloatTy);
            FloatTy tmpval_15744 = *(FloatTy *) tmpcur_15743;
            CursorTy tmpcur_15745 = tmpcur_15743 + sizeof(FloatTy);
            FloatTy tmpval_15746 = *(FloatTy *) tmpcur_15745;
            CursorTy tmpcur_15747 = tmpcur_15745 + sizeof(FloatTy);
            FloatTy tmpval_15748 = *(FloatTy *) tmpcur_15747;
            CursorTy tmpcur_15749 = tmpcur_15747 + sizeof(FloatTy);
            FloatTy tmpval_15750 = *(FloatTy *) tmpcur_15749;
            CursorTy tmpcur_15751 = tmpcur_15749 + sizeof(FloatTy);
            FloatTy tmpval_15752 = *(FloatTy *) tmpcur_15751;
            CursorTy tmpcur_15753 = tmpcur_15751 + sizeof(FloatTy);
            CursorTy jump_12235 = tmpcur_15751 + 4;
            CursorTy jump_12234 = tmpcur_15749 + 4;
            CursorTy jump_12233 = tmpcur_15747 + 4;
            CursorTy jump_12232 = tmpcur_15745 + 4;
            CursorTy jump_12231 = tmpcur_15743 + 4;
            CursorTy jump_12230 = tmpcur_15741 + 4;
            CursorTy jump_12229 = tmpcur_15739 + 4;
            CursorTy jump_12228 = tmpcur_15737 + 8;
            CursorTy jump_12227 = tmpcur_15735 + 8;
            CursorTy jump_12226 = tmpcur_15733 + 4;
            CursorTy jump_12225 = tmpcur_15731 + 4;
            CursorTy jump_12224 = tmpaftercur_15729 + 4;
            CursorTy jump_12223 = tmpcur_15727 + 8;

            return tmpval_15750;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15754 = *(FloatTy *) tmpcur_15727;
            CursorTy tmpcur_15755 = tmpcur_15727 + sizeof(FloatTy);
            FloatTy tmpval_15756 = *(FloatTy *) tmpcur_15755;
            CursorTy tmpcur_15757 = tmpcur_15755 + sizeof(FloatTy);
            FloatTy tmpval_15758 = *(FloatTy *) tmpcur_15757;
            CursorTy tmpcur_15759 = tmpcur_15757 + sizeof(FloatTy);
            CursorTy jump_12238 = tmpcur_15757 + 4;
            CursorTy jump_12237 = tmpcur_15755 + 4;
            CursorTy jump_12236 = tmpcur_15727 + 4;

            return tmpval_15758;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15760 = *(CursorTy *) tmpcur_15727;
            CursorTy tmpaftercur_15761 = tmpcur_15727 + 8;
            CursorTy jump_12766 = tmpcur_15727 + 8;
            FloatTy call_12767 =  get_minz_kdtree(end_r_10674, tmpcur_15760);

            return call_12767;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15762 = *(CursorTy *) tmpcur_15727;
            CursorTy tmpaftercur_15763 = tmpcur_15727 + 8;
            FloatTy call_12767 =  get_minz_kdtree(end_r_10674, tmpcur_15762);

            return call_12767;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15726");
            exit(1);
        }
    }
}
FloatTy get_maxy_kdtree(CursorTy end_r_10676, CursorTy tr_586_5000_7925)
{
    TagTyPacked tmpval_15765 = *(TagTyPacked *) tr_586_5000_7925;
    CursorTy tmpcur_15766 = tr_586_5000_7925 + 1;


  switch_15803:
    ;
    switch (tmpval_15765) {

      case 2:
        {
            CursorTy jump_12240 = tr_586_5000_7925 + 1;

            return 0.0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15767 = *(CursorTy *) tmpcur_15766;
            CursorTy tmpaftercur_15768 = tmpcur_15766 + 8;
            FloatTy tmpval_15769 = *(FloatTy *) tmpaftercur_15768;
            CursorTy tmpcur_15770 = tmpaftercur_15768 + sizeof(FloatTy);
            FloatTy tmpval_15771 = *(FloatTy *) tmpcur_15770;
            CursorTy tmpcur_15772 = tmpcur_15770 + sizeof(FloatTy);
            FloatTy tmpval_15773 = *(FloatTy *) tmpcur_15772;
            CursorTy tmpcur_15774 = tmpcur_15772 + sizeof(FloatTy);
            IntTy tmpval_15775 = *(IntTy *) tmpcur_15774;
            CursorTy tmpcur_15776 = tmpcur_15774 + sizeof(IntTy);
            IntTy tmpval_15777 = *(IntTy *) tmpcur_15776;
            CursorTy tmpcur_15778 = tmpcur_15776 + sizeof(IntTy);
            FloatTy tmpval_15779 = *(FloatTy *) tmpcur_15778;
            CursorTy tmpcur_15780 = tmpcur_15778 + sizeof(FloatTy);
            FloatTy tmpval_15781 = *(FloatTy *) tmpcur_15780;
            CursorTy tmpcur_15782 = tmpcur_15780 + sizeof(FloatTy);
            FloatTy tmpval_15783 = *(FloatTy *) tmpcur_15782;
            CursorTy tmpcur_15784 = tmpcur_15782 + sizeof(FloatTy);
            FloatTy tmpval_15785 = *(FloatTy *) tmpcur_15784;
            CursorTy tmpcur_15786 = tmpcur_15784 + sizeof(FloatTy);
            FloatTy tmpval_15787 = *(FloatTy *) tmpcur_15786;
            CursorTy tmpcur_15788 = tmpcur_15786 + sizeof(FloatTy);
            FloatTy tmpval_15789 = *(FloatTy *) tmpcur_15788;
            CursorTy tmpcur_15790 = tmpcur_15788 + sizeof(FloatTy);
            FloatTy tmpval_15791 = *(FloatTy *) tmpcur_15790;
            CursorTy tmpcur_15792 = tmpcur_15790 + sizeof(FloatTy);
            CursorTy jump_12253 = tmpcur_15790 + 4;
            CursorTy jump_12252 = tmpcur_15788 + 4;
            CursorTy jump_12251 = tmpcur_15786 + 4;
            CursorTy jump_12250 = tmpcur_15784 + 4;
            CursorTy jump_12249 = tmpcur_15782 + 4;
            CursorTy jump_12248 = tmpcur_15780 + 4;
            CursorTy jump_12247 = tmpcur_15778 + 4;
            CursorTy jump_12246 = tmpcur_15776 + 8;
            CursorTy jump_12245 = tmpcur_15774 + 8;
            CursorTy jump_12244 = tmpcur_15772 + 4;
            CursorTy jump_12243 = tmpcur_15770 + 4;
            CursorTy jump_12242 = tmpaftercur_15768 + 4;
            CursorTy jump_12241 = tmpcur_15766 + 8;

            return tmpval_15787;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15793 = *(FloatTy *) tmpcur_15766;
            CursorTy tmpcur_15794 = tmpcur_15766 + sizeof(FloatTy);
            FloatTy tmpval_15795 = *(FloatTy *) tmpcur_15794;
            CursorTy tmpcur_15796 = tmpcur_15794 + sizeof(FloatTy);
            FloatTy tmpval_15797 = *(FloatTy *) tmpcur_15796;
            CursorTy tmpcur_15798 = tmpcur_15796 + sizeof(FloatTy);
            CursorTy jump_12256 = tmpcur_15796 + 4;
            CursorTy jump_12255 = tmpcur_15794 + 4;
            CursorTy jump_12254 = tmpcur_15766 + 4;

            return tmpval_15795;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15799 = *(CursorTy *) tmpcur_15766;
            CursorTy tmpaftercur_15800 = tmpcur_15766 + 8;
            CursorTy jump_12771 = tmpcur_15766 + 8;
            FloatTy call_12772 =  get_maxy_kdtree(end_r_10676, tmpcur_15799);

            return call_12772;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15801 = *(CursorTy *) tmpcur_15766;
            CursorTy tmpaftercur_15802 = tmpcur_15766 + 8;
            FloatTy call_12772 =  get_maxy_kdtree(end_r_10676, tmpcur_15801);

            return call_12772;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15765");
            exit(1);
        }
    }
}
FloatTy get_miny_kdtree(CursorTy end_r_10678, CursorTy tr_604_5018_7943)
{
    TagTyPacked tmpval_15804 = *(TagTyPacked *) tr_604_5018_7943;
    CursorTy tmpcur_15805 = tr_604_5018_7943 + 1;


  switch_15842:
    ;
    switch (tmpval_15804) {

      case 2:
        {
            CursorTy jump_12258 = tr_604_5018_7943 + 1;

            return 0.0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15806 = *(CursorTy *) tmpcur_15805;
            CursorTy tmpaftercur_15807 = tmpcur_15805 + 8;
            FloatTy tmpval_15808 = *(FloatTy *) tmpaftercur_15807;
            CursorTy tmpcur_15809 = tmpaftercur_15807 + sizeof(FloatTy);
            FloatTy tmpval_15810 = *(FloatTy *) tmpcur_15809;
            CursorTy tmpcur_15811 = tmpcur_15809 + sizeof(FloatTy);
            FloatTy tmpval_15812 = *(FloatTy *) tmpcur_15811;
            CursorTy tmpcur_15813 = tmpcur_15811 + sizeof(FloatTy);
            IntTy tmpval_15814 = *(IntTy *) tmpcur_15813;
            CursorTy tmpcur_15815 = tmpcur_15813 + sizeof(IntTy);
            IntTy tmpval_15816 = *(IntTy *) tmpcur_15815;
            CursorTy tmpcur_15817 = tmpcur_15815 + sizeof(IntTy);
            FloatTy tmpval_15818 = *(FloatTy *) tmpcur_15817;
            CursorTy tmpcur_15819 = tmpcur_15817 + sizeof(FloatTy);
            FloatTy tmpval_15820 = *(FloatTy *) tmpcur_15819;
            CursorTy tmpcur_15821 = tmpcur_15819 + sizeof(FloatTy);
            FloatTy tmpval_15822 = *(FloatTy *) tmpcur_15821;
            CursorTy tmpcur_15823 = tmpcur_15821 + sizeof(FloatTy);
            FloatTy tmpval_15824 = *(FloatTy *) tmpcur_15823;
            CursorTy tmpcur_15825 = tmpcur_15823 + sizeof(FloatTy);
            FloatTy tmpval_15826 = *(FloatTy *) tmpcur_15825;
            CursorTy tmpcur_15827 = tmpcur_15825 + sizeof(FloatTy);
            FloatTy tmpval_15828 = *(FloatTy *) tmpcur_15827;
            CursorTy tmpcur_15829 = tmpcur_15827 + sizeof(FloatTy);
            FloatTy tmpval_15830 = *(FloatTy *) tmpcur_15829;
            CursorTy tmpcur_15831 = tmpcur_15829 + sizeof(FloatTy);
            CursorTy jump_12271 = tmpcur_15829 + 4;
            CursorTy jump_12270 = tmpcur_15827 + 4;
            CursorTy jump_12269 = tmpcur_15825 + 4;
            CursorTy jump_12268 = tmpcur_15823 + 4;
            CursorTy jump_12267 = tmpcur_15821 + 4;
            CursorTy jump_12266 = tmpcur_15819 + 4;
            CursorTy jump_12265 = tmpcur_15817 + 4;
            CursorTy jump_12264 = tmpcur_15815 + 8;
            CursorTy jump_12263 = tmpcur_15813 + 8;
            CursorTy jump_12262 = tmpcur_15811 + 4;
            CursorTy jump_12261 = tmpcur_15809 + 4;
            CursorTy jump_12260 = tmpaftercur_15807 + 4;
            CursorTy jump_12259 = tmpcur_15805 + 8;

            return tmpval_15824;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15832 = *(FloatTy *) tmpcur_15805;
            CursorTy tmpcur_15833 = tmpcur_15805 + sizeof(FloatTy);
            FloatTy tmpval_15834 = *(FloatTy *) tmpcur_15833;
            CursorTy tmpcur_15835 = tmpcur_15833 + sizeof(FloatTy);
            FloatTy tmpval_15836 = *(FloatTy *) tmpcur_15835;
            CursorTy tmpcur_15837 = tmpcur_15835 + sizeof(FloatTy);
            CursorTy jump_12274 = tmpcur_15835 + 4;
            CursorTy jump_12273 = tmpcur_15833 + 4;
            CursorTy jump_12272 = tmpcur_15805 + 4;

            return tmpval_15834;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15838 = *(CursorTy *) tmpcur_15805;
            CursorTy tmpaftercur_15839 = tmpcur_15805 + 8;
            CursorTy jump_12776 = tmpcur_15805 + 8;
            FloatTy call_12777 =  get_miny_kdtree(end_r_10678, tmpcur_15838);

            return call_12777;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15840 = *(CursorTy *) tmpcur_15805;
            CursorTy tmpaftercur_15841 = tmpcur_15805 + 8;
            FloatTy call_12777 =  get_miny_kdtree(end_r_10678, tmpcur_15840);

            return call_12777;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15804");
            exit(1);
        }
    }
}
FloatTy get_maxx_kdtree(CursorTy end_r_10680, CursorTy tr_622_5036_7961)
{
    TagTyPacked tmpval_15843 = *(TagTyPacked *) tr_622_5036_7961;
    CursorTy tmpcur_15844 = tr_622_5036_7961 + 1;


  switch_15881:
    ;
    switch (tmpval_15843) {

      case 2:
        {
            CursorTy jump_12276 = tr_622_5036_7961 + 1;

            return 0.0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15845 = *(CursorTy *) tmpcur_15844;
            CursorTy tmpaftercur_15846 = tmpcur_15844 + 8;
            FloatTy tmpval_15847 = *(FloatTy *) tmpaftercur_15846;
            CursorTy tmpcur_15848 = tmpaftercur_15846 + sizeof(FloatTy);
            FloatTy tmpval_15849 = *(FloatTy *) tmpcur_15848;
            CursorTy tmpcur_15850 = tmpcur_15848 + sizeof(FloatTy);
            FloatTy tmpval_15851 = *(FloatTy *) tmpcur_15850;
            CursorTy tmpcur_15852 = tmpcur_15850 + sizeof(FloatTy);
            IntTy tmpval_15853 = *(IntTy *) tmpcur_15852;
            CursorTy tmpcur_15854 = tmpcur_15852 + sizeof(IntTy);
            IntTy tmpval_15855 = *(IntTy *) tmpcur_15854;
            CursorTy tmpcur_15856 = tmpcur_15854 + sizeof(IntTy);
            FloatTy tmpval_15857 = *(FloatTy *) tmpcur_15856;
            CursorTy tmpcur_15858 = tmpcur_15856 + sizeof(FloatTy);
            FloatTy tmpval_15859 = *(FloatTy *) tmpcur_15858;
            CursorTy tmpcur_15860 = tmpcur_15858 + sizeof(FloatTy);
            FloatTy tmpval_15861 = *(FloatTy *) tmpcur_15860;
            CursorTy tmpcur_15862 = tmpcur_15860 + sizeof(FloatTy);
            FloatTy tmpval_15863 = *(FloatTy *) tmpcur_15862;
            CursorTy tmpcur_15864 = tmpcur_15862 + sizeof(FloatTy);
            FloatTy tmpval_15865 = *(FloatTy *) tmpcur_15864;
            CursorTy tmpcur_15866 = tmpcur_15864 + sizeof(FloatTy);
            FloatTy tmpval_15867 = *(FloatTy *) tmpcur_15866;
            CursorTy tmpcur_15868 = tmpcur_15866 + sizeof(FloatTy);
            FloatTy tmpval_15869 = *(FloatTy *) tmpcur_15868;
            CursorTy tmpcur_15870 = tmpcur_15868 + sizeof(FloatTy);
            CursorTy jump_12289 = tmpcur_15868 + 4;
            CursorTy jump_12288 = tmpcur_15866 + 4;
            CursorTy jump_12287 = tmpcur_15864 + 4;
            CursorTy jump_12286 = tmpcur_15862 + 4;
            CursorTy jump_12285 = tmpcur_15860 + 4;
            CursorTy jump_12284 = tmpcur_15858 + 4;
            CursorTy jump_12283 = tmpcur_15856 + 4;
            CursorTy jump_12282 = tmpcur_15854 + 8;
            CursorTy jump_12281 = tmpcur_15852 + 8;
            CursorTy jump_12280 = tmpcur_15850 + 4;
            CursorTy jump_12279 = tmpcur_15848 + 4;
            CursorTy jump_12278 = tmpaftercur_15846 + 4;
            CursorTy jump_12277 = tmpcur_15844 + 8;

            return tmpval_15861;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15871 = *(FloatTy *) tmpcur_15844;
            CursorTy tmpcur_15872 = tmpcur_15844 + sizeof(FloatTy);
            FloatTy tmpval_15873 = *(FloatTy *) tmpcur_15872;
            CursorTy tmpcur_15874 = tmpcur_15872 + sizeof(FloatTy);
            FloatTy tmpval_15875 = *(FloatTy *) tmpcur_15874;
            CursorTy tmpcur_15876 = tmpcur_15874 + sizeof(FloatTy);
            CursorTy jump_12292 = tmpcur_15874 + 4;
            CursorTy jump_12291 = tmpcur_15872 + 4;
            CursorTy jump_12290 = tmpcur_15844 + 4;

            return tmpval_15871;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15877 = *(CursorTy *) tmpcur_15844;
            CursorTy tmpaftercur_15878 = tmpcur_15844 + 8;
            CursorTy jump_12781 = tmpcur_15844 + 8;
            FloatTy call_12782 =  get_maxx_kdtree(end_r_10680, tmpcur_15877);

            return call_12782;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15879 = *(CursorTy *) tmpcur_15844;
            CursorTy tmpaftercur_15880 = tmpcur_15844 + 8;
            FloatTy call_12782 =  get_maxx_kdtree(end_r_10680, tmpcur_15879);

            return call_12782;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15843");
            exit(1);
        }
    }
}
FloatTy get_minx_kdtree(CursorTy end_r_10682, CursorTy tr_640_5054_7979)
{
    TagTyPacked tmpval_15882 = *(TagTyPacked *) tr_640_5054_7979;
    CursorTy tmpcur_15883 = tr_640_5054_7979 + 1;


  switch_15920:
    ;
    switch (tmpval_15882) {

      case 2:
        {
            CursorTy jump_12294 = tr_640_5054_7979 + 1;

            return 0.0;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15884 = *(CursorTy *) tmpcur_15883;
            CursorTy tmpaftercur_15885 = tmpcur_15883 + 8;
            FloatTy tmpval_15886 = *(FloatTy *) tmpaftercur_15885;
            CursorTy tmpcur_15887 = tmpaftercur_15885 + sizeof(FloatTy);
            FloatTy tmpval_15888 = *(FloatTy *) tmpcur_15887;
            CursorTy tmpcur_15889 = tmpcur_15887 + sizeof(FloatTy);
            FloatTy tmpval_15890 = *(FloatTy *) tmpcur_15889;
            CursorTy tmpcur_15891 = tmpcur_15889 + sizeof(FloatTy);
            IntTy tmpval_15892 = *(IntTy *) tmpcur_15891;
            CursorTy tmpcur_15893 = tmpcur_15891 + sizeof(IntTy);
            IntTy tmpval_15894 = *(IntTy *) tmpcur_15893;
            CursorTy tmpcur_15895 = tmpcur_15893 + sizeof(IntTy);
            FloatTy tmpval_15896 = *(FloatTy *) tmpcur_15895;
            CursorTy tmpcur_15897 = tmpcur_15895 + sizeof(FloatTy);
            FloatTy tmpval_15898 = *(FloatTy *) tmpcur_15897;
            CursorTy tmpcur_15899 = tmpcur_15897 + sizeof(FloatTy);
            FloatTy tmpval_15900 = *(FloatTy *) tmpcur_15899;
            CursorTy tmpcur_15901 = tmpcur_15899 + sizeof(FloatTy);
            FloatTy tmpval_15902 = *(FloatTy *) tmpcur_15901;
            CursorTy tmpcur_15903 = tmpcur_15901 + sizeof(FloatTy);
            FloatTy tmpval_15904 = *(FloatTy *) tmpcur_15903;
            CursorTy tmpcur_15905 = tmpcur_15903 + sizeof(FloatTy);
            FloatTy tmpval_15906 = *(FloatTy *) tmpcur_15905;
            CursorTy tmpcur_15907 = tmpcur_15905 + sizeof(FloatTy);
            FloatTy tmpval_15908 = *(FloatTy *) tmpcur_15907;
            CursorTy tmpcur_15909 = tmpcur_15907 + sizeof(FloatTy);
            CursorTy jump_12307 = tmpcur_15907 + 4;
            CursorTy jump_12306 = tmpcur_15905 + 4;
            CursorTy jump_12305 = tmpcur_15903 + 4;
            CursorTy jump_12304 = tmpcur_15901 + 4;
            CursorTy jump_12303 = tmpcur_15899 + 4;
            CursorTy jump_12302 = tmpcur_15897 + 4;
            CursorTy jump_12301 = tmpcur_15895 + 4;
            CursorTy jump_12300 = tmpcur_15893 + 8;
            CursorTy jump_12299 = tmpcur_15891 + 8;
            CursorTy jump_12298 = tmpcur_15889 + 4;
            CursorTy jump_12297 = tmpcur_15887 + 4;
            CursorTy jump_12296 = tmpaftercur_15885 + 4;
            CursorTy jump_12295 = tmpcur_15883 + 8;

            return tmpval_15898;
            break;
        }

      case 0:
        {
            FloatTy tmpval_15910 = *(FloatTy *) tmpcur_15883;
            CursorTy tmpcur_15911 = tmpcur_15883 + sizeof(FloatTy);
            FloatTy tmpval_15912 = *(FloatTy *) tmpcur_15911;
            CursorTy tmpcur_15913 = tmpcur_15911 + sizeof(FloatTy);
            FloatTy tmpval_15914 = *(FloatTy *) tmpcur_15913;
            CursorTy tmpcur_15915 = tmpcur_15913 + sizeof(FloatTy);
            CursorTy jump_12310 = tmpcur_15913 + 4;
            CursorTy jump_12309 = tmpcur_15911 + 4;
            CursorTy jump_12308 = tmpcur_15883 + 4;

            return tmpval_15910;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15916 = *(CursorTy *) tmpcur_15883;
            CursorTy tmpaftercur_15917 = tmpcur_15883 + 8;
            CursorTy jump_12786 = tmpcur_15883 + 8;
            FloatTy call_12787 =  get_minx_kdtree(end_r_10682, tmpcur_15916);

            return call_12787;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_15918 = *(CursorTy *) tmpcur_15883;
            CursorTy tmpaftercur_15919 = tmpcur_15883 + 8;
            FloatTy call_12787 =  get_minx_kdtree(end_r_10682, tmpcur_15918);

            return call_12787;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15882");
            exit(1);
        }
    }
}
FloatTy get_coord_point3d(IntTy axis_701_5115_7997,
                          Float32Float32Float32Prod pt_702_5116_7998)
{
    BoolTy fltIf_7209_8003 = axis_701_5115_7997 == 0;

    if (fltIf_7209_8003) {
        return pt_702_5116_7998.field0;
    } else {
        BoolTy fltIf_7210_8004 = axis_701_5115_7997 == 1;

        if (fltIf_7210_8004) {
            return pt_702_5116_7998.field1;
        } else {
            return pt_702_5116_7998.field2;
        }
    }
}
IntTy getNextAxis_3d(IntTy i_707_5121_8005)
{
    IntTy fltPrm_7211_8006 = i_707_5121_8005 + 1;
    IntTy tailprim_12311 = fltPrm_7211_8006 % 3;

    return tailprim_12311;
}
VectorTy *sort_point3d(IntTy axis_708_5122_8007, VectorTy *ls_709_5123_8008)
{
    IntTy fltAppE_7212_8010 = vector_length(ls_709_5123_8008);
    IntTy n__743_5756_8357_9075 =  maxInt(fltAppE_7212_8010, 0);
    IntTy tmp_149 = sizeof(Float32Float32Float32Prod);
    VectorTy *vec_744_5757_8358_9076 = vector_alloc(n__743_5756_8357_9075,
                                                    tmp_149);
    VectorTy *vec1_745_5758_8359_9077 =
              generate_loop_2376_3711(vec_744_5757_8358_9076, 0, n__743_5756_8357_9075, ls_709_5123_8008);
    BoolTy fltIf_7213_8012 = axis_708_5122_8007 == 0;

    if (fltIf_7213_8012) {
        VectorTy *tailprim_12312 = vector_inplace_sort(vec1_745_5758_8359_9077,
                                                       cmpx_point3d);

        return tailprim_12312;
    } else {
        BoolTy fltIf_7214_8014 = axis_708_5122_8007 == 1;

        if (fltIf_7214_8014) {
            VectorTy *tailprim_12313 =
                     vector_inplace_sort(vec1_745_5758_8359_9077, cmpy_point3d);

            return tailprim_12313;
        } else {
            VectorTy *tailprim_12314 =
                     vector_inplace_sort(vec1_745_5758_8359_9077, cmpz_point3d);

            return tailprim_12314;
        }
    }
}
FloatTy dist_point3d(Float32Float32Float32Prod a_711_5125_8017,
                     Float32Float32Float32Prod b_712_5126_8018)
{
    FloatTy d1_721_5135_8027 = a_711_5125_8017.field0 - b_712_5126_8018.field0;
    FloatTy d2_722_5136_8028 = a_711_5125_8017.field1 - b_712_5126_8018.field1;
    FloatTy d3_723_5137_8029 = a_711_5125_8017.field2 - b_712_5126_8018.field2;
    FloatTy fltPrm_7216_8030 = d1_721_5135_8027 * d1_721_5135_8027;
    FloatTy fltPrm_7217_8031 = d2_722_5136_8028 * d2_722_5136_8028;
    FloatTy fltPrm_7215_8032 = fltPrm_7216_8030 + fltPrm_7217_8031;
    FloatTy fltPrm_7218_8033 = d3_723_5137_8029 * d3_723_5137_8029;
    FloatTy tailprim_12315 = fltPrm_7215_8032 + fltPrm_7218_8033;

    return tailprim_12315;
}
unsigned char print_check(BoolTy b_726_5138_8034)
{
    if (b_726_5138_8034) {
        unsigned char wildcard__14_727_5139_8035 = print_symbol(14963);

        return 0;
    } else {
        unsigned char wildcard__16_728_5140_8036 = print_symbol(14965);

        return 0;
    }
}
FloatTy float_abs(FloatTy f_729_5141_8037)
{
    BoolTy fltIf_7219_8038 = f_729_5141_8037 < 0.0;

    if (fltIf_7219_8038) {
        FloatTy fltPrm_7220_8039 = 0.0 - 1.0;
        FloatTy tailprim_12318 = f_729_5141_8037 * fltPrm_7220_8039;

        return tailprim_12318;
    } else {
        return f_729_5141_8037;
    }
}
BoolTy eq_point3d(Float32Float32Float32Prod a_730_5142_8040,
                  Float32Float32Float32Prod b_731_5143_8041)
{
    BoolTy fltPrm_7221_8050 = a_730_5142_8040.field0 == b_731_5143_8041.field0;
    BoolTy fltPrm_7223_8051 = a_730_5142_8040.field1 == b_731_5143_8041.field1;
    BoolTy fltPrm_7224_8052 = a_730_5142_8040.field2 == b_731_5143_8041.field2;
    BoolTy fltPrm_7222_8053 = fltPrm_7223_8051 && fltPrm_7224_8052;
    BoolTy tailprim_12319 = fltPrm_7221_8050 && fltPrm_7222_8053;

    return tailprim_12319;
}
VectorTy *masspointsInBox_seq(Float32Float32Float32Float32Prod box_792_5178_8054,
                              VectorTy *mpts_793_5179_8055)
{
    IntTy fltAppE_7225_8058 = vector_length(mpts_793_5179_8055);
    IntTy n__743_5921_8363_9081 =  maxInt(fltAppE_7225_8058, 0);
    IntTy tmp_151 = sizeof(IntTy);
    VectorTy *vec_744_5922_8364_9082 = vector_alloc(n__743_5921_8363_9081,
                                                    tmp_151);
    VectorTy *vec1_745_5923_8365_9083 =
              generate_loop_2374_3717(vec_744_5922_8364_9082, 0, n__743_5921_8363_9081, mpts_793_5179_8055, (Float32Float32Float32Float32Prod) {box_792_5178_8054.field0, box_792_5178_8054.field1, box_792_5178_8054.field2, box_792_5178_8054.field3});
    IntTy fltAppE_7297_8368_9086 = vector_length(vec1_745_5923_8365_9083);
    IntTy num_ones_1034_5717_6585_8060 =
           foldl_loop_2380_3709(0, fltAppE_7297_8368_9086, 0, vec1_745_5923_8365_9083);
    IntTy tmp_150 = sizeof(Float32Float32Float32Prod);
    VectorTy *to_1035_5718_6586_8061 =
             vector_alloc(num_ones_1034_5717_6585_8060, tmp_150);
    IntTy len_idxs_1036_5719_6587_8062 = vector_length(vec1_745_5923_8365_9083);
    VectorTy *tailapp_12320 =
              filter_loop_2379(vec1_745_5923_8365_9083, 0, 0, len_idxs_1036_5719_6587_8062, mpts_793_5179_8055, to_1035_5718_6586_8061);

    return tailapp_12320;
}
Float32Float32Float32Prod calcCentroid_seq(VectorTy *mpts_808_5190_8063)
{
    IntTy fltAppE_7226_8066 = vector_length(mpts_808_5190_8063);
    Float32Float32Float32Prod tmp_struct_152 =
                               foldl_loop_2371_3737(0, fltAppE_7226_8066, (Float32Float32Float32Prod) {0.0, 0.0, 0.0}, mpts_808_5190_8063);
    FloatTy pvrtmp_15931 = tmp_struct_152.field0;
    FloatTy pvrtmp_15932 = tmp_struct_152.field1;
    FloatTy pvrtmp_15933 = tmp_struct_152.field2;
    FloatTy fltPrd_7227_8072 = pvrtmp_15931 / pvrtmp_15933;
    FloatTy fltPrd_7228_8073 = pvrtmp_15932 / pvrtmp_15933;

    return (Float32Float32Float32Prod) {fltPrd_7227_8072, fltPrd_7228_8073,
                                        pvrtmp_15933};
}
Float32Float32Prod calcAccel_seq(CursorTy end_r_10684,
                                 Float32Float32Float32Prod mpt_825_5196_8074,
                                 CursorTy tr_826_5197_8075)
{
    TagTyPacked tmpval_15937 = *(TagTyPacked *) tr_826_5197_8075;
    CursorTy tmpcur_15938 = tr_826_5197_8075 + 1;


  switch_16011:
    ;
    switch (tmpval_15937) {

      case 0:
        {
            CursorTy jump_12322 = tr_826_5197_8075 + 1;

            return (Float32Float32Prod) {0.0, 0.0};
            break;
        }

      case 1:
        {
            FloatTy tmpval_15941 = *(FloatTy *) tmpcur_15938;
            CursorTy tmpcur_15942 = tmpcur_15938 + sizeof(FloatTy);
            FloatTy tmpval_15943 = *(FloatTy *) tmpcur_15942;
            CursorTy tmpcur_15944 = tmpcur_15942 + sizeof(FloatTy);
            FloatTy tmpval_15945 = *(FloatTy *) tmpcur_15944;
            CursorTy tmpcur_15946 = tmpcur_15944 + sizeof(FloatTy);
            CursorTy jump_12326 = tmpcur_15944 + 4;
            CursorTy jump_12325 = tmpcur_15942 + 4;
            CursorTy jump_12324 = tmpcur_15938 + 4;
            BoolTy fltPrm_7230_8087 = mpt_825_5196_8074.field0 == tmpval_15941;
            BoolTy fltPrm_7232_8088 = mpt_825_5196_8074.field1 == tmpval_15943;
            BoolTy fltPrm_7233_8089 = mpt_825_5196_8074.field2 == tmpval_15945;
            BoolTy fltPrm_7231_8090 = fltPrm_7232_8088 && fltPrm_7233_8089;
            BoolTy fltIf_7229_8091 = fltPrm_7230_8087 && fltPrm_7231_8090;

            if (fltIf_7229_8091) {
                return (Float32Float32Prod) {0.0, 0.0};
            } else {
                FloatTy dx_862_5233_6598_8092 = mpt_825_5196_8074.field0 -
                        tmpval_15941;
                FloatTy dy_863_5234_6599_8093 = mpt_825_5196_8074.field1 -
                        tmpval_15943;
                FloatTy fltPrm_7234_8094 = dx_862_5233_6598_8092 *
                        dx_862_5233_6598_8092;
                FloatTy fltPrm_7235_8095 = dy_863_5234_6599_8093 *
                        dy_863_5234_6599_8093;
                FloatTy rsqr_864_5235_6600_8096 = fltPrm_7234_8094 +
                        fltPrm_7235_8095;
                FloatTy r_865_5236_6601_8097 = sqrt(rsqr_864_5235_6600_8096);
                FloatTy fltPrm_7236_8098 = mpt_825_5196_8074.field2 *
                        tmpval_15945;
                FloatTy fltPrm_7237_8099 = rsqr_864_5235_6600_8096 *
                        r_865_5236_6601_8097;
                FloatTy s_866_5237_6602_8100 = fltPrm_7236_8098 /
                        fltPrm_7237_8099;
                FloatTy fltPrd_7238_8101 = dx_862_5233_6598_8092 *
                        s_866_5237_6602_8100;
                FloatTy fltPrd_7239_8102 = dy_863_5234_6599_8093 *
                        s_866_5237_6602_8100;

                return (Float32Float32Prod) {fltPrd_7238_8101,
                                             fltPrd_7239_8102};
            }
            break;
        }

      case 3:
        {
            CursorTy tmpcur_15951 = *(CursorTy *) tmpcur_15938;
            CursorTy tmpaftercur_15952 = tmpcur_15938 + 8;
            CursorTy tmpcur_15953 = *(CursorTy *) tmpaftercur_15952;
            CursorTy tmpaftercur_15954 = tmpaftercur_15952 + 8;
            CursorTy tmpcur_15955 = *(CursorTy *) tmpaftercur_15954;
            CursorTy tmpaftercur_15956 = tmpaftercur_15954 + 8;
            FloatTy tmpval_15957 = *(FloatTy *) tmpaftercur_15956;
            CursorTy tmpcur_15958 = tmpaftercur_15956 + sizeof(FloatTy);
            FloatTy tmpval_15959 = *(FloatTy *) tmpcur_15958;
            CursorTy tmpcur_15960 = tmpcur_15958 + sizeof(FloatTy);
            FloatTy tmpval_15961 = *(FloatTy *) tmpcur_15960;
            CursorTy tmpcur_15962 = tmpcur_15960 + sizeof(FloatTy);
            IntTy tmpval_15963 = *(IntTy *) tmpcur_15962;
            CursorTy tmpcur_15964 = tmpcur_15962 + sizeof(IntTy);
            FloatTy tmpval_15965 = *(FloatTy *) tmpcur_15964;
            CursorTy tmpcur_15966 = tmpcur_15964 + sizeof(FloatTy);
            CursorTy jump_12336 = tmpcur_15964 + 4;
            CursorTy jump_12335 = tmpcur_15962 + 8;
            CursorTy jump_12334 = tmpcur_15960 + 4;
            CursorTy jump_12333 = tmpcur_15958 + 4;
            CursorTy jump_12332 = tmpaftercur_15956 + 4;
            CursorTy jump_12331 = tmpaftercur_15954 + 8;
            CursorTy jump_12330 = tmpaftercur_15952 + 8;
            CursorTy jump_12329 = tmpcur_15938 + 8;
            FloatTy d1_1025_5390_8243_9095 = mpt_825_5196_8074.field0 -
                    tmpval_15957;
            FloatTy d2_1026_5391_8244_9096 = mpt_825_5196_8074.field1 -
                    tmpval_15959;
            FloatTy fltPrm_7276_8245_9097 = d1_1025_5390_8243_9095 *
                    d1_1025_5390_8243_9095;
            FloatTy fltPrm_7277_8246_9098 = d2_1026_5391_8244_9096 *
                    d2_1026_5391_8244_9096;
            FloatTy r2_870_5241_6606_8118 = fltPrm_7276_8245_9097 +
                    fltPrm_7277_8246_9098;
            FloatTy widthsq_871_5242_6607_8119 = tmpval_15965 * tmpval_15965;
            BoolTy fltIf_7240_8120 = r2_870_5241_6606_8118 <
                   widthsq_871_5242_6607_8119;

            if (fltIf_7240_8120) {
                Float32Float32Prod tmp_struct_153 =
                                    calcAccel_seq(end_r_10684, (Float32Float32Float32Prod) {mpt_825_5196_8074.field0, mpt_825_5196_8074.field1, mpt_825_5196_8074.field2}, tmpcur_15966);
                FloatTy pvrtmp_15974 = tmp_struct_153.field0;
                FloatTy pvrtmp_15975 = tmp_struct_153.field1;
                Float32Float32Prod tmp_struct_154 =
                                    calcAccel_seq(end_r_10684, (Float32Float32Float32Prod) {mpt_825_5196_8074.field0, mpt_825_5196_8074.field1, mpt_825_5196_8074.field2}, tmpcur_15951);
                FloatTy pvrtmp_15979 = tmp_struct_154.field0;
                FloatTy pvrtmp_15980 = tmp_struct_154.field1;
                Float32Float32Prod tmp_struct_155 =
                                    calcAccel_seq(end_r_10684, (Float32Float32Float32Prod) {mpt_825_5196_8074.field0, mpt_825_5196_8074.field1, mpt_825_5196_8074.field2}, tmpcur_15953);
                FloatTy pvrtmp_15984 = tmp_struct_155.field0;
                FloatTy pvrtmp_15985 = tmp_struct_155.field1;
                Float32Float32Prod tmp_struct_156 =
                                    calcAccel_seq(end_r_10684, (Float32Float32Float32Prod) {mpt_825_5196_8074.field0, mpt_825_5196_8074.field1, mpt_825_5196_8074.field2}, tmpcur_15955);
                FloatTy pvrtmp_15989 = tmp_struct_156.field0;
                FloatTy pvrtmp_15990 = tmp_struct_156.field1;
                FloatTy fltPrm_7243_8133 = pvrtmp_15974 + pvrtmp_15979;
                FloatTy fltPrm_7242_8134 = fltPrm_7243_8133 + pvrtmp_15984;
                FloatTy fltPrd_7241_8135 = fltPrm_7242_8134 + pvrtmp_15989;
                FloatTy fltPrm_7246_8136 = pvrtmp_15975 + pvrtmp_15980;
                FloatTy fltPrm_7245_8137 = fltPrm_7246_8136 + pvrtmp_15985;
                FloatTy fltPrd_7244_8138 = fltPrm_7245_8137 + pvrtmp_15990;

                return (Float32Float32Prod) {fltPrd_7241_8135,
                                             fltPrd_7244_8138};
            } else {
                BoolTy fltPrm_7248_8147 = mpt_825_5196_8074.field0 ==
                       tmpval_15957;
                BoolTy fltPrm_7250_8148 = mpt_825_5196_8074.field1 ==
                       tmpval_15959;
                BoolTy fltPrm_7251_8149 = mpt_825_5196_8074.field2 ==
                       tmpval_15961;
                BoolTy fltPrm_7249_8150 = fltPrm_7250_8148 && fltPrm_7251_8149;
                BoolTy fltIf_7247_8151 = fltPrm_7248_8147 && fltPrm_7249_8150;

                if (fltIf_7247_8151) {
                    return (Float32Float32Prod) {0.0, 0.0};
                } else {
                    FloatTy dx_862_5233_6616_8152 = mpt_825_5196_8074.field0 -
                            tmpval_15957;
                    FloatTy dy_863_5234_6617_8153 = mpt_825_5196_8074.field1 -
                            tmpval_15959;
                    FloatTy fltPrm_7252_8154 = dx_862_5233_6616_8152 *
                            dx_862_5233_6616_8152;
                    FloatTy fltPrm_7253_8155 = dy_863_5234_6617_8153 *
                            dy_863_5234_6617_8153;
                    FloatTy rsqr_864_5235_6618_8156 = fltPrm_7252_8154 +
                            fltPrm_7253_8155;
                    FloatTy r_865_5236_6619_8157 =
                            sqrt(rsqr_864_5235_6618_8156);
                    FloatTy fltPrm_7254_8158 = mpt_825_5196_8074.field2 *
                            tmpval_15961;
                    FloatTy fltPrm_7255_8159 = rsqr_864_5235_6618_8156 *
                            r_865_5236_6619_8157;
                    FloatTy s_866_5237_6620_8160 = fltPrm_7254_8158 /
                            fltPrm_7255_8159;
                    FloatTy fltPrd_7256_8161 = dx_862_5233_6616_8152 *
                            s_866_5237_6620_8160;
                    FloatTy fltPrd_7257_8162 = dy_863_5234_6617_8153 *
                            s_866_5237_6620_8160;

                    return (Float32Float32Prod) {fltPrd_7256_8161,
                                                 fltPrd_7257_8162};
                }
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_15997 = *(CursorTy *) tmpcur_15938;
            CursorTy tmpaftercur_15998 = tmpcur_15938 + 8;
            CursorTy jump_12791 = tmpcur_15938 + 8;
            Float32Float32Prod tmp_struct_157 =
                                calcAccel_seq(end_r_10684, (Float32Float32Float32Prod) {mpt_825_5196_8074.field0, mpt_825_5196_8074.field1, mpt_825_5196_8074.field2}, tmpcur_15997);
            FloatTy pvrtmp_16002 = tmp_struct_157.field0;
            FloatTy pvrtmp_16003 = tmp_struct_157.field1;

            return (Float32Float32Prod) {pvrtmp_16002, pvrtmp_16003};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16004 = *(CursorTy *) tmpcur_15938;
            CursorTy tmpaftercur_16005 = tmpcur_15938 + 8;
            Float32Float32Prod tmp_struct_158 =
                                calcAccel_seq(end_r_10684, (Float32Float32Float32Prod) {mpt_825_5196_8074.field0, mpt_825_5196_8074.field1, mpt_825_5196_8074.field2}, tmpcur_16004);
            FloatTy pvrtmp_16009 = tmp_struct_158.field0;
            FloatTy pvrtmp_16010 = tmp_struct_158.field1;

            return (Float32Float32Prod) {pvrtmp_16009, pvrtmp_16010};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_15937");
            exit(1);
        }
    }
}
IntTy getTotalPoints_qtree(CursorTy end_r_10686, CursorTy tr_884_5255_8179)
{
    TagTyPacked tmpval_16012 = *(TagTyPacked *) tr_884_5255_8179;
    CursorTy tmpcur_16013 = tr_884_5255_8179 + 1;


  switch_16040:
    ;
    switch (tmpval_16012) {

      case 0:
        {
            CursorTy jump_12342 = tr_884_5255_8179 + 1;

            return 0;
            break;
        }

      case 1:
        {
            FloatTy tmpval_16014 = *(FloatTy *) tmpcur_16013;
            CursorTy tmpcur_16015 = tmpcur_16013 + sizeof(FloatTy);
            FloatTy tmpval_16016 = *(FloatTy *) tmpcur_16015;
            CursorTy tmpcur_16017 = tmpcur_16015 + sizeof(FloatTy);
            FloatTy tmpval_16018 = *(FloatTy *) tmpcur_16017;
            CursorTy tmpcur_16019 = tmpcur_16017 + sizeof(FloatTy);
            CursorTy jump_12345 = tmpcur_16017 + 4;
            CursorTy jump_12344 = tmpcur_16015 + 4;
            CursorTy jump_12343 = tmpcur_16013 + 4;

            return 1;
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16020 = *(CursorTy *) tmpcur_16013;
            CursorTy tmpaftercur_16021 = tmpcur_16013 + 8;
            CursorTy tmpcur_16022 = *(CursorTy *) tmpaftercur_16021;
            CursorTy tmpaftercur_16023 = tmpaftercur_16021 + 8;
            CursorTy tmpcur_16024 = *(CursorTy *) tmpaftercur_16023;
            CursorTy tmpaftercur_16025 = tmpaftercur_16023 + 8;
            FloatTy tmpval_16026 = *(FloatTy *) tmpaftercur_16025;
            CursorTy tmpcur_16027 = tmpaftercur_16025 + sizeof(FloatTy);
            FloatTy tmpval_16028 = *(FloatTy *) tmpcur_16027;
            CursorTy tmpcur_16029 = tmpcur_16027 + sizeof(FloatTy);
            FloatTy tmpval_16030 = *(FloatTy *) tmpcur_16029;
            CursorTy tmpcur_16031 = tmpcur_16029 + sizeof(FloatTy);
            IntTy tmpval_16032 = *(IntTy *) tmpcur_16031;
            CursorTy tmpcur_16033 = tmpcur_16031 + sizeof(IntTy);
            FloatTy tmpval_16034 = *(FloatTy *) tmpcur_16033;
            CursorTy tmpcur_16035 = tmpcur_16033 + sizeof(FloatTy);
            CursorTy jump_12353 = tmpcur_16033 + 4;
            CursorTy jump_12352 = tmpcur_16031 + 8;
            CursorTy jump_12351 = tmpcur_16029 + 4;
            CursorTy jump_12350 = tmpcur_16027 + 4;
            CursorTy jump_12349 = tmpaftercur_16025 + 4;
            CursorTy jump_12348 = tmpaftercur_16023 + 8;
            CursorTy jump_12347 = tmpaftercur_16021 + 8;
            CursorTy jump_12346 = tmpcur_16013 + 8;

            return tmpval_16032;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16036 = *(CursorTy *) tmpcur_16013;
            CursorTy tmpaftercur_16037 = tmpcur_16013 + 8;
            CursorTy jump_12796 = tmpcur_16013 + 8;
            IntTy call_12797 =  getTotalPoints_qtree(end_r_10686, tmpcur_16036);

            return call_12797;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16038 = *(CursorTy *) tmpcur_16013;
            CursorTy tmpaftercur_16039 = tmpcur_16013 + 8;
            IntTy call_12797 =  getTotalPoints_qtree(end_r_10686, tmpcur_16038);

            return call_12797;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16012");
            exit(1);
        }
    }
}
FloatTy sum_mass_points(VectorTy *mpts_951_5322_8192)
{
    IntTy fltAppE_7262_8195 = vector_length(mpts_951_5322_8192);
    FloatTy tailapp_12354 =
             foldl_loop_2370_3739(0, fltAppE_7262_8195, 0.0, mpts_951_5322_8192);

    return tailapp_12354;
}
CursorInt64Prod countLeavesQtree(CursorTy end_r_10688,
                                 CursorTy tr_958_5323_8196)
{
    TagTyPacked tmpval_16041 = *(TagTyPacked *) tr_958_5323_8196;
    CursorTy tmpcur_16042 = tr_958_5323_8196 + 1;


  switch_16081:
    ;
    switch (tmpval_16041) {

      case 0:
        {
            CursorTy jump_12357 = tr_958_5323_8196 + 1;

            return (CursorInt64Prod) {jump_12357, 0};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16043 = *(FloatTy *) tmpcur_16042;
            CursorTy tmpcur_16044 = tmpcur_16042 + sizeof(FloatTy);
            FloatTy tmpval_16045 = *(FloatTy *) tmpcur_16044;
            CursorTy tmpcur_16046 = tmpcur_16044 + sizeof(FloatTy);
            FloatTy tmpval_16047 = *(FloatTy *) tmpcur_16046;
            CursorTy tmpcur_16048 = tmpcur_16046 + sizeof(FloatTy);
            CursorTy jump_12360 = tmpcur_16046 + 4;
            CursorTy jump_12359 = tmpcur_16044 + 4;
            CursorTy jump_12358 = tmpcur_16042 + 4;

            return (CursorInt64Prod) {jump_12360, 1};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16049 = *(CursorTy *) tmpcur_16042;
            CursorTy tmpaftercur_16050 = tmpcur_16042 + 8;
            CursorTy tmpcur_16051 = *(CursorTy *) tmpaftercur_16050;
            CursorTy tmpaftercur_16052 = tmpaftercur_16050 + 8;
            CursorTy tmpcur_16053 = *(CursorTy *) tmpaftercur_16052;
            CursorTy tmpaftercur_16054 = tmpaftercur_16052 + 8;
            FloatTy tmpval_16055 = *(FloatTy *) tmpaftercur_16054;
            CursorTy tmpcur_16056 = tmpaftercur_16054 + sizeof(FloatTy);
            FloatTy tmpval_16057 = *(FloatTy *) tmpcur_16056;
            CursorTy tmpcur_16058 = tmpcur_16056 + sizeof(FloatTy);
            FloatTy tmpval_16059 = *(FloatTy *) tmpcur_16058;
            CursorTy tmpcur_16060 = tmpcur_16058 + sizeof(FloatTy);
            IntTy tmpval_16061 = *(IntTy *) tmpcur_16060;
            CursorTy tmpcur_16062 = tmpcur_16060 + sizeof(IntTy);
            FloatTy tmpval_16063 = *(FloatTy *) tmpcur_16062;
            CursorTy tmpcur_16064 = tmpcur_16062 + sizeof(FloatTy);
            CursorTy jump_12368 = tmpcur_16062 + 4;
            CursorTy jump_12367 = tmpcur_16060 + 8;
            CursorTy jump_12366 = tmpcur_16058 + 4;
            CursorTy jump_12365 = tmpcur_16056 + 4;
            CursorTy jump_12364 = tmpaftercur_16054 + 4;
            CursorTy jump_12363 = tmpaftercur_16052 + 8;
            CursorTy jump_12362 = tmpaftercur_16050 + 8;
            CursorTy jump_12361 = tmpcur_16042 + 8;
            CursorInt64Prod tmp_struct_159 =
                             countLeavesQtree(end_r_10688, tmpcur_16064);
            CursorTy pvrtmp_16065 = tmp_struct_159.field0;
            IntTy pvrtmp_16066 = tmp_struct_159.field1;
            CursorInt64Prod tmp_struct_160 =
                             countLeavesQtree(end_r_10688, tmpcur_16049);
            CursorTy pvrtmp_16067 = tmp_struct_160.field0;
            IntTy pvrtmp_16068 = tmp_struct_160.field1;
            IntTy fltPrm_7264_8211 = pvrtmp_16066 + pvrtmp_16068;
            CursorInt64Prod tmp_struct_161 =
                             countLeavesQtree(end_r_10688, tmpcur_16051);
            CursorTy pvrtmp_16069 = tmp_struct_161.field0;
            IntTy pvrtmp_16070 = tmp_struct_161.field1;
            IntTy fltPrm_7263_8213 = fltPrm_7264_8211 + pvrtmp_16070;
            CursorInt64Prod tmp_struct_162 =
                             countLeavesQtree(end_r_10688, tmpcur_16053);
            CursorTy pvrtmp_16071 = tmp_struct_162.field0;
            IntTy pvrtmp_16072 = tmp_struct_162.field1;
            IntTy tailprim_12373 = fltPrm_7263_8213 + pvrtmp_16072;

            return (CursorInt64Prod) {pvrtmp_16071, tailprim_12373};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16073 = *(CursorTy *) tmpcur_16042;
            CursorTy tmpaftercur_16074 = tmpcur_16042 + 8;
            CursorTy jump_12801 = tmpcur_16042 + 8;
            CursorInt64Prod tmp_struct_163 =
                             countLeavesQtree(end_r_10688, tmpcur_16073);
            CursorTy pvrtmp_16075 = tmp_struct_163.field0;
            IntTy pvrtmp_16076 = tmp_struct_163.field1;

            return (CursorInt64Prod) {jump_12801, pvrtmp_16076};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16077 = *(CursorTy *) tmpcur_16042;
            CursorTy tmpaftercur_16078 = tmpcur_16042 + 8;
            CursorInt64Prod tmp_struct_164 =
                             countLeavesQtree(end_r_10688, tmpcur_16077);
            CursorTy pvrtmp_16079 = tmp_struct_164.field0;
            IntTy pvrtmp_16080 = tmp_struct_164.field1;

            return (CursorInt64Prod) {pvrtmp_16079, pvrtmp_16080};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16041");
            exit(1);
        }
    }
}
CursorFloat32Prod sumQtree(CursorTy end_r_10690, CursorTy tr_971_5336_8215)
{
    TagTyPacked tmpval_16082 = *(TagTyPacked *) tr_971_5336_8215;
    CursorTy tmpcur_16083 = tr_971_5336_8215 + 1;


  switch_16122:
    ;
    switch (tmpval_16082) {

      case 0:
        {
            CursorTy jump_12375 = tr_971_5336_8215 + 1;

            return (CursorFloat32Prod) {jump_12375, 0.0};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16084 = *(FloatTy *) tmpcur_16083;
            CursorTy tmpcur_16085 = tmpcur_16083 + sizeof(FloatTy);
            FloatTy tmpval_16086 = *(FloatTy *) tmpcur_16085;
            CursorTy tmpcur_16087 = tmpcur_16085 + sizeof(FloatTy);
            FloatTy tmpval_16088 = *(FloatTy *) tmpcur_16087;
            CursorTy tmpcur_16089 = tmpcur_16087 + sizeof(FloatTy);
            CursorTy jump_12378 = tmpcur_16087 + 4;
            CursorTy jump_12377 = tmpcur_16085 + 4;
            CursorTy jump_12376 = tmpcur_16083 + 4;
            FloatTy fltPrm_7269_8219 = tmpval_16084 + tmpval_16086;
            FloatTy tailprim_12379 = fltPrm_7269_8219 + tmpval_16088;

            return (CursorFloat32Prod) {jump_12378, tailprim_12379};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16090 = *(CursorTy *) tmpcur_16083;
            CursorTy tmpaftercur_16091 = tmpcur_16083 + 8;
            CursorTy tmpcur_16092 = *(CursorTy *) tmpaftercur_16091;
            CursorTy tmpaftercur_16093 = tmpaftercur_16091 + 8;
            CursorTy tmpcur_16094 = *(CursorTy *) tmpaftercur_16093;
            CursorTy tmpaftercur_16095 = tmpaftercur_16093 + 8;
            FloatTy tmpval_16096 = *(FloatTy *) tmpaftercur_16095;
            CursorTy tmpcur_16097 = tmpaftercur_16095 + sizeof(FloatTy);
            FloatTy tmpval_16098 = *(FloatTy *) tmpcur_16097;
            CursorTy tmpcur_16099 = tmpcur_16097 + sizeof(FloatTy);
            FloatTy tmpval_16100 = *(FloatTy *) tmpcur_16099;
            CursorTy tmpcur_16101 = tmpcur_16099 + sizeof(FloatTy);
            IntTy tmpval_16102 = *(IntTy *) tmpcur_16101;
            CursorTy tmpcur_16103 = tmpcur_16101 + sizeof(IntTy);
            FloatTy tmpval_16104 = *(FloatTy *) tmpcur_16103;
            CursorTy tmpcur_16105 = tmpcur_16103 + sizeof(FloatTy);
            CursorTy jump_12387 = tmpcur_16103 + 4;
            CursorTy jump_12386 = tmpcur_16101 + 8;
            CursorTy jump_12385 = tmpcur_16099 + 4;
            CursorTy jump_12384 = tmpcur_16097 + 4;
            CursorTy jump_12383 = tmpaftercur_16095 + 4;
            CursorTy jump_12382 = tmpaftercur_16093 + 8;
            CursorTy jump_12381 = tmpaftercur_16091 + 8;
            CursorTy jump_12380 = tmpcur_16083 + 8;
            CursorFloat32Prod tmp_struct_165 =
                               sumQtree(end_r_10690, tmpcur_16105);
            CursorTy pvrtmp_16106 = tmp_struct_165.field0;
            FloatTy pvrtmp_16107 = tmp_struct_165.field1;
            CursorFloat32Prod tmp_struct_166 =
                               sumQtree(end_r_10690, tmpcur_16090);
            CursorTy pvrtmp_16108 = tmp_struct_166.field0;
            FloatTy pvrtmp_16109 = tmp_struct_166.field1;
            FloatTy fltPrm_7271_8231 = pvrtmp_16107 + pvrtmp_16109;
            CursorFloat32Prod tmp_struct_167 =
                               sumQtree(end_r_10690, tmpcur_16092);
            CursorTy pvrtmp_16110 = tmp_struct_167.field0;
            FloatTy pvrtmp_16111 = tmp_struct_167.field1;
            FloatTy fltPrm_7270_8233 = fltPrm_7271_8231 + pvrtmp_16111;
            CursorFloat32Prod tmp_struct_168 =
                               sumQtree(end_r_10690, tmpcur_16094);
            CursorTy pvrtmp_16112 = tmp_struct_168.field0;
            FloatTy pvrtmp_16113 = tmp_struct_168.field1;
            FloatTy tailprim_12392 = fltPrm_7270_8233 + pvrtmp_16113;

            return (CursorFloat32Prod) {pvrtmp_16112, tailprim_12392};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16114 = *(CursorTy *) tmpcur_16083;
            CursorTy tmpaftercur_16115 = tmpcur_16083 + 8;
            CursorTy jump_12807 = tmpcur_16083 + 8;
            CursorFloat32Prod tmp_struct_169 =
                               sumQtree(end_r_10690, tmpcur_16114);
            CursorTy pvrtmp_16116 = tmp_struct_169.field0;
            FloatTy pvrtmp_16117 = tmp_struct_169.field1;

            return (CursorFloat32Prod) {jump_12807, pvrtmp_16117};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16118 = *(CursorTy *) tmpcur_16083;
            CursorTy tmpaftercur_16119 = tmpcur_16083 + 8;
            CursorFloat32Prod tmp_struct_170 =
                               sumQtree(end_r_10690, tmpcur_16118);
            CursorTy pvrtmp_16120 = tmp_struct_170.field0;
            FloatTy pvrtmp_16121 = tmp_struct_170.field1;

            return (CursorFloat32Prod) {pvrtmp_16120, pvrtmp_16121};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16082");
            exit(1);
        }
    }
}
CursorProd trav_exp(CursorTy end_r_10692, CursorTy exp_1043_5392_8247)
{
    TagTyPacked tmpval_16123 = *(TagTyPacked *) exp_1043_5392_8247;
    CursorTy tmpcur_16124 = exp_1043_5392_8247 + 1;


  switch_16135:
    ;
    switch (tmpval_16123) {

      case 0:
        {
            IntTy tmpval_16125 = *(IntTy *) tmpcur_16124;
            CursorTy tmpcur_16126 = tmpcur_16124 + sizeof(IntTy);
            CursorTy jump_12393 = tmpcur_16124 + 8;

            return (CursorProd) {jump_12393};
            break;
        }

      case 1:
        {
            CursorTy jump_12395 = exp_1043_5392_8247 + 1;

            return (CursorProd) {jump_12395};
            break;
        }

      case 2:
        {
            CursorTy jump_12397 = exp_1043_5392_8247 + 1;

            return (CursorProd) {jump_12397};
            break;
        }

      case 3:
        {
            CursorProd tmp_struct_171 =  trav_exp(end_r_10692, tmpcur_16124);
            CursorTy pvrtmp_16127 = tmp_struct_171.field0;
            CursorProd tmp_struct_172 =  trav_exp(end_r_10692, pvrtmp_16127);
            CursorTy pvrtmp_16128 = tmp_struct_172.field0;

            return (CursorProd) {pvrtmp_16128};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16129 = *(CursorTy *) tmpcur_16124;
            CursorTy tmpaftercur_16130 = tmpcur_16124 + 8;
            CursorTy jump_12813 = tmpcur_16124 + 8;
            CursorProd tmp_struct_173 =  trav_exp(end_r_10692, tmpcur_16129);
            CursorTy pvrtmp_16131 = tmp_struct_173.field0;

            return (CursorProd) {jump_12813};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16132 = *(CursorTy *) tmpcur_16124;
            CursorTy tmpaftercur_16133 = tmpcur_16124 + 8;
            CursorProd tmp_struct_174 =  trav_exp(end_r_10692, tmpcur_16132);
            CursorTy pvrtmp_16134 = tmp_struct_174.field0;

            return (CursorProd) {pvrtmp_16134};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16123");
            exit(1);
        }
    }
}
FloatTy maybeLit(CursorTy end_r_10694, CursorTy exp_1050_5399_8253)
{
    TagTyPacked tmpval_16136 = *(TagTyPacked *) exp_1050_5399_8253;
    CursorTy tmpcur_16137 = exp_1050_5399_8253 + 1;


  switch_16144:
    ;
    switch (tmpval_16136) {

      case 0:
        {
            IntTy tmpval_16138 = *(IntTy *) tmpcur_16137;
            CursorTy tmpcur_16139 = tmpcur_16137 + sizeof(IntTy);
            CursorTy jump_12402 = tmpcur_16137 + 8;
            FloatTy tailprim_12403 = (FloatTy) tmpval_16138;

            return tailprim_12403;
            break;
        }

      case 3:
        {
            FloatTy tailprim_12404 = 0.0 - 3.14;

            return tailprim_12404;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16140 = *(CursorTy *) tmpcur_16137;
            CursorTy tmpaftercur_16141 = tmpcur_16137 + 8;
            CursorTy jump_12819 = tmpcur_16137 + 8;
            FloatTy call_12820 =  maybeLit(end_r_10694, tmpcur_16140);

            return call_12820;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16142 = *(CursorTy *) tmpcur_16137;
            CursorTy tmpaftercur_16143 = tmpcur_16137 + 8;
            FloatTy call_12820 =  maybeLit(end_r_10694, tmpcur_16142);

            return call_12820;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16136");
            exit(1);
        }
    }
}
IntTy maxInt(IntTy a_1063_5412_8257, IntTy b_1064_5413_8258)
{
    BoolTy fltIf_7278_8259 = a_1063_5412_8257 > b_1064_5413_8258;

    if (fltIf_7278_8259) {
        return a_1063_5412_8257;
    } else {
        return b_1064_5413_8258;
    }
}
IntTy cmpz_point3d_original(Float32Float32Float32Prod a_1340_5498_8260,
                            Float32Float32Float32Prod b_1341_5499_8261)
{
    BoolTy fltIf_7279_8268 = a_1340_5498_8260.field2 < b_1341_5499_8261.field2;

    if (fltIf_7279_8268) {
        IntTy tailprim_12407 = 0 - 1;

        return tailprim_12407;
    } else {
        BoolTy fltIf_7280_8269 = a_1340_5498_8260.field2 >
               b_1341_5499_8261.field2;

        if (fltIf_7280_8269) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpz_point3d(const void *a_1340_5498_8260, const void *b_1341_5499_8261)
{
    Float32Float32Float32Prod fst_175 =
                              *(Float32Float32Float32Prod *) a_1340_5498_8260;
    Float32Float32Float32Prod snd_176 =
                              *(Float32Float32Float32Prod *) b_1341_5499_8261;

    return cmpz_point3d_original(fst_175, snd_176);
}
IntTy cmpy_point3d_original(Float32Float32Float32Prod a_1346_5504_8270,
                            Float32Float32Float32Prod b_1347_5505_8271)
{
    BoolTy fltIf_7281_8278 = a_1346_5504_8270.field1 < b_1347_5505_8271.field1;

    if (fltIf_7281_8278) {
        IntTy tailprim_12410 = 0 - 1;

        return tailprim_12410;
    } else {
        BoolTy fltIf_7282_8279 = a_1346_5504_8270.field1 >
               b_1347_5505_8271.field1;

        if (fltIf_7282_8279) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpy_point3d(const void *a_1346_5504_8270, const void *b_1347_5505_8271)
{
    Float32Float32Float32Prod fst_177 =
                              *(Float32Float32Float32Prod *) a_1346_5504_8270;
    Float32Float32Float32Prod snd_178 =
                              *(Float32Float32Float32Prod *) b_1347_5505_8271;

    return cmpy_point3d_original(fst_177, snd_178);
}
IntTy cmpx_point3d_original(Float32Float32Float32Prod a_1352_5510_8280,
                            Float32Float32Float32Prod b_1353_5511_8281)
{
    BoolTy fltIf_7283_8288 = a_1352_5510_8280.field0 < b_1353_5511_8281.field0;

    if (fltIf_7283_8288) {
        IntTy tailprim_12413 = 0 - 1;

        return tailprim_12413;
    } else {
        BoolTy fltIf_7284_8289 = a_1352_5510_8280.field0 >
               b_1353_5511_8281.field0;

        if (fltIf_7284_8289) {
            return 1;
        } else {
            return 0;
        }
    }
}
int cmpx_point3d(const void *a_1352_5510_8280, const void *b_1353_5511_8281)
{
    Float32Float32Float32Prod fst_179 =
                              *(Float32Float32Float32Prod *) a_1352_5510_8280;
    Float32Float32Float32Prod snd_180 =
                              *(Float32Float32Float32Prod *) b_1353_5511_8281;

    return cmpx_point3d_original(fst_179, snd_180);
}
VectorTy *filter_loop_2379(VectorTy *idxs_1075_5571_8290,
                           IntTy write_at_1076_5572_8291,
                           IntTy start_1077_5573_8292, IntTy end_1078_5574_8293,
                           VectorTy *from_1079_5575_8294,
                           VectorTy *to_1080_5576_8295)
{
    BoolTy fltIf_7285_8296 = start_1077_5573_8292 == end_1078_5574_8293;

    if (fltIf_7285_8296) {
        return to_1080_5576_8295;
    } else {
        IntTy *tmp_182;

        tmp_182 = (IntTy *) vector_nth(idxs_1075_5571_8290,
                                       start_1077_5573_8292);

        IntTy idx_1082_5577_8299 = *tmp_182;
        IntTy fltPrm_7287_8300 = 0 - 1;
        BoolTy fltIf_7286_8301 = idx_1082_5577_8299 == fltPrm_7287_8300;

        if (fltIf_7286_8301) {
            IntTy fltAppE_7288_8302 = start_1077_5573_8292 + 1;
            VectorTy *tailapp_12414 =
                      filter_loop_2379(idxs_1075_5571_8290, write_at_1076_5572_8291, fltAppE_7288_8302, end_1078_5574_8293, from_1079_5575_8294, to_1080_5576_8295);

            return tailapp_12414;
        } else {
            Float32Float32Float32Prod *tmp_181;

            tmp_181 =
                (Float32Float32Float32Prod *) vector_nth(from_1079_5575_8294,
                                                         idx_1082_5577_8299);

            Float32Float32Float32Prod elt_1083_5578_8305 = *tmp_181;
            VectorTy *to1_1084_5579_8306 =
                     vector_inplace_update(to_1080_5576_8295,
                                           write_at_1076_5572_8291,
                                           &elt_1083_5578_8305);
            IntTy fltAppE_7289_8307 = write_at_1076_5572_8291 + 1;
            IntTy fltAppE_7290_8308 = start_1077_5573_8292 + 1;
            VectorTy *tailapp_12415 =
                      filter_loop_2379(idxs_1075_5571_8290, fltAppE_7289_8307, fltAppE_7290_8308, end_1078_5574_8293, from_1079_5575_8294, to1_1084_5579_8306);

            return tailapp_12415;
        }
    }
}
IntTy foldl_loop_2380_3709(IntTy idx_1164_5926_8369, IntTy end_1165_5927_8370,
                           IntTy acc_1167_5928_8371,
                           VectorTy *vec_1168_5929_8372)
{
    BoolTy fltIf_7298_8373 = idx_1164_5926_8369 == end_1165_5927_8370;

    if (fltIf_7298_8373) {
        return acc_1167_5928_8371;
    } else {
        IntTy *tmp_183;

        tmp_183 = (IntTy *) vector_nth(vec_1168_5929_8372, idx_1164_5926_8369);

        IntTy x_1032_5917_6929_8375 = *tmp_183;
        IntTy fltPrm_7300_8376 = 0 - 1;
        BoolTy fltIf_7299_8377 = x_1032_5917_6929_8375 == fltPrm_7300_8376;
        IntTy acc1_1171_5930_8378;

        if (fltIf_7299_8377) {
            acc1_1171_5930_8378 = acc_1167_5928_8371;
        } else {
            IntTy flt_16145 = acc_1167_5928_8371 + 1;

            acc1_1171_5930_8378 = flt_16145;
        }

        IntTy fltAppE_7301_8379 = idx_1164_5926_8369 + 1;
        IntTy tailapp_12416 =
               foldl_loop_2380_3709(fltAppE_7301_8379, end_1165_5927_8370, acc1_1171_5930_8378, vec_1168_5929_8372);

        return tailapp_12416;
    }
}
VectorTy *generate_loop_2377_3710(CursorTy end_r_10696,
                                  VectorTy *vec_1196_5931_8380,
                                  IntTy idx_1197_5932_8381,
                                  IntTy end_1198_5933_8382,
                                  CursorTy bht_274_5934_8383,
                                  VectorTy *mpts_275_5935_8384,
                                  VectorTy *ps_276_5936_8385)
{
    BoolTy fltIf_7302_8386 = idx_1197_5932_8381 == end_1198_5933_8382;

    if (fltIf_7302_8386) {
        return vec_1196_5931_8380;
    } else {
        Float32Float32Float32Float32Float32Prod *tmp_186;

        tmp_186 =
            (Float32Float32Float32Float32Float32Prod *) vector_nth(ps_276_5936_8385,
                                                                   idx_1197_5932_8381);

        Float32Float32Float32Float32Float32Prod p_278_5659_6934_8391 = *tmp_186;
        Float32Float32Float32Prod *tmp_185;

        tmp_185 = (Float32Float32Float32Prod *) vector_nth(mpts_275_5935_8384,
                                                           idx_1197_5932_8381);

        Float32Float32Float32Prod mpt_279_5660_6935_8392 = *tmp_185;
        Float32Float32Prod tmp_struct_184 =
                            calcAccel_seq(end_r_10696, (Float32Float32Float32Prod) {mpt_279_5660_6935_8392.field0, mpt_279_5660_6935_8392.field1, mpt_279_5660_6935_8392.field2}, bht_274_5934_8383);
        FloatTy pvrtmp_16149 = tmp_struct_184.field0;
        FloatTy pvrtmp_16150 = tmp_struct_184.field1;
        FloatTy fltPrm_7259_8175_9115 = pvrtmp_16149 * 2.0;
        FloatTy fltPrd_7258_8176_9116 = p_278_5659_6934_8391.field3 +
                fltPrm_7259_8175_9115;
        FloatTy fltPrm_7261_8177_9117 = pvrtmp_16150 * 2.0;
        FloatTy fltPrd_7260_8178_9118 = p_278_5659_6934_8391.field4 +
                fltPrm_7261_8177_9117;
        VectorTy *vec1_1201_5937_8395 =
                 vector_inplace_update(vec_1196_5931_8380, idx_1197_5932_8381,
                                       &(Float32Float32Float32Float32Float32Prod) {p_278_5659_6934_8391.field0,
                                                                                   p_278_5659_6934_8391.field1,
                                                                                   p_278_5659_6934_8391.field2,
                                                                                   fltPrd_7258_8176_9116,
                                                                                   fltPrd_7260_8178_9118});
        IntTy fltAppE_7304_8396 = idx_1197_5932_8381 + 1;
        VectorTy *tailapp_12417 =
                  generate_loop_2377_3710(end_r_10696, vec1_1201_5937_8395, fltAppE_7304_8396, end_1198_5933_8382, bht_274_5934_8383, mpts_275_5935_8384, ps_276_5936_8385);

        return tailapp_12417;
    }
}
VectorTy *generate_loop_2376_3711(VectorTy *vec_1196_5938_8397,
                                  IntTy idx_1197_5939_8398,
                                  IntTy end_1198_5940_8399,
                                  VectorTy *vec_1193_5941_8400)
{
    BoolTy fltIf_7305_8401 = idx_1197_5939_8398 == end_1198_5940_8399;

    if (fltIf_7305_8401) {
        return vec_1196_5938_8397;
    } else {
        Float32Float32Float32Prod *tmp_187;

        tmp_187 = (Float32Float32Float32Prod *) vector_nth(vec_1193_5941_8400,
                                                           idx_1197_5939_8398);

        Float32Float32Float32Prod fltPrm_7306_8404 = *tmp_187;
        VectorTy *vec1_1201_5942_8405 =
                 vector_inplace_update(vec_1196_5938_8397, idx_1197_5939_8398,
                                       &fltPrm_7306_8404);
        IntTy fltAppE_7307_8406 = idx_1197_5939_8398 + 1;
        VectorTy *tailapp_12418 =
                  generate_loop_2376_3711(vec1_1201_5942_8405, fltAppE_7307_8406, end_1198_5940_8399, vec_1193_5941_8400);

        return tailapp_12418;
    }
}
VectorTy *generate_loop_2374_3714(VectorTy *vec_1196_5960_8407,
                                  IntTy idx_1197_5961_8408,
                                  IntTy end_1198_5962_8409)
{
    BoolTy fltIf_7308_8410 = idx_1197_5961_8408 == end_1198_5962_8409;

    if (fltIf_7308_8410) {
        return vec_1196_5960_8407;
    } else {
        VectorTy *vec1_1201_5963_8413 =
                 vector_inplace_update(vec_1196_5960_8407, idx_1197_5961_8408,
                                       &idx_1197_5961_8408);
        IntTy fltAppE_7310_8414 = idx_1197_5961_8408 + 1;
        VectorTy *tailapp_12419 =
                  generate_loop_2374_3714(vec1_1201_5963_8413, fltAppE_7310_8414, end_1198_5962_8409);

        return tailapp_12419;
    }
}
VectorTy *generate_loop_2374_3717(VectorTy *vec_1196_5974_8415,
                                  IntTy idx_1197_5975_8416,
                                  IntTy end_1198_5976_8417,
                                  VectorTy *vec_1028_5977_8418,
                                  Float32Float32Float32Float32Prod box_792_5978_8419)
{
    BoolTy fltIf_7311_8420 = idx_1197_5975_8416 == end_1198_5976_8417;

    if (fltIf_7311_8420) {
        return vec_1196_5974_8415;
    } else {
        Float32Float32Float32Prod *tmp_188;

        tmp_188 = (Float32Float32Float32Prod *) vector_nth(vec_1028_5977_8418,
                                                           idx_1197_5975_8416);

        Float32Float32Float32Prod fltAppE_7314_8424 = *tmp_188;
        BoolTy fltPrm_7291_8349_9138 = fltAppE_7314_8424.field0 >=
               box_792_5978_8419.field0;
        BoolTy fltPrm_7293_8350_9139 = fltAppE_7314_8424.field0 <=
               box_792_5978_8419.field2;
        BoolTy fltPrm_7295_8351_9140 = fltAppE_7314_8424.field1 >=
               box_792_5978_8419.field1;
        BoolTy fltPrm_7296_8352_9141 = fltAppE_7314_8424.field1 <=
               box_792_5978_8419.field3;
        BoolTy fltPrm_7294_8353_9142 = fltPrm_7295_8351_9140 &&
               fltPrm_7296_8352_9141;
        BoolTy fltPrm_7292_8354_9143 = fltPrm_7293_8350_9139 &&
               fltPrm_7294_8353_9142;
        BoolTy fltIf_7313_8425 = fltPrm_7291_8349_9138 && fltPrm_7292_8354_9143;
        IntTy fltPrm_7312_8426;

        if (fltIf_7313_8425) {
            fltPrm_7312_8426 = idx_1197_5975_8416;
        } else {
            IntTy flt_16158 = 0 - 1;

            fltPrm_7312_8426 = flt_16158;
        }

        VectorTy *vec1_1201_5979_8427 =
                 vector_inplace_update(vec_1196_5974_8415, idx_1197_5975_8416,
                                       &fltPrm_7312_8426);
        IntTy fltAppE_7315_8428 = idx_1197_5975_8416 + 1;
        VectorTy *tailapp_12420 =
                  generate_loop_2374_3717(vec1_1201_5979_8427, fltAppE_7315_8428, end_1198_5976_8417, vec_1028_5977_8418, (Float32Float32Float32Float32Prod) {box_792_5978_8419.field0, box_792_5978_8419.field1, box_792_5978_8419.field2, box_792_5978_8419.field3});

        return tailapp_12420;
    }
}
VectorTy *generate_loop_2376_3720(CursorTy end_r_10698,
                                  VectorTy *vec_1196_5989_8435,
                                  IntTy idx_1197_5990_8436,
                                  IntTy end_1198_5991_8437,
                                  VectorTy *vec_270_5992_8438,
                                  CursorTy tr_207_5993_8439)
{
    BoolTy fltIf_7316_8440 = idx_1197_5990_8436 == end_1198_5991_8437;

    if (fltIf_7316_8440) {
        return vec_1196_5989_8435;
    } else {
        Float32Float32Float32Prod *tmp_190;

        tmp_190 = (Float32Float32Float32Prod *) vector_nth(vec_270_5992_8438,
                                                           idx_1197_5990_8436);

        Float32Float32Float32Prod fltAppE_7318_8444 = *tmp_190;
        Float32Float32Float32Prod tmp_struct_189 =
                                   nearest(end_r_10698, tr_207_5993_8439, (Float32Float32Float32Prod) {fltAppE_7318_8444.field0, fltAppE_7318_8444.field1, fltAppE_7318_8444.field2});
        FloatTy pvrtmp_16166 = tmp_struct_189.field0;
        FloatTy pvrtmp_16167 = tmp_struct_189.field1;
        FloatTy pvrtmp_16168 = tmp_struct_189.field2;
        VectorTy *vec1_1201_5994_8446 =
                 vector_inplace_update(vec_1196_5989_8435, idx_1197_5990_8436,
                                       &(Float32Float32Float32Prod) {pvrtmp_16166,
                                                                     pvrtmp_16167,
                                                                     pvrtmp_16168});
        IntTy fltAppE_7319_8447 = idx_1197_5990_8436 + 1;
        VectorTy *tailapp_12421 =
                  generate_loop_2376_3720(end_r_10698, vec1_1201_5994_8446, fltAppE_7319_8447, end_1198_5991_8437, vec_270_5992_8438, tr_207_5993_8439);

        return tailapp_12421;
    }
}
VectorTy *generate_loop_2374_3723(CursorTy end_r_10700,
                                  VectorTy *vec_1196_6006_8455,
                                  IntTy idx_1197_6007_8456,
                                  IntTy end_1198_6008_8457,
                                  VectorTy *vec_270_6009_8458,
                                  FloatTy radius_183_6010_8459,
                                  CursorTy tr_184_6011_8460)
{
    BoolTy fltIf_7320_8461 = idx_1197_6007_8456 == end_1198_6008_8457;

    if (fltIf_7320_8461) {
        return vec_1196_6006_8455;
    } else {
        Float32Float32Float32Prod *tmp_191;

        tmp_191 = (Float32Float32Float32Prod *) vector_nth(vec_270_6009_8458,
                                                           idx_1197_6007_8456);

        Float32Float32Float32Prod fltAppE_7322_8466 = *tmp_191;
        IntTy fltPrm_7321_8467 =
               countCorr_seq(end_r_10700, (Float32Float32Float32Prod) {fltAppE_7322_8466.field0, fltAppE_7322_8466.field1, fltAppE_7322_8466.field2}, radius_183_6010_8459, tr_184_6011_8460);
        VectorTy *vec1_1201_6012_8468 =
                 vector_inplace_update(vec_1196_6006_8455, idx_1197_6007_8456,
                                       &fltPrm_7321_8467);
        IntTy fltAppE_7323_8469 = idx_1197_6007_8456 + 1;
        VectorTy *tailapp_12422 =
                  generate_loop_2374_3723(end_r_10700, vec1_1201_6012_8468, fltAppE_7323_8469, end_1198_6008_8457, vec_270_6009_8458, radius_183_6010_8459, tr_184_6011_8460);

        return tailapp_12422;
    }
}
VectorTy *generate_loop_2377_3726(VectorTy *vec_1196_6021_8475,
                                  IntTy idx_1197_6022_8476,
                                  IntTy end_1198_6023_8477,
                                  VectorTy *vec_270_6024_8478)
{
    BoolTy fltIf_7324_8479 = idx_1197_6022_8476 == end_1198_6023_8477;

    if (fltIf_7324_8479) {
        return vec_1196_6021_8475;
    } else {
        Float32Float32Prod *tmp_192;

        tmp_192 = (Float32Float32Prod *) vector_nth(vec_270_6024_8478,
                                                    idx_1197_6022_8476);

        Float32Float32Prod fltAppE_7326_8482 = *tmp_192;
        VectorTy *vec1_1201_6025_8484 =
                 vector_inplace_update(vec_1196_6021_8475, idx_1197_6022_8476,
                                       &(Float32Float32Float32Float32Float32Prod) {fltAppE_7326_8482.field0,
                                                                                   fltAppE_7326_8482.field1,
                                                                                   1.0,
                                                                                   0.0,
                                                                                   0.0});
        IntTy fltAppE_7327_8485 = idx_1197_6022_8476 + 1;
        VectorTy *tailapp_12423 =
                  generate_loop_2377_3726(vec1_1201_6025_8484, fltAppE_7327_8485, end_1198_6023_8477, vec_270_6024_8478);

        return tailapp_12423;
    }
}
VectorTy *generate_loop_2377_3729(VectorTy *vec_1196_6034_8491,
                                  IntTy idx_1197_6035_8492,
                                  IntTy end_1198_6036_8493,
                                  VectorTy *vec_270_6037_8494)
{
    BoolTy fltIf_7328_8495 = idx_1197_6035_8492 == end_1198_6036_8493;

    if (fltIf_7328_8495) {
        return vec_1196_6034_8491;
    } else {
        Float32Float32Prod *tmp_193;

        tmp_193 = (Float32Float32Prod *) vector_nth(vec_270_6037_8494,
                                                    idx_1197_6035_8492);

        Float32Float32Prod fltAppE_7330_8498 = *tmp_193;
        VectorTy *vec1_1201_6038_8500 =
                 vector_inplace_update(vec_1196_6034_8491, idx_1197_6035_8492,
                                       &(Float32Float32Float32Float32Float32Prod) {fltAppE_7330_8498.field0,
                                                                                   fltAppE_7330_8498.field1,
                                                                                   1.0,
                                                                                   0.0,
                                                                                   0.0});
        IntTy fltAppE_7331_8501 = idx_1197_6035_8492 + 1;
        VectorTy *tailapp_12424 =
                  generate_loop_2377_3729(vec1_1201_6038_8500, fltAppE_7331_8501, end_1198_6036_8493, vec_270_6037_8494);

        return tailapp_12424;
    }
}
VectorTy *generate_loop_2376_3732(VectorTy *vec_1196_6047_8507,
                                  IntTy idx_1197_6048_8508,
                                  IntTy end_1198_6049_8509,
                                  VectorTy *vec_270_6050_8510)
{
    BoolTy fltIf_7332_8511 = idx_1197_6048_8508 == end_1198_6049_8509;

    if (fltIf_7332_8511) {
        return vec_1196_6047_8507;
    } else {
        Float32Float32Prod *tmp_194;

        tmp_194 = (Float32Float32Prod *) vector_nth(vec_270_6050_8510,
                                                    idx_1197_6048_8508);

        Float32Float32Prod fltAppE_7334_8514 = *tmp_194;
        VectorTy *vec1_1201_6051_8516 =
                 vector_inplace_update(vec_1196_6047_8507, idx_1197_6048_8508,
                                       &(Float32Float32Float32Prod) {fltAppE_7334_8514.field0,
                                                                     fltAppE_7334_8514.field1,
                                                                     1.0});
        IntTy fltAppE_7335_8517 = idx_1197_6048_8508 + 1;
        VectorTy *tailapp_12425 =
                  generate_loop_2376_3732(vec1_1201_6051_8516, fltAppE_7335_8517, end_1198_6049_8509, vec_270_6050_8510);

        return tailapp_12425;
    }
}
VectorTy *generate_loop_2376_3735(VectorTy *vec_1196_6060_8523,
                                  IntTy idx_1197_6061_8524,
                                  IntTy end_1198_6062_8525,
                                  VectorTy *vec_270_6063_8526)
{
    BoolTy fltIf_7336_8527 = idx_1197_6061_8524 == end_1198_6062_8525;

    if (fltIf_7336_8527) {
        return vec_1196_6060_8523;
    } else {
        Float32Float32Prod *tmp_195;

        tmp_195 = (Float32Float32Prod *) vector_nth(vec_270_6063_8526,
                                                    idx_1197_6061_8524);

        Float32Float32Prod fltAppE_7338_8530 = *tmp_195;
        VectorTy *vec1_1201_6064_8532 =
                 vector_inplace_update(vec_1196_6060_8523, idx_1197_6061_8524,
                                       &(Float32Float32Float32Prod) {fltAppE_7338_8530.field0,
                                                                     fltAppE_7338_8530.field1,
                                                                     1.0});
        IntTy fltAppE_7339_8533 = idx_1197_6061_8524 + 1;
        VectorTy *tailapp_12426 =
                  generate_loop_2376_3735(vec1_1201_6064_8532, fltAppE_7339_8533, end_1198_6062_8525, vec_270_6063_8526);

        return tailapp_12426;
    }
}
Float32Float32Float32Prod foldl_loop_2371_3737(IntTy idx_1164_6073_8534,
                                               IntTy end_1165_6074_8535,
                                               Float32Float32Float32Prod acc_1167_6075_8536,
                                               VectorTy *vec_1168_6076_8537)
{
    BoolTy fltIf_7340_8538 = idx_1164_6073_8534 == end_1165_6074_8535;

    if (fltIf_7340_8538) {
        return acc_1167_6075_8536;
    } else {
        Float32Float32Float32Prod *tmp_197;

        tmp_197 = (Float32Float32Float32Prod *) vector_nth(vec_1168_6076_8537,
                                                           idx_1164_6073_8534);

        Float32Float32Float32Prod mpt_809_5705_7025_8540 = *tmp_197;
        FloatTy fltPrm_7342_8549 = mpt_809_5705_7025_8540.field0 *
                mpt_809_5705_7025_8540.field2;
        FloatTy fltPrd_7341_8550 = acc_1167_6075_8536.field0 + fltPrm_7342_8549;
        FloatTy fltPrm_7344_8551 = mpt_809_5705_7025_8540.field1 *
                mpt_809_5705_7025_8540.field2;
        FloatTy fltPrd_7343_8552 = acc_1167_6075_8536.field1 + fltPrm_7344_8551;
        FloatTy fltPrd_7345_8553 = acc_1167_6075_8536.field2 +
                mpt_809_5705_7025_8540.field2;
        IntTy fltAppE_7346_8555 = idx_1164_6073_8534 + 1;
        Float32Float32Float32Prod tmp_struct_196 =
                                   foldl_loop_2371_3737(fltAppE_7346_8555, end_1165_6074_8535, (Float32Float32Float32Prod) {fltPrd_7341_8550, fltPrd_7343_8552, fltPrd_7345_8553}, vec_1168_6076_8537);
        FloatTy pvrtmp_16194 = tmp_struct_196.field0;
        FloatTy pvrtmp_16195 = tmp_struct_196.field1;
        FloatTy pvrtmp_16196 = tmp_struct_196.field2;

        return (Float32Float32Float32Prod) {pvrtmp_16194, pvrtmp_16195,
                                            pvrtmp_16196};
    }
}
FloatTy foldl_loop_2370_3738(IntTy idx_1164_6080_8556, IntTy end_1165_6081_8557,
                             FloatTy acc_1167_6082_8558,
                             VectorTy *vec_1168_6083_8559)
{
    BoolTy fltIf_7347_8560 = idx_1164_6080_8556 == end_1165_6081_8557;

    if (fltIf_7347_8560) {
        return acc_1167_6082_8558;
    } else {
        Float32Float32Float32Prod *tmp_198;

        tmp_198 = (Float32Float32Float32Prod *) vector_nth(vec_1168_6083_8559,
                                                           idx_1164_6080_8556);

        Float32Float32Float32Prod pt_318_5670_7035_8562 = *tmp_198;
        FloatTy fltPrm_7349_8567 = acc_1167_6082_8558 +
                pt_318_5670_7035_8562.field0;
        FloatTy fltPrm_7348_8568 = fltPrm_7349_8567 +
                pt_318_5670_7035_8562.field1;
        FloatTy acc1_1171_6084_8569 = fltPrm_7348_8568 +
                pt_318_5670_7035_8562.field2;
        IntTy fltAppE_7350_8570 = idx_1164_6080_8556 + 1;
        FloatTy tailapp_12428 =
                 foldl_loop_2370_3738(fltAppE_7350_8570, end_1165_6081_8557, acc1_1171_6084_8569, vec_1168_6083_8559);

        return tailapp_12428;
    }
}
FloatTy foldl_loop_2370_3739(IntTy idx_1164_6087_8571, IntTy end_1165_6088_8572,
                             FloatTy acc_1167_6089_8573,
                             VectorTy *vec_1168_6090_8574)
{
    BoolTy fltIf_7351_8575 = idx_1164_6087_8571 == end_1165_6088_8572;

    if (fltIf_7351_8575) {
        return acc_1167_6089_8573;
    } else {
        Float32Float32Float32Prod *tmp_199;

        tmp_199 = (Float32Float32Float32Prod *) vector_nth(vec_1168_6090_8574,
                                                           idx_1164_6087_8571);

        Float32Float32Float32Prod pt_952_5721_7041_8577 = *tmp_199;
        FloatTy fltPrm_7353_8582 = acc_1167_6089_8573 +
                pt_952_5721_7041_8577.field0;
        FloatTy fltPrm_7352_8583 = fltPrm_7353_8582 +
                pt_952_5721_7041_8577.field1;
        FloatTy acc1_1171_6091_8584 = fltPrm_7352_8583 +
                pt_952_5721_7041_8577.field2;
        IntTy fltAppE_7354_8585 = idx_1164_6087_8571 + 1;
        FloatTy tailapp_12429 =
                 foldl_loop_2370_3739(fltAppE_7354_8585, end_1165_6088_8572, acc1_1171_6091_8584, vec_1168_6090_8574);

        return tailapp_12429;
    }
}
IntTy foldl_loop_2369_3740(IntTy idx_1164_6092_8586, IntTy end_1165_6093_8587,
                           IntTy acc_1167_6094_8588,
                           VectorTy *vec_1168_6095_8589,
                           Float32Float32Float32Prod query_167_6096_8590,
                           FloatTy radius_sq_170_6097_8591)
{
    BoolTy fltIf_7355_8592 = idx_1164_6092_8586 == end_1165_6093_8587;

    if (fltIf_7355_8592) {
        return acc_1167_6094_8588;
    } else {
        Float32Float32Float32Prod *tmp_200;

        tmp_200 = (Float32Float32Float32Prod *) vector_nth(vec_1168_6095_8589,
                                                           idx_1164_6092_8586);

        Float32Float32Float32Prod pt_171_5624_7047_8594 = *tmp_200;
        FloatTy fltPrm_7357_8597 =
                 dist_point3d((Float32Float32Float32Prod) {query_167_6096_8590.field0, query_167_6096_8590.field1, query_167_6096_8590.field2}, (Float32Float32Float32Prod) {pt_171_5624_7047_8594.field0, pt_171_5624_7047_8594.field1, pt_171_5624_7047_8594.field2});
        BoolTy fltIf_7356_8598 = fltPrm_7357_8597 < radius_sq_170_6097_8591;
        IntTy acc1_1171_6098_8599;

        if (fltIf_7356_8598) {
            IntTy flt_16203 = acc_1167_6094_8588 + 1;

            acc1_1171_6098_8599 = flt_16203;
        } else {
            acc1_1171_6098_8599 = acc_1167_6094_8588;
        }

        IntTy fltAppE_7358_8600 = idx_1164_6092_8586 + 1;
        IntTy tailapp_12430 =
               foldl_loop_2369_3740(fltAppE_7358_8600, end_1165_6093_8587, acc1_1171_6098_8599, vec_1168_6095_8589, (Float32Float32Float32Prod) {query_167_6096_8590.field0, query_167_6096_8590.field1, query_167_6096_8590.field2}, radius_sq_170_6097_8591);

        return tailapp_12430;
    }
}
FloatTy foldl_loop_2368_3741(IntTy idx_1164_6101_8601, IntTy end_1165_6102_8602,
                             FloatTy acc_1167_6103_8603,
                             VectorTy *vec_1168_6104_8604)
{
    BoolTy fltIf_7359_8605 = idx_1164_6101_8601 == end_1165_6102_8602;

    if (fltIf_7359_8605) {
        return acc_1167_6103_8603;
    } else {
        Float32Float32Prod *tmp_201;

        tmp_201 = (Float32Float32Prod *) vector_nth(vec_1168_6104_8604,
                                                    idx_1164_6101_8601);

        Float32Float32Prod pt_102_5600_7051_8607 = *tmp_201;
        FloatTy acc1_1171_6105_8609 =
                 minFloat(pt_102_5600_7051_8607.field0, acc_1167_6103_8603);
        IntTy fltAppE_7361_8610 = idx_1164_6101_8601 + 1;
        FloatTy tailapp_12431 =
                 foldl_loop_2368_3741(fltAppE_7361_8610, end_1165_6102_8602, acc1_1171_6105_8609, vec_1168_6104_8604);

        return tailapp_12431;
    }
}
FloatTy foldl_loop_2368_3742(IntTy idx_1164_6108_8611, IntTy end_1165_6109_8612,
                             FloatTy acc_1167_6110_8613,
                             VectorTy *vec_1168_6111_8614)
{
    BoolTy fltIf_7362_8615 = idx_1164_6108_8611 == end_1165_6109_8612;

    if (fltIf_7362_8615) {
        return acc_1167_6110_8613;
    } else {
        Float32Float32Prod *tmp_202;

        tmp_202 = (Float32Float32Prod *) vector_nth(vec_1168_6111_8614,
                                                    idx_1164_6108_8611);

        Float32Float32Prod pt_105_5602_7053_8617 = *tmp_202;
        FloatTy acc1_1171_6112_8619 =
                 minFloat(pt_105_5602_7053_8617.field1, acc_1167_6110_8613);
        IntTy fltAppE_7364_8620 = idx_1164_6108_8611 + 1;
        FloatTy tailapp_12432 =
                 foldl_loop_2368_3742(fltAppE_7364_8620, end_1165_6109_8612, acc1_1171_6112_8619, vec_1168_6111_8614);

        return tailapp_12432;
    }
}
FloatTy foldl_loop_2368_3743(IntTy idx_1164_6115_8621, IntTy end_1165_6116_8622,
                             FloatTy acc_1167_6117_8623,
                             VectorTy *vec_1168_6118_8624)
{
    BoolTy fltIf_7365_8625 = idx_1164_6115_8621 == end_1165_6116_8622;

    if (fltIf_7365_8625) {
        return acc_1167_6117_8623;
    } else {
        Float32Float32Prod *tmp_203;

        tmp_203 = (Float32Float32Prod *) vector_nth(vec_1168_6118_8624,
                                                    idx_1164_6115_8621);

        Float32Float32Prod pt_108_5604_7055_8627 = *tmp_203;
        FloatTy acc1_1171_6119_8629 =
                 maxFloat(pt_108_5604_7055_8627.field0, acc_1167_6117_8623);
        IntTy fltAppE_7367_8630 = idx_1164_6115_8621 + 1;
        FloatTy tailapp_12433 =
                 foldl_loop_2368_3743(fltAppE_7367_8630, end_1165_6116_8622, acc1_1171_6119_8629, vec_1168_6118_8624);

        return tailapp_12433;
    }
}
FloatTy foldl_loop_2368_3744(IntTy idx_1164_6122_8631, IntTy end_1165_6123_8632,
                             FloatTy acc_1167_6124_8633,
                             VectorTy *vec_1168_6125_8634)
{
    BoolTy fltIf_7368_8635 = idx_1164_6122_8631 == end_1165_6123_8632;

    if (fltIf_7368_8635) {
        return acc_1167_6124_8633;
    } else {
        Float32Float32Prod *tmp_204;

        tmp_204 = (Float32Float32Prod *) vector_nth(vec_1168_6125_8634,
                                                    idx_1164_6122_8631);

        Float32Float32Prod pt_111_5606_7057_8637 = *tmp_204;
        FloatTy acc1_1171_6126_8639 =
                 maxFloat(pt_111_5606_7057_8637.field1, acc_1167_6124_8633);
        IntTy fltAppE_7370_8640 = idx_1164_6122_8631 + 1;
        FloatTy tailapp_12434 =
                 foldl_loop_2368_3744(fltAppE_7370_8640, end_1165_6123_8632, acc1_1171_6126_8639, vec_1168_6125_8634);

        return tailapp_12434;
    }
}
FloatTy foldl_loop_2368_3745(IntTy idx_1164_6129_8641, IntTy end_1165_6130_8642,
                             FloatTy acc_1167_6131_8643,
                             VectorTy *vec_1168_6132_8644)
{
    BoolTy fltIf_7371_8645 = idx_1164_6129_8641 == end_1165_6130_8642;

    if (fltIf_7371_8645) {
        return acc_1167_6131_8643;
    } else {
        Float32Float32Prod *tmp_205;

        tmp_205 = (Float32Float32Prod *) vector_nth(vec_1168_6132_8644,
                                                    idx_1164_6129_8641);

        Float32Float32Prod pt_129_5616_7059_8647 = *tmp_205;
        FloatTy acc1_1171_6133_8649 =
                 minFloat(pt_129_5616_7059_8647.field0, acc_1167_6131_8643);
        IntTy fltAppE_7373_8650 = idx_1164_6129_8641 + 1;
        FloatTy tailapp_12435 =
                 foldl_loop_2368_3745(fltAppE_7373_8650, end_1165_6130_8642, acc1_1171_6133_8649, vec_1168_6132_8644);

        return tailapp_12435;
    }
}
FloatTy foldl_loop_2368_3746(IntTy idx_1164_6136_8651, IntTy end_1165_6137_8652,
                             FloatTy acc_1167_6138_8653,
                             VectorTy *vec_1168_6139_8654)
{
    BoolTy fltIf_7374_8655 = idx_1164_6136_8651 == end_1165_6137_8652;

    if (fltIf_7374_8655) {
        return acc_1167_6138_8653;
    } else {
        Float32Float32Prod *tmp_206;

        tmp_206 = (Float32Float32Prod *) vector_nth(vec_1168_6139_8654,
                                                    idx_1164_6136_8651);

        Float32Float32Prod pt_132_5618_7061_8657 = *tmp_206;
        FloatTy acc1_1171_6140_8659 =
                 minFloat(pt_132_5618_7061_8657.field1, acc_1167_6138_8653);
        IntTy fltAppE_7376_8660 = idx_1164_6136_8651 + 1;
        FloatTy tailapp_12436 =
                 foldl_loop_2368_3746(fltAppE_7376_8660, end_1165_6137_8652, acc1_1171_6140_8659, vec_1168_6139_8654);

        return tailapp_12436;
    }
}
FloatTy foldl_loop_2368_3747(IntTy idx_1164_6143_8661, IntTy end_1165_6144_8662,
                             FloatTy acc_1167_6145_8663,
                             VectorTy *vec_1168_6146_8664)
{
    BoolTy fltIf_7377_8665 = idx_1164_6143_8661 == end_1165_6144_8662;

    if (fltIf_7377_8665) {
        return acc_1167_6145_8663;
    } else {
        Float32Float32Prod *tmp_207;

        tmp_207 = (Float32Float32Prod *) vector_nth(vec_1168_6146_8664,
                                                    idx_1164_6143_8661);

        Float32Float32Prod pt_135_5620_7063_8667 = *tmp_207;
        FloatTy acc1_1171_6147_8669 =
                 maxFloat(pt_135_5620_7063_8667.field0, acc_1167_6145_8663);
        IntTy fltAppE_7379_8670 = idx_1164_6143_8661 + 1;
        FloatTy tailapp_12437 =
                 foldl_loop_2368_3747(fltAppE_7379_8670, end_1165_6144_8662, acc1_1171_6147_8669, vec_1168_6146_8664);

        return tailapp_12437;
    }
}
FloatTy foldl_loop_2368_3748(IntTy idx_1164_6150_8671, IntTy end_1165_6151_8672,
                             FloatTy acc_1167_6152_8673,
                             VectorTy *vec_1168_6153_8674)
{
    BoolTy fltIf_7380_8675 = idx_1164_6150_8671 == end_1165_6151_8672;

    if (fltIf_7380_8675) {
        return acc_1167_6152_8673;
    } else {
        Float32Float32Prod *tmp_208;

        tmp_208 = (Float32Float32Prod *) vector_nth(vec_1168_6153_8674,
                                                    idx_1164_6150_8671);

        Float32Float32Prod pt_138_5622_7065_8677 = *tmp_208;
        FloatTy acc1_1171_6154_8679 =
                 maxFloat(pt_138_5622_7065_8677.field1, acc_1167_6152_8673);
        IntTy fltAppE_7382_8680 = idx_1164_6150_8671 + 1;
        FloatTy tailapp_12438 =
                 foldl_loop_2368_3748(fltAppE_7382_8680, end_1165_6151_8672, acc1_1171_6154_8679, vec_1168_6153_8674);

        return tailapp_12438;
    }
}
BoolInt64Prod foldl_loop_2367_3749(IntTy idx_1164_6155_8681,
                                   IntTy end_1165_6156_8682,
                                   BoolInt64Prod acc_1167_6157_8683,
                                   VectorTy *vec_1168_6158_8684,
                                   VectorTy *pts_191_6159_8685,
                                   VectorTy *actual_192_6160_8686)
{
    BoolTy fltIf_7383_8687 = idx_1164_6155_8681 == end_1165_6156_8682;

    if (fltIf_7383_8687) {
        return acc_1167_6157_8683;
    } else {
        IntTy *tmp_212;

        tmp_212 = (IntTy *) vector_nth(vec_1168_6158_8684, idx_1164_6155_8681);

        IntTy i_196_5639_7067_8689 = *tmp_212;
        Float32Float32Float32Prod *tmp_211;

        tmp_211 = (Float32Float32Float32Prod *) vector_nth(pts_191_6159_8685,
                                                           i_196_5639_7067_8689);

        Float32Float32Float32Prod pt_198_5642_7070_8692 = *tmp_211;
        Float32Float32Float32Prod *tmp_210;

        tmp_210 = (Float32Float32Float32Prod *) vector_nth(actual_192_6160_8686,
                                                           i_196_5639_7067_8689);

        Float32Float32Float32Prod nn_199_5643_7071_8693 = *tmp_210;
        BoolTy fltIf_7384_8697 =
                eq_point3d((Float32Float32Float32Prod) {pt_198_5642_7070_8692.field0, pt_198_5642_7070_8692.field1, pt_198_5642_7070_8692.field2}, (Float32Float32Float32Prod) {nn_199_5643_7071_8693.field0, nn_199_5643_7071_8693.field1, nn_199_5643_7071_8693.field2});
        BoolTy pvrtmp_16213;
        IntTy pvrtmp_16214;

        if (fltIf_7384_8697) {
            BoolTy fltPrd_7385_8699 = acc_1167_6157_8683.field0 && true;

            pvrtmp_16213 = fltPrd_7385_8699;
            pvrtmp_16214 = acc_1167_6157_8683.field1;
        } else {
            IntTy fltPrd_7388_8701 = acc_1167_6157_8683.field1 + 1;

            pvrtmp_16213 = false;
            pvrtmp_16214 = fltPrd_7388_8701;
        }

        IntTy fltAppE_7389_8703 = idx_1164_6155_8681 + 1;
        BoolInt64Prod tmp_struct_209 =
                       foldl_loop_2367_3749(fltAppE_7389_8703, end_1165_6156_8682, (BoolInt64Prod) {pvrtmp_16213, pvrtmp_16214}, vec_1168_6158_8684, pts_191_6159_8685, actual_192_6160_8686);
        BoolTy pvrtmp_16217 = tmp_struct_209.field0;
        IntTy pvrtmp_16218 = tmp_struct_209.field1;

        return (BoolInt64Prod) {pvrtmp_16217, pvrtmp_16218};
    }
}
CursorCursorCursorCursorProd _copy_KdTree(CursorTy end_r_10703,
                                          CursorTy end_r_10704,
                                          CursorTy loc_10702,
                                          CursorTy arg_4208_6162_8704)
{
    if (loc_10702 + 73 > end_r_10704) {
        ChunkTy new_chunk_217 = alloc_chunk(end_r_10704);
        CursorTy chunk_start_218 = new_chunk_217.chunk_start;
        CursorTy chunk_end_219 = new_chunk_217.chunk_end;

        end_r_10704 = chunk_end_219;
        *(TagTyPacked *) loc_10702 = 255;

        CursorTy redir = loc_10702 + 1;

        *(CursorTy *) redir = chunk_start_218;
        loc_10702 = chunk_start_218;
    }

    CursorTy loc_11386 = loc_10702 + 1;
    CursorTy loc_11387 = loc_11386 + 8;
    CursorTy loc_11388 = loc_11387 + 4;
    CursorTy loc_11389 = loc_11388 + 4;
    CursorTy loc_11390 = loc_11389 + 4;
    CursorTy loc_11391 = loc_11390 + 8;
    CursorTy loc_11392 = loc_11391 + 8;
    CursorTy loc_11393 = loc_11392 + 4;
    CursorTy loc_11394 = loc_11393 + 4;
    CursorTy loc_11395 = loc_11394 + 4;
    CursorTy loc_11396 = loc_11395 + 4;
    CursorTy loc_11397 = loc_11396 + 4;
    CursorTy loc_11398 = loc_11397 + 4;
    CursorTy loc_11399 = loc_11398 + 4;
    TagTyPacked tmpval_16219 = *(TagTyPacked *) arg_4208_6162_8704;
    CursorTy tmpcur_16220 = arg_4208_6162_8704 + 1;


  switch_16305:
    ;
    switch (tmpval_16219) {

      case 0:
        {
            FloatTy tmpval_16221 = *(FloatTy *) tmpcur_16220;
            CursorTy tmpcur_16222 = tmpcur_16220 + sizeof(FloatTy);
            FloatTy tmpval_16223 = *(FloatTy *) tmpcur_16222;
            CursorTy tmpcur_16224 = tmpcur_16222 + sizeof(FloatTy);
            FloatTy tmpval_16225 = *(FloatTy *) tmpcur_16224;
            CursorTy tmpcur_16226 = tmpcur_16224 + sizeof(FloatTy);
            CursorTy jump_12442 = tmpcur_16224 + 4;
            CursorTy jump_12441 = tmpcur_16222 + 4;
            CursorTy jump_12440 = tmpcur_16220 + 4;

            *(TagTyPacked *) loc_10702 = 0;

            CursorTy writetag_13462 = loc_10702 + 1;

            *(FloatTy *) writetag_13462 = tmpval_16221;

            CursorTy writecur_13463 = writetag_13462 + sizeof(FloatTy);

            *(FloatTy *) writecur_13463 = tmpval_16223;

            CursorTy writecur_13464 = writecur_13463 + sizeof(FloatTy);

            *(FloatTy *) writecur_13464 = tmpval_16225;

            CursorTy writecur_13465 = writecur_13464 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_10704, jump_12442,
                                                   loc_10702, writecur_13465};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16231 = *(CursorTy *) tmpcur_16220;
            CursorTy tmpaftercur_16232 = tmpcur_16220 + 8;
            FloatTy tmpval_16233 = *(FloatTy *) tmpaftercur_16232;
            CursorTy tmpcur_16234 = tmpaftercur_16232 + sizeof(FloatTy);
            FloatTy tmpval_16235 = *(FloatTy *) tmpcur_16234;
            CursorTy tmpcur_16236 = tmpcur_16234 + sizeof(FloatTy);
            FloatTy tmpval_16237 = *(FloatTy *) tmpcur_16236;
            CursorTy tmpcur_16238 = tmpcur_16236 + sizeof(FloatTy);
            IntTy tmpval_16239 = *(IntTy *) tmpcur_16238;
            CursorTy tmpcur_16240 = tmpcur_16238 + sizeof(IntTy);
            IntTy tmpval_16241 = *(IntTy *) tmpcur_16240;
            CursorTy tmpcur_16242 = tmpcur_16240 + sizeof(IntTy);
            FloatTy tmpval_16243 = *(FloatTy *) tmpcur_16242;
            CursorTy tmpcur_16244 = tmpcur_16242 + sizeof(FloatTy);
            FloatTy tmpval_16245 = *(FloatTy *) tmpcur_16244;
            CursorTy tmpcur_16246 = tmpcur_16244 + sizeof(FloatTy);
            FloatTy tmpval_16247 = *(FloatTy *) tmpcur_16246;
            CursorTy tmpcur_16248 = tmpcur_16246 + sizeof(FloatTy);
            FloatTy tmpval_16249 = *(FloatTy *) tmpcur_16248;
            CursorTy tmpcur_16250 = tmpcur_16248 + sizeof(FloatTy);
            FloatTy tmpval_16251 = *(FloatTy *) tmpcur_16250;
            CursorTy tmpcur_16252 = tmpcur_16250 + sizeof(FloatTy);
            FloatTy tmpval_16253 = *(FloatTy *) tmpcur_16252;
            CursorTy tmpcur_16254 = tmpcur_16252 + sizeof(FloatTy);
            FloatTy tmpval_16255 = *(FloatTy *) tmpcur_16254;
            CursorTy tmpcur_16256 = tmpcur_16254 + sizeof(FloatTy);
            CursorTy jump_12456 = tmpcur_16254 + 4;
            CursorTy jump_12455 = tmpcur_16252 + 4;
            CursorTy jump_12454 = tmpcur_16250 + 4;
            CursorTy jump_12453 = tmpcur_16248 + 4;
            CursorTy jump_12452 = tmpcur_16246 + 4;
            CursorTy jump_12451 = tmpcur_16244 + 4;
            CursorTy jump_12450 = tmpcur_16242 + 4;
            CursorTy jump_12449 = tmpcur_16240 + 8;
            CursorTy jump_12448 = tmpcur_16238 + 8;
            CursorTy jump_12447 = tmpcur_16236 + 4;
            CursorTy jump_12446 = tmpcur_16234 + 4;
            CursorTy jump_12445 = tmpaftercur_16232 + 4;
            CursorTy jump_12444 = tmpcur_16220 + 8;
            CursorCursorCursorCursorProd tmp_struct_213 =
                                          _copy_KdTree(end_r_10703, end_r_10704, loc_11399, tmpcur_16256);
            CursorTy pvrtmp_16257 = tmp_struct_213.field0;
            CursorTy pvrtmp_16258 = tmp_struct_213.field1;
            CursorTy pvrtmp_16259 = tmp_struct_213.field2;
            CursorTy pvrtmp_16260 = tmp_struct_213.field3;
            CursorCursorCursorCursorProd tmp_struct_214 =
                                          _copy_KdTree(end_r_10703, pvrtmp_16257, pvrtmp_16260, tmpcur_16231);
            CursorTy pvrtmp_16265 = tmp_struct_214.field0;
            CursorTy pvrtmp_16266 = tmp_struct_214.field1;
            CursorTy pvrtmp_16267 = tmp_struct_214.field2;
            CursorTy pvrtmp_16268 = tmp_struct_214.field3;

            *(TagTyPacked *) loc_10702 = 3;

            CursorTy writetag_13483 = loc_10702 + 1;

            *(CursorTy *) writetag_13483 = pvrtmp_16260;

            CursorTy writecur_13484 = writetag_13483 + 8;

            *(FloatTy *) writecur_13484 = tmpval_16233;

            CursorTy writecur_13485 = writecur_13484 + sizeof(FloatTy);

            *(FloatTy *) writecur_13485 = tmpval_16235;

            CursorTy writecur_13486 = writecur_13485 + sizeof(FloatTy);

            *(FloatTy *) writecur_13486 = tmpval_16237;

            CursorTy writecur_13487 = writecur_13486 + sizeof(FloatTy);

            *(IntTy *) writecur_13487 = tmpval_16239;

            CursorTy writecur_13488 = writecur_13487 + sizeof(IntTy);

            *(IntTy *) writecur_13488 = tmpval_16241;

            CursorTy writecur_13489 = writecur_13488 + sizeof(IntTy);

            *(FloatTy *) writecur_13489 = tmpval_16243;

            CursorTy writecur_13490 = writecur_13489 + sizeof(FloatTy);

            *(FloatTy *) writecur_13490 = tmpval_16245;

            CursorTy writecur_13491 = writecur_13490 + sizeof(FloatTy);

            *(FloatTy *) writecur_13491 = tmpval_16247;

            CursorTy writecur_13492 = writecur_13491 + sizeof(FloatTy);

            *(FloatTy *) writecur_13492 = tmpval_16249;

            CursorTy writecur_13493 = writecur_13492 + sizeof(FloatTy);

            *(FloatTy *) writecur_13493 = tmpval_16251;

            CursorTy writecur_13494 = writecur_13493 + sizeof(FloatTy);

            *(FloatTy *) writecur_13494 = tmpval_16253;

            CursorTy writecur_13495 = writecur_13494 + sizeof(FloatTy);

            *(FloatTy *) writecur_13495 = tmpval_16255;

            CursorTy writecur_13496 = writecur_13495 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_16265, pvrtmp_16266,
                                                   loc_10702, pvrtmp_16268};
            break;
        }

      case 2:
        {
            CursorTy jump_12460 = arg_4208_6162_8704 + 1;

            *(TagTyPacked *) loc_10702 = 2;

            CursorTy writetag_13501 = loc_10702 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10704, jump_12460,
                                                   loc_10702, writetag_13501};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16281 = *(CursorTy *) tmpcur_16220;
            CursorTy tmpaftercur_16282 = tmpcur_16220 + 8;
            CursorTy jump_12824 = tmpcur_16220 + 8;
            CursorCursorCursorCursorProd tmp_struct_215 =
                                          _copy_KdTree(end_r_10703, end_r_10704, loc_10702, tmpcur_16281);
            CursorTy pvrtmp_16283 = tmp_struct_215.field0;
            CursorTy pvrtmp_16284 = tmp_struct_215.field1;
            CursorTy pvrtmp_16285 = tmp_struct_215.field2;
            CursorTy pvrtmp_16286 = tmp_struct_215.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16283, jump_12824,
                                                   pvrtmp_16285, pvrtmp_16286};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16293 = *(CursorTy *) tmpcur_16220;
            CursorTy tmpaftercur_16294 = tmpcur_16220 + 8;
            CursorCursorCursorCursorProd tmp_struct_216 =
                                          _copy_KdTree(end_r_10703, end_r_10704, loc_10702, tmpcur_16293);
            CursorTy pvrtmp_16295 = tmp_struct_216.field0;
            CursorTy pvrtmp_16296 = tmp_struct_216.field1;
            CursorTy pvrtmp_16297 = tmp_struct_216.field2;
            CursorTy pvrtmp_16298 = tmp_struct_216.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16295, pvrtmp_16296,
                                                   pvrtmp_16297, pvrtmp_16298};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16219");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_KdTree(CursorTy end_r_10707,
                                                       CursorTy end_r_10708,
                                                       CursorTy loc_10706,
                                                       CursorTy arg_4243_6197_8739)
{
    CursorTy loc_11465 = loc_10706 + 1;
    CursorTy loc_11466 = loc_11465 + 4;
    CursorTy loc_11467 = loc_11466 + 4;
    CursorTy loc_11468 = loc_11467 + 4;
    CursorTy loc_11469 = loc_11468 + 8;
    CursorTy loc_11470 = loc_11469 + 8;
    CursorTy loc_11471 = loc_11470 + 4;
    CursorTy loc_11472 = loc_11471 + 4;
    CursorTy loc_11473 = loc_11472 + 4;
    CursorTy loc_11474 = loc_11473 + 4;
    CursorTy loc_11475 = loc_11474 + 4;
    CursorTy loc_11476 = loc_11475 + 4;
    CursorTy loc_11477 = loc_11476 + 4;
    TagTyPacked tmpval_16306 = *(TagTyPacked *) arg_4243_6197_8739;
    CursorTy tmpcur_16307 = arg_4243_6197_8739 + 1;


  switch_16392:
    ;
    switch (tmpval_16306) {

      case 0:
        {
            FloatTy tmpval_16308 = *(FloatTy *) tmpcur_16307;
            CursorTy tmpcur_16309 = tmpcur_16307 + sizeof(FloatTy);
            FloatTy tmpval_16310 = *(FloatTy *) tmpcur_16309;
            CursorTy tmpcur_16311 = tmpcur_16309 + sizeof(FloatTy);
            FloatTy tmpval_16312 = *(FloatTy *) tmpcur_16311;
            CursorTy tmpcur_16313 = tmpcur_16311 + sizeof(FloatTy);
            CursorTy jump_12464 = tmpcur_16311 + 4;
            CursorTy jump_12463 = tmpcur_16309 + 4;
            CursorTy jump_12462 = tmpcur_16307 + 4;

            *(TagTyPacked *) loc_10706 = 0;

            CursorTy writetag_13513 = loc_10706 + 1;

            *(FloatTy *) writetag_13513 = tmpval_16308;

            CursorTy writecur_13514 = writetag_13513 + sizeof(FloatTy);

            *(FloatTy *) writecur_13514 = tmpval_16310;

            CursorTy writecur_13515 = writecur_13514 + sizeof(FloatTy);

            *(FloatTy *) writecur_13515 = tmpval_16312;

            CursorTy writecur_13516 = writecur_13515 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_10708, jump_12464,
                                                   loc_10706, writecur_13516};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16318 = *(CursorTy *) tmpcur_16307;
            CursorTy tmpaftercur_16319 = tmpcur_16307 + 8;
            FloatTy tmpval_16320 = *(FloatTy *) tmpaftercur_16319;
            CursorTy tmpcur_16321 = tmpaftercur_16319 + sizeof(FloatTy);
            FloatTy tmpval_16322 = *(FloatTy *) tmpcur_16321;
            CursorTy tmpcur_16323 = tmpcur_16321 + sizeof(FloatTy);
            FloatTy tmpval_16324 = *(FloatTy *) tmpcur_16323;
            CursorTy tmpcur_16325 = tmpcur_16323 + sizeof(FloatTy);
            IntTy tmpval_16326 = *(IntTy *) tmpcur_16325;
            CursorTy tmpcur_16327 = tmpcur_16325 + sizeof(IntTy);
            IntTy tmpval_16328 = *(IntTy *) tmpcur_16327;
            CursorTy tmpcur_16329 = tmpcur_16327 + sizeof(IntTy);
            FloatTy tmpval_16330 = *(FloatTy *) tmpcur_16329;
            CursorTy tmpcur_16331 = tmpcur_16329 + sizeof(FloatTy);
            FloatTy tmpval_16332 = *(FloatTy *) tmpcur_16331;
            CursorTy tmpcur_16333 = tmpcur_16331 + sizeof(FloatTy);
            FloatTy tmpval_16334 = *(FloatTy *) tmpcur_16333;
            CursorTy tmpcur_16335 = tmpcur_16333 + sizeof(FloatTy);
            FloatTy tmpval_16336 = *(FloatTy *) tmpcur_16335;
            CursorTy tmpcur_16337 = tmpcur_16335 + sizeof(FloatTy);
            FloatTy tmpval_16338 = *(FloatTy *) tmpcur_16337;
            CursorTy tmpcur_16339 = tmpcur_16337 + sizeof(FloatTy);
            FloatTy tmpval_16340 = *(FloatTy *) tmpcur_16339;
            CursorTy tmpcur_16341 = tmpcur_16339 + sizeof(FloatTy);
            FloatTy tmpval_16342 = *(FloatTy *) tmpcur_16341;
            CursorTy tmpcur_16343 = tmpcur_16341 + sizeof(FloatTy);
            CursorTy jump_12478 = tmpcur_16341 + 4;
            CursorTy jump_12477 = tmpcur_16339 + 4;
            CursorTy jump_12476 = tmpcur_16337 + 4;
            CursorTy jump_12475 = tmpcur_16335 + 4;
            CursorTy jump_12474 = tmpcur_16333 + 4;
            CursorTy jump_12473 = tmpcur_16331 + 4;
            CursorTy jump_12472 = tmpcur_16329 + 4;
            CursorTy jump_12471 = tmpcur_16327 + 8;
            CursorTy jump_12470 = tmpcur_16325 + 8;
            CursorTy jump_12469 = tmpcur_16323 + 4;
            CursorTy jump_12468 = tmpcur_16321 + 4;
            CursorTy jump_12467 = tmpaftercur_16319 + 4;
            CursorTy jump_12466 = tmpcur_16307 + 8;
            CursorCursorCursorCursorProd tmp_struct_220 =
                                          _copy_without_ptrs_KdTree(end_r_10707, end_r_10708, loc_11477, tmpcur_16343);
            CursorTy pvrtmp_16344 = tmp_struct_220.field0;
            CursorTy pvrtmp_16345 = tmp_struct_220.field1;
            CursorTy pvrtmp_16346 = tmp_struct_220.field2;
            CursorTy pvrtmp_16347 = tmp_struct_220.field3;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          _copy_without_ptrs_KdTree(end_r_10707, pvrtmp_16344, pvrtmp_16347, tmpcur_16318);
            CursorTy pvrtmp_16352 = tmp_struct_221.field0;
            CursorTy pvrtmp_16353 = tmp_struct_221.field1;
            CursorTy pvrtmp_16354 = tmp_struct_221.field2;
            CursorTy pvrtmp_16355 = tmp_struct_221.field3;

            *(TagTyPacked *) loc_10706 = 1;

            CursorTy writetag_13534 = loc_10706 + 1;

            *(FloatTy *) writetag_13534 = tmpval_16320;

            CursorTy writecur_13535 = writetag_13534 + sizeof(FloatTy);

            *(FloatTy *) writecur_13535 = tmpval_16322;

            CursorTy writecur_13536 = writecur_13535 + sizeof(FloatTy);

            *(FloatTy *) writecur_13536 = tmpval_16324;

            CursorTy writecur_13537 = writecur_13536 + sizeof(FloatTy);

            *(IntTy *) writecur_13537 = tmpval_16326;

            CursorTy writecur_13538 = writecur_13537 + sizeof(IntTy);

            *(IntTy *) writecur_13538 = tmpval_16328;

            CursorTy writecur_13539 = writecur_13538 + sizeof(IntTy);

            *(FloatTy *) writecur_13539 = tmpval_16330;

            CursorTy writecur_13540 = writecur_13539 + sizeof(FloatTy);

            *(FloatTy *) writecur_13540 = tmpval_16332;

            CursorTy writecur_13541 = writecur_13540 + sizeof(FloatTy);

            *(FloatTy *) writecur_13541 = tmpval_16334;

            CursorTy writecur_13542 = writecur_13541 + sizeof(FloatTy);

            *(FloatTy *) writecur_13542 = tmpval_16336;

            CursorTy writecur_13543 = writecur_13542 + sizeof(FloatTy);

            *(FloatTy *) writecur_13543 = tmpval_16338;

            CursorTy writecur_13544 = writecur_13543 + sizeof(FloatTy);

            *(FloatTy *) writecur_13544 = tmpval_16340;

            CursorTy writecur_13545 = writecur_13544 + sizeof(FloatTy);

            *(FloatTy *) writecur_13545 = tmpval_16342;

            CursorTy writecur_13546 = writecur_13545 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_16352, pvrtmp_16353,
                                                   loc_10706, pvrtmp_16355};
            break;
        }

      case 2:
        {
            CursorTy jump_12482 = arg_4243_6197_8739 + 1;

            *(TagTyPacked *) loc_10706 = 2;

            CursorTy writetag_13551 = loc_10706 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10708, jump_12482,
                                                   loc_10706, writetag_13551};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16368 = *(CursorTy *) tmpcur_16307;
            CursorTy tmpaftercur_16369 = tmpcur_16307 + 8;
            CursorTy jump_12830 = tmpcur_16307 + 8;
            CursorCursorCursorCursorProd tmp_struct_222 =
                                          _copy_without_ptrs_KdTree(end_r_10707, end_r_10708, loc_10706, tmpcur_16368);
            CursorTy pvrtmp_16370 = tmp_struct_222.field0;
            CursorTy pvrtmp_16371 = tmp_struct_222.field1;
            CursorTy pvrtmp_16372 = tmp_struct_222.field2;
            CursorTy pvrtmp_16373 = tmp_struct_222.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16370, jump_12830,
                                                   pvrtmp_16372, pvrtmp_16373};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16380 = *(CursorTy *) tmpcur_16307;
            CursorTy tmpaftercur_16381 = tmpcur_16307 + 8;
            CursorCursorCursorCursorProd tmp_struct_223 =
                                          _copy_without_ptrs_KdTree(end_r_10707, end_r_10708, loc_10706, tmpcur_16380);
            CursorTy pvrtmp_16382 = tmp_struct_223.field0;
            CursorTy pvrtmp_16383 = tmp_struct_223.field1;
            CursorTy pvrtmp_16384 = tmp_struct_223.field2;
            CursorTy pvrtmp_16385 = tmp_struct_223.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16382, pvrtmp_16383,
                                                   pvrtmp_16384, pvrtmp_16385};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16306");
            exit(1);
        }
    }
}
CursorProd _traverse_KdTree(CursorTy end_r_10710, CursorTy arg_4278_6232_8774)
{
    TagTyPacked tmpval_16393 = *(TagTyPacked *) arg_4278_6232_8774;
    CursorTy tmpcur_16394 = arg_4278_6232_8774 + 1;


  switch_16435:
    ;
    switch (tmpval_16393) {

      case 0:
        {
            FloatTy tmpval_16395 = *(FloatTy *) tmpcur_16394;
            CursorTy tmpcur_16396 = tmpcur_16394 + sizeof(FloatTy);
            FloatTy tmpval_16397 = *(FloatTy *) tmpcur_16396;
            CursorTy tmpcur_16398 = tmpcur_16396 + sizeof(FloatTy);
            FloatTy tmpval_16399 = *(FloatTy *) tmpcur_16398;
            CursorTy tmpcur_16400 = tmpcur_16398 + sizeof(FloatTy);
            CursorTy jump_12486 = tmpcur_16398 + 4;
            CursorTy jump_12485 = tmpcur_16396 + 4;
            CursorTy jump_12484 = tmpcur_16394 + 4;

            return (CursorProd) {jump_12486};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16401 = *(CursorTy *) tmpcur_16394;
            CursorTy tmpaftercur_16402 = tmpcur_16394 + 8;
            FloatTy tmpval_16403 = *(FloatTy *) tmpaftercur_16402;
            CursorTy tmpcur_16404 = tmpaftercur_16402 + sizeof(FloatTy);
            FloatTy tmpval_16405 = *(FloatTy *) tmpcur_16404;
            CursorTy tmpcur_16406 = tmpcur_16404 + sizeof(FloatTy);
            FloatTy tmpval_16407 = *(FloatTy *) tmpcur_16406;
            CursorTy tmpcur_16408 = tmpcur_16406 + sizeof(FloatTy);
            IntTy tmpval_16409 = *(IntTy *) tmpcur_16408;
            CursorTy tmpcur_16410 = tmpcur_16408 + sizeof(IntTy);
            IntTy tmpval_16411 = *(IntTy *) tmpcur_16410;
            CursorTy tmpcur_16412 = tmpcur_16410 + sizeof(IntTy);
            FloatTy tmpval_16413 = *(FloatTy *) tmpcur_16412;
            CursorTy tmpcur_16414 = tmpcur_16412 + sizeof(FloatTy);
            FloatTy tmpval_16415 = *(FloatTy *) tmpcur_16414;
            CursorTy tmpcur_16416 = tmpcur_16414 + sizeof(FloatTy);
            FloatTy tmpval_16417 = *(FloatTy *) tmpcur_16416;
            CursorTy tmpcur_16418 = tmpcur_16416 + sizeof(FloatTy);
            FloatTy tmpval_16419 = *(FloatTy *) tmpcur_16418;
            CursorTy tmpcur_16420 = tmpcur_16418 + sizeof(FloatTy);
            FloatTy tmpval_16421 = *(FloatTy *) tmpcur_16420;
            CursorTy tmpcur_16422 = tmpcur_16420 + sizeof(FloatTy);
            FloatTy tmpval_16423 = *(FloatTy *) tmpcur_16422;
            CursorTy tmpcur_16424 = tmpcur_16422 + sizeof(FloatTy);
            FloatTy tmpval_16425 = *(FloatTy *) tmpcur_16424;
            CursorTy tmpcur_16426 = tmpcur_16424 + sizeof(FloatTy);
            CursorTy jump_12500 = tmpcur_16424 + 4;
            CursorTy jump_12499 = tmpcur_16422 + 4;
            CursorTy jump_12498 = tmpcur_16420 + 4;
            CursorTy jump_12497 = tmpcur_16418 + 4;
            CursorTy jump_12496 = tmpcur_16416 + 4;
            CursorTy jump_12495 = tmpcur_16414 + 4;
            CursorTy jump_12494 = tmpcur_16412 + 4;
            CursorTy jump_12493 = tmpcur_16410 + 8;
            CursorTy jump_12492 = tmpcur_16408 + 8;
            CursorTy jump_12491 = tmpcur_16406 + 4;
            CursorTy jump_12490 = tmpcur_16404 + 4;
            CursorTy jump_12489 = tmpaftercur_16402 + 4;
            CursorTy jump_12488 = tmpcur_16394 + 8;
            CursorProd tmp_struct_224 =
                        _traverse_KdTree(end_r_10710, tmpcur_16426);
            CursorTy pvrtmp_16427 = tmp_struct_224.field0;
            CursorProd tmp_struct_225 =
                        _traverse_KdTree(end_r_10710, tmpcur_16401);
            CursorTy pvrtmp_16428 = tmp_struct_225.field0;

            return (CursorProd) {pvrtmp_16428};
            break;
        }

      case 2:
        {
            CursorTy jump_12504 = arg_4278_6232_8774 + 1;

            return (CursorProd) {jump_12504};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16429 = *(CursorTy *) tmpcur_16394;
            CursorTy tmpaftercur_16430 = tmpcur_16394 + 8;
            CursorTy jump_12836 = tmpcur_16394 + 8;
            CursorProd tmp_struct_226 =
                        _traverse_KdTree(end_r_10710, tmpcur_16429);
            CursorTy pvrtmp_16431 = tmp_struct_226.field0;

            return (CursorProd) {jump_12836};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16432 = *(CursorTy *) tmpcur_16394;
            CursorTy tmpaftercur_16433 = tmpcur_16394 + 8;
            CursorProd tmp_struct_227 =
                        _traverse_KdTree(end_r_10710, tmpcur_16432);
            CursorTy pvrtmp_16434 = tmp_struct_227.field0;

            return (CursorProd) {pvrtmp_16434};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16393");
            exit(1);
        }
    }
}
CursorProd _print_KdTree(CursorTy end_r_10712, CursorTy arg_4313_6252_8794)
{
    TagTyPacked tmpval_16436 = *(TagTyPacked *) arg_4313_6252_8794;
    CursorTy tmpcur_16437 = arg_4313_6252_8794 + 1;


  switch_16478:
    ;
    switch (tmpval_16436) {

      case 0:
        {
            FloatTy tmpval_16438 = *(FloatTy *) tmpcur_16437;
            CursorTy tmpcur_16439 = tmpcur_16437 + sizeof(FloatTy);
            FloatTy tmpval_16440 = *(FloatTy *) tmpcur_16439;
            CursorTy tmpcur_16441 = tmpcur_16439 + sizeof(FloatTy);
            FloatTy tmpval_16442 = *(FloatTy *) tmpcur_16441;
            CursorTy tmpcur_16443 = tmpcur_16441 + sizeof(FloatTy);
            CursorTy jump_12508 = tmpcur_16441 + 4;
            CursorTy jump_12507 = tmpcur_16439 + 4;
            CursorTy jump_12506 = tmpcur_16437 + 4;
            unsigned char wildcard_4320_6256_8798 = print_symbol(14976);
            unsigned char wildcard_4324_6257_8799 = print_symbol(14984);
            unsigned char y_4317_6258_8800 = printf("%.2f", tmpval_16438);
            unsigned char wildcard_4323_6259_8801 = print_symbol(14984);
            unsigned char y_4318_6260_8802 = printf("%.2f", tmpval_16440);
            unsigned char wildcard_4322_6261_8803 = print_symbol(14984);
            unsigned char y_4319_6262_8804 = printf("%.2f", tmpval_16442);
            unsigned char wildcard_4321_6263_8805 = print_symbol(14969);

            return (CursorProd) {jump_12508};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16444 = *(CursorTy *) tmpcur_16437;
            CursorTy tmpaftercur_16445 = tmpcur_16437 + 8;
            FloatTy tmpval_16446 = *(FloatTy *) tmpaftercur_16445;
            CursorTy tmpcur_16447 = tmpaftercur_16445 + sizeof(FloatTy);
            FloatTy tmpval_16448 = *(FloatTy *) tmpcur_16447;
            CursorTy tmpcur_16449 = tmpcur_16447 + sizeof(FloatTy);
            FloatTy tmpval_16450 = *(FloatTy *) tmpcur_16449;
            CursorTy tmpcur_16451 = tmpcur_16449 + sizeof(FloatTy);
            IntTy tmpval_16452 = *(IntTy *) tmpcur_16451;
            CursorTy tmpcur_16453 = tmpcur_16451 + sizeof(IntTy);
            IntTy tmpval_16454 = *(IntTy *) tmpcur_16453;
            CursorTy tmpcur_16455 = tmpcur_16453 + sizeof(IntTy);
            FloatTy tmpval_16456 = *(FloatTy *) tmpcur_16455;
            CursorTy tmpcur_16457 = tmpcur_16455 + sizeof(FloatTy);
            FloatTy tmpval_16458 = *(FloatTy *) tmpcur_16457;
            CursorTy tmpcur_16459 = tmpcur_16457 + sizeof(FloatTy);
            FloatTy tmpval_16460 = *(FloatTy *) tmpcur_16459;
            CursorTy tmpcur_16461 = tmpcur_16459 + sizeof(FloatTy);
            FloatTy tmpval_16462 = *(FloatTy *) tmpcur_16461;
            CursorTy tmpcur_16463 = tmpcur_16461 + sizeof(FloatTy);
            FloatTy tmpval_16464 = *(FloatTy *) tmpcur_16463;
            CursorTy tmpcur_16465 = tmpcur_16463 + sizeof(FloatTy);
            FloatTy tmpval_16466 = *(FloatTy *) tmpcur_16465;
            CursorTy tmpcur_16467 = tmpcur_16465 + sizeof(FloatTy);
            FloatTy tmpval_16468 = *(FloatTy *) tmpcur_16467;
            CursorTy tmpcur_16469 = tmpcur_16467 + sizeof(FloatTy);
            CursorTy jump_12522 = tmpcur_16467 + 4;
            CursorTy jump_12521 = tmpcur_16465 + 4;
            CursorTy jump_12520 = tmpcur_16463 + 4;
            CursorTy jump_12519 = tmpcur_16461 + 4;
            CursorTy jump_12518 = tmpcur_16459 + 4;
            CursorTy jump_12517 = tmpcur_16457 + 4;
            CursorTy jump_12516 = tmpcur_16455 + 4;
            CursorTy jump_12515 = tmpcur_16453 + 8;
            CursorTy jump_12514 = tmpcur_16451 + 8;
            CursorTy jump_12513 = tmpcur_16449 + 4;
            CursorTy jump_12512 = tmpcur_16447 + 4;
            CursorTy jump_12511 = tmpaftercur_16445 + 4;
            CursorTy jump_12510 = tmpcur_16437 + 8;
            unsigned char wildcard_4353_6278_8820 = print_symbol(14975);
            unsigned char wildcard_4368_6279_8821 = print_symbol(14984);
            unsigned char y_4339_6280_8822 = printf("%.2f", tmpval_16446);
            unsigned char wildcard_4367_6281_8823 = print_symbol(14984);
            unsigned char y_4340_6282_8824 = printf("%.2f", tmpval_16448);
            unsigned char wildcard_4366_6283_8825 = print_symbol(14984);
            unsigned char y_4341_6284_8826 = printf("%.2f", tmpval_16450);
            unsigned char wildcard_4365_6285_8827 = print_symbol(14984);
            unsigned char y_4342_6286_8828 = printf("%lld", tmpval_16452);
            unsigned char wildcard_4364_6287_8829 = print_symbol(14984);
            unsigned char y_4343_6288_8830 = printf("%lld", tmpval_16454);
            unsigned char wildcard_4363_6289_8831 = print_symbol(14984);
            unsigned char y_4344_6290_8832 = printf("%.2f", tmpval_16456);
            unsigned char wildcard_4362_6291_8833 = print_symbol(14984);
            unsigned char y_4345_6292_8834 = printf("%.2f", tmpval_16458);
            unsigned char wildcard_4361_6293_8835 = print_symbol(14984);
            unsigned char y_4346_6294_8836 = printf("%.2f", tmpval_16460);
            unsigned char wildcard_4360_6295_8837 = print_symbol(14984);
            unsigned char y_4347_6296_8838 = printf("%.2f", tmpval_16462);
            unsigned char wildcard_4359_6297_8839 = print_symbol(14984);
            unsigned char y_4348_6298_8840 = printf("%.2f", tmpval_16464);
            unsigned char wildcard_4358_6299_8841 = print_symbol(14984);
            unsigned char y_4349_6300_8842 = printf("%.2f", tmpval_16466);
            unsigned char wildcard_4357_6301_8843 = print_symbol(14984);
            unsigned char y_4350_6302_8844 = printf("%.2f", tmpval_16468);
            unsigned char wildcard_4356_6303_8845 = print_symbol(14984);
            CursorProd tmp_struct_228 =
                        _print_KdTree(end_r_10712, tmpcur_16469);
            CursorTy pvrtmp_16470 = tmp_struct_228.field0;
            unsigned char wildcard_4355_6305_8847 = print_symbol(14984);
            CursorProd tmp_struct_229 =
                        _print_KdTree(end_r_10712, tmpcur_16444);
            CursorTy pvrtmp_16471 = tmp_struct_229.field0;
            unsigned char wildcard_4354_6307_8849 = print_symbol(14969);

            return (CursorProd) {pvrtmp_16471};
            break;
        }

      case 2:
        {
            CursorTy jump_12526 = arg_4313_6252_8794 + 1;
            unsigned char wildcard_4369_6308_8850 = print_symbol(14977);
            unsigned char wildcard_4370_6309_8851 = print_symbol(14969);

            return (CursorProd) {jump_12526};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16472 = *(CursorTy *) tmpcur_16437;
            CursorTy tmpaftercur_16473 = tmpcur_16437 + 8;
            CursorTy jump_12842 = tmpcur_16437 + 8;
            unsigned char wildcard_12845 = print_symbol(14983);
            CursorProd tmp_struct_230 =
                        _print_KdTree(end_r_10712, tmpcur_16472);
            CursorTy pvrtmp_16474 = tmp_struct_230.field0;

            return (CursorProd) {jump_12842};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16475 = *(CursorTy *) tmpcur_16437;
            CursorTy tmpaftercur_16476 = tmpcur_16437 + 8;
            unsigned char wildcard_12845 = print_symbol(14982);
            CursorProd tmp_struct_231 =
                        _print_KdTree(end_r_10712, tmpcur_16475);
            CursorTy pvrtmp_16477 = tmp_struct_231.field0;

            return (CursorProd) {pvrtmp_16477};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16436");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_BH_Tree(CursorTy end_r_10715,
                                           CursorTy end_r_10716,
                                           CursorTy loc_10714,
                                           CursorTy arg_4371_6310_8852)
{
    if (loc_10714 + 57 > end_r_10716) {
        ChunkTy new_chunk_238 = alloc_chunk(end_r_10716);
        CursorTy chunk_start_239 = new_chunk_238.chunk_start;
        CursorTy chunk_end_240 = new_chunk_238.chunk_end;

        end_r_10716 = chunk_end_240;
        *(TagTyPacked *) loc_10714 = 255;

        CursorTy redir = loc_10714 + 1;

        *(CursorTy *) redir = chunk_start_239;
        loc_10714 = chunk_start_239;
    }

    CursorTy loc_11593 = loc_10714 + 1;
    CursorTy loc_11594 = loc_11593 + 8;
    CursorTy loc_11595 = loc_11594 + 8;
    CursorTy loc_11596 = loc_11595 + 8;
    CursorTy loc_11597 = loc_11596 + 4;
    CursorTy loc_11598 = loc_11597 + 4;
    CursorTy loc_11599 = loc_11598 + 4;
    CursorTy loc_11600 = loc_11599 + 8;
    CursorTy loc_11601 = loc_11600 + 4;
    TagTyPacked tmpval_16479 = *(TagTyPacked *) arg_4371_6310_8852;
    CursorTy tmpcur_16480 = arg_4371_6310_8852 + 1;


  switch_16571:
    ;
    switch (tmpval_16479) {

      case 0:
        {
            CursorTy jump_12528 = arg_4371_6310_8852 + 1;

            *(TagTyPacked *) loc_10714 = 0;

            CursorTy writetag_13614 = loc_10714 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10716, jump_12528,
                                                   loc_10714, writetag_13614};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16485 = *(FloatTy *) tmpcur_16480;
            CursorTy tmpcur_16486 = tmpcur_16480 + sizeof(FloatTy);
            FloatTy tmpval_16487 = *(FloatTy *) tmpcur_16486;
            CursorTy tmpcur_16488 = tmpcur_16486 + sizeof(FloatTy);
            FloatTy tmpval_16489 = *(FloatTy *) tmpcur_16488;
            CursorTy tmpcur_16490 = tmpcur_16488 + sizeof(FloatTy);
            CursorTy jump_12532 = tmpcur_16488 + 4;
            CursorTy jump_12531 = tmpcur_16486 + 4;
            CursorTy jump_12530 = tmpcur_16480 + 4;

            *(TagTyPacked *) loc_10714 = 1;

            CursorTy writetag_13620 = loc_10714 + 1;

            *(FloatTy *) writetag_13620 = tmpval_16485;

            CursorTy writecur_13621 = writetag_13620 + sizeof(FloatTy);

            *(FloatTy *) writecur_13621 = tmpval_16487;

            CursorTy writecur_13622 = writecur_13621 + sizeof(FloatTy);

            *(FloatTy *) writecur_13622 = tmpval_16489;

            CursorTy writecur_13623 = writecur_13622 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_10716, jump_12532,
                                                   loc_10714, writecur_13623};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16495 = *(CursorTy *) tmpcur_16480;
            CursorTy tmpaftercur_16496 = tmpcur_16480 + 8;
            CursorTy tmpcur_16497 = *(CursorTy *) tmpaftercur_16496;
            CursorTy tmpaftercur_16498 = tmpaftercur_16496 + 8;
            CursorTy tmpcur_16499 = *(CursorTy *) tmpaftercur_16498;
            CursorTy tmpaftercur_16500 = tmpaftercur_16498 + 8;
            FloatTy tmpval_16501 = *(FloatTy *) tmpaftercur_16500;
            CursorTy tmpcur_16502 = tmpaftercur_16500 + sizeof(FloatTy);
            FloatTy tmpval_16503 = *(FloatTy *) tmpcur_16502;
            CursorTy tmpcur_16504 = tmpcur_16502 + sizeof(FloatTy);
            FloatTy tmpval_16505 = *(FloatTy *) tmpcur_16504;
            CursorTy tmpcur_16506 = tmpcur_16504 + sizeof(FloatTy);
            IntTy tmpval_16507 = *(IntTy *) tmpcur_16506;
            CursorTy tmpcur_16508 = tmpcur_16506 + sizeof(IntTy);
            FloatTy tmpval_16509 = *(FloatTy *) tmpcur_16508;
            CursorTy tmpcur_16510 = tmpcur_16508 + sizeof(FloatTy);
            CursorTy jump_12541 = tmpcur_16508 + 4;
            CursorTy jump_12540 = tmpcur_16506 + 8;
            CursorTy jump_12539 = tmpcur_16504 + 4;
            CursorTy jump_12538 = tmpcur_16502 + 4;
            CursorTy jump_12537 = tmpaftercur_16500 + 4;
            CursorTy jump_12536 = tmpaftercur_16498 + 8;
            CursorTy jump_12535 = tmpaftercur_16496 + 8;
            CursorTy jump_12534 = tmpcur_16480 + 8;
            CursorCursorCursorCursorProd tmp_struct_232 =
                                          _copy_BH_Tree(end_r_10715, end_r_10716, loc_11601, tmpcur_16510);
            CursorTy pvrtmp_16511 = tmp_struct_232.field0;
            CursorTy pvrtmp_16512 = tmp_struct_232.field1;
            CursorTy pvrtmp_16513 = tmp_struct_232.field2;
            CursorTy pvrtmp_16514 = tmp_struct_232.field3;
            CursorCursorCursorCursorProd tmp_struct_233 =
                                          _copy_BH_Tree(end_r_10715, pvrtmp_16511, pvrtmp_16514, tmpcur_16495);
            CursorTy pvrtmp_16519 = tmp_struct_233.field0;
            CursorTy pvrtmp_16520 = tmp_struct_233.field1;
            CursorTy pvrtmp_16521 = tmp_struct_233.field2;
            CursorTy pvrtmp_16522 = tmp_struct_233.field3;
            CursorCursorCursorCursorProd tmp_struct_234 =
                                          _copy_BH_Tree(end_r_10715, pvrtmp_16519, pvrtmp_16522, tmpcur_16497);
            CursorTy pvrtmp_16527 = tmp_struct_234.field0;
            CursorTy pvrtmp_16528 = tmp_struct_234.field1;
            CursorTy pvrtmp_16529 = tmp_struct_234.field2;
            CursorTy pvrtmp_16530 = tmp_struct_234.field3;
            CursorCursorCursorCursorProd tmp_struct_235 =
                                          _copy_BH_Tree(end_r_10715, pvrtmp_16527, pvrtmp_16530, tmpcur_16499);
            CursorTy pvrtmp_16535 = tmp_struct_235.field0;
            CursorTy pvrtmp_16536 = tmp_struct_235.field1;
            CursorTy pvrtmp_16537 = tmp_struct_235.field2;
            CursorTy pvrtmp_16538 = tmp_struct_235.field3;

            *(TagTyPacked *) loc_10714 = 3;

            CursorTy writetag_13638 = loc_10714 + 1;

            *(CursorTy *) writetag_13638 = pvrtmp_16514;

            CursorTy writecur_13639 = writetag_13638 + 8;

            *(CursorTy *) writecur_13639 = pvrtmp_16522;

            CursorTy writecur_13640 = writecur_13639 + 8;

            *(CursorTy *) writecur_13640 = pvrtmp_16530;

            CursorTy writecur_13641 = writecur_13640 + 8;

            *(FloatTy *) writecur_13641 = tmpval_16501;

            CursorTy writecur_13642 = writecur_13641 + sizeof(FloatTy);

            *(FloatTy *) writecur_13642 = tmpval_16503;

            CursorTy writecur_13643 = writecur_13642 + sizeof(FloatTy);

            *(FloatTy *) writecur_13643 = tmpval_16505;

            CursorTy writecur_13644 = writecur_13643 + sizeof(FloatTy);

            *(IntTy *) writecur_13644 = tmpval_16507;

            CursorTy writecur_13645 = writecur_13644 + sizeof(IntTy);

            *(FloatTy *) writecur_13645 = tmpval_16509;

            CursorTy writecur_13646 = writecur_13645 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_16535, pvrtmp_16536,
                                                   loc_10714, pvrtmp_16538};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16547 = *(CursorTy *) tmpcur_16480;
            CursorTy tmpaftercur_16548 = tmpcur_16480 + 8;
            CursorTy jump_12848 = tmpcur_16480 + 8;
            CursorCursorCursorCursorProd tmp_struct_236 =
                                          _copy_BH_Tree(end_r_10715, end_r_10716, loc_10714, tmpcur_16547);
            CursorTy pvrtmp_16549 = tmp_struct_236.field0;
            CursorTy pvrtmp_16550 = tmp_struct_236.field1;
            CursorTy pvrtmp_16551 = tmp_struct_236.field2;
            CursorTy pvrtmp_16552 = tmp_struct_236.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16549, jump_12848,
                                                   pvrtmp_16551, pvrtmp_16552};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16559 = *(CursorTy *) tmpcur_16480;
            CursorTy tmpaftercur_16560 = tmpcur_16480 + 8;
            CursorCursorCursorCursorProd tmp_struct_237 =
                                          _copy_BH_Tree(end_r_10715, end_r_10716, loc_10714, tmpcur_16559);
            CursorTy pvrtmp_16561 = tmp_struct_237.field0;
            CursorTy pvrtmp_16562 = tmp_struct_237.field1;
            CursorTy pvrtmp_16563 = tmp_struct_237.field2;
            CursorTy pvrtmp_16564 = tmp_struct_237.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16561, pvrtmp_16562,
                                                   pvrtmp_16563, pvrtmp_16564};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16479");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_BH_Tree(CursorTy end_r_10719,
                                                        CursorTy end_r_10720,
                                                        CursorTy loc_10718,
                                                        CursorTy arg_4396_6335_8877)
{
    CursorTy loc_11664 = loc_10718 + 1;
    CursorTy loc_11665 = loc_11664 + 4;
    CursorTy loc_11666 = loc_11665 + 4;
    CursorTy loc_11667 = loc_11666 + 4;
    CursorTy loc_11668 = loc_11667 + 8;
    CursorTy loc_11669 = loc_11668 + 4;
    TagTyPacked tmpval_16572 = *(TagTyPacked *) arg_4396_6335_8877;
    CursorTy tmpcur_16573 = arg_4396_6335_8877 + 1;


  switch_16664:
    ;
    switch (tmpval_16572) {

      case 0:
        {
            CursorTy jump_12547 = arg_4396_6335_8877 + 1;

            *(TagTyPacked *) loc_10718 = 0;

            CursorTy writetag_13659 = loc_10718 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10720, jump_12547,
                                                   loc_10718, writetag_13659};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16578 = *(FloatTy *) tmpcur_16573;
            CursorTy tmpcur_16579 = tmpcur_16573 + sizeof(FloatTy);
            FloatTy tmpval_16580 = *(FloatTy *) tmpcur_16579;
            CursorTy tmpcur_16581 = tmpcur_16579 + sizeof(FloatTy);
            FloatTy tmpval_16582 = *(FloatTy *) tmpcur_16581;
            CursorTy tmpcur_16583 = tmpcur_16581 + sizeof(FloatTy);
            CursorTy jump_12551 = tmpcur_16581 + 4;
            CursorTy jump_12550 = tmpcur_16579 + 4;
            CursorTy jump_12549 = tmpcur_16573 + 4;

            *(TagTyPacked *) loc_10718 = 1;

            CursorTy writetag_13665 = loc_10718 + 1;

            *(FloatTy *) writetag_13665 = tmpval_16578;

            CursorTy writecur_13666 = writetag_13665 + sizeof(FloatTy);

            *(FloatTy *) writecur_13666 = tmpval_16580;

            CursorTy writecur_13667 = writecur_13666 + sizeof(FloatTy);

            *(FloatTy *) writecur_13667 = tmpval_16582;

            CursorTy writecur_13668 = writecur_13667 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_10720, jump_12551,
                                                   loc_10718, writecur_13668};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16588 = *(CursorTy *) tmpcur_16573;
            CursorTy tmpaftercur_16589 = tmpcur_16573 + 8;
            CursorTy tmpcur_16590 = *(CursorTy *) tmpaftercur_16589;
            CursorTy tmpaftercur_16591 = tmpaftercur_16589 + 8;
            CursorTy tmpcur_16592 = *(CursorTy *) tmpaftercur_16591;
            CursorTy tmpaftercur_16593 = tmpaftercur_16591 + 8;
            FloatTy tmpval_16594 = *(FloatTy *) tmpaftercur_16593;
            CursorTy tmpcur_16595 = tmpaftercur_16593 + sizeof(FloatTy);
            FloatTy tmpval_16596 = *(FloatTy *) tmpcur_16595;
            CursorTy tmpcur_16597 = tmpcur_16595 + sizeof(FloatTy);
            FloatTy tmpval_16598 = *(FloatTy *) tmpcur_16597;
            CursorTy tmpcur_16599 = tmpcur_16597 + sizeof(FloatTy);
            IntTy tmpval_16600 = *(IntTy *) tmpcur_16599;
            CursorTy tmpcur_16601 = tmpcur_16599 + sizeof(IntTy);
            FloatTy tmpval_16602 = *(FloatTy *) tmpcur_16601;
            CursorTy tmpcur_16603 = tmpcur_16601 + sizeof(FloatTy);
            CursorTy jump_12560 = tmpcur_16601 + 4;
            CursorTy jump_12559 = tmpcur_16599 + 8;
            CursorTy jump_12558 = tmpcur_16597 + 4;
            CursorTy jump_12557 = tmpcur_16595 + 4;
            CursorTy jump_12556 = tmpaftercur_16593 + 4;
            CursorTy jump_12555 = tmpaftercur_16591 + 8;
            CursorTy jump_12554 = tmpaftercur_16589 + 8;
            CursorTy jump_12553 = tmpcur_16573 + 8;
            CursorCursorCursorCursorProd tmp_struct_241 =
                                          _copy_without_ptrs_BH_Tree(end_r_10719, end_r_10720, loc_11669, tmpcur_16603);
            CursorTy pvrtmp_16604 = tmp_struct_241.field0;
            CursorTy pvrtmp_16605 = tmp_struct_241.field1;
            CursorTy pvrtmp_16606 = tmp_struct_241.field2;
            CursorTy pvrtmp_16607 = tmp_struct_241.field3;
            CursorCursorCursorCursorProd tmp_struct_242 =
                                          _copy_without_ptrs_BH_Tree(end_r_10719, pvrtmp_16604, pvrtmp_16607, tmpcur_16588);
            CursorTy pvrtmp_16612 = tmp_struct_242.field0;
            CursorTy pvrtmp_16613 = tmp_struct_242.field1;
            CursorTy pvrtmp_16614 = tmp_struct_242.field2;
            CursorTy pvrtmp_16615 = tmp_struct_242.field3;
            CursorCursorCursorCursorProd tmp_struct_243 =
                                          _copy_without_ptrs_BH_Tree(end_r_10719, pvrtmp_16612, pvrtmp_16615, tmpcur_16590);
            CursorTy pvrtmp_16620 = tmp_struct_243.field0;
            CursorTy pvrtmp_16621 = tmp_struct_243.field1;
            CursorTy pvrtmp_16622 = tmp_struct_243.field2;
            CursorTy pvrtmp_16623 = tmp_struct_243.field3;
            CursorCursorCursorCursorProd tmp_struct_244 =
                                          _copy_without_ptrs_BH_Tree(end_r_10719, pvrtmp_16620, pvrtmp_16623, tmpcur_16592);
            CursorTy pvrtmp_16628 = tmp_struct_244.field0;
            CursorTy pvrtmp_16629 = tmp_struct_244.field1;
            CursorTy pvrtmp_16630 = tmp_struct_244.field2;
            CursorTy pvrtmp_16631 = tmp_struct_244.field3;

            *(TagTyPacked *) loc_10718 = 2;

            CursorTy writetag_13683 = loc_10718 + 1;

            *(FloatTy *) writetag_13683 = tmpval_16594;

            CursorTy writecur_13684 = writetag_13683 + sizeof(FloatTy);

            *(FloatTy *) writecur_13684 = tmpval_16596;

            CursorTy writecur_13685 = writecur_13684 + sizeof(FloatTy);

            *(FloatTy *) writecur_13685 = tmpval_16598;

            CursorTy writecur_13686 = writecur_13685 + sizeof(FloatTy);

            *(IntTy *) writecur_13686 = tmpval_16600;

            CursorTy writecur_13687 = writecur_13686 + sizeof(IntTy);

            *(FloatTy *) writecur_13687 = tmpval_16602;

            CursorTy writecur_13688 = writecur_13687 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_16628, pvrtmp_16629,
                                                   loc_10718, pvrtmp_16631};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16640 = *(CursorTy *) tmpcur_16573;
            CursorTy tmpaftercur_16641 = tmpcur_16573 + 8;
            CursorTy jump_12854 = tmpcur_16573 + 8;
            CursorCursorCursorCursorProd tmp_struct_245 =
                                          _copy_without_ptrs_BH_Tree(end_r_10719, end_r_10720, loc_10718, tmpcur_16640);
            CursorTy pvrtmp_16642 = tmp_struct_245.field0;
            CursorTy pvrtmp_16643 = tmp_struct_245.field1;
            CursorTy pvrtmp_16644 = tmp_struct_245.field2;
            CursorTy pvrtmp_16645 = tmp_struct_245.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16642, jump_12854,
                                                   pvrtmp_16644, pvrtmp_16645};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16652 = *(CursorTy *) tmpcur_16573;
            CursorTy tmpaftercur_16653 = tmpcur_16573 + 8;
            CursorCursorCursorCursorProd tmp_struct_246 =
                                          _copy_without_ptrs_BH_Tree(end_r_10719, end_r_10720, loc_10718, tmpcur_16652);
            CursorTy pvrtmp_16654 = tmp_struct_246.field0;
            CursorTy pvrtmp_16655 = tmp_struct_246.field1;
            CursorTy pvrtmp_16656 = tmp_struct_246.field2;
            CursorTy pvrtmp_16657 = tmp_struct_246.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16654, pvrtmp_16655,
                                                   pvrtmp_16656, pvrtmp_16657};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16572");
            exit(1);
        }
    }
}
CursorProd _traverse_BH_Tree(CursorTy end_r_10722, CursorTy arg_4421_6360_8902)
{
    TagTyPacked tmpval_16665 = *(TagTyPacked *) arg_4421_6360_8902;
    CursorTy tmpcur_16666 = arg_4421_6360_8902 + 1;


  switch_16699:
    ;
    switch (tmpval_16665) {

      case 0:
        {
            CursorTy jump_12566 = arg_4421_6360_8902 + 1;

            return (CursorProd) {jump_12566};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16667 = *(FloatTy *) tmpcur_16666;
            CursorTy tmpcur_16668 = tmpcur_16666 + sizeof(FloatTy);
            FloatTy tmpval_16669 = *(FloatTy *) tmpcur_16668;
            CursorTy tmpcur_16670 = tmpcur_16668 + sizeof(FloatTy);
            FloatTy tmpval_16671 = *(FloatTy *) tmpcur_16670;
            CursorTy tmpcur_16672 = tmpcur_16670 + sizeof(FloatTy);
            CursorTy jump_12570 = tmpcur_16670 + 4;
            CursorTy jump_12569 = tmpcur_16668 + 4;
            CursorTy jump_12568 = tmpcur_16666 + 4;

            return (CursorProd) {jump_12570};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16673 = *(CursorTy *) tmpcur_16666;
            CursorTy tmpaftercur_16674 = tmpcur_16666 + 8;
            CursorTy tmpcur_16675 = *(CursorTy *) tmpaftercur_16674;
            CursorTy tmpaftercur_16676 = tmpaftercur_16674 + 8;
            CursorTy tmpcur_16677 = *(CursorTy *) tmpaftercur_16676;
            CursorTy tmpaftercur_16678 = tmpaftercur_16676 + 8;
            FloatTy tmpval_16679 = *(FloatTy *) tmpaftercur_16678;
            CursorTy tmpcur_16680 = tmpaftercur_16678 + sizeof(FloatTy);
            FloatTy tmpval_16681 = *(FloatTy *) tmpcur_16680;
            CursorTy tmpcur_16682 = tmpcur_16680 + sizeof(FloatTy);
            FloatTy tmpval_16683 = *(FloatTy *) tmpcur_16682;
            CursorTy tmpcur_16684 = tmpcur_16682 + sizeof(FloatTy);
            IntTy tmpval_16685 = *(IntTy *) tmpcur_16684;
            CursorTy tmpcur_16686 = tmpcur_16684 + sizeof(IntTy);
            FloatTy tmpval_16687 = *(FloatTy *) tmpcur_16686;
            CursorTy tmpcur_16688 = tmpcur_16686 + sizeof(FloatTy);
            CursorTy jump_12579 = tmpcur_16686 + 4;
            CursorTy jump_12578 = tmpcur_16684 + 8;
            CursorTy jump_12577 = tmpcur_16682 + 4;
            CursorTy jump_12576 = tmpcur_16680 + 4;
            CursorTy jump_12575 = tmpaftercur_16678 + 4;
            CursorTy jump_12574 = tmpaftercur_16676 + 8;
            CursorTy jump_12573 = tmpaftercur_16674 + 8;
            CursorTy jump_12572 = tmpcur_16666 + 8;
            CursorProd tmp_struct_247 =
                        _traverse_BH_Tree(end_r_10722, tmpcur_16688);
            CursorTy pvrtmp_16689 = tmp_struct_247.field0;
            CursorProd tmp_struct_248 =
                        _traverse_BH_Tree(end_r_10722, tmpcur_16673);
            CursorTy pvrtmp_16690 = tmp_struct_248.field0;
            CursorProd tmp_struct_249 =
                        _traverse_BH_Tree(end_r_10722, tmpcur_16675);
            CursorTy pvrtmp_16691 = tmp_struct_249.field0;
            CursorProd tmp_struct_250 =
                        _traverse_BH_Tree(end_r_10722, tmpcur_16677);
            CursorTy pvrtmp_16692 = tmp_struct_250.field0;

            return (CursorProd) {pvrtmp_16692};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16693 = *(CursorTy *) tmpcur_16666;
            CursorTy tmpaftercur_16694 = tmpcur_16666 + 8;
            CursorTy jump_12860 = tmpcur_16666 + 8;
            CursorProd tmp_struct_251 =
                        _traverse_BH_Tree(end_r_10722, tmpcur_16693);
            CursorTy pvrtmp_16695 = tmp_struct_251.field0;

            return (CursorProd) {jump_12860};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16696 = *(CursorTy *) tmpcur_16666;
            CursorTy tmpaftercur_16697 = tmpcur_16666 + 8;
            CursorProd tmp_struct_252 =
                        _traverse_BH_Tree(end_r_10722, tmpcur_16696);
            CursorTy pvrtmp_16698 = tmp_struct_252.field0;

            return (CursorProd) {pvrtmp_16698};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16665");
            exit(1);
        }
    }
}
CursorProd _print_BH_Tree(CursorTy end_r_10724, CursorTy arg_4446_6377_8919)
{
    TagTyPacked tmpval_16700 = *(TagTyPacked *) arg_4446_6377_8919;
    CursorTy tmpcur_16701 = arg_4446_6377_8919 + 1;


  switch_16734:
    ;
    switch (tmpval_16700) {

      case 0:
        {
            CursorTy jump_12585 = arg_4446_6377_8919 + 1;
            unsigned char wildcard_4447_6378_8920 = print_symbol(14980);
            unsigned char wildcard_4448_6379_8921 = print_symbol(14969);

            return (CursorProd) {jump_12585};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16702 = *(FloatTy *) tmpcur_16701;
            CursorTy tmpcur_16703 = tmpcur_16701 + sizeof(FloatTy);
            FloatTy tmpval_16704 = *(FloatTy *) tmpcur_16703;
            CursorTy tmpcur_16705 = tmpcur_16703 + sizeof(FloatTy);
            FloatTy tmpval_16706 = *(FloatTy *) tmpcur_16705;
            CursorTy tmpcur_16707 = tmpcur_16705 + sizeof(FloatTy);
            CursorTy jump_12589 = tmpcur_16705 + 4;
            CursorTy jump_12588 = tmpcur_16703 + 4;
            CursorTy jump_12587 = tmpcur_16701 + 4;
            unsigned char wildcard_4455_6383_8925 = print_symbol(14979);
            unsigned char wildcard_4459_6384_8926 = print_symbol(14984);
            unsigned char y_4452_6385_8927 = printf("%.2f", tmpval_16702);
            unsigned char wildcard_4458_6386_8928 = print_symbol(14984);
            unsigned char y_4453_6387_8929 = printf("%.2f", tmpval_16704);
            unsigned char wildcard_4457_6388_8930 = print_symbol(14984);
            unsigned char y_4454_6389_8931 = printf("%.2f", tmpval_16706);
            unsigned char wildcard_4456_6390_8932 = print_symbol(14969);

            return (CursorProd) {jump_12589};
            break;
        }

      case 3:
        {
            CursorTy tmpcur_16708 = *(CursorTy *) tmpcur_16701;
            CursorTy tmpaftercur_16709 = tmpcur_16701 + 8;
            CursorTy tmpcur_16710 = *(CursorTy *) tmpaftercur_16709;
            CursorTy tmpaftercur_16711 = tmpaftercur_16709 + 8;
            CursorTy tmpcur_16712 = *(CursorTy *) tmpaftercur_16711;
            CursorTy tmpaftercur_16713 = tmpaftercur_16711 + 8;
            FloatTy tmpval_16714 = *(FloatTy *) tmpaftercur_16713;
            CursorTy tmpcur_16715 = tmpaftercur_16713 + sizeof(FloatTy);
            FloatTy tmpval_16716 = *(FloatTy *) tmpcur_16715;
            CursorTy tmpcur_16717 = tmpcur_16715 + sizeof(FloatTy);
            FloatTy tmpval_16718 = *(FloatTy *) tmpcur_16717;
            CursorTy tmpcur_16719 = tmpcur_16717 + sizeof(FloatTy);
            IntTy tmpval_16720 = *(IntTy *) tmpcur_16719;
            CursorTy tmpcur_16721 = tmpcur_16719 + sizeof(IntTy);
            FloatTy tmpval_16722 = *(FloatTy *) tmpcur_16721;
            CursorTy tmpcur_16723 = tmpcur_16721 + sizeof(FloatTy);
            CursorTy jump_12598 = tmpcur_16721 + 4;
            CursorTy jump_12597 = tmpcur_16719 + 8;
            CursorTy jump_12596 = tmpcur_16717 + 4;
            CursorTy jump_12595 = tmpcur_16715 + 4;
            CursorTy jump_12594 = tmpaftercur_16713 + 4;
            CursorTy jump_12593 = tmpaftercur_16711 + 8;
            CursorTy jump_12592 = tmpaftercur_16709 + 8;
            CursorTy jump_12591 = tmpcur_16701 + 8;
            unsigned char wildcard_4478_6400_8942 = print_symbol(14978);
            unsigned char wildcard_4488_6401_8943 = print_symbol(14984);
            unsigned char y_4469_6402_8944 = printf("%.2f", tmpval_16714);
            unsigned char wildcard_4487_6403_8945 = print_symbol(14984);
            unsigned char y_4470_6404_8946 = printf("%.2f", tmpval_16716);
            unsigned char wildcard_4486_6405_8947 = print_symbol(14984);
            unsigned char y_4471_6406_8948 = printf("%.2f", tmpval_16718);
            unsigned char wildcard_4485_6407_8949 = print_symbol(14984);
            unsigned char y_4472_6408_8950 = printf("%lld", tmpval_16720);
            unsigned char wildcard_4484_6409_8951 = print_symbol(14984);
            unsigned char y_4473_6410_8952 = printf("%.2f", tmpval_16722);
            unsigned char wildcard_4483_6411_8953 = print_symbol(14984);
            CursorProd tmp_struct_253 =
                        _print_BH_Tree(end_r_10724, tmpcur_16723);
            CursorTy pvrtmp_16724 = tmp_struct_253.field0;
            unsigned char wildcard_4482_6413_8955 = print_symbol(14984);
            CursorProd tmp_struct_254 =
                        _print_BH_Tree(end_r_10724, tmpcur_16708);
            CursorTy pvrtmp_16725 = tmp_struct_254.field0;
            unsigned char wildcard_4481_6415_8957 = print_symbol(14984);
            CursorProd tmp_struct_255 =
                        _print_BH_Tree(end_r_10724, tmpcur_16710);
            CursorTy pvrtmp_16726 = tmp_struct_255.field0;
            unsigned char wildcard_4480_6417_8959 = print_symbol(14984);
            CursorProd tmp_struct_256 =
                        _print_BH_Tree(end_r_10724, tmpcur_16712);
            CursorTy pvrtmp_16727 = tmp_struct_256.field0;
            unsigned char wildcard_4479_6419_8961 = print_symbol(14969);

            return (CursorProd) {pvrtmp_16727};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16728 = *(CursorTy *) tmpcur_16701;
            CursorTy tmpaftercur_16729 = tmpcur_16701 + 8;
            CursorTy jump_12866 = tmpcur_16701 + 8;
            unsigned char wildcard_12869 = print_symbol(14983);
            CursorProd tmp_struct_257 =
                        _print_BH_Tree(end_r_10724, tmpcur_16728);
            CursorTy pvrtmp_16730 = tmp_struct_257.field0;

            return (CursorProd) {jump_12866};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16731 = *(CursorTy *) tmpcur_16701;
            CursorTy tmpaftercur_16732 = tmpcur_16701 + 8;
            unsigned char wildcard_12869 = print_symbol(14982);
            CursorProd tmp_struct_258 =
                        _print_BH_Tree(end_r_10724, tmpcur_16731);
            CursorTy pvrtmp_16733 = tmp_struct_258.field0;

            return (CursorProd) {pvrtmp_16733};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16700");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Exp(CursorTy end_r_10727,
                                       CursorTy end_r_10728, CursorTy loc_10726,
                                       CursorTy arg_4489_6420_8962)
{
    if (loc_10726 + 32 > end_r_10728) {
        ChunkTy new_chunk_267 = alloc_chunk(end_r_10728);
        CursorTy chunk_start_268 = new_chunk_267.chunk_start;
        CursorTy chunk_end_269 = new_chunk_267.chunk_end;

        end_r_10728 = chunk_end_269;
        *(TagTyPacked *) loc_10726 = 255;

        CursorTy redir = loc_10726 + 1;

        *(CursorTy *) redir = chunk_start_268;
        loc_10726 = chunk_start_268;
    }

    TagTyPacked tmpval_16735 = *(TagTyPacked *) arg_4489_6420_8962;
    CursorTy tmpcur_16736 = arg_4489_6420_8962 + 1;


  switch_16835:
    ;
    switch (tmpval_16735) {

      case 0:
        {
            IntTy tmpval_16737 = *(IntTy *) tmpcur_16736;
            CursorTy tmpcur_16738 = tmpcur_16736 + sizeof(IntTy);
            CursorTy jump_12604 = tmpcur_16736 + 8;

            *(TagTyPacked *) loc_10726 = 0;

            CursorTy writetag_13750 = loc_10726 + 1;

            *(IntTy *) writetag_13750 = tmpval_16737;

            CursorTy writecur_13751 = writetag_13750 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_10728, jump_12604,
                                                   loc_10726, writecur_13751};
            break;
        }

      case 1:
        {
            CursorTy jump_12606 = arg_4489_6420_8962 + 1;

            *(TagTyPacked *) loc_10726 = 1;

            CursorTy writetag_13754 = loc_10726 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10728, jump_12606,
                                                   loc_10726, writetag_13754};
            break;
        }

      case 2:
        {
            CursorTy jump_12608 = arg_4489_6420_8962 + 1;

            *(TagTyPacked *) loc_10726 = 2;

            CursorTy writetag_13757 = loc_10726 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10728, jump_12608,
                                                   loc_10726, writetag_13757};
            break;
        }

      case 3:
        {
            CursorTy loc_11753 = loc_10726 + 1;
            CursorCursorCursorCursorProd tmp_struct_259 =
                                          _copy_Exp(end_r_10727, end_r_10728, loc_11753, tmpcur_16736);
            CursorTy pvrtmp_16751 = tmp_struct_259.field0;
            CursorTy pvrtmp_16752 = tmp_struct_259.field1;
            CursorTy pvrtmp_16753 = tmp_struct_259.field2;
            CursorTy pvrtmp_16754 = tmp_struct_259.field3;
            CursorCursorCursorCursorProd tmp_struct_260 =
                                          _copy_Exp(end_r_10727, pvrtmp_16751, pvrtmp_16754, pvrtmp_16752);
            CursorTy pvrtmp_16759 = tmp_struct_260.field0;
            CursorTy pvrtmp_16760 = tmp_struct_260.field1;
            CursorTy pvrtmp_16761 = tmp_struct_260.field2;
            CursorTy pvrtmp_16762 = tmp_struct_260.field3;

            *(TagTyPacked *) loc_10726 = 3;

            CursorTy writetag_13762 = loc_10726 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_16759, pvrtmp_16760,
                                                   loc_10726, pvrtmp_16762};
            break;
        }

      case 4:
        {
            CursorTy loc_11765 = loc_10726 + 1;
            CursorCursorCursorCursorProd tmp_struct_261 =
                                          _copy_Exp(end_r_10727, end_r_10728, loc_11765, tmpcur_16736);
            CursorTy pvrtmp_16771 = tmp_struct_261.field0;
            CursorTy pvrtmp_16772 = tmp_struct_261.field1;
            CursorTy pvrtmp_16773 = tmp_struct_261.field2;
            CursorTy pvrtmp_16774 = tmp_struct_261.field3;
            CursorCursorCursorCursorProd tmp_struct_262 =
                                          _copy_Exp(end_r_10727, pvrtmp_16771, pvrtmp_16774, pvrtmp_16772);
            CursorTy pvrtmp_16779 = tmp_struct_262.field0;
            CursorTy pvrtmp_16780 = tmp_struct_262.field1;
            CursorTy pvrtmp_16781 = tmp_struct_262.field2;
            CursorTy pvrtmp_16782 = tmp_struct_262.field3;

            *(TagTyPacked *) loc_10726 = 4;

            CursorTy writetag_13769 = loc_10726 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_16779, pvrtmp_16780,
                                                   loc_10726, pvrtmp_16782};
            break;
        }

      case 5:
        {
            CursorTy loc_11777 = loc_10726 + 1;
            CursorCursorCursorCursorProd tmp_struct_263 =
                                          _copy_Exp(end_r_10727, end_r_10728, loc_11777, tmpcur_16736);
            CursorTy pvrtmp_16791 = tmp_struct_263.field0;
            CursorTy pvrtmp_16792 = tmp_struct_263.field1;
            CursorTy pvrtmp_16793 = tmp_struct_263.field2;
            CursorTy pvrtmp_16794 = tmp_struct_263.field3;
            CursorCursorCursorCursorProd tmp_struct_264 =
                                          _copy_Exp(end_r_10727, pvrtmp_16791, pvrtmp_16794, pvrtmp_16792);
            CursorTy pvrtmp_16799 = tmp_struct_264.field0;
            CursorTy pvrtmp_16800 = tmp_struct_264.field1;
            CursorTy pvrtmp_16801 = tmp_struct_264.field2;
            CursorTy pvrtmp_16802 = tmp_struct_264.field3;

            *(TagTyPacked *) loc_10726 = 5;

            CursorTy writetag_13776 = loc_10726 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_16799, pvrtmp_16800,
                                                   loc_10726, pvrtmp_16802};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16811 = *(CursorTy *) tmpcur_16736;
            CursorTy tmpaftercur_16812 = tmpcur_16736 + 8;
            CursorTy jump_12872 = tmpcur_16736 + 8;
            CursorCursorCursorCursorProd tmp_struct_265 =
                                          _copy_Exp(end_r_10727, end_r_10728, loc_10726, tmpcur_16811);
            CursorTy pvrtmp_16813 = tmp_struct_265.field0;
            CursorTy pvrtmp_16814 = tmp_struct_265.field1;
            CursorTy pvrtmp_16815 = tmp_struct_265.field2;
            CursorTy pvrtmp_16816 = tmp_struct_265.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16813, jump_12872,
                                                   pvrtmp_16815, pvrtmp_16816};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16823 = *(CursorTy *) tmpcur_16736;
            CursorTy tmpaftercur_16824 = tmpcur_16736 + 8;
            CursorCursorCursorCursorProd tmp_struct_266 =
                                          _copy_Exp(end_r_10727, end_r_10728, loc_10726, tmpcur_16823);
            CursorTy pvrtmp_16825 = tmp_struct_266.field0;
            CursorTy pvrtmp_16826 = tmp_struct_266.field1;
            CursorTy pvrtmp_16827 = tmp_struct_266.field2;
            CursorTy pvrtmp_16828 = tmp_struct_266.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16825, pvrtmp_16826,
                                                   pvrtmp_16827, pvrtmp_16828};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16735");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Exp(CursorTy end_r_10731,
                                                    CursorTy end_r_10732,
                                                    CursorTy loc_10730,
                                                    CursorTy arg_4504_6435_8977)
{
    TagTyPacked tmpval_16836 = *(TagTyPacked *) arg_4504_6435_8977;
    CursorTy tmpcur_16837 = arg_4504_6435_8977 + 1;


  switch_16936:
    ;
    switch (tmpval_16836) {

      case 0:
        {
            IntTy tmpval_16838 = *(IntTy *) tmpcur_16837;
            CursorTy tmpcur_16839 = tmpcur_16837 + sizeof(IntTy);
            CursorTy jump_12619 = tmpcur_16837 + 8;

            *(TagTyPacked *) loc_10730 = 0;

            CursorTy writetag_13788 = loc_10730 + 1;

            *(IntTy *) writetag_13788 = tmpval_16838;

            CursorTy writecur_13789 = writetag_13788 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_10732, jump_12619,
                                                   loc_10730, writecur_13789};
            break;
        }

      case 1:
        {
            CursorTy jump_12621 = arg_4504_6435_8977 + 1;

            *(TagTyPacked *) loc_10730 = 1;

            CursorTy writetag_13792 = loc_10730 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10732, jump_12621,
                                                   loc_10730, writetag_13792};
            break;
        }

      case 2:
        {
            CursorTy jump_12623 = arg_4504_6435_8977 + 1;

            *(TagTyPacked *) loc_10730 = 2;

            CursorTy writetag_13795 = loc_10730 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10732, jump_12623,
                                                   loc_10730, writetag_13795};
            break;
        }

      case 3:
        {
            CursorTy loc_11797 = loc_10730 + 1;
            CursorCursorCursorCursorProd tmp_struct_270 =
                                          _copy_without_ptrs_Exp(end_r_10731, end_r_10732, loc_11797, tmpcur_16837);
            CursorTy pvrtmp_16852 = tmp_struct_270.field0;
            CursorTy pvrtmp_16853 = tmp_struct_270.field1;
            CursorTy pvrtmp_16854 = tmp_struct_270.field2;
            CursorTy pvrtmp_16855 = tmp_struct_270.field3;
            CursorCursorCursorCursorProd tmp_struct_271 =
                                          _copy_without_ptrs_Exp(end_r_10731, pvrtmp_16852, pvrtmp_16855, pvrtmp_16853);
            CursorTy pvrtmp_16860 = tmp_struct_271.field0;
            CursorTy pvrtmp_16861 = tmp_struct_271.field1;
            CursorTy pvrtmp_16862 = tmp_struct_271.field2;
            CursorTy pvrtmp_16863 = tmp_struct_271.field3;

            *(TagTyPacked *) loc_10730 = 3;

            CursorTy writetag_13800 = loc_10730 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_16860, pvrtmp_16861,
                                                   loc_10730, pvrtmp_16863};
            break;
        }

      case 4:
        {
            CursorTy loc_11809 = loc_10730 + 1;
            CursorCursorCursorCursorProd tmp_struct_272 =
                                          _copy_without_ptrs_Exp(end_r_10731, end_r_10732, loc_11809, tmpcur_16837);
            CursorTy pvrtmp_16872 = tmp_struct_272.field0;
            CursorTy pvrtmp_16873 = tmp_struct_272.field1;
            CursorTy pvrtmp_16874 = tmp_struct_272.field2;
            CursorTy pvrtmp_16875 = tmp_struct_272.field3;
            CursorCursorCursorCursorProd tmp_struct_273 =
                                          _copy_without_ptrs_Exp(end_r_10731, pvrtmp_16872, pvrtmp_16875, pvrtmp_16873);
            CursorTy pvrtmp_16880 = tmp_struct_273.field0;
            CursorTy pvrtmp_16881 = tmp_struct_273.field1;
            CursorTy pvrtmp_16882 = tmp_struct_273.field2;
            CursorTy pvrtmp_16883 = tmp_struct_273.field3;

            *(TagTyPacked *) loc_10730 = 4;

            CursorTy writetag_13807 = loc_10730 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_16880, pvrtmp_16881,
                                                   loc_10730, pvrtmp_16883};
            break;
        }

      case 5:
        {
            CursorTy loc_11821 = loc_10730 + 1;
            CursorCursorCursorCursorProd tmp_struct_274 =
                                          _copy_without_ptrs_Exp(end_r_10731, end_r_10732, loc_11821, tmpcur_16837);
            CursorTy pvrtmp_16892 = tmp_struct_274.field0;
            CursorTy pvrtmp_16893 = tmp_struct_274.field1;
            CursorTy pvrtmp_16894 = tmp_struct_274.field2;
            CursorTy pvrtmp_16895 = tmp_struct_274.field3;
            CursorCursorCursorCursorProd tmp_struct_275 =
                                          _copy_without_ptrs_Exp(end_r_10731, pvrtmp_16892, pvrtmp_16895, pvrtmp_16893);
            CursorTy pvrtmp_16900 = tmp_struct_275.field0;
            CursorTy pvrtmp_16901 = tmp_struct_275.field1;
            CursorTy pvrtmp_16902 = tmp_struct_275.field2;
            CursorTy pvrtmp_16903 = tmp_struct_275.field3;

            *(TagTyPacked *) loc_10730 = 5;

            CursorTy writetag_13814 = loc_10730 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_16900, pvrtmp_16901,
                                                   loc_10730, pvrtmp_16903};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16912 = *(CursorTy *) tmpcur_16837;
            CursorTy tmpaftercur_16913 = tmpcur_16837 + 8;
            CursorTy jump_12878 = tmpcur_16837 + 8;
            CursorCursorCursorCursorProd tmp_struct_276 =
                                          _copy_without_ptrs_Exp(end_r_10731, end_r_10732, loc_10730, tmpcur_16912);
            CursorTy pvrtmp_16914 = tmp_struct_276.field0;
            CursorTy pvrtmp_16915 = tmp_struct_276.field1;
            CursorTy pvrtmp_16916 = tmp_struct_276.field2;
            CursorTy pvrtmp_16917 = tmp_struct_276.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16914, jump_12878,
                                                   pvrtmp_16916, pvrtmp_16917};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16924 = *(CursorTy *) tmpcur_16837;
            CursorTy tmpaftercur_16925 = tmpcur_16837 + 8;
            CursorCursorCursorCursorProd tmp_struct_277 =
                                          _copy_without_ptrs_Exp(end_r_10731, end_r_10732, loc_10730, tmpcur_16924);
            CursorTy pvrtmp_16926 = tmp_struct_277.field0;
            CursorTy pvrtmp_16927 = tmp_struct_277.field1;
            CursorTy pvrtmp_16928 = tmp_struct_277.field2;
            CursorTy pvrtmp_16929 = tmp_struct_277.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_16926, pvrtmp_16927,
                                                   pvrtmp_16928, pvrtmp_16929};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16836");
            exit(1);
        }
    }
}
CursorProd _traverse_Exp(CursorTy end_r_10734, CursorTy arg_4519_6450_8992)
{
    TagTyPacked tmpval_16937 = *(TagTyPacked *) arg_4519_6450_8992;
    CursorTy tmpcur_16938 = arg_4519_6450_8992 + 1;


  switch_16953:
    ;
    switch (tmpval_16937) {

      case 0:
        {
            IntTy tmpval_16939 = *(IntTy *) tmpcur_16938;
            CursorTy tmpcur_16940 = tmpcur_16938 + sizeof(IntTy);
            CursorTy jump_12634 = tmpcur_16938 + 8;

            return (CursorProd) {jump_12634};
            break;
        }

      case 1:
        {
            CursorTy jump_12636 = arg_4519_6450_8992 + 1;

            return (CursorProd) {jump_12636};
            break;
        }

      case 2:
        {
            CursorTy jump_12638 = arg_4519_6450_8992 + 1;

            return (CursorProd) {jump_12638};
            break;
        }

      case 3:
        {
            CursorProd tmp_struct_278 =
                        _traverse_Exp(end_r_10734, tmpcur_16938);
            CursorTy pvrtmp_16941 = tmp_struct_278.field0;
            CursorProd tmp_struct_279 =
                        _traverse_Exp(end_r_10734, pvrtmp_16941);
            CursorTy pvrtmp_16942 = tmp_struct_279.field0;

            return (CursorProd) {pvrtmp_16942};
            break;
        }

      case 4:
        {
            CursorProd tmp_struct_280 =
                        _traverse_Exp(end_r_10734, tmpcur_16938);
            CursorTy pvrtmp_16943 = tmp_struct_280.field0;
            CursorProd tmp_struct_281 =
                        _traverse_Exp(end_r_10734, pvrtmp_16943);
            CursorTy pvrtmp_16944 = tmp_struct_281.field0;

            return (CursorProd) {pvrtmp_16944};
            break;
        }

      case 5:
        {
            CursorProd tmp_struct_282 =
                        _traverse_Exp(end_r_10734, tmpcur_16938);
            CursorTy pvrtmp_16945 = tmp_struct_282.field0;
            CursorProd tmp_struct_283 =
                        _traverse_Exp(end_r_10734, pvrtmp_16945);
            CursorTy pvrtmp_16946 = tmp_struct_283.field0;

            return (CursorProd) {pvrtmp_16946};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16947 = *(CursorTy *) tmpcur_16938;
            CursorTy tmpaftercur_16948 = tmpcur_16938 + 8;
            CursorTy jump_12884 = tmpcur_16938 + 8;
            CursorProd tmp_struct_284 =
                        _traverse_Exp(end_r_10734, tmpcur_16947);
            CursorTy pvrtmp_16949 = tmp_struct_284.field0;

            return (CursorProd) {jump_12884};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16950 = *(CursorTy *) tmpcur_16938;
            CursorTy tmpaftercur_16951 = tmpcur_16938 + 8;
            CursorProd tmp_struct_285 =
                        _traverse_Exp(end_r_10734, tmpcur_16950);
            CursorTy pvrtmp_16952 = tmp_struct_285.field0;

            return (CursorProd) {pvrtmp_16952};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16937");
            exit(1);
        }
    }
}
CursorProd _print_Exp(CursorTy end_r_10736, CursorTy arg_4534_6464_9006)
{
    TagTyPacked tmpval_16954 = *(TagTyPacked *) arg_4534_6464_9006;
    CursorTy tmpcur_16955 = arg_4534_6464_9006 + 1;


  switch_16970:
    ;
    switch (tmpval_16954) {

      case 0:
        {
            IntTy tmpval_16956 = *(IntTy *) tmpcur_16955;
            CursorTy tmpcur_16957 = tmpcur_16955 + sizeof(IntTy);
            CursorTy jump_12649 = tmpcur_16955 + 8;
            unsigned char wildcard_4537_6466_9008 = print_symbol(14974);
            unsigned char wildcard_4539_6467_9009 = print_symbol(14984);
            unsigned char y_4536_6468_9010 = printf("%lld", tmpval_16956);
            unsigned char wildcard_4538_6469_9011 = print_symbol(14969);

            return (CursorProd) {jump_12649};
            break;
        }

      case 1:
        {
            CursorTy jump_12651 = arg_4534_6464_9006 + 1;
            unsigned char wildcard_4540_6470_9012 = print_symbol(14972);
            unsigned char wildcard_4541_6471_9013 = print_symbol(14969);

            return (CursorProd) {jump_12651};
            break;
        }

      case 2:
        {
            CursorTy jump_12653 = arg_4534_6464_9006 + 1;
            unsigned char wildcard_4542_6472_9014 = print_symbol(14973);
            unsigned char wildcard_4543_6473_9015 = print_symbol(14969);

            return (CursorProd) {jump_12653};
            break;
        }

      case 3:
        {
            unsigned char wildcard_4548_6476_9018 = print_symbol(14970);
            unsigned char wildcard_4551_6477_9019 = print_symbol(14984);
            CursorProd tmp_struct_286 =  _print_Exp(end_r_10736, tmpcur_16955);
            CursorTy pvrtmp_16958 = tmp_struct_286.field0;
            unsigned char wildcard_4550_6479_9021 = print_symbol(14984);
            CursorProd tmp_struct_287 =  _print_Exp(end_r_10736, pvrtmp_16958);
            CursorTy pvrtmp_16959 = tmp_struct_287.field0;
            unsigned char wildcard_4549_6481_9023 = print_symbol(14969);

            return (CursorProd) {pvrtmp_16959};
            break;
        }

      case 4:
        {
            unsigned char wildcard_4556_6484_9026 = print_symbol(14981);
            unsigned char wildcard_4559_6485_9027 = print_symbol(14984);
            CursorProd tmp_struct_288 =  _print_Exp(end_r_10736, tmpcur_16955);
            CursorTy pvrtmp_16960 = tmp_struct_288.field0;
            unsigned char wildcard_4558_6487_9029 = print_symbol(14984);
            CursorProd tmp_struct_289 =  _print_Exp(end_r_10736, pvrtmp_16960);
            CursorTy pvrtmp_16961 = tmp_struct_289.field0;
            unsigned char wildcard_4557_6489_9031 = print_symbol(14969);

            return (CursorProd) {pvrtmp_16961};
            break;
        }

      case 5:
        {
            unsigned char wildcard_4564_6492_9034 = print_symbol(14971);
            unsigned char wildcard_4567_6493_9035 = print_symbol(14984);
            CursorProd tmp_struct_290 =  _print_Exp(end_r_10736, tmpcur_16955);
            CursorTy pvrtmp_16962 = tmp_struct_290.field0;
            unsigned char wildcard_4566_6495_9037 = print_symbol(14984);
            CursorProd tmp_struct_291 =  _print_Exp(end_r_10736, pvrtmp_16962);
            CursorTy pvrtmp_16963 = tmp_struct_291.field0;
            unsigned char wildcard_4565_6497_9039 = print_symbol(14969);

            return (CursorProd) {pvrtmp_16963};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_16964 = *(CursorTy *) tmpcur_16955;
            CursorTy tmpaftercur_16965 = tmpcur_16955 + 8;
            CursorTy jump_12890 = tmpcur_16955 + 8;
            unsigned char wildcard_12893 = print_symbol(14983);
            CursorProd tmp_struct_292 =  _print_Exp(end_r_10736, tmpcur_16964);
            CursorTy pvrtmp_16966 = tmp_struct_292.field0;

            return (CursorProd) {jump_12890};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_16967 = *(CursorTy *) tmpcur_16955;
            CursorTy tmpaftercur_16968 = tmpcur_16955 + 8;
            unsigned char wildcard_12893 = print_symbol(14982);
            CursorProd tmp_struct_293 =  _print_Exp(end_r_10736, tmpcur_16967);
            CursorTy pvrtmp_16969 = tmp_struct_293.field0;

            return (CursorProd) {pvrtmp_16969};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16954");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_KdTree(CursorTy end_r_10739,
                                                              CursorTy end_r_10740,
                                                              CursorTy loc_10738,
                                                              CursorTy arg_10456)
{
    if (loc_10738 + 73 > end_r_10740) {
        ChunkTy new_chunk_298 = alloc_chunk(end_r_10740);
        CursorTy chunk_start_299 = new_chunk_298.chunk_start;
        CursorTy chunk_end_300 = new_chunk_298.chunk_end;

        end_r_10740 = chunk_end_300;
        *(TagTyPacked *) loc_10738 = 255;

        CursorTy redir = loc_10738 + 1;

        *(CursorTy *) redir = chunk_start_299;
        loc_10738 = chunk_start_299;
    }

    CursorTy loc_11901 = loc_10738 + 1;
    CursorTy loc_11902 = loc_11901 + 8;
    CursorTy loc_11903 = loc_11902 + 8;
    CursorTy loc_11904 = loc_11903 + 4;
    CursorTy loc_11905 = loc_11904 + 4;
    CursorTy loc_11906 = loc_11905 + 4;
    CursorTy loc_11907 = loc_11906 + 8;
    CursorTy loc_11908 = loc_11907 + 8;
    CursorTy loc_11909 = loc_11908 + 4;
    CursorTy loc_11910 = loc_11909 + 4;
    CursorTy loc_11911 = loc_11910 + 4;
    CursorTy loc_11912 = loc_11911 + 4;
    CursorTy loc_11913 = loc_11912 + 4;
    CursorTy loc_11914 = loc_11913 + 4;
    CursorTy loc_11915 = loc_11914 + 4;
    TagTyPacked tmpval_16971 = *(TagTyPacked *) arg_10456;
    CursorTy tmpcur_16972 = arg_10456 + 1;


  switch_17055:
    ;
    switch (tmpval_16971) {

      case 0:
        {
            FloatTy tmpval_16973 = *(FloatTy *) tmpcur_16972;
            CursorTy tmpcur_16974 = tmpcur_16972 + sizeof(FloatTy);
            FloatTy tmpval_16975 = *(FloatTy *) tmpcur_16974;
            CursorTy tmpcur_16976 = tmpcur_16974 + sizeof(FloatTy);
            FloatTy tmpval_16977 = *(FloatTy *) tmpcur_16976;
            CursorTy tmpcur_16978 = tmpcur_16976 + sizeof(FloatTy);
            CursorTy jump_12666 = tmpcur_16976 + 4;
            CursorTy jump_12665 = tmpcur_16974 + 4;
            CursorTy jump_12664 = tmpcur_16972 + 4;

            *(TagTyPacked *) loc_10738 = 0;

            CursorTy writetag_13866 = loc_10738 + 1;

            *(FloatTy *) writetag_13866 = tmpval_16973;

            CursorTy writecur_13867 = writetag_13866 + sizeof(FloatTy);

            *(FloatTy *) writecur_13867 = tmpval_16975;

            CursorTy writecur_13868 = writecur_13867 + sizeof(FloatTy);

            *(FloatTy *) writecur_13868 = tmpval_16977;

            CursorTy writecur_13869 = writecur_13868 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_10740, jump_12666,
                                                   loc_10738, writecur_13869};
            break;
        }

      case 1:
        {
            FloatTy tmpval_16983 = *(FloatTy *) tmpcur_16972;
            CursorTy tmpcur_16984 = tmpcur_16972 + sizeof(FloatTy);
            FloatTy tmpval_16985 = *(FloatTy *) tmpcur_16984;
            CursorTy tmpcur_16986 = tmpcur_16984 + sizeof(FloatTy);
            FloatTy tmpval_16987 = *(FloatTy *) tmpcur_16986;
            CursorTy tmpcur_16988 = tmpcur_16986 + sizeof(FloatTy);
            IntTy tmpval_16989 = *(IntTy *) tmpcur_16988;
            CursorTy tmpcur_16990 = tmpcur_16988 + sizeof(IntTy);
            IntTy tmpval_16991 = *(IntTy *) tmpcur_16990;
            CursorTy tmpcur_16992 = tmpcur_16990 + sizeof(IntTy);
            FloatTy tmpval_16993 = *(FloatTy *) tmpcur_16992;
            CursorTy tmpcur_16994 = tmpcur_16992 + sizeof(FloatTy);
            FloatTy tmpval_16995 = *(FloatTy *) tmpcur_16994;
            CursorTy tmpcur_16996 = tmpcur_16994 + sizeof(FloatTy);
            FloatTy tmpval_16997 = *(FloatTy *) tmpcur_16996;
            CursorTy tmpcur_16998 = tmpcur_16996 + sizeof(FloatTy);
            FloatTy tmpval_16999 = *(FloatTy *) tmpcur_16998;
            CursorTy tmpcur_17000 = tmpcur_16998 + sizeof(FloatTy);
            FloatTy tmpval_17001 = *(FloatTy *) tmpcur_17000;
            CursorTy tmpcur_17002 = tmpcur_17000 + sizeof(FloatTy);
            FloatTy tmpval_17003 = *(FloatTy *) tmpcur_17002;
            CursorTy tmpcur_17004 = tmpcur_17002 + sizeof(FloatTy);
            FloatTy tmpval_17005 = *(FloatTy *) tmpcur_17004;
            CursorTy tmpcur_17006 = tmpcur_17004 + sizeof(FloatTy);
            CursorTy jump_12679 = tmpcur_17004 + 4;
            CursorTy jump_12678 = tmpcur_17002 + 4;
            CursorTy jump_12677 = tmpcur_17000 + 4;
            CursorTy jump_12676 = tmpcur_16998 + 4;
            CursorTy jump_12675 = tmpcur_16996 + 4;
            CursorTy jump_12674 = tmpcur_16994 + 4;
            CursorTy jump_12673 = tmpcur_16992 + 4;
            CursorTy jump_12672 = tmpcur_16990 + 8;
            CursorTy jump_12671 = tmpcur_16988 + 8;
            CursorTy jump_12670 = tmpcur_16986 + 4;
            CursorTy jump_12669 = tmpcur_16984 + 4;
            CursorTy jump_12668 = tmpcur_16972 + 4;
            CursorCursorCursorCursorProd tmp_struct_294 =
                                          _add_size_and_rel_offsets_KdTree(end_r_10739, end_r_10740, loc_11915, tmpcur_17006);
            CursorTy pvrtmp_17007 = tmp_struct_294.field0;
            CursorTy pvrtmp_17008 = tmp_struct_294.field1;
            CursorTy pvrtmp_17009 = tmp_struct_294.field2;
            CursorTy pvrtmp_17010 = tmp_struct_294.field3;
            CursorCursorCursorCursorProd tmp_struct_295 =
                                          _add_size_and_rel_offsets_KdTree(end_r_10739, pvrtmp_17007, pvrtmp_17010, pvrtmp_17008);
            CursorTy pvrtmp_17015 = tmp_struct_295.field0;
            CursorTy pvrtmp_17016 = tmp_struct_295.field1;
            CursorTy pvrtmp_17017 = tmp_struct_295.field2;
            CursorTy pvrtmp_17018 = tmp_struct_295.field3;
            IntTy sizeof_y_10489__10503 = pvrtmp_17010 - pvrtmp_17009;
            IntTy sizeof_y_10490__10504 = pvrtmp_17018 - pvrtmp_17017;
            IntTy fltPrm_10571 = 4 + sizeof_y_10489__10503;
            IntTy fltPrm_10570 = 4 + fltPrm_10571;
            IntTy fltPrm_10569 = 4 + fltPrm_10570;
            IntTy fltPrm_10568 = 4 + fltPrm_10569;
            IntTy fltPrm_10567 = 4 + fltPrm_10568;
            IntTy fltPrm_10566 = 4 + fltPrm_10567;
            IntTy fltPrm_10565 = 4 + fltPrm_10566;
            IntTy fltPrm_10564 = 8 + fltPrm_10565;
            IntTy fltPrm_10563 = 8 + fltPrm_10564;
            IntTy fltPrm_10562 = 4 + fltPrm_10563;
            IntTy fltPrm_10561 = 4 + fltPrm_10562;
            IntTy fltPrm_10560 = 4 + fltPrm_10561;
            IntTy offset__10505 = 0 + fltPrm_10560;
            IntTy fltPrm_10584 = sizeof_y_10489__10503 + sizeof_y_10490__10504;
            IntTy fltPrm_10583 = 4 + fltPrm_10584;
            IntTy fltPrm_10582 = 4 + fltPrm_10583;
            IntTy fltPrm_10581 = 4 + fltPrm_10582;
            IntTy fltPrm_10580 = 4 + fltPrm_10581;
            IntTy fltPrm_10579 = 4 + fltPrm_10580;
            IntTy fltPrm_10578 = 4 + fltPrm_10579;
            IntTy fltPrm_10577 = 4 + fltPrm_10578;
            IntTy fltPrm_10576 = 8 + fltPrm_10577;
            IntTy fltPrm_10575 = 8 + fltPrm_10576;
            IntTy fltPrm_10574 = 4 + fltPrm_10575;
            IntTy fltPrm_10573 = 4 + fltPrm_10574;
            IntTy fltPrm_10572 = 4 + fltPrm_10573;
            IntTy size_dcon_10506 = 9 + fltPrm_10572;

            *(TagTyPacked *) loc_10738 = 154;

            CursorTy writetag_13886 = loc_10738 + 1;

            *(IntTy *) writetag_13886 = size_dcon_10506;

            CursorTy writecur_13887 = writetag_13886 + sizeof(IntTy);

            *(IntTy *) writecur_13887 = offset__10505;

            CursorTy writecur_13888 = writecur_13887 + sizeof(IntTy);

            *(FloatTy *) writecur_13888 = tmpval_16983;

            CursorTy writecur_13889 = writecur_13888 + sizeof(FloatTy);

            *(FloatTy *) writecur_13889 = tmpval_16985;

            CursorTy writecur_13890 = writecur_13889 + sizeof(FloatTy);

            *(FloatTy *) writecur_13890 = tmpval_16987;

            CursorTy writecur_13891 = writecur_13890 + sizeof(FloatTy);

            *(IntTy *) writecur_13891 = tmpval_16989;

            CursorTy writecur_13892 = writecur_13891 + sizeof(IntTy);

            *(IntTy *) writecur_13892 = tmpval_16991;

            CursorTy writecur_13893 = writecur_13892 + sizeof(IntTy);

            *(FloatTy *) writecur_13893 = tmpval_16993;

            CursorTy writecur_13894 = writecur_13893 + sizeof(FloatTy);

            *(FloatTy *) writecur_13894 = tmpval_16995;

            CursorTy writecur_13895 = writecur_13894 + sizeof(FloatTy);

            *(FloatTy *) writecur_13895 = tmpval_16997;

            CursorTy writecur_13896 = writecur_13895 + sizeof(FloatTy);

            *(FloatTy *) writecur_13896 = tmpval_16999;

            CursorTy writecur_13897 = writecur_13896 + sizeof(FloatTy);

            *(FloatTy *) writecur_13897 = tmpval_17001;

            CursorTy writecur_13898 = writecur_13897 + sizeof(FloatTy);

            *(FloatTy *) writecur_13898 = tmpval_17003;

            CursorTy writecur_13899 = writecur_13898 + sizeof(FloatTy);

            *(FloatTy *) writecur_13899 = tmpval_17005;

            CursorTy writecur_13900 = writecur_13899 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_17015, pvrtmp_17016,
                                                   loc_10738, pvrtmp_17018};
            break;
        }

      case 2:
        {
            CursorTy jump_12683 = arg_10456 + 1;

            *(TagTyPacked *) loc_10738 = 2;

            CursorTy writetag_13905 = loc_10738 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10740, jump_12683,
                                                   loc_10738, writetag_13905};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_17031 = *(CursorTy *) tmpcur_16972;
            CursorTy tmpaftercur_17032 = tmpcur_16972 + 8;
            CursorTy jump_12896 = tmpcur_16972 + 8;
            CursorCursorCursorCursorProd tmp_struct_296 =
                                          _add_size_and_rel_offsets_KdTree(end_r_10739, end_r_10740, loc_10738, tmpcur_17031);
            CursorTy pvrtmp_17033 = tmp_struct_296.field0;
            CursorTy pvrtmp_17034 = tmp_struct_296.field1;
            CursorTy pvrtmp_17035 = tmp_struct_296.field2;
            CursorTy pvrtmp_17036 = tmp_struct_296.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_17033, jump_12896,
                                                   pvrtmp_17035, pvrtmp_17036};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_17043 = *(CursorTy *) tmpcur_16972;
            CursorTy tmpaftercur_17044 = tmpcur_16972 + 8;
            CursorCursorCursorCursorProd tmp_struct_297 =
                                          _add_size_and_rel_offsets_KdTree(end_r_10739, end_r_10740, loc_10738, tmpcur_17043);
            CursorTy pvrtmp_17045 = tmp_struct_297.field0;
            CursorTy pvrtmp_17046 = tmp_struct_297.field1;
            CursorTy pvrtmp_17047 = tmp_struct_297.field2;
            CursorTy pvrtmp_17048 = tmp_struct_297.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_17045, pvrtmp_17046,
                                                   pvrtmp_17047, pvrtmp_17048};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_16971");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_BH_Tree(CursorTy end_r_10743,
                                                               CursorTy end_r_10744,
                                                               CursorTy loc_10742,
                                                               CursorTy arg_10507)
{
    if (loc_10742 + 57 > end_r_10744) {
        ChunkTy new_chunk_307 = alloc_chunk(end_r_10744);
        CursorTy chunk_start_308 = new_chunk_307.chunk_start;
        CursorTy chunk_end_309 = new_chunk_307.chunk_end;

        end_r_10744 = chunk_end_309;
        *(TagTyPacked *) loc_10742 = 255;

        CursorTy redir = loc_10742 + 1;

        *(CursorTy *) redir = chunk_start_308;
        loc_10742 = chunk_start_308;
    }

    CursorTy loc_11984 = loc_10742 + 1;
    CursorTy loc_11985 = loc_11984 + 8;
    CursorTy loc_11986 = loc_11985 + 8;
    CursorTy loc_11987 = loc_11986 + 8;
    CursorTy loc_11988 = loc_11987 + 8;
    CursorTy loc_11989 = loc_11988 + 4;
    CursorTy loc_11990 = loc_11989 + 4;
    CursorTy loc_11991 = loc_11990 + 4;
    CursorTy loc_11992 = loc_11991 + 8;
    CursorTy loc_11993 = loc_11992 + 4;
    TagTyPacked tmpval_17056 = *(TagTyPacked *) arg_10507;
    CursorTy tmpcur_17057 = arg_10507 + 1;


  switch_17142:
    ;
    switch (tmpval_17056) {

      case 0:
        {
            CursorTy jump_12685 = arg_10507 + 1;

            *(TagTyPacked *) loc_10742 = 0;

            CursorTy writetag_13914 = loc_10742 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10744, jump_12685,
                                                   loc_10742, writetag_13914};
            break;
        }

      case 1:
        {
            FloatTy tmpval_17062 = *(FloatTy *) tmpcur_17057;
            CursorTy tmpcur_17063 = tmpcur_17057 + sizeof(FloatTy);
            FloatTy tmpval_17064 = *(FloatTy *) tmpcur_17063;
            CursorTy tmpcur_17065 = tmpcur_17063 + sizeof(FloatTy);
            FloatTy tmpval_17066 = *(FloatTy *) tmpcur_17065;
            CursorTy tmpcur_17067 = tmpcur_17065 + sizeof(FloatTy);
            CursorTy jump_12689 = tmpcur_17065 + 4;
            CursorTy jump_12688 = tmpcur_17063 + 4;
            CursorTy jump_12687 = tmpcur_17057 + 4;

            *(TagTyPacked *) loc_10742 = 1;

            CursorTy writetag_13920 = loc_10742 + 1;

            *(FloatTy *) writetag_13920 = tmpval_17062;

            CursorTy writecur_13921 = writetag_13920 + sizeof(FloatTy);

            *(FloatTy *) writecur_13921 = tmpval_17064;

            CursorTy writecur_13922 = writecur_13921 + sizeof(FloatTy);

            *(FloatTy *) writecur_13922 = tmpval_17066;

            CursorTy writecur_13923 = writecur_13922 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {end_r_10744, jump_12689,
                                                   loc_10742, writecur_13923};
            break;
        }

      case 2:
        {
            FloatTy tmpval_17072 = *(FloatTy *) tmpcur_17057;
            CursorTy tmpcur_17073 = tmpcur_17057 + sizeof(FloatTy);
            FloatTy tmpval_17074 = *(FloatTy *) tmpcur_17073;
            CursorTy tmpcur_17075 = tmpcur_17073 + sizeof(FloatTy);
            FloatTy tmpval_17076 = *(FloatTy *) tmpcur_17075;
            CursorTy tmpcur_17077 = tmpcur_17075 + sizeof(FloatTy);
            IntTy tmpval_17078 = *(IntTy *) tmpcur_17077;
            CursorTy tmpcur_17079 = tmpcur_17077 + sizeof(IntTy);
            FloatTy tmpval_17080 = *(FloatTy *) tmpcur_17079;
            CursorTy tmpcur_17081 = tmpcur_17079 + sizeof(FloatTy);
            CursorTy jump_12695 = tmpcur_17079 + 4;
            CursorTy jump_12694 = tmpcur_17077 + 8;
            CursorTy jump_12693 = tmpcur_17075 + 4;
            CursorTy jump_12692 = tmpcur_17073 + 4;
            CursorTy jump_12691 = tmpcur_17057 + 4;
            CursorCursorCursorCursorProd tmp_struct_301 =
                                          _add_size_and_rel_offsets_BH_Tree(end_r_10743, end_r_10744, loc_11993, tmpcur_17081);
            CursorTy pvrtmp_17082 = tmp_struct_301.field0;
            CursorTy pvrtmp_17083 = tmp_struct_301.field1;
            CursorTy pvrtmp_17084 = tmp_struct_301.field2;
            CursorTy pvrtmp_17085 = tmp_struct_301.field3;
            CursorCursorCursorCursorProd tmp_struct_302 =
                                          _add_size_and_rel_offsets_BH_Tree(end_r_10743, pvrtmp_17082, pvrtmp_17085, pvrtmp_17083);
            CursorTy pvrtmp_17090 = tmp_struct_302.field0;
            CursorTy pvrtmp_17091 = tmp_struct_302.field1;
            CursorTy pvrtmp_17092 = tmp_struct_302.field2;
            CursorTy pvrtmp_17093 = tmp_struct_302.field3;
            CursorCursorCursorCursorProd tmp_struct_303 =
                                          _add_size_and_rel_offsets_BH_Tree(end_r_10743, pvrtmp_17090, pvrtmp_17093, pvrtmp_17091);
            CursorTy pvrtmp_17098 = tmp_struct_303.field0;
            CursorTy pvrtmp_17099 = tmp_struct_303.field1;
            CursorTy pvrtmp_17100 = tmp_struct_303.field2;
            CursorTy pvrtmp_17101 = tmp_struct_303.field3;
            CursorCursorCursorCursorProd tmp_struct_304 =
                                          _add_size_and_rel_offsets_BH_Tree(end_r_10743, pvrtmp_17098, pvrtmp_17101, pvrtmp_17099);
            CursorTy pvrtmp_17106 = tmp_struct_304.field0;
            CursorTy pvrtmp_17107 = tmp_struct_304.field1;
            CursorTy pvrtmp_17108 = tmp_struct_304.field2;
            CursorTy pvrtmp_17109 = tmp_struct_304.field3;
            IntTy sizeof_y_10528__10537 = pvrtmp_17085 - pvrtmp_17084;
            IntTy sizeof_y_10529__10538 = pvrtmp_17093 - pvrtmp_17092;
            IntTy sizeof_y_10530__10539 = pvrtmp_17101 - pvrtmp_17100;
            IntTy sizeof_y_10531__10540 = pvrtmp_17109 - pvrtmp_17108;
            IntTy fltPrm_10589 = 4 + sizeof_y_10528__10537;
            IntTy fltPrm_10588 = 8 + fltPrm_10589;
            IntTy fltPrm_10587 = 4 + fltPrm_10588;
            IntTy fltPrm_10586 = 4 + fltPrm_10587;
            IntTy fltPrm_10585 = 4 + fltPrm_10586;
            IntTy offset__10541 = 16 + fltPrm_10585;
            IntTy fltPrm_10595 = sizeof_y_10528__10537 + sizeof_y_10529__10538;
            IntTy fltPrm_10594 = 4 + fltPrm_10595;
            IntTy fltPrm_10593 = 8 + fltPrm_10594;
            IntTy fltPrm_10592 = 4 + fltPrm_10593;
            IntTy fltPrm_10591 = 4 + fltPrm_10592;
            IntTy fltPrm_10590 = 4 + fltPrm_10591;
            IntTy offset__10542 = 8 + fltPrm_10590;
            IntTy fltPrm_10602 = sizeof_y_10529__10538 + sizeof_y_10530__10539;
            IntTy fltPrm_10601 = sizeof_y_10528__10537 + fltPrm_10602;
            IntTy fltPrm_10600 = 4 + fltPrm_10601;
            IntTy fltPrm_10599 = 8 + fltPrm_10600;
            IntTy fltPrm_10598 = 4 + fltPrm_10599;
            IntTy fltPrm_10597 = 4 + fltPrm_10598;
            IntTy fltPrm_10596 = 4 + fltPrm_10597;
            IntTy offset__10543 = 0 + fltPrm_10596;
            IntTy fltPrm_10610 = sizeof_y_10530__10539 + sizeof_y_10531__10540;
            IntTy fltPrm_10609 = sizeof_y_10529__10538 + fltPrm_10610;
            IntTy fltPrm_10608 = sizeof_y_10528__10537 + fltPrm_10609;
            IntTy fltPrm_10607 = 4 + fltPrm_10608;
            IntTy fltPrm_10606 = 8 + fltPrm_10607;
            IntTy fltPrm_10605 = 4 + fltPrm_10606;
            IntTy fltPrm_10604 = 4 + fltPrm_10605;
            IntTy fltPrm_10603 = 4 + fltPrm_10604;
            IntTy size_dcon_10544 = 25 + fltPrm_10603;

            *(TagTyPacked *) loc_10742 = 154;

            CursorTy writetag_13935 = loc_10742 + 1;

            *(IntTy *) writetag_13935 = size_dcon_10544;

            CursorTy writecur_13936 = writetag_13935 + sizeof(IntTy);

            *(IntTy *) writecur_13936 = offset__10541;

            CursorTy writecur_13937 = writecur_13936 + sizeof(IntTy);

            *(IntTy *) writecur_13937 = offset__10542;

            CursorTy writecur_13938 = writecur_13937 + sizeof(IntTy);

            *(IntTy *) writecur_13938 = offset__10543;

            CursorTy writecur_13939 = writecur_13938 + sizeof(IntTy);

            *(FloatTy *) writecur_13939 = tmpval_17072;

            CursorTy writecur_13940 = writecur_13939 + sizeof(FloatTy);

            *(FloatTy *) writecur_13940 = tmpval_17074;

            CursorTy writecur_13941 = writecur_13940 + sizeof(FloatTy);

            *(FloatTy *) writecur_13941 = tmpval_17076;

            CursorTy writecur_13942 = writecur_13941 + sizeof(FloatTy);

            *(IntTy *) writecur_13942 = tmpval_17078;

            CursorTy writecur_13943 = writecur_13942 + sizeof(IntTy);

            *(FloatTy *) writecur_13943 = tmpval_17080;

            CursorTy writecur_13944 = writecur_13943 + sizeof(FloatTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_17106, pvrtmp_17107,
                                                   loc_10742, pvrtmp_17109};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_17118 = *(CursorTy *) tmpcur_17057;
            CursorTy tmpaftercur_17119 = tmpcur_17057 + 8;
            CursorTy jump_12902 = tmpcur_17057 + 8;
            CursorCursorCursorCursorProd tmp_struct_305 =
                                          _add_size_and_rel_offsets_BH_Tree(end_r_10743, end_r_10744, loc_10742, tmpcur_17118);
            CursorTy pvrtmp_17120 = tmp_struct_305.field0;
            CursorTy pvrtmp_17121 = tmp_struct_305.field1;
            CursorTy pvrtmp_17122 = tmp_struct_305.field2;
            CursorTy pvrtmp_17123 = tmp_struct_305.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_17120, jump_12902,
                                                   pvrtmp_17122, pvrtmp_17123};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_17130 = *(CursorTy *) tmpcur_17057;
            CursorTy tmpaftercur_17131 = tmpcur_17057 + 8;
            CursorCursorCursorCursorProd tmp_struct_306 =
                                          _add_size_and_rel_offsets_BH_Tree(end_r_10743, end_r_10744, loc_10742, tmpcur_17130);
            CursorTy pvrtmp_17132 = tmp_struct_306.field0;
            CursorTy pvrtmp_17133 = tmp_struct_306.field1;
            CursorTy pvrtmp_17134 = tmp_struct_306.field2;
            CursorTy pvrtmp_17135 = tmp_struct_306.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_17132, pvrtmp_17133,
                                                   pvrtmp_17134, pvrtmp_17135};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17056");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Exp(CursorTy end_r_10747,
                                                           CursorTy end_r_10748,
                                                           CursorTy loc_10746,
                                                           CursorTy arg_10545)
{
    if (loc_10746 + 32 > end_r_10748) {
        ChunkTy new_chunk_318 = alloc_chunk(end_r_10748);
        CursorTy chunk_start_319 = new_chunk_318.chunk_start;
        CursorTy chunk_end_320 = new_chunk_318.chunk_end;

        end_r_10748 = chunk_end_320;
        *(TagTyPacked *) loc_10746 = 255;

        CursorTy redir = loc_10746 + 1;

        *(CursorTy *) redir = chunk_start_319;
        loc_10746 = chunk_start_319;
    }

    TagTyPacked tmpval_17143 = *(TagTyPacked *) arg_10545;
    CursorTy tmpcur_17144 = arg_10545 + 1;


  switch_17243:
    ;
    switch (tmpval_17143) {

      case 0:
        {
            IntTy tmpval_17145 = *(IntTy *) tmpcur_17144;
            CursorTy tmpcur_17146 = tmpcur_17144 + sizeof(IntTy);
            CursorTy jump_12701 = tmpcur_17144 + 8;

            *(TagTyPacked *) loc_10746 = 0;

            CursorTy writetag_13958 = loc_10746 + 1;

            *(IntTy *) writetag_13958 = tmpval_17145;

            CursorTy writecur_13959 = writetag_13958 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_10748, jump_12701,
                                                   loc_10746, writecur_13959};
            break;
        }

      case 1:
        {
            CursorTy jump_12703 = arg_10545 + 1;

            *(TagTyPacked *) loc_10746 = 1;

            CursorTy writetag_13962 = loc_10746 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10748, jump_12703,
                                                   loc_10746, writetag_13962};
            break;
        }

      case 2:
        {
            CursorTy jump_12705 = arg_10545 + 1;

            *(TagTyPacked *) loc_10746 = 2;

            CursorTy writetag_13965 = loc_10746 + 1;

            return (CursorCursorCursorCursorProd) {end_r_10748, jump_12705,
                                                   loc_10746, writetag_13965};
            break;
        }

      case 3:
        {
            CursorTy loc_12035 = loc_10746 + 1;
            CursorCursorCursorCursorProd tmp_struct_310 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, end_r_10748, loc_12035, tmpcur_17144);
            CursorTy pvrtmp_17159 = tmp_struct_310.field0;
            CursorTy pvrtmp_17160 = tmp_struct_310.field1;
            CursorTy pvrtmp_17161 = tmp_struct_310.field2;
            CursorTy pvrtmp_17162 = tmp_struct_310.field3;
            CursorCursorCursorCursorProd tmp_struct_311 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, pvrtmp_17159, pvrtmp_17162, pvrtmp_17160);
            CursorTy pvrtmp_17167 = tmp_struct_311.field0;
            CursorTy pvrtmp_17168 = tmp_struct_311.field1;
            CursorTy pvrtmp_17169 = tmp_struct_311.field2;
            CursorTy pvrtmp_17170 = tmp_struct_311.field3;

            *(TagTyPacked *) loc_10746 = 3;

            CursorTy writetag_13970 = loc_10746 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_17167, pvrtmp_17168,
                                                   loc_10746, pvrtmp_17170};
            break;
        }

      case 4:
        {
            CursorTy loc_12047 = loc_10746 + 1;
            CursorCursorCursorCursorProd tmp_struct_312 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, end_r_10748, loc_12047, tmpcur_17144);
            CursorTy pvrtmp_17179 = tmp_struct_312.field0;
            CursorTy pvrtmp_17180 = tmp_struct_312.field1;
            CursorTy pvrtmp_17181 = tmp_struct_312.field2;
            CursorTy pvrtmp_17182 = tmp_struct_312.field3;
            CursorCursorCursorCursorProd tmp_struct_313 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, pvrtmp_17179, pvrtmp_17182, pvrtmp_17180);
            CursorTy pvrtmp_17187 = tmp_struct_313.field0;
            CursorTy pvrtmp_17188 = tmp_struct_313.field1;
            CursorTy pvrtmp_17189 = tmp_struct_313.field2;
            CursorTy pvrtmp_17190 = tmp_struct_313.field3;

            *(TagTyPacked *) loc_10746 = 4;

            CursorTy writetag_13977 = loc_10746 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_17187, pvrtmp_17188,
                                                   loc_10746, pvrtmp_17190};
            break;
        }

      case 5:
        {
            CursorTy loc_12059 = loc_10746 + 1;
            CursorCursorCursorCursorProd tmp_struct_314 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, end_r_10748, loc_12059, tmpcur_17144);
            CursorTy pvrtmp_17199 = tmp_struct_314.field0;
            CursorTy pvrtmp_17200 = tmp_struct_314.field1;
            CursorTy pvrtmp_17201 = tmp_struct_314.field2;
            CursorTy pvrtmp_17202 = tmp_struct_314.field3;
            CursorCursorCursorCursorProd tmp_struct_315 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, pvrtmp_17199, pvrtmp_17202, pvrtmp_17200);
            CursorTy pvrtmp_17207 = tmp_struct_315.field0;
            CursorTy pvrtmp_17208 = tmp_struct_315.field1;
            CursorTy pvrtmp_17209 = tmp_struct_315.field2;
            CursorTy pvrtmp_17210 = tmp_struct_315.field3;

            *(TagTyPacked *) loc_10746 = 5;

            CursorTy writetag_13984 = loc_10746 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_17207, pvrtmp_17208,
                                                   loc_10746, pvrtmp_17210};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_17219 = *(CursorTy *) tmpcur_17144;
            CursorTy tmpaftercur_17220 = tmpcur_17144 + 8;
            CursorTy jump_12908 = tmpcur_17144 + 8;
            CursorCursorCursorCursorProd tmp_struct_316 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, end_r_10748, loc_10746, tmpcur_17219);
            CursorTy pvrtmp_17221 = tmp_struct_316.field0;
            CursorTy pvrtmp_17222 = tmp_struct_316.field1;
            CursorTy pvrtmp_17223 = tmp_struct_316.field2;
            CursorTy pvrtmp_17224 = tmp_struct_316.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_17221, jump_12908,
                                                   pvrtmp_17223, pvrtmp_17224};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_17231 = *(CursorTy *) tmpcur_17144;
            CursorTy tmpaftercur_17232 = tmpcur_17144 + 8;
            CursorCursorCursorCursorProd tmp_struct_317 =
                                          _add_size_and_rel_offsets_Exp(end_r_10747, end_r_10748, loc_10746, tmpcur_17231);
            CursorTy pvrtmp_17233 = tmp_struct_317.field0;
            CursorTy pvrtmp_17234 = tmp_struct_317.field1;
            CursorTy pvrtmp_17235 = tmp_struct_317.field2;
            CursorTy pvrtmp_17236 = tmp_struct_317.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_17233, pvrtmp_17234,
                                                   pvrtmp_17235, pvrtmp_17236};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_17143");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(14960,
               "benchrunner: select benchmark to run with --bench-prog\n");
    add_symbol(14961, "actual= ");
    add_symbol(14962, "Sum: expected= ");
    add_symbol(14963, "OK\n");
    add_symbol(14964, "Expected: ");
    add_symbol(14965, "Err\n");
    add_symbol(14966, "Counts: ");
    add_symbol(14967, "Actual: ");
    add_symbol(14968, ", ");
    add_symbol(14969, ")");
    add_symbol(14970, "(Plus");
    add_symbol(14971, "(Or");
    add_symbol(14972, "(MkTrue");
    add_symbol(14973, "(MkFalse");
    add_symbol(14974, "(Lit");
    add_symbol(14975, "(KdNode");
    add_symbol(14976, "(KdLeaf");
    add_symbol(14977, "(KdEmpty");
    add_symbol(14978, "(BH_Node");
    add_symbol(14979, "(BH_Leaf");
    add_symbol(14980, "(BH_Empty");
    add_symbol(14981, "(And");
    add_symbol(14982, " ->r ");
    add_symbol(14983, " ->i ");
    add_symbol(14984, " ");
    add_symbol(14985, "\n");

    BoolTy fltIf_7075_7390 = strcmp("seqbuildkdtree",
                                    global_bench_prog_param) == 0;

    if (fltIf_7075_7390) {
        unsigned char tailapp_12716 =  bench_seqbuildkdtree();

        printf("'#()");
        printf("\n");
        free_symtable();
        return 0;
    } else {
        BoolTy fltIf_7076_7391 = strcmp("seqcountcorr",
                                        global_bench_prog_param) == 0;

        if (fltIf_7076_7391) {
            unsigned char tailapp_12717 =  bench_seqcountcorr();

            printf("'#()");
            printf("\n");
            free_symtable();
            return 0;
        } else {
            BoolTy fltIf_7077_7392 = strcmp("seqnearest",
                                            global_bench_prog_param) == 0;

            if (fltIf_7077_7392) {
                unsigned char tailapp_12718 =  bench_seqnearest();

                printf("'#()");
                printf("\n");
                free_symtable();
                return 0;
            } else {
                BoolTy fltIf_7078_7393 = strcmp("seqbuildquadtree",
                                                global_bench_prog_param) == 0;

                if (fltIf_7078_7393) {
                    unsigned char tailapp_12719 =  bench_seqbuildquadtree();

                    printf("'#()");
                    printf("\n");
                    free_symtable();
                    return 0;
                } else {
                    BoolTy fltIf_7079_7394 = strcmp("seqbhut",
                                                    global_bench_prog_param) ==
                           0;

                    if (fltIf_7079_7394) {
                        unsigned char tailapp_12720 =  bench_seqbhut();

                        printf("'#()");
                        printf("\n");
                        free_symtable();
                        return 0;
                    } else {
                        BoolTy fltIf_7080_7395 = strcmp("seqfoldconstants",
                                                        global_bench_prog_param) ==
                               0;

                        if (fltIf_7080_7395) {
                            unsigned char tailapp_12721 =
                                           bench_seqfoldconstants();

                            printf("'#()");
                            printf("\n");
                            free_symtable();
                            return 0;
                        } else {
                            unsigned char tailprim_12722 = print_symbol(14960);

                            printf("'#()");
                            printf("\n");
                            free_symtable();
                            return 0;
                        }
                    }
                }
            }
        }
    }
}
