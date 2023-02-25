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
    heap = malloc(total_size);
    // if (size <= NURSERY_ALLOC_UPPER_BOUND) {
    //     heap = ALLOC_PACKED_SMALL(total_size);
    //     if (heap == NULL) {
    //         heap = malloc(total_size);
    //         nursery_allocated = false;
    //     }
    // } else {
    //     heap = ALLOC_PACKED_BIG(total_size);
    //     nursery_allocated = false;
    // }
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
typedef struct Int64Int64Prod_struct {
            IntTy field0;
            IntTy field1;
        } Int64Int64Prod;
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
CursorInt64Prod lenA(CursorTy end_r_1153, CursorTy ls_65_488_675);
CursorProd check_coins(CursorTy end_r_1155, IntTy amt_70_493_682,
                       CursorTy tr_71_494_683);
CursorCursorCursorProd payA_seq(CursorTy end_r_1158, CursorTy end_r_1159,
                                CursorTy loc_1157, IntTy amt_77_500_692,
                                CursorTy coins_78_501_693);
CursorCursorCursorProd getCoins1(CursorTy end_r_1162, CursorTy end_r_1163,
                                 CursorTy loc_1161, IntTy c_95_518_705,
                                 IntTy q_96_519_706,
                                 CursorTy coins_rst_97_520_707);
unsigned char print_check(BoolTy b_110_521_711);
static inline
Int64Int64Prod head_plist_282(CursorTy end_r_1165, CursorTy ls_106_541_714);
static inline
CursorCursorCursorProd tail_plist_283(CursorTy end_r_1168, CursorTy end_r_1169,
                                      CursorTy loc_1167,
                                      CursorTy ls_102_545_718);
static inline
BoolTy is_empty_plist_281(CursorTy end_r_1171, CursorTy ls_98_549_722);
CursorCursorCursorCursorProd _copy_AList(CursorTy end_r_1174,
                                         CursorTy end_r_1175, CursorTy loc_1173,
                                         CursorTy arg_387_553_726);
CursorCursorCursorCursorProd _copy_without_ptrs_AList(CursorTy end_r_1178,
                                                      CursorTy end_r_1179,
                                                      CursorTy loc_1177,
                                                      CursorTy arg_396_562_735);
CursorProd _traverse_AList(CursorTy end_r_1181, CursorTy arg_405_571_744);
CursorProd _print_AList(CursorTy end_r_1183, CursorTy arg_414_578_751);
CursorCursorCursorCursorProd _copy_PList_v_280(CursorTy end_r_1186,
                                               CursorTy end_r_1187,
                                               CursorTy loc_1185,
                                               CursorTy arg_433_597_770);
CursorCursorCursorCursorProd _copy_without_ptrs_PList_v_280(CursorTy end_r_1190,
                                                            CursorTy end_r_1191,
                                                            CursorTy loc_1189,
                                                            CursorTy arg_440_604_777);
CursorProd _traverse_PList_v_280(CursorTy end_r_1193, CursorTy arg_447_611_784);
CursorProd _print_PList_v_280(CursorTy end_r_1195, CursorTy arg_454_616_789);
CursorCursorCursorCursorProd _copy_Maybe_v_284(CursorTy end_r_1198,
                                               CursorTy end_r_1199,
                                               CursorTy loc_1197,
                                               CursorTy arg_468_630_803);
CursorCursorCursorCursorProd _copy_without_ptrs_Maybe_v_284(CursorTy end_r_1202,
                                                            CursorTy end_r_1203,
                                                            CursorTy loc_1201,
                                                            CursorTy arg_471_633_806);
CursorProd _traverse_Maybe_v_284(CursorTy end_r_1205, CursorTy arg_474_636_809);
CursorProd _print_Maybe_v_284(CursorTy end_r_1207, CursorTy arg_477_638_811);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_AList(CursorTy end_r_1210, CursorTy end_r_1211,
                                CursorTy loc_1209, CursorTy arg_1130);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_PList_v_280(CursorTy end_r_1214, CursorTy end_r_1215,
                                      CursorTy loc_1213, CursorTy arg_1139);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Maybe_v_284(CursorTy end_r_1218, CursorTy end_r_1219,
                                      CursorTy loc_1217, CursorTy arg_1146);
CursorInt64Prod lenA(CursorTy end_r_1153, CursorTy ls_65_488_675)
{
    TagTyPacked tmpval_2532 = *(TagTyPacked *) ls_65_488_675;
    CursorTy tmpcur_2533 = ls_65_488_675 + 1;


  switch_2550:
    ;
    switch (tmpval_2532) {

      case 0:
        {
            IntTy tmpval_2534 = *(IntTy *) tmpcur_2533;
            CursorTy tmpcur_2535 = tmpcur_2533 + sizeof(IntTy);
            CursorTy jump_1520 = tmpcur_2533 + 8;

            return (CursorInt64Prod) {jump_1520, 0};
            break;
        }

      case 1:
        {
            IntTy tmpval_2536 = *(IntTy *) tmpcur_2533;
            CursorTy tmpcur_2537 = tmpcur_2533 + sizeof(IntTy);
            CursorTy jump_1521 = tmpcur_2533 + 8;

            return (CursorInt64Prod) {jump_1521, 1};
            break;
        }

      case 2:
        {
            CursorInt64Prod tmp_struct_0 =  lenA(end_r_1153, tmpcur_2533);
            CursorTy pvrtmp_2538 = tmp_struct_0.field0;
            IntTy pvrtmp_2539 = tmp_struct_0.field1;
            CursorInt64Prod tmp_struct_1 =  lenA(end_r_1153, pvrtmp_2538);
            CursorTy pvrtmp_2540 = tmp_struct_1.field0;
            IntTy pvrtmp_2541 = tmp_struct_1.field1;
            IntTy tailprim_1524 = pvrtmp_2539 + pvrtmp_2541;

            return (CursorInt64Prod) {pvrtmp_2540, tailprim_1524};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2542 = *(CursorTy *) tmpcur_2533;
            CursorTy tmpaftercur_2543 = tmpcur_2533 + 8;
            CursorTy jump_1639 = tmpcur_2533 + 8;
            CursorInt64Prod tmp_struct_2 =  lenA(end_r_1153, tmpcur_2542);
            CursorTy pvrtmp_2544 = tmp_struct_2.field0;
            IntTy pvrtmp_2545 = tmp_struct_2.field1;

            return (CursorInt64Prod) {jump_1639, pvrtmp_2545};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2546 = *(CursorTy *) tmpcur_2533;
            CursorTy tmpaftercur_2547 = tmpcur_2533 + 8;
            CursorInt64Prod tmp_struct_3 =  lenA(end_r_1153, tmpcur_2546);
            CursorTy pvrtmp_2548 = tmp_struct_3.field0;
            IntTy pvrtmp_2549 = tmp_struct_3.field1;

            return (CursorInt64Prod) {pvrtmp_2548, pvrtmp_2549};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2532");
            exit(1);
        }
    }
}
CursorProd check_coins(CursorTy end_r_1155, IntTy amt_70_493_682,
                       CursorTy tr_71_494_683)
{
    CursorInt64Prod tmp_struct_4 =  lenA(end_r_1155, tr_71_494_683);
    CursorTy pvrtmp_2551 = tmp_struct_4.field0;
    IntTy pvrtmp_2552 = tmp_struct_4.field1;
    BoolTy fltIf_654_685 = amt_70_493_682 == 777;

    if (fltIf_654_685) {
        BoolTy fltAppE_655_686 = pvrtmp_2552 == 140899;
        unsigned char tailapp_1526 =  print_check(fltAppE_655_686);

        return (CursorProd) {pvrtmp_2551};
    } else {
        BoolTy fltIf_656_687 = amt_70_493_682 == 999;

        if (fltIf_656_687) {
            BoolTy fltAppE_657_688 = pvrtmp_2552 == 329565;
            unsigned char tailapp_1527 =  print_check(fltAppE_657_688);

            return (CursorProd) {pvrtmp_2551};
        } else {
            unsigned char wildcard__45_73_496_689 = printf("%lld", pvrtmp_2552);
            unsigned char wildcard__43_74_497_690 = print_symbol(2493);
            unsigned char tailapp_1528 =  print_check(true);

            return (CursorProd) {pvrtmp_2551};
        }
    }
}
CursorCursorCursorProd payA_seq(CursorTy end_r_1158, CursorTy end_r_1159,
                                CursorTy loc_1157, IntTy amt_77_500_692,
                                CursorTy coins_78_501_693)
{
    if (loc_1157 + 32 > end_r_1159) {
        ChunkTy new_chunk_11 = alloc_chunk(end_r_1159);
        CursorTy chunk_start_12 = new_chunk_11.chunk_start;
        CursorTy chunk_end_13 = new_chunk_11.chunk_end;

        end_r_1159 = chunk_end_13;
        *(TagTyPacked *) loc_1157 = 255;

        CursorTy redir = loc_1157 + 1;

        *(CursorTy *) redir = chunk_start_12;
        loc_1157 = chunk_start_12;
    }

    BoolTy fltIf_659_694 = amt_77_500_692 == 0;

    if (fltIf_659_694) {
        *(TagTyPacked *) loc_1157 = 1;

        CursorTy writetag_1797 = loc_1157 + 1;

        *(IntTy *) writetag_1797 = 1;

        CursorTy writecur_1798 = writetag_1797 + sizeof(IntTy);

        return (CursorCursorCursorProd) {end_r_1159, loc_1157, writecur_1798};
    } else {
        BoolTy fltIf_660_695 =
                is_empty_plist_281(end_r_1158, coins_78_501_693);

        if (fltIf_660_695) {
            *(TagTyPacked *) loc_1157 = 0;

            CursorTy writetag_1800 = loc_1157 + 1;

            *(IntTy *) writetag_1800 = 0;

            CursorTy writecur_1801 = writetag_1800 + sizeof(IntTy);

            return (CursorCursorCursorProd) {end_r_1159, loc_1157,
                                             writecur_1801};
        } else {
            RegionTy *region_2561 = alloc_region(32);
            CursorTy r_1304 = region_2561->reg_heap;
            IntTy sizeof_end_r_1304_2562 = 32;
            CursorTy end_r_1304 = r_1304 + sizeof_end_r_1304_2562;
            Int64Int64Prod tmp_struct_5 =
                            head_plist_282(end_r_1158, coins_78_501_693);
            IntTy pvrtmp_2563 = tmp_struct_5.field0;
            IntTy pvrtmp_2564 = tmp_struct_5.field1;
            CursorCursorCursorProd tmp_struct_6 =
                                    tail_plist_283(end_r_1158, end_r_1304, r_1304, coins_78_501_693);
            CursorTy pvrtmp_2565 = tmp_struct_6.field0;
            CursorTy pvrtmp_2566 = tmp_struct_6.field1;
            CursorTy pvrtmp_2567 = tmp_struct_6.field2;
            BoolTy fltIf_661_700 = pvrtmp_2563 > amt_77_500_692;

            if (fltIf_661_700) {
                CursorCursorCursorProd tmp_struct_7 =
                        payA_seq(pvrtmp_2565, end_r_1159, loc_1157, amt_77_500_692, pvrtmp_2566);
                // CursorTy pvrtmp_2572 = tmp_struct_7.field0;
                // CursorTy pvrtmp_2573 = tmp_struct_7.field1;
                // CursorTy pvrtmp_2574 = tmp_struct_7.field2;

                free_region(end_r_1304);
                return tmp_struct_7;
                // return (CursorCursorCursorProd) {pvrtmp_2572, pvrtmp_2573,
                //                                  pvrtmp_2574};
            } else {
                RegionTy *region_2581 = alloc_region(32);
                CursorTy r_1303 = region_2581->reg_heap;
                IntTy sizeof_end_r_1303_2582 = 32;
                CursorTy end_r_1303 = r_1303 + sizeof_end_r_1303_2582;
                CursorCursorCursorProd tmp_struct_8 =
                                        getCoins1(pvrtmp_2565, end_r_1303, r_1303, pvrtmp_2563, pvrtmp_2564, pvrtmp_2566);
                CursorTy pvrtmp_2583 = tmp_struct_8.field0;
                CursorTy pvrtmp_2584 = tmp_struct_8.field1;
                CursorTy pvrtmp_2585 = tmp_struct_8.field2;
                IntTy fltAppE_662_702 = amt_77_500_692 - pvrtmp_2563;
                CursorTy loc_1299 = loc_1157 + 1;
                CursorCursorCursorProd tmp_struct_9 =
                                        payA_seq(pvrtmp_2583, end_r_1159, loc_1299, fltAppE_662_702, pvrtmp_2584);
                CursorTy pvrtmp_2590 = tmp_struct_9.field0;
                CursorTy pvrtmp_2591 = tmp_struct_9.field1;
                CursorTy pvrtmp_2592 = tmp_struct_9.field2;
                CursorCursorCursorProd tmp_struct_10 =
                                        payA_seq(pvrtmp_2565, pvrtmp_2590, pvrtmp_2592, amt_77_500_692, pvrtmp_2566);
                CursorTy pvrtmp_2597 = tmp_struct_10.field0;
                CursorTy pvrtmp_2598 = tmp_struct_10.field1;
                CursorTy pvrtmp_2599 = tmp_struct_10.field2;

                *(TagTyPacked *) loc_1157 = 2;

                CursorTy writetag_1808 = loc_1157 + 1;

                free_region(end_r_1303);
                free_region(end_r_1304);
                return (CursorCursorCursorProd) {pvrtmp_2597, loc_1157,
                                                 pvrtmp_2599};
            }
        }
    }
}
CursorCursorCursorProd getCoins1(CursorTy end_r_1162, CursorTy end_r_1163,
                                 CursorTy loc_1161, IntTy c_95_518_705,
                                 IntTy q_96_519_706,
                                 CursorTy coins_rst_97_520_707)
{
    // if (loc_1161 + 32 > end_r_1163) {
    //     ChunkTy new_chunk_14 = alloc_chunk(end_r_1163);
    //     CursorTy chunk_start_15 = new_chunk_14.chunk_start;
    //     CursorTy chunk_end_16 = new_chunk_14.chunk_end;

    //     end_r_1163 = chunk_end_16;
    //     *(TagTyPacked *) loc_1161 = 255;

    //     CursorTy redir = loc_1161 + 1;

    //     *(CursorTy *) redir = chunk_start_15;
    //     loc_1161 = chunk_start_15;
    // }

    BoolTy fltIf_663_708 = q_96_519_706 == 1;

    if (fltIf_663_708) {
        bump_ref_count(end_r_1163, end_r_1162);
        *(TagTyPacked *) loc_1161 = 254;

        CursorTy writetag_1812 = loc_1161 + 1;

        *(CursorTy *) writetag_1812 = coins_rst_97_520_707;

        CursorTy writecur_1813 = writetag_1812 + 8;

        return (CursorCursorCursorProd) {end_r_1163, loc_1161, writecur_1813};
    } else {
        IntTy fltPkd_664_709 = q_96_519_706 - 1;
        CursorTy loc_1312 = loc_1161 + 1;
        CursorTy loc_1313 = loc_1312 + 8;
        CursorTy loc_1314 = loc_1313 + 8;

        bump_ref_count(end_r_1163, end_r_1162);
        *(TagTyPacked *) loc_1314 = 254;

        CursorTy writetag_1815 = loc_1314 + 1;

        *(CursorTy *) writetag_1815 = coins_rst_97_520_707;

        CursorTy writecur_1816 = writetag_1815 + 8;

        *(TagTyPacked *) loc_1161 = 1;

        CursorTy writetag_1818 = loc_1161 + 1;

        *(IntTy *) writetag_1818 = c_95_518_705;

        CursorTy writecur_1819 = writetag_1818 + sizeof(IntTy);

        *(IntTy *) writecur_1819 = fltPkd_664_709;

        CursorTy writecur_1820 = writecur_1819 + sizeof(IntTy);

        return (CursorCursorCursorProd) {end_r_1163, loc_1161, writecur_1816};
    }
}
unsigned char print_check(BoolTy b_110_521_711)
{
    if (b_110_521_711) {
        unsigned char wildcard__14_111_522_712 = print_symbol(2480);

        return 0;
    } else {
        unsigned char wildcard__16_112_523_713 = print_symbol(2481);

        return 0;
    }
}
static inline
Int64Int64Prod head_plist_282(CursorTy end_r_1165, CursorTy ls_106_541_714)
{
    TagTyPacked tmpval_2618 = *(TagTyPacked *) ls_106_541_714;
    CursorTy tmpcur_2619 = ls_106_541_714 + 1;


  switch_2634:
    ;
    switch (tmpval_2618) {

      case 1:
        {
            IntTy tmpval_2620 = *(IntTy *) tmpcur_2619;
            CursorTy tmpcur_2621 = tmpcur_2619 + sizeof(IntTy);
            IntTy tmpval_2622 = *(IntTy *) tmpcur_2621;
            CursorTy tmpcur_2623 = tmpcur_2621 + sizeof(IntTy);
            CursorTy jump_1537 = tmpcur_2621 + 8;
            CursorTy jump_1536 = tmpcur_2619 + 8;

            return (Int64Int64Prod) {tmpval_2620, tmpval_2622};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2626 = *(CursorTy *) tmpcur_2619;
            CursorTy tmpaftercur_2627 = tmpcur_2619 + 8;
            CursorTy jump_1645 = tmpcur_2619 + 8;
            Int64Int64Prod tmp_struct_17 =
                            head_plist_282(end_r_1165, tmpcur_2626);
            IntTy pvrtmp_2628 = tmp_struct_17.field0;
            IntTy pvrtmp_2629 = tmp_struct_17.field1;

            return (Int64Int64Prod) {pvrtmp_2628, pvrtmp_2629};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2630 = *(CursorTy *) tmpcur_2619;
            CursorTy tmpaftercur_2631 = tmpcur_2619 + 8;
            Int64Int64Prod tmp_struct_18 =
                            head_plist_282(end_r_1165, tmpcur_2630);
            IntTy pvrtmp_2632 = tmp_struct_18.field0;
            IntTy pvrtmp_2633 = tmp_struct_18.field1;

            return (Int64Int64Prod) {pvrtmp_2632, pvrtmp_2633};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2618");
            exit(1);
        }
    }
}
static inline
CursorCursorCursorProd tail_plist_283(CursorTy end_r_1168, CursorTy end_r_1169,
                                      CursorTy loc_1167,
                                      CursorTy ls_102_545_718)
{
    // if (loc_1167 + 32 > end_r_1169) {
    //     ChunkTy new_chunk_21 = alloc_chunk(end_r_1169);
    //     CursorTy chunk_start_22 = new_chunk_21.chunk_start;
    //     CursorTy chunk_end_23 = new_chunk_21.chunk_end;

    //     end_r_1169 = chunk_end_23;
    //     *(TagTyPacked *) loc_1167 = 255;

    //     CursorTy redir = loc_1167 + 1;

    //     *(CursorTy *) redir = chunk_start_22;
    //     loc_1167 = chunk_start_22;
    // }

    TagTyPacked tmpval_2635 = *(TagTyPacked *) ls_102_545_718;
    CursorTy tmpcur_2636 = ls_102_545_718 + 1;


  switch_2667:
    ;
    switch (tmpval_2635) {

      case 1:
        {
            IntTy tmpval_2637 = *(IntTy *) tmpcur_2636;
            CursorTy tmpcur_2638 = tmpcur_2636 + sizeof(IntTy);
            IntTy tmpval_2639 = *(IntTy *) tmpcur_2638;
            CursorTy tmpcur_2640 = tmpcur_2638 + sizeof(IntTy);
            CursorTy jump_1540 = tmpcur_2638 + 8;
            CursorTy jump_1539 = tmpcur_2636 + 8;

            bump_ref_count(end_r_1169, end_r_1168);
            *(TagTyPacked *) loc_1167 = 254;

            CursorTy writetag_1833 = loc_1167 + 1;

            *(CursorTy *) writetag_1833 = tmpcur_2640;

            CursorTy writecur_1834 = writetag_1833 + 8;

            return (CursorCursorCursorProd) {end_r_1169, loc_1167,
                                             writecur_1834};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2645 = *(CursorTy *) tmpcur_2636;
            CursorTy tmpaftercur_2646 = tmpcur_2636 + 8;
            CursorTy jump_1650 = tmpcur_2636 + 8;
            CursorCursorCursorProd tmp_struct_19 =
                                    tail_plist_283(end_r_1168, end_r_1169, loc_1167, tmpcur_2645);
            CursorTy pvrtmp_2647 = tmp_struct_19.field0;
            CursorTy pvrtmp_2648 = tmp_struct_19.field1;
            CursorTy pvrtmp_2649 = tmp_struct_19.field2;

            return (CursorCursorCursorProd) {pvrtmp_2647, pvrtmp_2648,
                                             pvrtmp_2649};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2656 = *(CursorTy *) tmpcur_2636;
            CursorTy tmpaftercur_2657 = tmpcur_2636 + 8;
            CursorCursorCursorProd tmp_struct_20 =
                                    tail_plist_283(end_r_1168, end_r_1169, loc_1167, tmpcur_2656);
            CursorTy pvrtmp_2658 = tmp_struct_20.field0;
            CursorTy pvrtmp_2659 = tmp_struct_20.field1;
            CursorTy pvrtmp_2660 = tmp_struct_20.field2;

            return (CursorCursorCursorProd) {pvrtmp_2658, pvrtmp_2659,
                                             pvrtmp_2660};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2635");
            exit(1);
        }
    }
}
static inline
BoolTy is_empty_plist_281(CursorTy end_r_1171, CursorTy ls_98_549_722)
{
    TagTyPacked tmpval_2668 = *(TagTyPacked *) ls_98_549_722;
    CursorTy tmpcur_2669 = ls_98_549_722 + 1;


  switch_2678:
    ;
    switch (tmpval_2668) {

      case 0:
        {
            CursorTy jump_1543 = ls_98_549_722 + 1;

            return true;
            break;
        }

      case 1:
        {
            IntTy tmpval_2670 = *(IntTy *) tmpcur_2669;
            CursorTy tmpcur_2671 = tmpcur_2669 + sizeof(IntTy);
            IntTy tmpval_2672 = *(IntTy *) tmpcur_2671;
            CursorTy tmpcur_2673 = tmpcur_2671 + sizeof(IntTy);
            CursorTy jump_1545 = tmpcur_2671 + 8;
            CursorTy jump_1544 = tmpcur_2669 + 8;

            return false;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2674 = *(CursorTy *) tmpcur_2669;
            CursorTy tmpaftercur_2675 = tmpcur_2669 + 8;
            CursorTy jump_1655 = tmpcur_2669 + 8;
            BoolTy call_1656 =  is_empty_plist_281(end_r_1171, tmpcur_2674);

            return call_1656;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2676 = *(CursorTy *) tmpcur_2669;
            CursorTy tmpaftercur_2677 = tmpcur_2669 + 8;
            BoolTy call_1656 =  is_empty_plist_281(end_r_1171, tmpcur_2676);

            return call_1656;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2668");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_AList(CursorTy end_r_1174,
                                         CursorTy end_r_1175, CursorTy loc_1173,
                                         CursorTy arg_387_553_726)
{
    if (loc_1173 + 32 > end_r_1175) {
        ChunkTy new_chunk_28 = alloc_chunk(end_r_1175);
        CursorTy chunk_start_29 = new_chunk_28.chunk_start;
        CursorTy chunk_end_30 = new_chunk_28.chunk_end;

        end_r_1175 = chunk_end_30;
        *(TagTyPacked *) loc_1173 = 255;

        CursorTy redir = loc_1173 + 1;

        *(CursorTy *) redir = chunk_start_29;
        loc_1173 = chunk_start_29;
    }

    TagTyPacked tmpval_2679 = *(TagTyPacked *) arg_387_553_726;
    CursorTy tmpcur_2680 = arg_387_553_726 + 1;


  switch_2737:
    ;
    switch (tmpval_2679) {

      case 0:
        {
            IntTy tmpval_2681 = *(IntTy *) tmpcur_2680;
            CursorTy tmpcur_2682 = tmpcur_2680 + sizeof(IntTy);
            CursorTy jump_1546 = tmpcur_2680 + 8;

            *(TagTyPacked *) loc_1173 = 0;

            CursorTy writetag_1852 = loc_1173 + 1;

            *(IntTy *) writetag_1852 = tmpval_2681;

            CursorTy writecur_1853 = writetag_1852 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1175, jump_1546,
                                                   loc_1173, writecur_1853};
            break;
        }

      case 1:
        {
            IntTy tmpval_2687 = *(IntTy *) tmpcur_2680;
            CursorTy tmpcur_2688 = tmpcur_2680 + sizeof(IntTy);
            CursorTy jump_1548 = tmpcur_2680 + 8;

            *(TagTyPacked *) loc_1173 = 1;

            CursorTy writetag_1857 = loc_1173 + 1;

            *(IntTy *) writetag_1857 = tmpval_2687;

            CursorTy writecur_1858 = writetag_1857 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1175, jump_1548,
                                                   loc_1173, writecur_1858};
            break;
        }

      case 2:
        {
            CursorTy loc_1353 = loc_1173 + 1;
            CursorCursorCursorCursorProd tmp_struct_24 =
                                          _copy_AList(end_r_1174, end_r_1175, loc_1353, tmpcur_2680);
            CursorTy pvrtmp_2693 = tmp_struct_24.field0;
            CursorTy pvrtmp_2694 = tmp_struct_24.field1;
            CursorTy pvrtmp_2695 = tmp_struct_24.field2;
            CursorTy pvrtmp_2696 = tmp_struct_24.field3;
            CursorCursorCursorCursorProd tmp_struct_25 =
                                          _copy_AList(end_r_1174, pvrtmp_2693, pvrtmp_2696, pvrtmp_2694);
            CursorTy pvrtmp_2701 = tmp_struct_25.field0;
            CursorTy pvrtmp_2702 = tmp_struct_25.field1;
            CursorTy pvrtmp_2703 = tmp_struct_25.field2;
            CursorTy pvrtmp_2704 = tmp_struct_25.field3;

            *(TagTyPacked *) loc_1173 = 2;

            CursorTy writetag_1863 = loc_1173 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_2701, pvrtmp_2702,
                                                   loc_1173, pvrtmp_2704};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2713 = *(CursorTy *) tmpcur_2680;
            CursorTy tmpaftercur_2714 = tmpcur_2680 + 8;
            CursorTy jump_1660 = tmpcur_2680 + 8;
            CursorCursorCursorCursorProd tmp_struct_26 =
                                          _copy_AList(end_r_1174, end_r_1175, loc_1173, tmpcur_2713);
            CursorTy pvrtmp_2715 = tmp_struct_26.field0;
            CursorTy pvrtmp_2716 = tmp_struct_26.field1;
            CursorTy pvrtmp_2717 = tmp_struct_26.field2;
            CursorTy pvrtmp_2718 = tmp_struct_26.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2715, jump_1660,
                                                   pvrtmp_2717, pvrtmp_2718};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2725 = *(CursorTy *) tmpcur_2680;
            CursorTy tmpaftercur_2726 = tmpcur_2680 + 8;
            CursorCursorCursorCursorProd tmp_struct_27 =
                                          _copy_AList(end_r_1174, end_r_1175, loc_1173, tmpcur_2725);
            CursorTy pvrtmp_2727 = tmp_struct_27.field0;
            CursorTy pvrtmp_2728 = tmp_struct_27.field1;
            CursorTy pvrtmp_2729 = tmp_struct_27.field2;
            CursorTy pvrtmp_2730 = tmp_struct_27.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2727, pvrtmp_2728,
                                                   pvrtmp_2729, pvrtmp_2730};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2679");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_AList(CursorTy end_r_1178,
                                                      CursorTy end_r_1179,
                                                      CursorTy loc_1177,
                                                      CursorTy arg_396_562_735)
{
    TagTyPacked tmpval_2738 = *(TagTyPacked *) arg_396_562_735;
    CursorTy tmpcur_2739 = arg_396_562_735 + 1;


  switch_2796:
    ;
    switch (tmpval_2738) {

      case 0:
        {
            IntTy tmpval_2740 = *(IntTy *) tmpcur_2739;
            CursorTy tmpcur_2741 = tmpcur_2739 + sizeof(IntTy);
            CursorTy jump_1553 = tmpcur_2739 + 8;

            *(TagTyPacked *) loc_1177 = 0;

            CursorTy writetag_1875 = loc_1177 + 1;

            *(IntTy *) writetag_1875 = tmpval_2740;

            CursorTy writecur_1876 = writetag_1875 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1179, jump_1553,
                                                   loc_1177, writecur_1876};
            break;
        }

      case 1:
        {
            IntTy tmpval_2746 = *(IntTy *) tmpcur_2739;
            CursorTy tmpcur_2747 = tmpcur_2739 + sizeof(IntTy);
            CursorTy jump_1555 = tmpcur_2739 + 8;

            *(TagTyPacked *) loc_1177 = 1;

            CursorTy writetag_1880 = loc_1177 + 1;

            *(IntTy *) writetag_1880 = tmpval_2746;

            CursorTy writecur_1881 = writetag_1880 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1179, jump_1555,
                                                   loc_1177, writecur_1881};
            break;
        }

      case 2:
        {
            CursorTy loc_1375 = loc_1177 + 1;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_without_ptrs_AList(end_r_1178, end_r_1179, loc_1375, tmpcur_2739);
            CursorTy pvrtmp_2752 = tmp_struct_31.field0;
            CursorTy pvrtmp_2753 = tmp_struct_31.field1;
            CursorTy pvrtmp_2754 = tmp_struct_31.field2;
            CursorTy pvrtmp_2755 = tmp_struct_31.field3;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_without_ptrs_AList(end_r_1178, pvrtmp_2752, pvrtmp_2755, pvrtmp_2753);
            CursorTy pvrtmp_2760 = tmp_struct_32.field0;
            CursorTy pvrtmp_2761 = tmp_struct_32.field1;
            CursorTy pvrtmp_2762 = tmp_struct_32.field2;
            CursorTy pvrtmp_2763 = tmp_struct_32.field3;

            *(TagTyPacked *) loc_1177 = 2;

            CursorTy writetag_1886 = loc_1177 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_2760, pvrtmp_2761,
                                                   loc_1177, pvrtmp_2763};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2772 = *(CursorTy *) tmpcur_2739;
            CursorTy tmpaftercur_2773 = tmpcur_2739 + 8;
            CursorTy jump_1666 = tmpcur_2739 + 8;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_without_ptrs_AList(end_r_1178, end_r_1179, loc_1177, tmpcur_2772);
            CursorTy pvrtmp_2774 = tmp_struct_33.field0;
            CursorTy pvrtmp_2775 = tmp_struct_33.field1;
            CursorTy pvrtmp_2776 = tmp_struct_33.field2;
            CursorTy pvrtmp_2777 = tmp_struct_33.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2774, jump_1666,
                                                   pvrtmp_2776, pvrtmp_2777};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2784 = *(CursorTy *) tmpcur_2739;
            CursorTy tmpaftercur_2785 = tmpcur_2739 + 8;
            CursorCursorCursorCursorProd tmp_struct_34 =
                                          _copy_without_ptrs_AList(end_r_1178, end_r_1179, loc_1177, tmpcur_2784);
            CursorTy pvrtmp_2786 = tmp_struct_34.field0;
            CursorTy pvrtmp_2787 = tmp_struct_34.field1;
            CursorTy pvrtmp_2788 = tmp_struct_34.field2;
            CursorTy pvrtmp_2789 = tmp_struct_34.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2786, pvrtmp_2787,
                                                   pvrtmp_2788, pvrtmp_2789};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2738");
            exit(1);
        }
    }
}
CursorProd _traverse_AList(CursorTy end_r_1181, CursorTy arg_405_571_744)
{
    TagTyPacked tmpval_2797 = *(TagTyPacked *) arg_405_571_744;
    CursorTy tmpcur_2798 = arg_405_571_744 + 1;


  switch_2811:
    ;
    switch (tmpval_2797) {

      case 0:
        {
            IntTy tmpval_2799 = *(IntTy *) tmpcur_2798;
            CursorTy tmpcur_2800 = tmpcur_2798 + sizeof(IntTy);
            CursorTy jump_1560 = tmpcur_2798 + 8;

            return (CursorProd) {jump_1560};
            break;
        }

      case 1:
        {
            IntTy tmpval_2801 = *(IntTy *) tmpcur_2798;
            CursorTy tmpcur_2802 = tmpcur_2798 + sizeof(IntTy);
            CursorTy jump_1562 = tmpcur_2798 + 8;

            return (CursorProd) {jump_1562};
            break;
        }

      case 2:
        {
            CursorProd tmp_struct_35 =
                        _traverse_AList(end_r_1181, tmpcur_2798);
            CursorTy pvrtmp_2803 = tmp_struct_35.field0;
            CursorProd tmp_struct_36 =
                        _traverse_AList(end_r_1181, pvrtmp_2803);
            CursorTy pvrtmp_2804 = tmp_struct_36.field0;

            return (CursorProd) {pvrtmp_2804};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2805 = *(CursorTy *) tmpcur_2798;
            CursorTy tmpaftercur_2806 = tmpcur_2798 + 8;
            CursorTy jump_1672 = tmpcur_2798 + 8;
            CursorProd tmp_struct_37 =
                        _traverse_AList(end_r_1181, tmpcur_2805);
            CursorTy pvrtmp_2807 = tmp_struct_37.field0;

            return (CursorProd) {jump_1672};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2808 = *(CursorTy *) tmpcur_2798;
            CursorTy tmpaftercur_2809 = tmpcur_2798 + 8;
            CursorProd tmp_struct_38 =
                        _traverse_AList(end_r_1181, tmpcur_2808);
            CursorTy pvrtmp_2810 = tmp_struct_38.field0;

            return (CursorProd) {pvrtmp_2810};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2797");
            exit(1);
        }
    }
}
CursorProd _print_AList(CursorTy end_r_1183, CursorTy arg_414_578_751)
{
    TagTyPacked tmpval_2812 = *(TagTyPacked *) arg_414_578_751;
    CursorTy tmpcur_2813 = arg_414_578_751 + 1;


  switch_2826:
    ;
    switch (tmpval_2812) {

      case 0:
        {
            IntTy tmpval_2814 = *(IntTy *) tmpcur_2813;
            CursorTy tmpcur_2815 = tmpcur_2813 + sizeof(IntTy);
            CursorTy jump_1567 = tmpcur_2813 + 8;
            unsigned char wildcard_417_580_753 = print_symbol(2489);
            unsigned char wildcard_419_581_754 = print_symbol(2492);
            unsigned char y_416_582_755 = printf("%lld", tmpval_2814);
            unsigned char wildcard_418_583_756 = print_symbol(2482);

            return (CursorProd) {jump_1567};
            break;
        }

      case 1:
        {
            IntTy tmpval_2816 = *(IntTy *) tmpcur_2813;
            CursorTy tmpcur_2817 = tmpcur_2813 + sizeof(IntTy);
            CursorTy jump_1569 = tmpcur_2813 + 8;
            unsigned char wildcard_422_585_758 = print_symbol(2488);
            unsigned char wildcard_424_586_759 = print_symbol(2492);
            unsigned char y_421_587_760 = printf("%lld", tmpval_2816);
            unsigned char wildcard_423_588_761 = print_symbol(2482);

            return (CursorProd) {jump_1569};
            break;
        }

      case 2:
        {
            unsigned char wildcard_429_591_764 = print_symbol(2487);
            unsigned char wildcard_432_592_765 = print_symbol(2492);
            CursorProd tmp_struct_39 =  _print_AList(end_r_1183, tmpcur_2813);
            CursorTy pvrtmp_2818 = tmp_struct_39.field0;
            unsigned char wildcard_431_594_767 = print_symbol(2492);
            CursorProd tmp_struct_40 =  _print_AList(end_r_1183, pvrtmp_2818);
            CursorTy pvrtmp_2819 = tmp_struct_40.field0;
            unsigned char wildcard_430_596_769 = print_symbol(2482);

            return (CursorProd) {pvrtmp_2819};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2820 = *(CursorTy *) tmpcur_2813;
            CursorTy tmpaftercur_2821 = tmpcur_2813 + 8;
            CursorTy jump_1678 = tmpcur_2813 + 8;
            unsigned char wildcard_1681 = print_symbol(2491);
            CursorProd tmp_struct_41 =  _print_AList(end_r_1183, tmpcur_2820);
            CursorTy pvrtmp_2822 = tmp_struct_41.field0;

            return (CursorProd) {jump_1678};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2823 = *(CursorTy *) tmpcur_2813;
            CursorTy tmpaftercur_2824 = tmpcur_2813 + 8;
            unsigned char wildcard_1681 = print_symbol(2490);
            CursorProd tmp_struct_42 =  _print_AList(end_r_1183, tmpcur_2823);
            CursorTy pvrtmp_2825 = tmp_struct_42.field0;

            return (CursorProd) {pvrtmp_2825};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2812");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_PList_v_280(CursorTy end_r_1186,
                                               CursorTy end_r_1187,
                                               CursorTy loc_1185,
                                               CursorTy arg_433_597_770)
{
    if (loc_1185 + 32 > end_r_1187) {
        ChunkTy new_chunk_46 = alloc_chunk(end_r_1187);
        CursorTy chunk_start_47 = new_chunk_46.chunk_start;
        CursorTy chunk_end_48 = new_chunk_46.chunk_end;

        end_r_1187 = chunk_end_48;
        *(TagTyPacked *) loc_1185 = 255;

        CursorTy redir = loc_1185 + 1;

        *(CursorTy *) redir = chunk_start_47;
        loc_1185 = chunk_start_47;
    }

    TagTyPacked tmpval_2827 = *(TagTyPacked *) arg_433_597_770;
    CursorTy tmpcur_2828 = arg_433_597_770 + 1;


  switch_2873:
    ;
    switch (tmpval_2827) {

      case 0:
        {
            CursorTy jump_1574 = arg_433_597_770 + 1;

            *(TagTyPacked *) loc_1185 = 0;

            CursorTy writetag_1923 = loc_1185 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1187, jump_1574,
                                                   loc_1185, writetag_1923};
            break;
        }

      case 1:
        {
            IntTy tmpval_2833 = *(IntTy *) tmpcur_2828;
            CursorTy tmpcur_2834 = tmpcur_2828 + sizeof(IntTy);
            IntTy tmpval_2835 = *(IntTy *) tmpcur_2834;
            CursorTy tmpcur_2836 = tmpcur_2834 + sizeof(IntTy);
            CursorTy jump_1577 = tmpcur_2834 + 8;
            CursorTy jump_1576 = tmpcur_2828 + 8;
            CursorTy loc_1408 = loc_1185 + 1;
            CursorTy loc_1409 = loc_1408 + 8;
            CursorTy loc_1410 = loc_1409 + 8;
            CursorCursorCursorCursorProd tmp_struct_43 =
                                          _copy_PList_v_280(end_r_1186, end_r_1187, loc_1410, tmpcur_2836);
            CursorTy pvrtmp_2837 = tmp_struct_43.field0;
            CursorTy pvrtmp_2838 = tmp_struct_43.field1;
            CursorTy pvrtmp_2839 = tmp_struct_43.field2;
            CursorTy pvrtmp_2840 = tmp_struct_43.field3;

            *(TagTyPacked *) loc_1185 = 1;

            CursorTy writetag_1929 = loc_1185 + 1;

            *(IntTy *) writetag_1929 = tmpval_2833;

            CursorTy writecur_1930 = writetag_1929 + sizeof(IntTy);

            *(IntTy *) writecur_1930 = tmpval_2835;

            CursorTy writecur_1931 = writecur_1930 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_2837, pvrtmp_2838,
                                                   loc_1185, pvrtmp_2840};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2849 = *(CursorTy *) tmpcur_2828;
            CursorTy tmpaftercur_2850 = tmpcur_2828 + 8;
            CursorTy jump_1684 = tmpcur_2828 + 8;
            CursorCursorCursorCursorProd tmp_struct_44 =
                                          _copy_PList_v_280(end_r_1186, end_r_1187, loc_1185, tmpcur_2849);
            CursorTy pvrtmp_2851 = tmp_struct_44.field0;
            CursorTy pvrtmp_2852 = tmp_struct_44.field1;
            CursorTy pvrtmp_2853 = tmp_struct_44.field2;
            CursorTy pvrtmp_2854 = tmp_struct_44.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2851, jump_1684,
                                                   pvrtmp_2853, pvrtmp_2854};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2861 = *(CursorTy *) tmpcur_2828;
            CursorTy tmpaftercur_2862 = tmpcur_2828 + 8;
            CursorCursorCursorCursorProd tmp_struct_45 =
                                          _copy_PList_v_280(end_r_1186, end_r_1187, loc_1185, tmpcur_2861);
            CursorTy pvrtmp_2863 = tmp_struct_45.field0;
            CursorTy pvrtmp_2864 = tmp_struct_45.field1;
            CursorTy pvrtmp_2865 = tmp_struct_45.field2;
            CursorTy pvrtmp_2866 = tmp_struct_45.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2863, pvrtmp_2864,
                                                   pvrtmp_2865, pvrtmp_2866};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2827");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_PList_v_280(CursorTy end_r_1190,
                                                            CursorTy end_r_1191,
                                                            CursorTy loc_1189,
                                                            CursorTy arg_440_604_777)
{
    TagTyPacked tmpval_2874 = *(TagTyPacked *) arg_440_604_777;
    CursorTy tmpcur_2875 = arg_440_604_777 + 1;


  switch_2920:
    ;
    switch (tmpval_2874) {

      case 0:
        {
            CursorTy jump_1580 = arg_440_604_777 + 1;

            *(TagTyPacked *) loc_1189 = 0;

            CursorTy writetag_1941 = loc_1189 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1191, jump_1580,
                                                   loc_1189, writetag_1941};
            break;
        }

      case 1:
        {
            IntTy tmpval_2880 = *(IntTy *) tmpcur_2875;
            CursorTy tmpcur_2881 = tmpcur_2875 + sizeof(IntTy);
            IntTy tmpval_2882 = *(IntTy *) tmpcur_2881;
            CursorTy tmpcur_2883 = tmpcur_2881 + sizeof(IntTy);
            CursorTy jump_1583 = tmpcur_2881 + 8;
            CursorTy jump_1582 = tmpcur_2875 + 8;
            CursorTy loc_1425 = loc_1189 + 1;
            CursorTy loc_1426 = loc_1425 + 8;
            CursorTy loc_1427 = loc_1426 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_without_ptrs_PList_v_280(end_r_1190, end_r_1191, loc_1427, tmpcur_2883);
            CursorTy pvrtmp_2884 = tmp_struct_49.field0;
            CursorTy pvrtmp_2885 = tmp_struct_49.field1;
            CursorTy pvrtmp_2886 = tmp_struct_49.field2;
            CursorTy pvrtmp_2887 = tmp_struct_49.field3;

            *(TagTyPacked *) loc_1189 = 1;

            CursorTy writetag_1947 = loc_1189 + 1;

            *(IntTy *) writetag_1947 = tmpval_2880;

            CursorTy writecur_1948 = writetag_1947 + sizeof(IntTy);

            *(IntTy *) writecur_1948 = tmpval_2882;

            CursorTy writecur_1949 = writecur_1948 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_2884, pvrtmp_2885,
                                                   loc_1189, pvrtmp_2887};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2896 = *(CursorTy *) tmpcur_2875;
            CursorTy tmpaftercur_2897 = tmpcur_2875 + 8;
            CursorTy jump_1690 = tmpcur_2875 + 8;
            CursorCursorCursorCursorProd tmp_struct_50 =
                                          _copy_without_ptrs_PList_v_280(end_r_1190, end_r_1191, loc_1189, tmpcur_2896);
            CursorTy pvrtmp_2898 = tmp_struct_50.field0;
            CursorTy pvrtmp_2899 = tmp_struct_50.field1;
            CursorTy pvrtmp_2900 = tmp_struct_50.field2;
            CursorTy pvrtmp_2901 = tmp_struct_50.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2898, jump_1690,
                                                   pvrtmp_2900, pvrtmp_2901};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2908 = *(CursorTy *) tmpcur_2875;
            CursorTy tmpaftercur_2909 = tmpcur_2875 + 8;
            CursorCursorCursorCursorProd tmp_struct_51 =
                                          _copy_without_ptrs_PList_v_280(end_r_1190, end_r_1191, loc_1189, tmpcur_2908);
            CursorTy pvrtmp_2910 = tmp_struct_51.field0;
            CursorTy pvrtmp_2911 = tmp_struct_51.field1;
            CursorTy pvrtmp_2912 = tmp_struct_51.field2;
            CursorTy pvrtmp_2913 = tmp_struct_51.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2910, pvrtmp_2911,
                                                   pvrtmp_2912, pvrtmp_2913};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2874");
            exit(1);
        }
    }
}
CursorProd _traverse_PList_v_280(CursorTy end_r_1193, CursorTy arg_447_611_784)
{
    TagTyPacked tmpval_2921 = *(TagTyPacked *) arg_447_611_784;
    CursorTy tmpcur_2922 = arg_447_611_784 + 1;


  switch_2934:
    ;
    switch (tmpval_2921) {

      case 0:
        {
            CursorTy jump_1586 = arg_447_611_784 + 1;

            return (CursorProd) {jump_1586};
            break;
        }

      case 1:
        {
            IntTy tmpval_2923 = *(IntTy *) tmpcur_2922;
            CursorTy tmpcur_2924 = tmpcur_2922 + sizeof(IntTy);
            IntTy tmpval_2925 = *(IntTy *) tmpcur_2924;
            CursorTy tmpcur_2926 = tmpcur_2924 + sizeof(IntTy);
            CursorTy jump_1589 = tmpcur_2924 + 8;
            CursorTy jump_1588 = tmpcur_2922 + 8;
            CursorProd tmp_struct_52 =
                        _traverse_PList_v_280(end_r_1193, tmpcur_2926);
            CursorTy pvrtmp_2927 = tmp_struct_52.field0;

            return (CursorProd) {pvrtmp_2927};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2928 = *(CursorTy *) tmpcur_2922;
            CursorTy tmpaftercur_2929 = tmpcur_2922 + 8;
            CursorTy jump_1696 = tmpcur_2922 + 8;
            CursorProd tmp_struct_53 =
                        _traverse_PList_v_280(end_r_1193, tmpcur_2928);
            CursorTy pvrtmp_2930 = tmp_struct_53.field0;

            return (CursorProd) {jump_1696};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2931 = *(CursorTy *) tmpcur_2922;
            CursorTy tmpaftercur_2932 = tmpcur_2922 + 8;
            CursorProd tmp_struct_54 =
                        _traverse_PList_v_280(end_r_1193, tmpcur_2931);
            CursorTy pvrtmp_2933 = tmp_struct_54.field0;

            return (CursorProd) {pvrtmp_2933};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2921");
            exit(1);
        }
    }
}
CursorProd _print_PList_v_280(CursorTy end_r_1195, CursorTy arg_454_616_789)
{
    TagTyPacked tmpval_2935 = *(TagTyPacked *) arg_454_616_789;
    CursorTy tmpcur_2936 = arg_454_616_789 + 1;


  switch_2948:
    ;
    switch (tmpval_2935) {

      case 0:
        {
            CursorTy jump_1592 = arg_454_616_789 + 1;
            unsigned char wildcard_455_617_790 = print_symbol(2484);
            unsigned char wildcard_456_618_791 = print_symbol(2482);

            return (CursorProd) {jump_1592};
            break;
        }

      case 1:
        {
            IntTy tmpval_2937 = *(IntTy *) tmpcur_2936;
            CursorTy tmpcur_2938 = tmpcur_2936 + sizeof(IntTy);
            IntTy tmpval_2939 = *(IntTy *) tmpcur_2938;
            CursorTy tmpcur_2940 = tmpcur_2938 + sizeof(IntTy);
            CursorTy jump_1595 = tmpcur_2938 + 8;
            CursorTy jump_1594 = tmpcur_2936 + 8;
            unsigned char wildcard_463_622_795 = print_symbol(2486);
            unsigned char wildcard_467_623_796 = print_symbol(2492);
            unsigned char y_460_624_797 = printf("%lld", tmpval_2937);
            unsigned char wildcard_466_625_798 = print_symbol(2492);
            unsigned char y_461_626_799 = printf("%lld", tmpval_2939);
            unsigned char wildcard_465_627_800 = print_symbol(2492);
            CursorProd tmp_struct_55 =
                        _print_PList_v_280(end_r_1195, tmpcur_2940);
            CursorTy pvrtmp_2941 = tmp_struct_55.field0;
            unsigned char wildcard_464_629_802 = print_symbol(2482);

            return (CursorProd) {pvrtmp_2941};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2942 = *(CursorTy *) tmpcur_2936;
            CursorTy tmpaftercur_2943 = tmpcur_2936 + 8;
            CursorTy jump_1702 = tmpcur_2936 + 8;
            unsigned char wildcard_1705 = print_symbol(2491);
            CursorProd tmp_struct_56 =
                        _print_PList_v_280(end_r_1195, tmpcur_2942);
            CursorTy pvrtmp_2944 = tmp_struct_56.field0;

            return (CursorProd) {jump_1702};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2945 = *(CursorTy *) tmpcur_2936;
            CursorTy tmpaftercur_2946 = tmpcur_2936 + 8;
            unsigned char wildcard_1705 = print_symbol(2490);
            CursorProd tmp_struct_57 =
                        _print_PList_v_280(end_r_1195, tmpcur_2945);
            CursorTy pvrtmp_2947 = tmp_struct_57.field0;

            return (CursorProd) {pvrtmp_2947};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2935");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Maybe_v_284(CursorTy end_r_1198,
                                               CursorTy end_r_1199,
                                               CursorTy loc_1197,
                                               CursorTy arg_468_630_803)
{
    if (loc_1197 + 32 > end_r_1199) {
        ChunkTy new_chunk_60 = alloc_chunk(end_r_1199);
        CursorTy chunk_start_61 = new_chunk_60.chunk_start;
        CursorTy chunk_end_62 = new_chunk_60.chunk_end;

        end_r_1199 = chunk_end_62;
        *(TagTyPacked *) loc_1197 = 255;

        CursorTy redir = loc_1197 + 1;

        *(CursorTy *) redir = chunk_start_61;
        loc_1197 = chunk_start_61;
    }

    TagTyPacked tmpval_2949 = *(TagTyPacked *) arg_468_630_803;
    CursorTy tmpcur_2950 = arg_468_630_803 + 1;


  switch_2985:
    ;
    switch (tmpval_2949) {

      case 0:
        {
            IntTy tmpval_2951 = *(IntTy *) tmpcur_2950;
            CursorTy tmpcur_2952 = tmpcur_2950 + sizeof(IntTy);
            CursorTy jump_1598 = tmpcur_2950 + 8;

            *(TagTyPacked *) loc_1197 = 0;

            CursorTy writetag_1982 = loc_1197 + 1;

            *(IntTy *) writetag_1982 = tmpval_2951;

            CursorTy writecur_1983 = writetag_1982 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1199, jump_1598,
                                                   loc_1197, writecur_1983};
            break;
        }

      case 1:
        {
            CursorTy jump_1600 = arg_468_630_803 + 1;

            *(TagTyPacked *) loc_1197 = 1;

            CursorTy writetag_1986 = loc_1197 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1199, jump_1600,
                                                   loc_1197, writetag_1986};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2961 = *(CursorTy *) tmpcur_2950;
            CursorTy tmpaftercur_2962 = tmpcur_2950 + 8;
            CursorTy jump_1708 = tmpcur_2950 + 8;
            CursorCursorCursorCursorProd tmp_struct_58 =
                                          _copy_Maybe_v_284(end_r_1198, end_r_1199, loc_1197, tmpcur_2961);
            CursorTy pvrtmp_2963 = tmp_struct_58.field0;
            CursorTy pvrtmp_2964 = tmp_struct_58.field1;
            CursorTy pvrtmp_2965 = tmp_struct_58.field2;
            CursorTy pvrtmp_2966 = tmp_struct_58.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2963, jump_1708,
                                                   pvrtmp_2965, pvrtmp_2966};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_2973 = *(CursorTy *) tmpcur_2950;
            CursorTy tmpaftercur_2974 = tmpcur_2950 + 8;
            CursorCursorCursorCursorProd tmp_struct_59 =
                                          _copy_Maybe_v_284(end_r_1198, end_r_1199, loc_1197, tmpcur_2973);
            CursorTy pvrtmp_2975 = tmp_struct_59.field0;
            CursorTy pvrtmp_2976 = tmp_struct_59.field1;
            CursorTy pvrtmp_2977 = tmp_struct_59.field2;
            CursorTy pvrtmp_2978 = tmp_struct_59.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_2975, pvrtmp_2976,
                                                   pvrtmp_2977, pvrtmp_2978};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2949");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Maybe_v_284(CursorTy end_r_1202,
                                                            CursorTy end_r_1203,
                                                            CursorTy loc_1201,
                                                            CursorTy arg_471_633_806)
{
    TagTyPacked tmpval_2986 = *(TagTyPacked *) arg_471_633_806;
    CursorTy tmpcur_2987 = arg_471_633_806 + 1;


  switch_3022:
    ;
    switch (tmpval_2986) {

      case 0:
        {
            IntTy tmpval_2988 = *(IntTy *) tmpcur_2987;
            CursorTy tmpcur_2989 = tmpcur_2987 + sizeof(IntTy);
            CursorTy jump_1602 = tmpcur_2987 + 8;

            *(TagTyPacked *) loc_1201 = 0;

            CursorTy writetag_1996 = loc_1201 + 1;

            *(IntTy *) writetag_1996 = tmpval_2988;

            CursorTy writecur_1997 = writetag_1996 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1203, jump_1602,
                                                   loc_1201, writecur_1997};
            break;
        }

      case 1:
        {
            CursorTy jump_1604 = arg_471_633_806 + 1;

            *(TagTyPacked *) loc_1201 = 1;

            CursorTy writetag_2000 = loc_1201 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1203, jump_1604,
                                                   loc_1201, writetag_2000};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_2998 = *(CursorTy *) tmpcur_2987;
            CursorTy tmpaftercur_2999 = tmpcur_2987 + 8;
            CursorTy jump_1714 = tmpcur_2987 + 8;
            CursorCursorCursorCursorProd tmp_struct_63 =
                                          _copy_without_ptrs_Maybe_v_284(end_r_1202, end_r_1203, loc_1201, tmpcur_2998);
            CursorTy pvrtmp_3000 = tmp_struct_63.field0;
            CursorTy pvrtmp_3001 = tmp_struct_63.field1;
            CursorTy pvrtmp_3002 = tmp_struct_63.field2;
            CursorTy pvrtmp_3003 = tmp_struct_63.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3000, jump_1714,
                                                   pvrtmp_3002, pvrtmp_3003};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3010 = *(CursorTy *) tmpcur_2987;
            CursorTy tmpaftercur_3011 = tmpcur_2987 + 8;
            CursorCursorCursorCursorProd tmp_struct_64 =
                                          _copy_without_ptrs_Maybe_v_284(end_r_1202, end_r_1203, loc_1201, tmpcur_3010);
            CursorTy pvrtmp_3012 = tmp_struct_64.field0;
            CursorTy pvrtmp_3013 = tmp_struct_64.field1;
            CursorTy pvrtmp_3014 = tmp_struct_64.field2;
            CursorTy pvrtmp_3015 = tmp_struct_64.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3012, pvrtmp_3013,
                                                   pvrtmp_3014, pvrtmp_3015};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2986");
            exit(1);
        }
    }
}
CursorProd _traverse_Maybe_v_284(CursorTy end_r_1205, CursorTy arg_474_636_809)
{
    TagTyPacked tmpval_3023 = *(TagTyPacked *) arg_474_636_809;
    CursorTy tmpcur_3024 = arg_474_636_809 + 1;


  switch_3033:
    ;
    switch (tmpval_3023) {

      case 0:
        {
            IntTy tmpval_3025 = *(IntTy *) tmpcur_3024;
            CursorTy tmpcur_3026 = tmpcur_3024 + sizeof(IntTy);
            CursorTy jump_1606 = tmpcur_3024 + 8;

            return (CursorProd) {jump_1606};
            break;
        }

      case 1:
        {
            CursorTy jump_1608 = arg_474_636_809 + 1;

            return (CursorProd) {jump_1608};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3027 = *(CursorTy *) tmpcur_3024;
            CursorTy tmpaftercur_3028 = tmpcur_3024 + 8;
            CursorTy jump_1720 = tmpcur_3024 + 8;
            CursorProd tmp_struct_65 =
                        _traverse_Maybe_v_284(end_r_1205, tmpcur_3027);
            CursorTy pvrtmp_3029 = tmp_struct_65.field0;

            return (CursorProd) {jump_1720};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3030 = *(CursorTy *) tmpcur_3024;
            CursorTy tmpaftercur_3031 = tmpcur_3024 + 8;
            CursorProd tmp_struct_66 =
                        _traverse_Maybe_v_284(end_r_1205, tmpcur_3030);
            CursorTy pvrtmp_3032 = tmp_struct_66.field0;

            return (CursorProd) {pvrtmp_3032};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3023");
            exit(1);
        }
    }
}
CursorProd _print_Maybe_v_284(CursorTy end_r_1207, CursorTy arg_477_638_811)
{
    TagTyPacked tmpval_3034 = *(TagTyPacked *) arg_477_638_811;
    CursorTy tmpcur_3035 = arg_477_638_811 + 1;


  switch_3044:
    ;
    switch (tmpval_3034) {

      case 0:
        {
            IntTy tmpval_3036 = *(IntTy *) tmpcur_3035;
            CursorTy tmpcur_3037 = tmpcur_3035 + sizeof(IntTy);
            CursorTy jump_1610 = tmpcur_3035 + 8;
            unsigned char wildcard_480_640_813 = print_symbol(2485);
            unsigned char wildcard_482_641_814 = print_symbol(2492);
            unsigned char y_479_642_815 = printf("%lld", tmpval_3036);
            unsigned char wildcard_481_643_816 = print_symbol(2482);

            return (CursorProd) {jump_1610};
            break;
        }

      case 1:
        {
            CursorTy jump_1612 = arg_477_638_811 + 1;
            unsigned char wildcard_483_644_817 = print_symbol(2483);
            unsigned char wildcard_484_645_818 = print_symbol(2482);

            return (CursorProd) {jump_1612};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3038 = *(CursorTy *) tmpcur_3035;
            CursorTy tmpaftercur_3039 = tmpcur_3035 + 8;
            CursorTy jump_1726 = tmpcur_3035 + 8;
            unsigned char wildcard_1729 = print_symbol(2491);
            CursorProd tmp_struct_67 =
                        _print_Maybe_v_284(end_r_1207, tmpcur_3038);
            CursorTy pvrtmp_3040 = tmp_struct_67.field0;

            return (CursorProd) {jump_1726};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3041 = *(CursorTy *) tmpcur_3035;
            CursorTy tmpaftercur_3042 = tmpcur_3035 + 8;
            unsigned char wildcard_1729 = print_symbol(2490);
            CursorProd tmp_struct_68 =
                        _print_Maybe_v_284(end_r_1207, tmpcur_3041);
            CursorTy pvrtmp_3043 = tmp_struct_68.field0;

            return (CursorProd) {pvrtmp_3043};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3034");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_AList(CursorTy end_r_1210,
                                                             CursorTy end_r_1211,
                                                             CursorTy loc_1209,
                                                             CursorTy arg_1130)
{
    if (loc_1209 + 32 > end_r_1211) {
        ChunkTy new_chunk_73 = alloc_chunk(end_r_1211);
        CursorTy chunk_start_74 = new_chunk_73.chunk_start;
        CursorTy chunk_end_75 = new_chunk_73.chunk_end;

        end_r_1211 = chunk_end_75;
        *(TagTyPacked *) loc_1209 = 255;

        CursorTy redir = loc_1209 + 1;

        *(CursorTy *) redir = chunk_start_74;
        loc_1209 = chunk_start_74;
    }

    TagTyPacked tmpval_3045 = *(TagTyPacked *) arg_1130;
    CursorTy tmpcur_3046 = arg_1130 + 1;


  switch_3103:
    ;
    switch (tmpval_3045) {

      case 0:
        {
            IntTy tmpval_3047 = *(IntTy *) tmpcur_3046;
            CursorTy tmpcur_3048 = tmpcur_3046 + sizeof(IntTy);
            CursorTy jump_1614 = tmpcur_3046 + 8;

            *(TagTyPacked *) loc_1209 = 0;

            CursorTy writetag_2028 = loc_1209 + 1;

            *(IntTy *) writetag_2028 = tmpval_3047;

            CursorTy writecur_2029 = writetag_2028 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1211, jump_1614,
                                                   loc_1209, writecur_2029};
            break;
        }

      case 1:
        {
            IntTy tmpval_3053 = *(IntTy *) tmpcur_3046;
            CursorTy tmpcur_3054 = tmpcur_3046 + sizeof(IntTy);
            CursorTy jump_1616 = tmpcur_3046 + 8;

            *(TagTyPacked *) loc_1209 = 1;

            CursorTy writetag_2033 = loc_1209 + 1;

            *(IntTy *) writetag_2033 = tmpval_3053;

            CursorTy writecur_2034 = writetag_2033 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1211, jump_1616,
                                                   loc_1209, writecur_2034};
            break;
        }

      case 2:
        {
            CursorTy loc_1485 = loc_1209 + 1;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _add_size_and_rel_offsets_AList(end_r_1210, end_r_1211, loc_1485, tmpcur_3046);
            CursorTy pvrtmp_3059 = tmp_struct_69.field0;
            CursorTy pvrtmp_3060 = tmp_struct_69.field1;
            CursorTy pvrtmp_3061 = tmp_struct_69.field2;
            CursorTy pvrtmp_3062 = tmp_struct_69.field3;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _add_size_and_rel_offsets_AList(end_r_1210, pvrtmp_3059, pvrtmp_3062, pvrtmp_3060);
            CursorTy pvrtmp_3067 = tmp_struct_70.field0;
            CursorTy pvrtmp_3068 = tmp_struct_70.field1;
            CursorTy pvrtmp_3069 = tmp_struct_70.field2;
            CursorTy pvrtmp_3070 = tmp_struct_70.field3;

            *(TagTyPacked *) loc_1209 = 2;

            CursorTy writetag_2039 = loc_1209 + 1;

            return (CursorCursorCursorCursorProd) {pvrtmp_3067, pvrtmp_3068,
                                                   loc_1209, pvrtmp_3070};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3079 = *(CursorTy *) tmpcur_3046;
            CursorTy tmpaftercur_3080 = tmpcur_3046 + 8;
            CursorTy jump_1732 = tmpcur_3046 + 8;
            CursorCursorCursorCursorProd tmp_struct_71 =
                                          _add_size_and_rel_offsets_AList(end_r_1210, end_r_1211, loc_1209, tmpcur_3079);
            CursorTy pvrtmp_3081 = tmp_struct_71.field0;
            CursorTy pvrtmp_3082 = tmp_struct_71.field1;
            CursorTy pvrtmp_3083 = tmp_struct_71.field2;
            CursorTy pvrtmp_3084 = tmp_struct_71.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3081, jump_1732,
                                                   pvrtmp_3083, pvrtmp_3084};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3091 = *(CursorTy *) tmpcur_3046;
            CursorTy tmpaftercur_3092 = tmpcur_3046 + 8;
            CursorCursorCursorCursorProd tmp_struct_72 =
                                          _add_size_and_rel_offsets_AList(end_r_1210, end_r_1211, loc_1209, tmpcur_3091);
            CursorTy pvrtmp_3093 = tmp_struct_72.field0;
            CursorTy pvrtmp_3094 = tmp_struct_72.field1;
            CursorTy pvrtmp_3095 = tmp_struct_72.field2;
            CursorTy pvrtmp_3096 = tmp_struct_72.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3093, pvrtmp_3094,
                                                   pvrtmp_3095, pvrtmp_3096};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3045");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_PList_v_280(CursorTy end_r_1214,
                                                                   CursorTy end_r_1215,
                                                                   CursorTy loc_1213,
                                                                   CursorTy arg_1139)
{
    if (loc_1213 + 32 > end_r_1215) {
        ChunkTy new_chunk_79 = alloc_chunk(end_r_1215);
        CursorTy chunk_start_80 = new_chunk_79.chunk_start;
        CursorTy chunk_end_81 = new_chunk_79.chunk_end;

        end_r_1215 = chunk_end_81;
        *(TagTyPacked *) loc_1213 = 255;

        CursorTy redir = loc_1213 + 1;

        *(CursorTy *) redir = chunk_start_80;
        loc_1213 = chunk_start_80;
    }

    TagTyPacked tmpval_3104 = *(TagTyPacked *) arg_1139;
    CursorTy tmpcur_3105 = arg_1139 + 1;


  switch_3150:
    ;
    switch (tmpval_3104) {

      case 0:
        {
            CursorTy jump_1621 = arg_1139 + 1;

            *(TagTyPacked *) loc_1213 = 0;

            CursorTy writetag_2050 = loc_1213 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1215, jump_1621,
                                                   loc_1213, writetag_2050};
            break;
        }

      case 1:
        {
            IntTy tmpval_3110 = *(IntTy *) tmpcur_3105;
            CursorTy tmpcur_3111 = tmpcur_3105 + sizeof(IntTy);
            IntTy tmpval_3112 = *(IntTy *) tmpcur_3111;
            CursorTy tmpcur_3113 = tmpcur_3111 + sizeof(IntTy);
            CursorTy jump_1624 = tmpcur_3111 + 8;
            CursorTy jump_1623 = tmpcur_3105 + 8;
            CursorTy loc_1498 = loc_1213 + 1;
            CursorTy loc_1499 = loc_1498 + 8;
            CursorTy loc_1500 = loc_1499 + 8;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _add_size_and_rel_offsets_PList_v_280(end_r_1214, end_r_1215, loc_1500, tmpcur_3113);
            CursorTy pvrtmp_3114 = tmp_struct_76.field0;
            CursorTy pvrtmp_3115 = tmp_struct_76.field1;
            CursorTy pvrtmp_3116 = tmp_struct_76.field2;
            CursorTy pvrtmp_3117 = tmp_struct_76.field3;

            *(TagTyPacked *) loc_1213 = 1;

            CursorTy writetag_2056 = loc_1213 + 1;

            *(IntTy *) writetag_2056 = tmpval_3110;

            CursorTy writecur_2057 = writetag_2056 + sizeof(IntTy);

            *(IntTy *) writecur_2057 = tmpval_3112;

            CursorTy writecur_2058 = writecur_2057 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_3114, pvrtmp_3115,
                                                   loc_1213, pvrtmp_3117};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3126 = *(CursorTy *) tmpcur_3105;
            CursorTy tmpaftercur_3127 = tmpcur_3105 + 8;
            CursorTy jump_1738 = tmpcur_3105 + 8;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _add_size_and_rel_offsets_PList_v_280(end_r_1214, end_r_1215, loc_1213, tmpcur_3126);
            CursorTy pvrtmp_3128 = tmp_struct_77.field0;
            CursorTy pvrtmp_3129 = tmp_struct_77.field1;
            CursorTy pvrtmp_3130 = tmp_struct_77.field2;
            CursorTy pvrtmp_3131 = tmp_struct_77.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3128, jump_1738,
                                                   pvrtmp_3130, pvrtmp_3131};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3138 = *(CursorTy *) tmpcur_3105;
            CursorTy tmpaftercur_3139 = tmpcur_3105 + 8;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _add_size_and_rel_offsets_PList_v_280(end_r_1214, end_r_1215, loc_1213, tmpcur_3138);
            CursorTy pvrtmp_3140 = tmp_struct_78.field0;
            CursorTy pvrtmp_3141 = tmp_struct_78.field1;
            CursorTy pvrtmp_3142 = tmp_struct_78.field2;
            CursorTy pvrtmp_3143 = tmp_struct_78.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3140, pvrtmp_3141,
                                                   pvrtmp_3142, pvrtmp_3143};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3104");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Maybe_v_284(CursorTy end_r_1218,
                                                                   CursorTy end_r_1219,
                                                                   CursorTy loc_1217,
                                                                   CursorTy arg_1146)
{
    if (loc_1217 + 32 > end_r_1219) {
        ChunkTy new_chunk_84 = alloc_chunk(end_r_1219);
        CursorTy chunk_start_85 = new_chunk_84.chunk_start;
        CursorTy chunk_end_86 = new_chunk_84.chunk_end;

        end_r_1219 = chunk_end_86;
        *(TagTyPacked *) loc_1217 = 255;

        CursorTy redir = loc_1217 + 1;

        *(CursorTy *) redir = chunk_start_85;
        loc_1217 = chunk_start_85;
    }

    TagTyPacked tmpval_3151 = *(TagTyPacked *) arg_1146;
    CursorTy tmpcur_3152 = arg_1146 + 1;


  switch_3187:
    ;
    switch (tmpval_3151) {

      case 0:
        {
            IntTy tmpval_3153 = *(IntTy *) tmpcur_3152;
            CursorTy tmpcur_3154 = tmpcur_3152 + sizeof(IntTy);
            CursorTy jump_1627 = tmpcur_3152 + 8;

            *(TagTyPacked *) loc_1217 = 0;

            CursorTy writetag_2069 = loc_1217 + 1;

            *(IntTy *) writetag_2069 = tmpval_3153;

            CursorTy writecur_2070 = writetag_2069 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_1219, jump_1627,
                                                   loc_1217, writecur_2070};
            break;
        }

      case 1:
        {
            CursorTy jump_1629 = arg_1146 + 1;

            *(TagTyPacked *) loc_1217 = 1;

            CursorTy writetag_2073 = loc_1217 + 1;

            return (CursorCursorCursorCursorProd) {end_r_1219, jump_1629,
                                                   loc_1217, writetag_2073};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_3163 = *(CursorTy *) tmpcur_3152;
            CursorTy tmpaftercur_3164 = tmpcur_3152 + 8;
            CursorTy jump_1744 = tmpcur_3152 + 8;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _add_size_and_rel_offsets_Maybe_v_284(end_r_1218, end_r_1219, loc_1217, tmpcur_3163);
            CursorTy pvrtmp_3165 = tmp_struct_82.field0;
            CursorTy pvrtmp_3166 = tmp_struct_82.field1;
            CursorTy pvrtmp_3167 = tmp_struct_82.field2;
            CursorTy pvrtmp_3168 = tmp_struct_82.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3165, jump_1744,
                                                   pvrtmp_3167, pvrtmp_3168};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_3175 = *(CursorTy *) tmpcur_3152;
            CursorTy tmpaftercur_3176 = tmpcur_3152 + 8;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _add_size_and_rel_offsets_Maybe_v_284(end_r_1218, end_r_1219, loc_1217, tmpcur_3175);
            CursorTy pvrtmp_3177 = tmp_struct_83.field0;
            CursorTy pvrtmp_3178 = tmp_struct_83.field1;
            CursorTy pvrtmp_3179 = tmp_struct_83.field2;
            CursorTy pvrtmp_3180 = tmp_struct_83.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_3177, pvrtmp_3178,
                                                   pvrtmp_3179, pvrtmp_3180};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3151");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(2480, "OK\n");
    add_symbol(2481, "Err\n");
    add_symbol(2482, ")");
    add_symbol(2483, "(Nothing_v_284");
    add_symbol(2484, "(Nil_v_280");
    add_symbol(2485, "(Just_v_284");
    add_symbol(2486, "(Cons_v_280");
    add_symbol(2487, "(Append");
    add_symbol(2488, "(ASing");
    add_symbol(2489, "(ANil");
    add_symbol(2490, " ->r ");
    add_symbol(2491, " ->i ");
    add_symbol(2492, " ");
    add_symbol(2493, "\n");

    RegionTy *region_2494 = alloc_region(global_init_inf_buf_size);
    CursorTy r_1262 = region_2494->reg_heap;
    IntTy sizeof_end_r_1262_2495 = global_init_inf_buf_size;
    CursorTy end_r_1262 = r_1262 + sizeof_end_r_1262_2495;
    RegionTy *region_2496 = alloc_region(global_init_inf_buf_size);
    CursorTy r_1261 = region_2496->reg_heap;
    IntTy sizeof_end_r_1261_2497 = global_init_inf_buf_size;
    CursorTy end_r_1261 = r_1261 + sizeof_end_r_1261_2497;
    CursorTy loc_1248 = r_1262 + 1;
    CursorTy loc_1249 = loc_1248 + 8;
    CursorTy loc_1250 = loc_1249 + 8;
    CursorTy loc_1243 = loc_1250 + 1;
    CursorTy loc_1244 = loc_1243 + 8;
    CursorTy loc_1245 = loc_1244 + 8;
    CursorTy loc_1238 = loc_1245 + 1;
    CursorTy loc_1239 = loc_1238 + 8;
    CursorTy loc_1240 = loc_1239 + 8;
    CursorTy loc_1233 = loc_1240 + 1;
    CursorTy loc_1234 = loc_1233 + 8;
    CursorTy loc_1235 = loc_1234 + 8;
    CursorTy loc_1228 = loc_1235 + 1;
    CursorTy loc_1229 = loc_1228 + 8;
    CursorTy loc_1230 = loc_1229 + 8;
    CursorTy loc_1223 = loc_1230 + 1;
    CursorTy loc_1224 = loc_1223 + 8;
    CursorTy loc_1225 = loc_1224 + 8;

    *(TagTyPacked *) loc_1225 = 0;

    CursorTy writetag_2081 = loc_1225 + 1;

    *(TagTyPacked *) loc_1230 = 1;

    CursorTy writetag_2083 = loc_1230 + 1;

    *(IntTy *) writetag_2083 = 250;

    CursorTy writecur_2084 = writetag_2083 + sizeof(IntTy);

    *(IntTy *) writecur_2084 = 55;

    CursorTy writecur_2085 = writecur_2084 + sizeof(IntTy);

    *(TagTyPacked *) loc_1235 = 1;

    CursorTy writetag_2088 = loc_1235 + 1;

    *(IntTy *) writetag_2088 = 100;

    CursorTy writecur_2089 = writetag_2088 + sizeof(IntTy);

    *(IntTy *) writecur_2089 = 88;

    CursorTy writecur_2090 = writecur_2089 + sizeof(IntTy);

    *(TagTyPacked *) loc_1240 = 1;

    CursorTy writetag_2093 = loc_1240 + 1;

    *(IntTy *) writetag_2093 = 25;

    CursorTy writecur_2094 = writetag_2093 + sizeof(IntTy);

    *(IntTy *) writecur_2094 = 88;

    CursorTy writecur_2095 = writecur_2094 + sizeof(IntTy);

    *(TagTyPacked *) loc_1245 = 1;

    CursorTy writetag_2098 = loc_1245 + 1;

    *(IntTy *) writetag_2098 = 10;

    CursorTy writecur_2099 = writetag_2098 + sizeof(IntTy);

    *(IntTy *) writecur_2099 = 99;

    CursorTy writecur_2100 = writecur_2099 + sizeof(IntTy);

    *(TagTyPacked *) loc_1250 = 1;

    CursorTy writetag_2103 = loc_1250 + 1;

    *(IntTy *) writetag_2103 = 5;

    CursorTy writecur_2104 = writetag_2103 + sizeof(IntTy);

    *(IntTy *) writecur_2104 = 122;

    CursorTy writecur_2105 = writecur_2104 + sizeof(IntTy);

    *(TagTyPacked *) r_1262 = 1;

    CursorTy writetag_2108 = r_1262 + 1;

    *(IntTy *) writetag_2108 = 1;

    CursorTy writecur_2109 = writetag_2108 + sizeof(IntTy);

    *(IntTy *) writecur_2109 = 177;

    CursorTy writecur_2110 = writecur_2109 + sizeof(IntTy);
    IntTy amt_61_486_673 = global_size_param;
    CursorTy pvrtmp_2521;
    CursorTy pvrtmp_2522;
    CursorTy pvrtmp_2523;
    VectorTy *times_91 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_2521;
    struct timespec end_pvrtmp_2521;

    for (long long iters_pvrtmp_2521 = 0; iters_pvrtmp_2521 <
         global_iters_param; iters_pvrtmp_2521++) {
        if (iters_pvrtmp_2521 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2521);

        CursorCursorCursorProd tmp_struct_87 =
                                payA_seq(end_r_1262, end_r_1261, r_1261, amt_61_486_673, r_1262);
        CursorTy pvrtmp_2512 = tmp_struct_87.field0;
        CursorTy pvrtmp_2513 = tmp_struct_87.field1;
        CursorTy pvrtmp_2514 = tmp_struct_87.field2;

        pvrtmp_2521 = pvrtmp_2512;
        pvrtmp_2522 = pvrtmp_2513;
        pvrtmp_2523 = pvrtmp_2514;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2521);
        if (iters_pvrtmp_2521 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_88 = difftimespecs(&begin_pvrtmp_2521,
                                           &end_pvrtmp_2521);

        vector_inplace_update(times_91, iters_pvrtmp_2521, &itertime_88);
    }
    vector_inplace_sort(times_91, compare_doubles);

    double *tmp_92 = (double *) vector_nth(times_91, global_iters_param / 2);
    double selftimed_90 = *tmp_92;
    double batchtime_89 = sum_timing_array(times_91);

    print_timing_array(times_91);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_89);
    printf("SELFTIMED: %e\n", selftimed_90);

    CursorProd tmp_struct_93 =
                check_coins(end_r_1261, amt_61_486_673, pvrtmp_2522);
    CursorTy pvrtmp_2531 = tmp_struct_93.field0;

    printf("'#()");
    printf("\n");
    free_symtable();
    free_region(end_r_1261);
    free_region(end_r_1262);
    return 0;
}
