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
    RegionTy *reg = malloc(sizeof(RegionTy));
    if (reg == NULL) {
        printf("alloc_region: allocation failed: %ld", sizeof(RegionTy));
        exit(1);
    }

    // Allocate the first chunk.
    IntTy total_size = size + sizeof(RegionFooter);
    CursorTy heap;
    bool nursery_allocated = true;
    // heap = ALLOC_PACKED_BIG(total_size);
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
typedef struct Int64Int64Int64Prod_struct {
            IntTy field0;
            IntTy field1;
            IntTy field2;
        } Int64Int64Int64Prod;
typedef struct Int64Int64Int64Int64Int64Int64Prod_struct {
            IntTy field0;
            IntTy field1;
            IntTy field2;
            IntTy field3;
            IntTy field4;
            IntTy field5;
        } Int64Int64Int64Int64Int64Int64Prod;
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
typedef struct CursorBoolProd_struct {
            CursorTy field0;
            BoolTy field1;
        } CursorBoolProd;
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
typedef struct CursorCursorCursorCursorCursorProd_struct {
            CursorTy field0;
            CursorTy field1;
            CursorTy field2;
            CursorTy field3;
            CursorTy field4;
        } CursorCursorCursorCursorCursorProd;
CursorCursorCursorCursorProd zip0(CursorTy end_r_2436, CursorTy end_r_2437,
                                  CursorTy loc_2435, CursorTy ls_104_1236_1548);
Int64Int64Int64Prod very_small_opts_answer();
Int64Int64Int64Prod small_opts_answer();
Int64Int64Int64Prod fast_opts_answer();
Int64Int64Int64Prod norm_opts_answer();
Int64Int64Int64Prod slow_opts_answer();
Int64Int64Int64Int64Int64Int64Prod very_small_opts();
Int64Int64Int64Int64Int64Int64Prod small_opts();
Int64Int64Int64Int64Int64Int64Prod fast_opts();
Int64Int64Int64Int64Int64Int64Prod norm_opts();
Int64Int64Int64Int64Int64Int64Prod slow_opts();
BoolTy bench_lcss(Int64Int64Int64Int64Int64Int64Prod opts_107_1239_1552,
                  Int64Int64Int64Prod answer_108_1240_1553);
CursorBoolProd check_lcss(CursorTy end_r_2439, IntTy start_123_1255_1570,
                          IntTy step_124_1256_1571, IntTy end_125_1257_1572,
                          CursorTy list2_126_1258_1573);
CursorCursorCursorCursorCursorProd lcss(CursorTy end_r_2443,
                                        CursorTy end_r_2444,
                                        CursorTy end_r_2445, CursorTy loc_2442,
                                        CursorTy xs_129_1261_1579,
                                        CursorTy ys_130_1262_1580);
CursorCursorCursorProd mkList(CursorTy end_r_2447, CursorTy loc_2446,
                              IntTy start_131_1263_1584,
                              IntTy end_132_1264_1585,
                              IntTy skipFactor_133_1265_1586);
CursorInt64Prod findk(CursorTy end_r_2449, IntTy k_135_1267_1590,
                      IntTy km_136_1268_1591, IntTy m_137_1269_1592,
                      CursorTy ls_138_1270_1593);
CursorCursorCursorProd algc(CursorTy end_r_2454, CursorTy end_r_2455,
                            CursorTy end_r_2456, CursorTy end_r_2457,
                            CursorTy loc_2453, IntTy m_144_1277_1605,
                            IntTy n_145_1278_1606, CursorTy xs_146_1279_1607,
                            CursorTy ys_147_1280_1608,
                            CursorTy zs_148_1281_1609);
CursorCursorCursorCursorProd algb2(CursorTy end_r_2460, CursorTy end_r_2461,
                                   CursorTy loc_2459, IntTy x_164_1282_1611,
                                   IntTy k0j1_165_1283_1612,
                                   IntTy k1j1_166_1284_1613,
                                   CursorTy ls_167_1285_1614);
CursorCursorCursorCursorCursorProd algb1(CursorTy end_r_2465,
                                         CursorTy end_r_2466,
                                         CursorTy end_r_2467, CursorTy loc_2464,
                                         CursorTy xs_174_1293_1624,
                                         CursorTy ys_175_1294_1625);
CursorCursorCursorCursorCursorProd algb(CursorTy end_r_2471,
                                        CursorTy end_r_2472,
                                        CursorTy end_r_2473, CursorTy loc_2470,
                                        CursorTy xs_181_1297_1629,
                                        CursorTy ys_182_1298_1630);
IntTy maxInt(IntTy a_189_1299_1633, IntTy b_190_1300_1634);
CursorInt64Prod length_plist_780(CursorTy end_r_2475, CursorTy a_226_1319_1636);
CursorCursorCursorCursorProd reverse_plist_785(CursorTy end_r_2479,
                                               CursorTy end_r_2480,
                                               CursorTy end_r_2481,
                                               CursorTy loc_2478,
                                               CursorTy xs_221_1322_1640,
                                               CursorTy acc_222_1323_1641);
CursorCursorCursorProd zip_plist_786(CursorTy end_r_2485, CursorTy end_r_2486,
                                     CursorTy end_r_2487, CursorTy loc_2484,
                                     CursorTy as_213_1326_1645,
                                     CursorTy bs_214_1327_1646);
CursorCursorCursorProd drop_plist_784(CursorTy end_r_2490, CursorTy end_r_2491,
                                      CursorTy loc_2489,
                                      IntTy num_208_1330_1649,
                                      CursorTy list_209_1331_1650);
CursorCursorCursorProd take_plist_783(CursorTy end_r_2494, CursorTy end_r_2495,
                                      CursorTy loc_2493, IntTy n_203_1334_1655,
                                      CursorTy a_204_1335_1656);
BoolTy is_empty_plist_781(CursorTy end_r_2497, CursorTy ls_191_1336_1658);
BoolTy elem_plist_782_1069(CursorTy end_r_2499, IntTy a_196_1342_1661,
                           CursorTy list_197_1343_1662);
CursorCursorCursorCursorProd map_plist_787_1071(CursorTy end_r_2502,
                                                CursorTy end_r_2503,
                                                CursorTy loc_2501,
                                                CursorTy ls_184_1346_1673);
CursorCursorCursorCursorProd _copy_PList_v_778(CursorTy end_r_2506,
                                               CursorTy end_r_2507,
                                               CursorTy loc_2505,
                                               CursorTy arg_1136_1350_1682);
CursorCursorCursorCursorProd _copy_without_ptrs_PList_v_778(CursorTy end_r_2510,
                                                            CursorTy end_r_2511,
                                                            CursorTy loc_2509,
                                                            CursorTy arg_1141_1355_1687);
CursorProd _traverse_PList_v_778(CursorTy end_r_2513,
                                 CursorTy arg_1146_1360_1692);
CursorProd _print_PList_v_778(CursorTy end_r_2515, CursorTy arg_1151_1364_1696);
CursorCursorCursorCursorProd _copy_PList_v_779(CursorTy end_r_2518,
                                               CursorTy end_r_2519,
                                               CursorTy loc_2517,
                                               CursorTy arg_1162_1375_1707);
CursorCursorCursorCursorProd _copy_without_ptrs_PList_v_779(CursorTy end_r_2522,
                                                            CursorTy end_r_2523,
                                                            CursorTy loc_2521,
                                                            CursorTy arg_1169_1382_1714);
CursorProd _traverse_PList_v_779(CursorTy end_r_2525,
                                 CursorTy arg_1176_1389_1721);
CursorProd _print_PList_v_779(CursorTy end_r_2527, CursorTy arg_1183_1394_1726);
CursorCursorCursorCursorProd _copy_Maybe_v_788(CursorTy end_r_2530,
                                               CursorTy end_r_2531,
                                               CursorTy loc_2529,
                                               CursorTy arg_1197_1408_1740);
CursorCursorCursorCursorProd _copy_without_ptrs_Maybe_v_788(CursorTy end_r_2534,
                                                            CursorTy end_r_2535,
                                                            CursorTy loc_2533,
                                                            CursorTy arg_1200_1411_1743);
CursorProd _traverse_Maybe_v_788(CursorTy end_r_2537,
                                 CursorTy arg_1203_1414_1746);
CursorProd _print_Maybe_v_788(CursorTy end_r_2539, CursorTy arg_1206_1416_1748);
CursorCursorCursorProd caseFn_1214(CursorTy end_r_2545, CursorTy end_r_2546,
                                   CursorTy end_r_2547, CursorTy end_r_2548,
                                   CursorTy end_r_2549, CursorTy loc_2544,
                                   IntTy m_144_1215_1424_1756,
                                   IntTy n_145_1216_1425_1757,
                                   CursorTy xs_146_1217_1426_1758,
                                   CursorTy ys_147_1218_1427_1759,
                                   CursorTy zs_148_1219_1428_1760,
                                   CursorTy xs__150_1220_1429_1761,
                                   IntTy x_149_1221_1430_1762);
CursorCursorCursorProd caseFn_1222(CursorTy end_r_2554, CursorTy end_r_2555,
                                   CursorTy end_r_2556, CursorTy end_r_2557,
                                   CursorTy loc_2553,
                                   IntTy m_144_1223_1444_1787,
                                   IntTy n_145_1224_1445_1788,
                                   CursorTy xs_146_1225_1446_1789,
                                   CursorTy ys_147_1226_1447_1790,
                                   CursorTy zs_148_1227_1448_1791);
CursorCursorCursorProd caseFn_1228(CursorTy end_r_2561, CursorTy end_r_2562,
                                   CursorTy end_r_2563, CursorTy loc_2560,
                                   CursorTy bs_214_1229_1451_1794,
                                   IntTy z_217_1230_1452_1795,
                                   CursorTy zs_218_1231_1453_1796);
CursorCursorCursorProd caseFn_1232(CursorTy end_r_2566, CursorTy end_r_2567,
                                   CursorTy loc_2565,
                                   IntTy n_203_1233_1456_1800,
                                   CursorTy a_204_1234_1457_1801);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_PList_v_778(CursorTy end_r_2570, CursorTy end_r_2571,
                                      CursorTy loc_2569, CursorTy arg_2417);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_PList_v_779(CursorTy end_r_2574, CursorTy end_r_2575,
                                      CursorTy loc_2573, CursorTy arg_2422);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Maybe_v_788(CursorTy end_r_2578, CursorTy end_r_2579,
                                      CursorTy loc_2577, CursorTy arg_2429);
CursorCursorCursorCursorProd zip0(CursorTy end_r_2436, CursorTy end_r_2437,
                                  CursorTy loc_2435, CursorTy ls_104_1236_1548)
{
    if (loc_2435 + 32 > end_r_2437) {
        ChunkTy new_chunk_3 = alloc_chunk(end_r_2437);
        CursorTy chunk_start_4 = new_chunk_3.chunk_start;
        CursorTy chunk_end_5 = new_chunk_3.chunk_end;

        end_r_2437 = chunk_end_5;
        *(TagTyPacked *) loc_2435 = 255;

        CursorTy redir = loc_2435 + 1;

        *(CursorTy *) redir = chunk_start_4;
        loc_2435 = chunk_start_4;
    }

    TagTyPacked tmpval_4934 = *(TagTyPacked *) ls_104_1236_1548;
    CursorTy tmpcur_4935 = ls_104_1236_1548 + 1;


  switch_4978:
    ;
    switch (tmpval_4934) {

      case 0:
        {
            CursorTy jump_3092 = ls_104_1236_1548 + 1;

            *(TagTyPacked *) loc_2435 = 0;

            CursorTy writetag_3548 = loc_2435 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2437, jump_3092,
                                                   loc_2435, writetag_3548};
            break;
        }

      case 1:
        {
            IntTy tmpval_4940 = *(IntTy *) tmpcur_4935;
            CursorTy tmpcur_4941 = tmpcur_4935 + sizeof(IntTy);
            CursorTy jump_3094 = tmpcur_4935 + 8;
            CursorTy loc_2588 = loc_2435 + 1;
            CursorTy loc_2589 = loc_2588 + 8;
            CursorTy loc_2590 = loc_2589 + 8;
            CursorCursorCursorCursorProd tmp_struct_0 =
                                          zip0(end_r_2436, end_r_2437, loc_2590, tmpcur_4941);
            CursorTy pvrtmp_4942 = tmp_struct_0.field0;
            CursorTy pvrtmp_4943 = tmp_struct_0.field1;
            CursorTy pvrtmp_4944 = tmp_struct_0.field2;
            CursorTy pvrtmp_4945 = tmp_struct_0.field3;

            *(TagTyPacked *) loc_2435 = 1;

            CursorTy writetag_3553 = loc_2435 + 1;

            *(IntTy *) writetag_3553 = tmpval_4940;

            CursorTy writecur_3554 = writetag_3553 + sizeof(IntTy);

            *(IntTy *) writecur_3554 = 0;

            CursorTy writecur_3555 = writecur_3554 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_4942, pvrtmp_4943,
                                                   loc_2435, pvrtmp_4945};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_4954 = *(CursorTy *) tmpcur_4935;
            CursorTy tmpaftercur_4955 = tmpcur_4935 + 8;
            CursorTy jump_3291 = tmpcur_4935 + 8;
            CursorCursorCursorCursorProd tmp_struct_1 =
                                          zip0(end_r_2436, end_r_2437, loc_2435, tmpcur_4954);
            CursorTy pvrtmp_4956 = tmp_struct_1.field0;
            CursorTy pvrtmp_4957 = tmp_struct_1.field1;
            CursorTy pvrtmp_4958 = tmp_struct_1.field2;
            CursorTy pvrtmp_4959 = tmp_struct_1.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_4956, jump_3291,
                                                   pvrtmp_4958, pvrtmp_4959};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_4966 = *(CursorTy *) tmpcur_4935;
            CursorTy tmpaftercur_4967 = tmpcur_4935 + 8;
            CursorCursorCursorCursorProd tmp_struct_2 =
                                          zip0(end_r_2436, end_r_2437, loc_2435, tmpcur_4966);
            CursorTy pvrtmp_4968 = tmp_struct_2.field0;
            CursorTy pvrtmp_4969 = tmp_struct_2.field1;
            CursorTy pvrtmp_4970 = tmp_struct_2.field2;
            CursorTy pvrtmp_4971 = tmp_struct_2.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_4968, pvrtmp_4969,
                                                   pvrtmp_4970, pvrtmp_4971};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4934");
            exit(1);
        }
    }
}
Int64Int64Int64Prod very_small_opts_answer()
{
    return (Int64Int64Int64Prod) {1300, 1, 2000};
}
Int64Int64Int64Prod small_opts_answer()
{
    return (Int64Int64Int64Prod) {1000, 1, 2000};
}
Int64Int64Int64Prod fast_opts_answer()
{
    return (Int64Int64Int64Prod) {1000, 1, 2000};
}
Int64Int64Int64Prod norm_opts_answer()
{
    return (Int64Int64Int64Prod) {1000, 1, 3100};
}
Int64Int64Int64Prod slow_opts_answer()
{
    return (Int64Int64Int64Prod) {100, 1, 3500};
}
Int64Int64Int64Int64Int64Int64Prod very_small_opts()
{
    return (Int64Int64Int64Int64Int64Int64Prod) {1, 2, 2000, 1300, 1301, 2000};
}
Int64Int64Int64Int64Int64Int64Prod small_opts()
{
    return (Int64Int64Int64Int64Int64Int64Prod) {1, 2, 2000, 1000, 1001, 2000};
}
Int64Int64Int64Int64Int64Int64Prod fast_opts()
{
    return (Int64Int64Int64Int64Int64Int64Prod) {1, 2, 2000, 1000, 1001, 3000};
}
Int64Int64Int64Int64Int64Int64Prod norm_opts()
{
    return (Int64Int64Int64Int64Int64Int64Prod) {1, 2, 3100, 1000, 1001, 4000};
}
Int64Int64Int64Int64Int64Int64Prod slow_opts()
{
    return (Int64Int64Int64Int64Int64Int64Prod) {1, 2, 4000, 100, 101, 3500};
}
BoolTy bench_lcss(Int64Int64Int64Int64Int64Int64Prod opts_107_1239_1552,
                  Int64Int64Int64Prod answer_108_1240_1553)
{
    RegionTy *region_5024 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2610 = region_5024->reg_heap;
    IntTy sizeof_end_r_2610_5025 = global_init_inf_buf_size;
    CursorTy end_r_2610 = r_2610 + sizeof_end_r_2610_5025;
    RegionTy *region_5026 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2609 = region_5026->reg_heap;
    IntTy sizeof_end_r_2609_5027 = global_init_inf_buf_size;
    CursorTy end_r_2609 = r_2609 + sizeof_end_r_2609_5027;
    RegionTy *region_5028 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2608 = region_5028->reg_heap;
    IntTy sizeof_end_r_2608_5029 = global_init_inf_buf_size;
    CursorTy end_r_2608 = r_2608 + sizeof_end_r_2608_5029;
    IntTy fltAppE_1482_1561 = opts_107_1239_1552.field1 -
          opts_107_1239_1552.field0;
    CursorCursorCursorProd tmp_struct_6 =
                            mkList(end_r_2610, r_2610, opts_107_1239_1552.field0, opts_107_1239_1552.field2, fltAppE_1482_1561);
    CursorTy pvrtmp_5030 = tmp_struct_6.field0;
    CursorTy pvrtmp_5031 = tmp_struct_6.field1;
    CursorTy pvrtmp_5032 = tmp_struct_6.field2;
    IntTy fltAppE_1483_1563 = opts_107_1239_1552.field4 -
          opts_107_1239_1552.field3;
    CursorCursorCursorProd tmp_struct_7 =
                            mkList(end_r_2609, r_2609, opts_107_1239_1552.field3, opts_107_1239_1552.field5, fltAppE_1483_1563);
    CursorTy pvrtmp_5037 = tmp_struct_7.field0;
    CursorTy pvrtmp_5038 = tmp_struct_7.field1;
    CursorTy pvrtmp_5039 = tmp_struct_7.field2;
    CursorTy pvrtmp_5055;
    CursorTy pvrtmp_5056;
    CursorTy pvrtmp_5057;
    VectorTy *times_12 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_5055;
    struct timespec end_pvrtmp_5055;

    for (long long iters_pvrtmp_5055 = 0; iters_pvrtmp_5055 <
         global_iters_param; iters_pvrtmp_5055++) {
        if (iters_pvrtmp_5055 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_5055);

        CursorCursorCursorCursorCursorProd tmp_struct_8 =
                                            lcss(pvrtmp_5030, pvrtmp_5037, end_r_2608, r_2608, pvrtmp_5031, pvrtmp_5038);
        CursorTy pvrtmp_5044 = tmp_struct_8.field0;
        CursorTy pvrtmp_5045 = tmp_struct_8.field1;
        CursorTy pvrtmp_5046 = tmp_struct_8.field2;
        CursorTy pvrtmp_5047 = tmp_struct_8.field3;
        CursorTy pvrtmp_5048 = tmp_struct_8.field4;

        pvrtmp_5055 = pvrtmp_5044;
        pvrtmp_5056 = pvrtmp_5047;
        pvrtmp_5057 = pvrtmp_5048;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_5055);
        if (iters_pvrtmp_5055 != global_iters_param - 1)
            restore_alloc_state();

        double itertime_9 = difftimespecs(&begin_pvrtmp_5055, &end_pvrtmp_5055);

        vector_inplace_update(times_12, iters_pvrtmp_5055, &itertime_9);
    }
    vector_inplace_sort(times_12, compare_doubles);

    double *tmp_13 = (double *) vector_nth(times_12, global_iters_param / 2);
    double selftimed_11 = *tmp_13;
    double batchtime_10 = sum_timing_array(times_12);

    print_timing_array(times_12);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_10);
    printf("SELFTIMED: %e\n", selftimed_11);

    CursorBoolProd tmp_struct_14 =
                    check_lcss(end_r_2608, answer_108_1240_1553.field0, answer_108_1240_1553.field1, answer_108_1240_1553.field2, pvrtmp_5056);
    CursorTy pvrtmp_5065 = tmp_struct_14.field0;
    BoolTy pvrtmp_5066 = tmp_struct_14.field1;

    free_region(end_r_2608);
    free_region(end_r_2609);
    free_region(end_r_2610);
    return pvrtmp_5066;
}
CursorBoolProd check_lcss(CursorTy end_r_2439, IntTy start_123_1255_1570,
                          IntTy step_124_1256_1571, IntTy end_125_1257_1572,
                          CursorTy list2_126_1258_1573)
{
    TagTyPacked tmpval_5067 = *(TagTyPacked *) list2_126_1258_1573;
    CursorTy tmpcur_5068 = list2_126_1258_1573 + 1;


  switch_5081:
    ;
    switch (tmpval_5067) {

      case 0:
        {
            CursorTy jump_3112 = list2_126_1258_1573 + 1;
            BoolTy tailprim_3113 = start_123_1255_1570 > end_125_1257_1572;

            return (CursorBoolProd) {jump_3112, tailprim_3113};
            break;
        }

      case 1:
        {
            IntTy tmpval_5069 = *(IntTy *) tmpcur_5068;
            CursorTy tmpcur_5070 = tmpcur_5068 + sizeof(IntTy);
            CursorTy jump_3114 = tmpcur_5068 + 8;
            BoolTy fltPrm_1484_1576 = tmpval_5069 == start_123_1255_1570;
            IntTy fltAppE_1486_1577 = start_123_1255_1570 + step_124_1256_1571;
            CursorBoolProd tmp_struct_15 =
                            check_lcss(end_r_2439, fltAppE_1486_1577, step_124_1256_1571, end_125_1257_1572, tmpcur_5070);
            CursorTy pvrtmp_5071 = tmp_struct_15.field0;
            BoolTy pvrtmp_5072 = tmp_struct_15.field1;
            BoolTy tailprim_3116 = fltPrm_1484_1576 && pvrtmp_5072;

            return (CursorBoolProd) {pvrtmp_5071, tailprim_3116};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5073 = *(CursorTy *) tmpcur_5068;
            CursorTy tmpaftercur_5074 = tmpcur_5068 + 8;
            CursorTy jump_3297 = tmpcur_5068 + 8;
            CursorBoolProd tmp_struct_16 =
                            check_lcss(end_r_2439, start_123_1255_1570, step_124_1256_1571, end_125_1257_1572, tmpcur_5073);
            CursorTy pvrtmp_5075 = tmp_struct_16.field0;
            BoolTy pvrtmp_5076 = tmp_struct_16.field1;

            return (CursorBoolProd) {jump_3297, pvrtmp_5076};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5077 = *(CursorTy *) tmpcur_5068;
            CursorTy tmpaftercur_5078 = tmpcur_5068 + 8;
            CursorBoolProd tmp_struct_17 =
                            check_lcss(end_r_2439, start_123_1255_1570, step_124_1256_1571, end_125_1257_1572, tmpcur_5077);
            CursorTy pvrtmp_5079 = tmp_struct_17.field0;
            BoolTy pvrtmp_5080 = tmp_struct_17.field1;

            return (CursorBoolProd) {pvrtmp_5079, pvrtmp_5080};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5067");
            exit(1);
        }
    }
}
CursorCursorCursorCursorCursorProd lcss(CursorTy end_r_2443,
                                        CursorTy end_r_2444,
                                        CursorTy end_r_2445, CursorTy loc_2442,
                                        CursorTy xs_129_1261_1579,
                                        CursorTy ys_130_1262_1580)
{
    RegionTy *region_5082 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2632 = region_5082->reg_heap;
    IntTy sizeof_end_r_2632_5083 = global_init_inf_buf_size;
    CursorTy end_r_2632 = r_2632 + sizeof_end_r_2632_5083;

    if (loc_2442 + 32 > end_r_2445) {
        ChunkTy new_chunk_21 = alloc_chunk(end_r_2445);
        CursorTy chunk_start_22 = new_chunk_21.chunk_start;
        CursorTy chunk_end_23 = new_chunk_21.chunk_end;

        end_r_2445 = chunk_end_23;
        *(TagTyPacked *) loc_2442 = 255;

        CursorTy redir = loc_2442 + 1;

        *(CursorTy *) redir = chunk_start_22;
        loc_2442 = chunk_start_22;
    }

    CursorInt64Prod tmp_struct_18 =
                     length_plist_780(end_r_2443, xs_129_1261_1579);
    CursorTy pvrtmp_5084 = tmp_struct_18.field0;
    IntTy pvrtmp_5085 = tmp_struct_18.field1;
    CursorInt64Prod tmp_struct_19 =
                     length_plist_780(end_r_2444, ys_130_1262_1580);
    CursorTy pvrtmp_5086 = tmp_struct_19.field0;
    IntTy pvrtmp_5087 = tmp_struct_19.field1;

    *(TagTyPacked *) r_2632 = 0;

    CursorTy writetag_3581 = r_2632 + 1;
    CursorCursorCursorProd tmp_struct_20 =
                            algc(end_r_2443, end_r_2444, end_r_2632, end_r_2445, loc_2442, pvrtmp_5085, pvrtmp_5087, xs_129_1261_1579, ys_130_1262_1580, r_2632);
    CursorTy pvrtmp_5090 = tmp_struct_20.field0;
    CursorTy pvrtmp_5091 = tmp_struct_20.field1;
    CursorTy pvrtmp_5092 = tmp_struct_20.field2;

    free_region(end_r_2632);
    return (CursorCursorCursorCursorCursorProd) {pvrtmp_5090, pvrtmp_5084,
                                                 pvrtmp_5086, pvrtmp_5091,
                                                 pvrtmp_5092};
}
CursorCursorCursorProd mkList(CursorTy end_r_2447, CursorTy loc_2446,
                              IntTy start_131_1263_1584,
                              IntTy end_132_1264_1585,
                              IntTy skipFactor_133_1265_1586)
{
    if (loc_2446 + 32 > end_r_2447) {
        ChunkTy new_chunk_25 = alloc_chunk(end_r_2447);
        CursorTy chunk_start_26 = new_chunk_25.chunk_start;
        CursorTy chunk_end_27 = new_chunk_25.chunk_end;

        end_r_2447 = chunk_end_27;
        *(TagTyPacked *) loc_2446 = 255;

        CursorTy redir = loc_2446 + 1;

        *(CursorTy *) redir = chunk_start_26;
        loc_2446 = chunk_start_26;
    }

    BoolTy fltIf_1490_1587 = start_131_1263_1584 <= end_132_1264_1585;

    if (fltIf_1490_1587) {
        IntTy fltAppE_1491_1588 = start_131_1263_1584 +
              skipFactor_133_1265_1586;
        CursorTy loc_2634 = loc_2446 + 1;
        CursorTy loc_2635 = loc_2634 + 8;
        CursorCursorCursorProd tmp_struct_24 =
                                mkList(end_r_2447, loc_2635, fltAppE_1491_1588, end_132_1264_1585, skipFactor_133_1265_1586);
        CursorTy pvrtmp_5099 = tmp_struct_24.field0;
        CursorTy pvrtmp_5100 = tmp_struct_24.field1;
        CursorTy pvrtmp_5101 = tmp_struct_24.field2;

        *(TagTyPacked *) loc_2446 = 1;

        CursorTy writetag_3585 = loc_2446 + 1;

        *(IntTy *) writetag_3585 = start_131_1263_1584;

        CursorTy writecur_3586 = writetag_3585 + sizeof(IntTy);

        return (CursorCursorCursorProd) {pvrtmp_5099, loc_2446, pvrtmp_5101};
    } else {
        *(TagTyPacked *) loc_2446 = 0;

        CursorTy writetag_3589 = loc_2446 + 1;

        return (CursorCursorCursorProd) {end_r_2447, loc_2446, writetag_3589};
    }
}
CursorInt64Prod findk(CursorTy end_r_2449, IntTy k_135_1267_1590,
                      IntTy km_136_1268_1591, IntTy m_137_1269_1592,
                      CursorTy ls_138_1270_1593)
{
    TagTyPacked tmpval_5114 = *(TagTyPacked *) ls_138_1270_1593;
    CursorTy tmpcur_5115 = ls_138_1270_1593 + 1;


  switch_5134:
    ;
    switch (tmpval_5114) {

      case 0:
        {
            CursorTy jump_3122 = ls_138_1270_1593 + 1;

            return (CursorInt64Prod) {jump_3122, km_136_1268_1591};
            break;
        }

      case 1:
        {
            IntTy tmpval_5116 = *(IntTy *) tmpcur_5115;
            CursorTy tmpcur_5117 = tmpcur_5115 + sizeof(IntTy);
            IntTy tmpval_5118 = *(IntTy *) tmpcur_5117;
            CursorTy tmpcur_5119 = tmpcur_5117 + sizeof(IntTy);
            CursorTy jump_3124 = tmpcur_5117 + 8;
            CursorTy jump_3123 = tmpcur_5115 + 8;
            IntTy fltPrm_1493_1600 = tmpval_5116 + tmpval_5118;
            BoolTy fltIf_1492_1601 = fltPrm_1493_1600 >= m_137_1269_1592;

            if (fltIf_1492_1601) {
                IntTy fltAppE_1494_1602 = k_135_1267_1590 + 1;
                IntTy fltAppE_1495_1603 = tmpval_5116 + tmpval_5118;
                CursorInt64Prod tmp_struct_28 =
                                 findk(end_r_2449, fltAppE_1494_1602, k_135_1267_1590, fltAppE_1495_1603, tmpcur_5119);
                CursorTy pvrtmp_5122 = tmp_struct_28.field0;
                IntTy pvrtmp_5123 = tmp_struct_28.field1;

                return (CursorInt64Prod) {pvrtmp_5122, pvrtmp_5123};
            } else {
                IntTy fltAppE_1496_1604 = k_135_1267_1590 + 1;
                CursorInt64Prod tmp_struct_29 =
                                 findk(end_r_2449, fltAppE_1496_1604, km_136_1268_1591, m_137_1269_1592, tmpcur_5119);
                CursorTy pvrtmp_5124 = tmp_struct_29.field0;
                IntTy pvrtmp_5125 = tmp_struct_29.field1;

                return (CursorInt64Prod) {pvrtmp_5124, pvrtmp_5125};
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5126 = *(CursorTy *) tmpcur_5115;
            CursorTy tmpaftercur_5127 = tmpcur_5115 + 8;
            CursorTy jump_3303 = tmpcur_5115 + 8;
            CursorInt64Prod tmp_struct_30 =
                             findk(end_r_2449, k_135_1267_1590, km_136_1268_1591, m_137_1269_1592, tmpcur_5126);
            CursorTy pvrtmp_5128 = tmp_struct_30.field0;
            IntTy pvrtmp_5129 = tmp_struct_30.field1;

            return (CursorInt64Prod) {jump_3303, pvrtmp_5129};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5130 = *(CursorTy *) tmpcur_5115;
            CursorTy tmpaftercur_5131 = tmpcur_5115 + 8;
            CursorInt64Prod tmp_struct_31 =
                             findk(end_r_2449, k_135_1267_1590, km_136_1268_1591, m_137_1269_1592, tmpcur_5130);
            CursorTy pvrtmp_5132 = tmp_struct_31.field0;
            IntTy pvrtmp_5133 = tmp_struct_31.field1;

            return (CursorInt64Prod) {pvrtmp_5132, pvrtmp_5133};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5114");
            exit(1);
        }
    }
}
CursorCursorCursorProd algc(CursorTy end_r_2454, CursorTy end_r_2455,
                            CursorTy end_r_2456, CursorTy end_r_2457,
                            CursorTy loc_2453, IntTy m_144_1277_1605,
                            IntTy n_145_1278_1606, CursorTy xs_146_1279_1607,
                            CursorTy ys_147_1280_1608,
                            CursorTy zs_148_1281_1609)
{
    if (loc_2453 + 32 > end_r_2457) {
        ChunkTy new_chunk_33 = alloc_chunk(end_r_2457);
        CursorTy chunk_start_34 = new_chunk_33.chunk_start;
        CursorTy chunk_end_35 = new_chunk_33.chunk_end;

        end_r_2457 = chunk_end_35;
        *(TagTyPacked *) loc_2453 = 255;

        CursorTy redir = loc_2453 + 1;

        *(CursorTy *) redir = chunk_start_34;
        loc_2453 = chunk_start_34;
    }

    BoolTy fltIf_1497_1610 =  is_empty_plist_781(end_r_2455, ys_147_1280_1608);

    if (fltIf_1497_1610) {
        bump_ref_count(end_r_2457, end_r_2456);
        *(TagTyPacked *) loc_2453 = 254;

        CursorTy writetag_3603 = loc_2453 + 1;

        *(CursorTy *) writetag_3603 = zs_148_1281_1609;

        CursorTy writecur_3604 = writetag_3603 + 8;

        return (CursorCursorCursorProd) {end_r_2457, loc_2453, writecur_3604};
    } else {
        CursorCursorCursorProd tmp_struct_32 =
                                caseFn_1222(end_r_2454, end_r_2455, end_r_2456, end_r_2457, loc_2453, m_144_1277_1605, n_145_1278_1606, xs_146_1279_1607, ys_147_1280_1608, zs_148_1281_1609);
        CursorTy pvrtmp_5139 = tmp_struct_32.field0;
        CursorTy pvrtmp_5140 = tmp_struct_32.field1;
        CursorTy pvrtmp_5141 = tmp_struct_32.field2;

        return (CursorCursorCursorProd) {pvrtmp_5139, pvrtmp_5140, pvrtmp_5141};
    }
}
CursorCursorCursorCursorProd algb2(CursorTy end_r_2460, CursorTy end_r_2461,
                                   CursorTy loc_2459, IntTy x_164_1282_1611,
                                   IntTy k0j1_165_1283_1612,
                                   IntTy k1j1_166_1284_1613,
                                   CursorTy ls_167_1285_1614)
{
    if (loc_2459 + 32 > end_r_2461) {
        ChunkTy new_chunk_39 = alloc_chunk(end_r_2461);
        CursorTy chunk_start_40 = new_chunk_39.chunk_start;
        CursorTy chunk_end_41 = new_chunk_39.chunk_end;

        end_r_2461 = chunk_end_41;
        *(TagTyPacked *) loc_2459 = 255;

        CursorTy redir = loc_2459 + 1;

        *(CursorTy *) redir = chunk_start_40;
        loc_2459 = chunk_start_40;
    }

    TagTyPacked tmpval_5148 = *(TagTyPacked *) ls_167_1285_1614;
    CursorTy tmpcur_5149 = ls_167_1285_1614 + 1;


  switch_5197:
    ;
    switch (tmpval_5148) {

      case 0:
        {
            CursorTy jump_3130 = ls_167_1285_1614 + 1;

            *(TagTyPacked *) loc_2459 = 0;

            CursorTy writetag_3608 = loc_2459 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2461, jump_3130,
                                                   loc_2459, writetag_3608};
            break;
        }

      case 1:
        {
            IntTy tmpval_5154 = *(IntTy *) tmpcur_5149;
            CursorTy tmpcur_5155 = tmpcur_5149 + sizeof(IntTy);
            IntTy tmpval_5156 = *(IntTy *) tmpcur_5155;
            CursorTy tmpcur_5157 = tmpcur_5155 + sizeof(IntTy);
            CursorTy jump_3133 = tmpcur_5155 + 8;
            CursorTy jump_3132 = tmpcur_5149 + 8;
            BoolTy fltIf_1498_1621 = x_164_1282_1611 == tmpval_5154;
            IntTy kjcurr_173_1292_1622;

            if (fltIf_1498_1621) {
                IntTy flt_5160 = k0j1_165_1283_1612 + 1;

                kjcurr_173_1292_1622 = flt_5160;
            } else {
                IntTy kjcurr_173_1292_1622hack =
                       maxInt(k1j1_166_1284_1613, tmpval_5156);

                kjcurr_173_1292_1622 = kjcurr_173_1292_1622hack;
            }

            CursorTy loc_2668 = loc_2459 + 1;
            CursorTy loc_2669 = loc_2668 + 8;
            CursorTy loc_2670 = loc_2669 + 8;
            CursorCursorCursorCursorProd tmp_struct_36 =
                                          algb2(end_r_2460, end_r_2461, loc_2670, x_164_1282_1611, tmpval_5156, kjcurr_173_1292_1622, tmpcur_5157);
            CursorTy pvrtmp_5161 = tmp_struct_36.field0;
            CursorTy pvrtmp_5162 = tmp_struct_36.field1;
            CursorTy pvrtmp_5163 = tmp_struct_36.field2;
            CursorTy pvrtmp_5164 = tmp_struct_36.field3;

            *(TagTyPacked *) loc_2459 = 1;

            CursorTy writetag_3614 = loc_2459 + 1;

            *(IntTy *) writetag_3614 = tmpval_5154;

            CursorTy writecur_3615 = writetag_3614 + sizeof(IntTy);

            *(IntTy *) writecur_3615 = kjcurr_173_1292_1622;

            CursorTy writecur_3616 = writecur_3615 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_5161, pvrtmp_5162,
                                                   loc_2459, pvrtmp_5164};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5173 = *(CursorTy *) tmpcur_5149;
            CursorTy tmpaftercur_5174 = tmpcur_5149 + 8;
            CursorTy jump_3309 = tmpcur_5149 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          algb2(end_r_2460, end_r_2461, loc_2459, x_164_1282_1611, k0j1_165_1283_1612, k1j1_166_1284_1613, tmpcur_5173);
            CursorTy pvrtmp_5175 = tmp_struct_37.field0;
            CursorTy pvrtmp_5176 = tmp_struct_37.field1;
            CursorTy pvrtmp_5177 = tmp_struct_37.field2;
            CursorTy pvrtmp_5178 = tmp_struct_37.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5175, jump_3309,
                                                   pvrtmp_5177, pvrtmp_5178};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5185 = *(CursorTy *) tmpcur_5149;
            CursorTy tmpaftercur_5186 = tmpcur_5149 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          algb2(end_r_2460, end_r_2461, loc_2459, x_164_1282_1611, k0j1_165_1283_1612, k1j1_166_1284_1613, tmpcur_5185);
            CursorTy pvrtmp_5187 = tmp_struct_38.field0;
            CursorTy pvrtmp_5188 = tmp_struct_38.field1;
            CursorTy pvrtmp_5189 = tmp_struct_38.field2;
            CursorTy pvrtmp_5190 = tmp_struct_38.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5187, pvrtmp_5188,
                                                   pvrtmp_5189, pvrtmp_5190};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5148");
            exit(1);
        }
    }
}
CursorCursorCursorCursorCursorProd algb1(CursorTy end_r_2465,
                                         CursorTy end_r_2466,
                                         CursorTy end_r_2467, CursorTy loc_2464,
                                         CursorTy xs_174_1293_1624,
                                         CursorTy ys_175_1294_1625)
{
    if (loc_2464 + 32 > end_r_2467) {
        ChunkTy new_chunk_47 = alloc_chunk(end_r_2467);
        CursorTy chunk_start_48 = new_chunk_47.chunk_start;
        CursorTy chunk_end_49 = new_chunk_47.chunk_end;

        end_r_2467 = chunk_end_49;
        *(TagTyPacked *) loc_2464 = 255;

        CursorTy redir = loc_2464 + 1;

        *(CursorTy *) redir = chunk_start_48;
        loc_2464 = chunk_start_48;
    }

    TagTyPacked tmpval_5198 = *(TagTyPacked *) xs_174_1293_1624;
    CursorTy tmpcur_5199 = xs_174_1293_1624 + 1;


  switch_5259:
    ;
    switch (tmpval_5198) {

      case 0:
        {
            CursorTy jump_3136 = xs_174_1293_1624 + 1;
            CursorCursorCursorCursorProd tmp_struct_42 =
                                          map_plist_787_1071(end_r_2466, end_r_2467, loc_2464, ys_175_1294_1625);
            CursorTy pvrtmp_5200 = tmp_struct_42.field0;
            CursorTy pvrtmp_5201 = tmp_struct_42.field1;
            CursorTy pvrtmp_5202 = tmp_struct_42.field2;
            CursorTy pvrtmp_5203 = tmp_struct_42.field3;

            return (CursorCursorCursorCursorCursorProd) {pvrtmp_5200, jump_3136,
                                                         pvrtmp_5201,
                                                         pvrtmp_5202,
                                                         pvrtmp_5203};
            break;
        }

      case 1:
        {
            RegionTy *region_5210 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2694 = region_5210->reg_heap;
            IntTy sizeof_end_r_2694_5211 = global_init_inf_buf_size;
            CursorTy end_r_2694 = r_2694 + sizeof_end_r_2694_5211;
            IntTy tmpval_5212 = *(IntTy *) tmpcur_5199;
            CursorTy tmpcur_5213 = tmpcur_5199 + sizeof(IntTy);
            CursorTy jump_3139 = tmpcur_5199 + 8;
            CursorCursorCursorCursorProd tmp_struct_43 =
                                          algb2(end_r_2466, end_r_2694, r_2694, tmpval_5212, 0, 0, ys_175_1294_1625);
            CursorTy pvrtmp_5214 = tmp_struct_43.field0;
            CursorTy pvrtmp_5215 = tmp_struct_43.field1;
            CursorTy pvrtmp_5216 = tmp_struct_43.field2;
            CursorTy pvrtmp_5217 = tmp_struct_43.field3;
            CursorCursorCursorCursorCursorProd tmp_struct_44 =
                                                algb1(end_r_2465, pvrtmp_5214, end_r_2467, loc_2464, tmpcur_5213, pvrtmp_5216);
            CursorTy pvrtmp_5222 = tmp_struct_44.field0;
            CursorTy pvrtmp_5223 = tmp_struct_44.field1;
            CursorTy pvrtmp_5224 = tmp_struct_44.field2;
            CursorTy pvrtmp_5225 = tmp_struct_44.field3;
            CursorTy pvrtmp_5226 = tmp_struct_44.field4;

            free_region(end_r_2694);
            return (CursorCursorCursorCursorCursorProd) {pvrtmp_5222,
                                                         pvrtmp_5223,
                                                         pvrtmp_5215,
                                                         pvrtmp_5225,
                                                         pvrtmp_5226};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5233 = *(CursorTy *) tmpcur_5199;
            CursorTy tmpaftercur_5234 = tmpcur_5199 + 8;
            CursorTy jump_3315 = tmpcur_5199 + 8;
            CursorCursorCursorCursorCursorProd tmp_struct_45 =
                                                algb1(end_r_2465, end_r_2466, end_r_2467, loc_2464, tmpcur_5233, ys_175_1294_1625);
            CursorTy pvrtmp_5235 = tmp_struct_45.field0;
            CursorTy pvrtmp_5236 = tmp_struct_45.field1;
            CursorTy pvrtmp_5237 = tmp_struct_45.field2;
            CursorTy pvrtmp_5238 = tmp_struct_45.field3;
            CursorTy pvrtmp_5239 = tmp_struct_45.field4;

            return (CursorCursorCursorCursorCursorProd) {pvrtmp_5235, jump_3315,
                                                         pvrtmp_5237,
                                                         pvrtmp_5238,
                                                         pvrtmp_5239};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5246 = *(CursorTy *) tmpcur_5199;
            CursorTy tmpaftercur_5247 = tmpcur_5199 + 8;
            CursorCursorCursorCursorCursorProd tmp_struct_46 =
                                                algb1(end_r_2465, end_r_2466, end_r_2467, loc_2464, tmpcur_5246, ys_175_1294_1625);
            CursorTy pvrtmp_5248 = tmp_struct_46.field0;
            CursorTy pvrtmp_5249 = tmp_struct_46.field1;
            CursorTy pvrtmp_5250 = tmp_struct_46.field2;
            CursorTy pvrtmp_5251 = tmp_struct_46.field3;
            CursorTy pvrtmp_5252 = tmp_struct_46.field4;

            return (CursorCursorCursorCursorCursorProd) {pvrtmp_5248,
                                                         pvrtmp_5249,
                                                         pvrtmp_5250,
                                                         pvrtmp_5251,
                                                         pvrtmp_5252};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5198");
            exit(1);
        }
    }
}
CursorCursorCursorCursorCursorProd algb(CursorTy end_r_2471,
                                        CursorTy end_r_2472,
                                        CursorTy end_r_2473, CursorTy loc_2470,
                                        CursorTy xs_181_1297_1629,
                                        CursorTy ys_182_1298_1630)
{
    RegionTy *region_5260 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2707 = region_5260->reg_heap;
    IntTy sizeof_end_r_2707_5261 = global_init_inf_buf_size;
    CursorTy end_r_2707 = r_2707 + sizeof_end_r_2707_5261;

    if (loc_2470 + 32 > end_r_2473) {
        ChunkTy new_chunk_52 = alloc_chunk(end_r_2473);
        CursorTy chunk_start_53 = new_chunk_52.chunk_start;
        CursorTy chunk_end_54 = new_chunk_52.chunk_end;

        end_r_2473 = chunk_end_54;
        *(TagTyPacked *) loc_2470 = 255;

        CursorTy redir = loc_2470 + 1;

        *(CursorTy *) redir = chunk_start_53;
        loc_2470 = chunk_start_53;
    }

    CursorCursorCursorCursorProd tmp_struct_50 =
                                  zip0(end_r_2472, end_r_2707, r_2707, ys_182_1298_1630);
    CursorTy pvrtmp_5262 = tmp_struct_50.field0;
    CursorTy pvrtmp_5263 = tmp_struct_50.field1;
    CursorTy pvrtmp_5264 = tmp_struct_50.field2;
    CursorTy pvrtmp_5265 = tmp_struct_50.field3;
    CursorTy loc_2704 = loc_2470 + 1;
    CursorTy loc_2705 = loc_2704 + 8;
    CursorCursorCursorCursorCursorProd tmp_struct_51 =
                                        algb1(end_r_2471, pvrtmp_5262, end_r_2473, loc_2705, xs_181_1297_1629, pvrtmp_5264);
    CursorTy pvrtmp_5270 = tmp_struct_51.field0;
    CursorTy pvrtmp_5271 = tmp_struct_51.field1;
    CursorTy pvrtmp_5272 = tmp_struct_51.field2;
    CursorTy pvrtmp_5273 = tmp_struct_51.field3;
    CursorTy pvrtmp_5274 = tmp_struct_51.field4;

    *(TagTyPacked *) loc_2470 = 1;

    CursorTy writetag_3639 = loc_2470 + 1;

    *(IntTy *) writetag_3639 = 0;

    CursorTy writecur_3640 = writetag_3639 + sizeof(IntTy);

    free_region(end_r_2707);
    return (CursorCursorCursorCursorCursorProd) {pvrtmp_5270, pvrtmp_5271,
                                                 pvrtmp_5263, loc_2470,
                                                 pvrtmp_5274};
}
IntTy maxInt(IntTy a_189_1299_1633, IntTy b_190_1300_1634)
{
    BoolTy fltIf_1503_1635 = a_189_1299_1633 > b_190_1300_1634;

    if (fltIf_1503_1635) {
        return a_189_1299_1633;
    } else {
        return b_190_1300_1634;
    }
}
CursorInt64Prod length_plist_780(CursorTy end_r_2475, CursorTy a_226_1319_1636)
{
    TagTyPacked tmpval_5283 = *(TagTyPacked *) a_226_1319_1636;
    CursorTy tmpcur_5284 = a_226_1319_1636 + 1;


  switch_5297:
    ;
    switch (tmpval_5283) {

      case 0:
        {
            CursorTy jump_3149 = a_226_1319_1636 + 1;

            return (CursorInt64Prod) {jump_3149, 0};
            break;
        }

      case 1:
        {
            IntTy tmpval_5285 = *(IntTy *) tmpcur_5284;
            CursorTy tmpcur_5286 = tmpcur_5284 + sizeof(IntTy);
            CursorTy jump_3150 = tmpcur_5284 + 8;
            CursorInt64Prod tmp_struct_55 =
                             length_plist_780(end_r_2475, tmpcur_5286);
            CursorTy pvrtmp_5287 = tmp_struct_55.field0;
            IntTy pvrtmp_5288 = tmp_struct_55.field1;
            IntTy tailprim_3152 = 1 + pvrtmp_5288;

            return (CursorInt64Prod) {pvrtmp_5287, tailprim_3152};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5289 = *(CursorTy *) tmpcur_5284;
            CursorTy tmpaftercur_5290 = tmpcur_5284 + 8;
            CursorTy jump_3322 = tmpcur_5284 + 8;
            CursorInt64Prod tmp_struct_56 =
                             length_plist_780(end_r_2475, tmpcur_5289);
            CursorTy pvrtmp_5291 = tmp_struct_56.field0;
            IntTy pvrtmp_5292 = tmp_struct_56.field1;

            return (CursorInt64Prod) {jump_3322, pvrtmp_5292};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5293 = *(CursorTy *) tmpcur_5284;
            CursorTy tmpaftercur_5294 = tmpcur_5284 + 8;
            CursorInt64Prod tmp_struct_57 =
                             length_plist_780(end_r_2475, tmpcur_5293);
            CursorTy pvrtmp_5295 = tmp_struct_57.field0;
            IntTy pvrtmp_5296 = tmp_struct_57.field1;

            return (CursorInt64Prod) {pvrtmp_5295, pvrtmp_5296};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5283");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd reverse_plist_785(CursorTy end_r_2479,
                                               CursorTy end_r_2480,
                                               CursorTy end_r_2481,
                                               CursorTy loc_2478,
                                               CursorTy xs_221_1322_1640,
                                               CursorTy acc_222_1323_1641)
{
    if (loc_2478 + 32 > end_r_2481) {
        ChunkTy new_chunk_61 = alloc_chunk(end_r_2481);
        CursorTy chunk_start_62 = new_chunk_61.chunk_start;
        CursorTy chunk_end_63 = new_chunk_61.chunk_end;

        end_r_2481 = chunk_end_63;
        *(TagTyPacked *) loc_2478 = 255;

        CursorTy redir = loc_2478 + 1;

        *(CursorTy *) redir = chunk_start_62;
        loc_2478 = chunk_start_62;
    }

    TagTyPacked tmpval_5298 = *(TagTyPacked *) xs_221_1322_1640;
    CursorTy tmpcur_5299 = xs_221_1322_1640 + 1;


  switch_5346:
    ;
    switch (tmpval_5298) {

      case 0:
        {
            CursorTy jump_3153 = xs_221_1322_1640 + 1;

            bump_ref_count(end_r_2481, end_r_2480);
            *(TagTyPacked *) loc_2478 = 254;

            CursorTy writetag_3654 = loc_2478 + 1;

            *(CursorTy *) writetag_3654 = acc_222_1323_1641;

            CursorTy writecur_3655 = writetag_3654 + 8;

            return (CursorCursorCursorCursorProd) {end_r_2481, jump_3153,
                                                   loc_2478, writecur_3655};
            break;
        }

      case 1:
        {
            RegionTy *region_5304 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2731 = region_5304->reg_heap;
            IntTy sizeof_end_r_2731_5305 = global_init_inf_buf_size;
            CursorTy end_r_2731 = r_2731 + sizeof_end_r_2731_5305;
            IntTy tmpval_5306 = *(IntTy *) tmpcur_5299;
            CursorTy tmpcur_5307 = tmpcur_5299 + sizeof(IntTy);
            CursorTy jump_3154 = tmpcur_5299 + 8;
            CursorTy loc_2719 = r_2731 + 1;
            CursorTy loc_2720 = loc_2719 + 8;

            bump_ref_count(end_r_2731, end_r_2480);
            *(TagTyPacked *) loc_2720 = 254;

            CursorTy writetag_3659 = loc_2720 + 1;

            *(CursorTy *) writetag_3659 = acc_222_1323_1641;

            CursorTy writecur_3660 = writetag_3659 + 8;

            *(TagTyPacked *) r_2731 = 1;

            CursorTy writetag_3662 = r_2731 + 1;

            *(IntTy *) writetag_3662 = tmpval_5306;

            CursorTy writecur_3663 = writetag_3662 + sizeof(IntTy);
            CursorCursorCursorCursorProd tmp_struct_58 =
                                          reverse_plist_785(end_r_2479, end_r_2731, end_r_2481, loc_2478, tmpcur_5307, r_2731);
            CursorTy pvrtmp_5312 = tmp_struct_58.field0;
            CursorTy pvrtmp_5313 = tmp_struct_58.field1;
            CursorTy pvrtmp_5314 = tmp_struct_58.field2;
            CursorTy pvrtmp_5315 = tmp_struct_58.field3;

            free_region(end_r_2731);
            return (CursorCursorCursorCursorProd) {pvrtmp_5312, pvrtmp_5313,
                                                   pvrtmp_5314, pvrtmp_5315};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5322 = *(CursorTy *) tmpcur_5299;
            CursorTy tmpaftercur_5323 = tmpcur_5299 + 8;
            CursorTy jump_3328 = tmpcur_5299 + 8;
            CursorCursorCursorCursorProd tmp_struct_59 =
                                          reverse_plist_785(end_r_2479, end_r_2480, end_r_2481, loc_2478, tmpcur_5322, acc_222_1323_1641);
            CursorTy pvrtmp_5324 = tmp_struct_59.field0;
            CursorTy pvrtmp_5325 = tmp_struct_59.field1;
            CursorTy pvrtmp_5326 = tmp_struct_59.field2;
            CursorTy pvrtmp_5327 = tmp_struct_59.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5324, jump_3328,
                                                   pvrtmp_5326, pvrtmp_5327};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5334 = *(CursorTy *) tmpcur_5299;
            CursorTy tmpaftercur_5335 = tmpcur_5299 + 8;
            CursorCursorCursorCursorProd tmp_struct_60 =
                                          reverse_plist_785(end_r_2479, end_r_2480, end_r_2481, loc_2478, tmpcur_5334, acc_222_1323_1641);
            CursorTy pvrtmp_5336 = tmp_struct_60.field0;
            CursorTy pvrtmp_5337 = tmp_struct_60.field1;
            CursorTy pvrtmp_5338 = tmp_struct_60.field2;
            CursorTy pvrtmp_5339 = tmp_struct_60.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5336, pvrtmp_5337,
                                                   pvrtmp_5338, pvrtmp_5339};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5298");
            exit(1);
        }
    }
}
CursorCursorCursorProd zip_plist_786(CursorTy end_r_2485, CursorTy end_r_2486,
                                     CursorTy end_r_2487, CursorTy loc_2484,
                                     CursorTy as_213_1326_1645,
                                     CursorTy bs_214_1327_1646)
{
    if (loc_2484 + 32 > end_r_2487) {
        ChunkTy new_chunk_67 = alloc_chunk(end_r_2487);
        CursorTy chunk_start_68 = new_chunk_67.chunk_start;
        CursorTy chunk_end_69 = new_chunk_67.chunk_end;

        end_r_2487 = chunk_end_69;
        *(TagTyPacked *) loc_2484 = 255;

        CursorTy redir = loc_2484 + 1;

        *(CursorTy *) redir = chunk_start_68;
        loc_2484 = chunk_start_68;
    }

    TagTyPacked tmpval_5347 = *(TagTyPacked *) as_213_1326_1645;
    CursorTy tmpcur_5348 = as_213_1326_1645 + 1;


  switch_5386:
    ;
    switch (tmpval_5347) {

      case 0:
        {
            CursorTy jump_3157 = as_213_1326_1645 + 1;

            *(TagTyPacked *) loc_2484 = 0;

            CursorTy writetag_3674 = loc_2484 + 1;

            return (CursorCursorCursorProd) {end_r_2487, loc_2484,
                                             writetag_3674};
            break;
        }

      case 1:
        {
            IntTy tmpval_5353 = *(IntTy *) tmpcur_5348;
            CursorTy tmpcur_5354 = tmpcur_5348 + sizeof(IntTy);
            CursorTy jump_3159 = tmpcur_5348 + 8;
            CursorCursorCursorProd tmp_struct_64 =
                                    caseFn_1228(end_r_2486, end_r_2485, end_r_2487, loc_2484, bs_214_1327_1646, tmpval_5353, tmpcur_5354);
            CursorTy pvrtmp_5355 = tmp_struct_64.field0;
            CursorTy pvrtmp_5356 = tmp_struct_64.field1;
            CursorTy pvrtmp_5357 = tmp_struct_64.field2;

            return (CursorCursorCursorProd) {pvrtmp_5355, pvrtmp_5356,
                                             pvrtmp_5357};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5364 = *(CursorTy *) tmpcur_5348;
            CursorTy tmpaftercur_5365 = tmpcur_5348 + 8;
            CursorTy jump_3334 = tmpcur_5348 + 8;
            CursorCursorCursorProd tmp_struct_65 =
                                    zip_plist_786(end_r_2485, end_r_2486, end_r_2487, loc_2484, tmpcur_5364, bs_214_1327_1646);
            CursorTy pvrtmp_5366 = tmp_struct_65.field0;
            CursorTy pvrtmp_5367 = tmp_struct_65.field1;
            CursorTy pvrtmp_5368 = tmp_struct_65.field2;

            return (CursorCursorCursorProd) {pvrtmp_5366, pvrtmp_5367,
                                             pvrtmp_5368};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5375 = *(CursorTy *) tmpcur_5348;
            CursorTy tmpaftercur_5376 = tmpcur_5348 + 8;
            CursorCursorCursorProd tmp_struct_66 =
                                    zip_plist_786(end_r_2485, end_r_2486, end_r_2487, loc_2484, tmpcur_5375, bs_214_1327_1646);
            CursorTy pvrtmp_5377 = tmp_struct_66.field0;
            CursorTy pvrtmp_5378 = tmp_struct_66.field1;
            CursorTy pvrtmp_5379 = tmp_struct_66.field2;

            return (CursorCursorCursorProd) {pvrtmp_5377, pvrtmp_5378,
                                             pvrtmp_5379};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5347");
            exit(1);
        }
    }
}
CursorCursorCursorProd drop_plist_784(CursorTy end_r_2490, CursorTy end_r_2491,
                                      CursorTy loc_2489,
                                      IntTy num_208_1330_1649,
                                      CursorTy list_209_1331_1650)
{
    if (loc_2489 + 32 > end_r_2491) {
        ChunkTy new_chunk_73 = alloc_chunk(end_r_2491);
        CursorTy chunk_start_74 = new_chunk_73.chunk_start;
        CursorTy chunk_end_75 = new_chunk_73.chunk_end;

        end_r_2491 = chunk_end_75;
        *(TagTyPacked *) loc_2489 = 255;

        CursorTy redir = loc_2489 + 1;

        *(CursorTy *) redir = chunk_start_74;
        loc_2489 = chunk_start_74;
    }

    TagTyPacked tmpval_5387 = *(TagTyPacked *) list_209_1331_1650;
    CursorTy tmpcur_5388 = list_209_1331_1650 + 1;


  switch_5432:
    ;
    switch (tmpval_5387) {

      case 0:
        {
            CursorTy jump_3161 = list_209_1331_1650 + 1;

            *(TagTyPacked *) loc_2489 = 0;

            CursorTy writetag_3686 = loc_2489 + 1;

            return (CursorCursorCursorProd) {end_r_2491, loc_2489,
                                             writetag_3686};
            break;
        }

      case 1:
        {
            IntTy tmpval_5393 = *(IntTy *) tmpcur_5388;
            CursorTy tmpcur_5394 = tmpcur_5388 + sizeof(IntTy);
            CursorTy jump_3163 = tmpcur_5388 + 8;
            BoolTy fltIf_1506_1653 = num_208_1330_1649 <= 0;

            if (fltIf_1506_1653) {
                CursorTy loc_2748 = loc_2489 + 1;
                CursorTy loc_2749 = loc_2748 + 8;

                bump_ref_count(end_r_2491, end_r_2490);
                *(TagTyPacked *) loc_2749 = 254;

                CursorTy writetag_3690 = loc_2749 + 1;

                *(CursorTy *) writetag_3690 = tmpcur_5394;

                CursorTy writecur_3691 = writetag_3690 + 8;

                *(TagTyPacked *) loc_2489 = 1;

                CursorTy writetag_3693 = loc_2489 + 1;

                *(IntTy *) writetag_3693 = tmpval_5393;

                CursorTy writecur_3694 = writetag_3693 + sizeof(IntTy);

                return (CursorCursorCursorProd) {end_r_2491, loc_2489,
                                                 writecur_3691};
            } else {
                IntTy fltAppE_1507_1654 = num_208_1330_1649 - 1;
                CursorCursorCursorProd tmp_struct_70 =
                                        drop_plist_784(end_r_2490, end_r_2491, loc_2489, fltAppE_1507_1654, tmpcur_5394);
                CursorTy pvrtmp_5401 = tmp_struct_70.field0;
                CursorTy pvrtmp_5402 = tmp_struct_70.field1;
                CursorTy pvrtmp_5403 = tmp_struct_70.field2;

                return (CursorCursorCursorProd) {pvrtmp_5401, pvrtmp_5402,
                                                 pvrtmp_5403};
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5410 = *(CursorTy *) tmpcur_5388;
            CursorTy tmpaftercur_5411 = tmpcur_5388 + 8;
            CursorTy jump_3339 = tmpcur_5388 + 8;
            CursorCursorCursorProd tmp_struct_71 =
                                    drop_plist_784(end_r_2490, end_r_2491, loc_2489, num_208_1330_1649, tmpcur_5410);
            CursorTy pvrtmp_5412 = tmp_struct_71.field0;
            CursorTy pvrtmp_5413 = tmp_struct_71.field1;
            CursorTy pvrtmp_5414 = tmp_struct_71.field2;

            return (CursorCursorCursorProd) {pvrtmp_5412, pvrtmp_5413,
                                             pvrtmp_5414};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5421 = *(CursorTy *) tmpcur_5388;
            CursorTy tmpaftercur_5422 = tmpcur_5388 + 8;
            CursorCursorCursorProd tmp_struct_72 =
                                    drop_plist_784(end_r_2490, end_r_2491, loc_2489, num_208_1330_1649, tmpcur_5421);
            CursorTy pvrtmp_5423 = tmp_struct_72.field0;
            CursorTy pvrtmp_5424 = tmp_struct_72.field1;
            CursorTy pvrtmp_5425 = tmp_struct_72.field2;

            return (CursorCursorCursorProd) {pvrtmp_5423, pvrtmp_5424,
                                             pvrtmp_5425};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5387");
            exit(1);
        }
    }
}
CursorCursorCursorProd take_plist_783(CursorTy end_r_2494, CursorTy end_r_2495,
                                      CursorTy loc_2493, IntTy n_203_1334_1655,
                                      CursorTy a_204_1335_1656)
{
    if (loc_2493 + 32 > end_r_2495) {
        ChunkTy new_chunk_77 = alloc_chunk(end_r_2495);
        CursorTy chunk_start_78 = new_chunk_77.chunk_start;
        CursorTy chunk_end_79 = new_chunk_77.chunk_end;

        end_r_2495 = chunk_end_79;
        *(TagTyPacked *) loc_2493 = 255;

        CursorTy redir = loc_2493 + 1;

        *(CursorTy *) redir = chunk_start_78;
        loc_2493 = chunk_start_78;
    }

    BoolTy fltIf_1508_1657 = n_203_1334_1655 == 0;

    if (fltIf_1508_1657) {
        *(TagTyPacked *) loc_2493 = 0;

        CursorTy writetag_3704 = loc_2493 + 1;

        return (CursorCursorCursorProd) {end_r_2495, loc_2493, writetag_3704};
    } else {
        CursorCursorCursorProd tmp_struct_76 =
                                caseFn_1232(end_r_2494, end_r_2495, loc_2493, n_203_1334_1655, a_204_1335_1656);
        CursorTy pvrtmp_5437 = tmp_struct_76.field0;
        CursorTy pvrtmp_5438 = tmp_struct_76.field1;
        CursorTy pvrtmp_5439 = tmp_struct_76.field2;

        return (CursorCursorCursorProd) {pvrtmp_5437, pvrtmp_5438, pvrtmp_5439};
    }
}
BoolTy is_empty_plist_781(CursorTy end_r_2497, CursorTy ls_191_1336_1658)
{
    TagTyPacked tmpval_5446 = *(TagTyPacked *) ls_191_1336_1658;
    CursorTy tmpcur_5447 = ls_191_1336_1658 + 1;


  switch_5454:
    ;
    switch (tmpval_5446) {

      case 0:
        {
            CursorTy jump_3170 = ls_191_1336_1658 + 1;

            return true;
            break;
        }

      case 1:
        {
            IntTy tmpval_5448 = *(IntTy *) tmpcur_5447;
            CursorTy tmpcur_5449 = tmpcur_5447 + sizeof(IntTy);
            CursorTy jump_3171 = tmpcur_5447 + 8;

            return false;
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5450 = *(CursorTy *) tmpcur_5447;
            CursorTy tmpaftercur_5451 = tmpcur_5447 + 8;
            CursorTy jump_3344 = tmpcur_5447 + 8;
            BoolTy call_3345 =  is_empty_plist_781(end_r_2497, tmpcur_5450);

            return call_3345;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5452 = *(CursorTy *) tmpcur_5447;
            CursorTy tmpaftercur_5453 = tmpcur_5447 + 8;
            BoolTy call_3345 =  is_empty_plist_781(end_r_2497, tmpcur_5452);

            return call_3345;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5446");
            exit(1);
        }
    }
}
BoolTy elem_plist_782_1069(CursorTy end_r_2499, IntTy a_196_1342_1661,
                           CursorTy list_197_1343_1662)
{
    TagTyPacked tmpval_5455 = *(TagTyPacked *) list_197_1343_1662;
    CursorTy tmpcur_5456 = list_197_1343_1662 + 1;


  switch_5464:
    ;
    switch (tmpval_5455) {

      case 0:
        {
            CursorTy jump_3174 = list_197_1343_1662 + 1;

            return false;
            break;
        }

      case 1:
        {
            IntTy tmpval_5457 = *(IntTy *) tmpcur_5456;
            CursorTy tmpcur_5458 = tmpcur_5456 + sizeof(IntTy);
            CursorTy jump_3175 = tmpcur_5456 + 8;
            BoolTy fltIf_1511_1667 = tmpval_5457 < a_196_1342_1661;
            IntTy fltPrm_1510_1669;

            if (fltIf_1511_1667) {
                IntTy flt_5459 = 0 - 1;

                fltPrm_1510_1669 = flt_5459;
            } else {
                BoolTy fltIf_1512_1668 = tmpval_5457 > a_196_1342_1661;

                if (fltIf_1512_1668) {
                    fltPrm_1510_1669 = 1;
                } else {
                    fltPrm_1510_1669 = 0;
                }
            }

            BoolTy fltIf_1509_1670 = fltPrm_1510_1669 == 0;

            if (fltIf_1509_1670) {
                return true;
            } else {
                BoolTy fltPrm_1514_1672 =
                        elem_plist_782_1069(end_r_2499, a_196_1342_1661, tmpcur_5458);
                BoolTy tailprim_3176 = false || fltPrm_1514_1672;

                return tailprim_3176;
            }
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5460 = *(CursorTy *) tmpcur_5456;
            CursorTy tmpaftercur_5461 = tmpcur_5456 + 8;
            CursorTy jump_3349 = tmpcur_5456 + 8;
            BoolTy call_3350 =
                    elem_plist_782_1069(end_r_2499, a_196_1342_1661, tmpcur_5460);

            return call_3350;
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5462 = *(CursorTy *) tmpcur_5456;
            CursorTy tmpaftercur_5463 = tmpcur_5456 + 8;
            BoolTy call_3350 =
                    elem_plist_782_1069(end_r_2499, a_196_1342_1661, tmpcur_5462);

            return call_3350;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5455");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd map_plist_787_1071(CursorTy end_r_2502,
                                                CursorTy end_r_2503,
                                                CursorTy loc_2501,
                                                CursorTy ls_184_1346_1673)
{
    if (loc_2501 + 32 > end_r_2503) {
        ChunkTy new_chunk_83 = alloc_chunk(end_r_2503);
        CursorTy chunk_start_84 = new_chunk_83.chunk_start;
        CursorTy chunk_end_85 = new_chunk_83.chunk_end;

        end_r_2503 = chunk_end_85;
        *(TagTyPacked *) loc_2501 = 255;

        CursorTy redir = loc_2501 + 1;

        *(CursorTy *) redir = chunk_start_84;
        loc_2501 = chunk_start_84;
    }

    TagTyPacked tmpval_5465 = *(TagTyPacked *) ls_184_1346_1673;
    CursorTy tmpcur_5466 = ls_184_1346_1673 + 1;


  switch_5513:
    ;
    switch (tmpval_5465) {

      case 0:
        {
            CursorTy jump_3177 = ls_184_1346_1673 + 1;

            *(TagTyPacked *) loc_2501 = 0;

            CursorTy writetag_3722 = loc_2501 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2503, jump_3177,
                                                   loc_2501, writetag_3722};
            break;
        }

      case 1:
        {
            IntTy tmpval_5471 = *(IntTy *) tmpcur_5466;
            CursorTy tmpcur_5472 = tmpcur_5466 + sizeof(IntTy);
            IntTy tmpval_5473 = *(IntTy *) tmpcur_5472;
            CursorTy tmpcur_5474 = tmpcur_5472 + sizeof(IntTy);
            CursorTy jump_3180 = tmpcur_5472 + 8;
            CursorTy jump_3179 = tmpcur_5466 + 8;
            CursorTy loc_2781 = loc_2501 + 1;
            CursorTy loc_2782 = loc_2781 + 8;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          map_plist_787_1071(end_r_2502, end_r_2503, loc_2782, tmpcur_5474);
            CursorTy pvrtmp_5477 = tmp_struct_80.field0;
            CursorTy pvrtmp_5478 = tmp_struct_80.field1;
            CursorTy pvrtmp_5479 = tmp_struct_80.field2;
            CursorTy pvrtmp_5480 = tmp_struct_80.field3;

            *(TagTyPacked *) loc_2501 = 1;

            CursorTy writetag_3728 = loc_2501 + 1;

            *(IntTy *) writetag_3728 = tmpval_5473;

            CursorTy writecur_3729 = writetag_3728 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_5477, pvrtmp_5478,
                                                   loc_2501, pvrtmp_5480};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5489 = *(CursorTy *) tmpcur_5466;
            CursorTy tmpaftercur_5490 = tmpcur_5466 + 8;
            CursorTy jump_3354 = tmpcur_5466 + 8;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          map_plist_787_1071(end_r_2502, end_r_2503, loc_2501, tmpcur_5489);
            CursorTy pvrtmp_5491 = tmp_struct_81.field0;
            CursorTy pvrtmp_5492 = tmp_struct_81.field1;
            CursorTy pvrtmp_5493 = tmp_struct_81.field2;
            CursorTy pvrtmp_5494 = tmp_struct_81.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5491, jump_3354,
                                                   pvrtmp_5493, pvrtmp_5494};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5501 = *(CursorTy *) tmpcur_5466;
            CursorTy tmpaftercur_5502 = tmpcur_5466 + 8;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          map_plist_787_1071(end_r_2502, end_r_2503, loc_2501, tmpcur_5501);
            CursorTy pvrtmp_5503 = tmp_struct_82.field0;
            CursorTy pvrtmp_5504 = tmp_struct_82.field1;
            CursorTy pvrtmp_5505 = tmp_struct_82.field2;
            CursorTy pvrtmp_5506 = tmp_struct_82.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5503, pvrtmp_5504,
                                                   pvrtmp_5505, pvrtmp_5506};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5465");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_PList_v_778(CursorTy end_r_2506,
                                               CursorTy end_r_2507,
                                               CursorTy loc_2505,
                                               CursorTy arg_1136_1350_1682)
{
    if (loc_2505 + 32 > end_r_2507) {
        ChunkTy new_chunk_89 = alloc_chunk(end_r_2507);
        CursorTy chunk_start_90 = new_chunk_89.chunk_start;
        CursorTy chunk_end_91 = new_chunk_89.chunk_end;

        end_r_2507 = chunk_end_91;
        *(TagTyPacked *) loc_2505 = 255;

        CursorTy redir = loc_2505 + 1;

        *(CursorTy *) redir = chunk_start_90;
        loc_2505 = chunk_start_90;
    }

    TagTyPacked tmpval_5514 = *(TagTyPacked *) arg_1136_1350_1682;
    CursorTy tmpcur_5515 = arg_1136_1350_1682 + 1;


  switch_5558:
    ;
    switch (tmpval_5514) {

      case 0:
        {
            CursorTy jump_3183 = arg_1136_1350_1682 + 1;

            *(TagTyPacked *) loc_2505 = 0;

            CursorTy writetag_3739 = loc_2505 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2507, jump_3183,
                                                   loc_2505, writetag_3739};
            break;
        }

      case 1:
        {
            IntTy tmpval_5520 = *(IntTy *) tmpcur_5515;
            CursorTy tmpcur_5521 = tmpcur_5515 + sizeof(IntTy);
            CursorTy jump_3185 = tmpcur_5515 + 8;
            CursorTy loc_2794 = loc_2505 + 1;
            CursorTy loc_2795 = loc_2794 + 8;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_PList_v_778(end_r_2506, end_r_2507, loc_2795, tmpcur_5521);
            CursorTy pvrtmp_5522 = tmp_struct_86.field0;
            CursorTy pvrtmp_5523 = tmp_struct_86.field1;
            CursorTy pvrtmp_5524 = tmp_struct_86.field2;
            CursorTy pvrtmp_5525 = tmp_struct_86.field3;

            *(TagTyPacked *) loc_2505 = 1;

            CursorTy writetag_3744 = loc_2505 + 1;

            *(IntTy *) writetag_3744 = tmpval_5520;

            CursorTy writecur_3745 = writetag_3744 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_5522, pvrtmp_5523,
                                                   loc_2505, pvrtmp_5525};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5534 = *(CursorTy *) tmpcur_5515;
            CursorTy tmpaftercur_5535 = tmpcur_5515 + 8;
            CursorTy jump_3360 = tmpcur_5515 + 8;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_PList_v_778(end_r_2506, end_r_2507, loc_2505, tmpcur_5534);
            CursorTy pvrtmp_5536 = tmp_struct_87.field0;
            CursorTy pvrtmp_5537 = tmp_struct_87.field1;
            CursorTy pvrtmp_5538 = tmp_struct_87.field2;
            CursorTy pvrtmp_5539 = tmp_struct_87.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5536, jump_3360,
                                                   pvrtmp_5538, pvrtmp_5539};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5546 = *(CursorTy *) tmpcur_5515;
            CursorTy tmpaftercur_5547 = tmpcur_5515 + 8;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_PList_v_778(end_r_2506, end_r_2507, loc_2505, tmpcur_5546);
            CursorTy pvrtmp_5548 = tmp_struct_88.field0;
            CursorTy pvrtmp_5549 = tmp_struct_88.field1;
            CursorTy pvrtmp_5550 = tmp_struct_88.field2;
            CursorTy pvrtmp_5551 = tmp_struct_88.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5548, pvrtmp_5549,
                                                   pvrtmp_5550, pvrtmp_5551};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5514");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_PList_v_778(CursorTy end_r_2510,
                                                            CursorTy end_r_2511,
                                                            CursorTy loc_2509,
                                                            CursorTy arg_1141_1355_1687)
{
    TagTyPacked tmpval_5559 = *(TagTyPacked *) arg_1141_1355_1687;
    CursorTy tmpcur_5560 = arg_1141_1355_1687 + 1;


  switch_5603:
    ;
    switch (tmpval_5559) {

      case 0:
        {
            CursorTy jump_3188 = arg_1141_1355_1687 + 1;

            *(TagTyPacked *) loc_2509 = 0;

            CursorTy writetag_3755 = loc_2509 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2511, jump_3188,
                                                   loc_2509, writetag_3755};
            break;
        }

      case 1:
        {
            IntTy tmpval_5565 = *(IntTy *) tmpcur_5560;
            CursorTy tmpcur_5566 = tmpcur_5560 + sizeof(IntTy);
            CursorTy jump_3190 = tmpcur_5560 + 8;
            CursorTy loc_2807 = loc_2509 + 1;
            CursorTy loc_2808 = loc_2807 + 8;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_PList_v_778(end_r_2510, end_r_2511, loc_2808, tmpcur_5566);
            CursorTy pvrtmp_5567 = tmp_struct_92.field0;
            CursorTy pvrtmp_5568 = tmp_struct_92.field1;
            CursorTy pvrtmp_5569 = tmp_struct_92.field2;
            CursorTy pvrtmp_5570 = tmp_struct_92.field3;

            *(TagTyPacked *) loc_2509 = 1;

            CursorTy writetag_3760 = loc_2509 + 1;

            *(IntTy *) writetag_3760 = tmpval_5565;

            CursorTy writecur_3761 = writetag_3760 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_5567, pvrtmp_5568,
                                                   loc_2509, pvrtmp_5570};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5579 = *(CursorTy *) tmpcur_5560;
            CursorTy tmpaftercur_5580 = tmpcur_5560 + 8;
            CursorTy jump_3366 = tmpcur_5560 + 8;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_PList_v_778(end_r_2510, end_r_2511, loc_2509, tmpcur_5579);
            CursorTy pvrtmp_5581 = tmp_struct_93.field0;
            CursorTy pvrtmp_5582 = tmp_struct_93.field1;
            CursorTy pvrtmp_5583 = tmp_struct_93.field2;
            CursorTy pvrtmp_5584 = tmp_struct_93.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5581, jump_3366,
                                                   pvrtmp_5583, pvrtmp_5584};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5591 = *(CursorTy *) tmpcur_5560;
            CursorTy tmpaftercur_5592 = tmpcur_5560 + 8;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_PList_v_778(end_r_2510, end_r_2511, loc_2509, tmpcur_5591);
            CursorTy pvrtmp_5593 = tmp_struct_94.field0;
            CursorTy pvrtmp_5594 = tmp_struct_94.field1;
            CursorTy pvrtmp_5595 = tmp_struct_94.field2;
            CursorTy pvrtmp_5596 = tmp_struct_94.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5593, pvrtmp_5594,
                                                   pvrtmp_5595, pvrtmp_5596};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5559");
            exit(1);
        }
    }
}
CursorProd _traverse_PList_v_778(CursorTy end_r_2513,
                                 CursorTy arg_1146_1360_1692)
{
    TagTyPacked tmpval_5604 = *(TagTyPacked *) arg_1146_1360_1692;
    CursorTy tmpcur_5605 = arg_1146_1360_1692 + 1;


  switch_5615:
    ;
    switch (tmpval_5604) {

      case 0:
        {
            CursorTy jump_3193 = arg_1146_1360_1692 + 1;

            return (CursorProd) {jump_3193};
            break;
        }

      case 1:
        {
            IntTy tmpval_5606 = *(IntTy *) tmpcur_5605;
            CursorTy tmpcur_5607 = tmpcur_5605 + sizeof(IntTy);
            CursorTy jump_3195 = tmpcur_5605 + 8;
            CursorProd tmp_struct_95 =
                        _traverse_PList_v_778(end_r_2513, tmpcur_5607);
            CursorTy pvrtmp_5608 = tmp_struct_95.field0;

            return (CursorProd) {pvrtmp_5608};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5609 = *(CursorTy *) tmpcur_5605;
            CursorTy tmpaftercur_5610 = tmpcur_5605 + 8;
            CursorTy jump_3372 = tmpcur_5605 + 8;
            CursorProd tmp_struct_96 =
                        _traverse_PList_v_778(end_r_2513, tmpcur_5609);
            CursorTy pvrtmp_5611 = tmp_struct_96.field0;

            return (CursorProd) {jump_3372};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5612 = *(CursorTy *) tmpcur_5605;
            CursorTy tmpaftercur_5613 = tmpcur_5605 + 8;
            CursorProd tmp_struct_97 =
                        _traverse_PList_v_778(end_r_2513, tmpcur_5612);
            CursorTy pvrtmp_5614 = tmp_struct_97.field0;

            return (CursorProd) {pvrtmp_5614};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5604");
            exit(1);
        }
    }
}
CursorProd _print_PList_v_778(CursorTy end_r_2515, CursorTy arg_1151_1364_1696)
{
    TagTyPacked tmpval_5616 = *(TagTyPacked *) arg_1151_1364_1696;
    CursorTy tmpcur_5617 = arg_1151_1364_1696 + 1;


  switch_5627:
    ;
    switch (tmpval_5616) {

      case 0:
        {
            CursorTy jump_3198 = arg_1151_1364_1696 + 1;
            unsigned char wildcard_1152_1365_1697 = print_symbol(4837);
            unsigned char wildcard_1153_1366_1698 = print_symbol(4834);

            return (CursorProd) {jump_3198};
            break;
        }

      case 1:
        {
            IntTy tmpval_5618 = *(IntTy *) tmpcur_5617;
            CursorTy tmpcur_5619 = tmpcur_5617 + sizeof(IntTy);
            CursorTy jump_3200 = tmpcur_5617 + 8;
            unsigned char wildcard_1158_1369_1701 = print_symbol(4840);
            unsigned char wildcard_1161_1370_1702 = print_symbol(4843);
            unsigned char y_1156_1371_1703 = printf("%lld", tmpval_5618);
            unsigned char wildcard_1160_1372_1704 = print_symbol(4843);
            CursorProd tmp_struct_98 =
                        _print_PList_v_778(end_r_2515, tmpcur_5619);
            CursorTy pvrtmp_5620 = tmp_struct_98.field0;
            unsigned char wildcard_1159_1374_1706 = print_symbol(4834);

            return (CursorProd) {pvrtmp_5620};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5621 = *(CursorTy *) tmpcur_5617;
            CursorTy tmpaftercur_5622 = tmpcur_5617 + 8;
            CursorTy jump_3378 = tmpcur_5617 + 8;
            unsigned char wildcard_3381 = print_symbol(4842);
            CursorProd tmp_struct_99 =
                        _print_PList_v_778(end_r_2515, tmpcur_5621);
            CursorTy pvrtmp_5623 = tmp_struct_99.field0;

            return (CursorProd) {jump_3378};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5624 = *(CursorTy *) tmpcur_5617;
            CursorTy tmpaftercur_5625 = tmpcur_5617 + 8;
            unsigned char wildcard_3381 = print_symbol(4841);
            CursorProd tmp_struct_100 =
                        _print_PList_v_778(end_r_2515, tmpcur_5624);
            CursorTy pvrtmp_5626 = tmp_struct_100.field0;

            return (CursorProd) {pvrtmp_5626};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5616");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_PList_v_779(CursorTy end_r_2518,
                                               CursorTy end_r_2519,
                                               CursorTy loc_2517,
                                               CursorTy arg_1162_1375_1707)
{
    if (loc_2517 + 32 > end_r_2519) {
        ChunkTy new_chunk_104 = alloc_chunk(end_r_2519);
        CursorTy chunk_start_105 = new_chunk_104.chunk_start;
        CursorTy chunk_end_106 = new_chunk_104.chunk_end;

        end_r_2519 = chunk_end_106;
        *(TagTyPacked *) loc_2517 = 255;

        CursorTy redir = loc_2517 + 1;

        *(CursorTy *) redir = chunk_start_105;
        loc_2517 = chunk_start_105;
    }

    TagTyPacked tmpval_5628 = *(TagTyPacked *) arg_1162_1375_1707;
    CursorTy tmpcur_5629 = arg_1162_1375_1707 + 1;


  switch_5674:
    ;
    switch (tmpval_5628) {

      case 0:
        {
            CursorTy jump_3203 = arg_1162_1375_1707 + 1;

            *(TagTyPacked *) loc_2517 = 0;

            CursorTy writetag_3791 = loc_2517 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2519, jump_3203,
                                                   loc_2517, writetag_3791};
            break;
        }

      case 1:
        {
            IntTy tmpval_5634 = *(IntTy *) tmpcur_5629;
            CursorTy tmpcur_5635 = tmpcur_5629 + sizeof(IntTy);
            IntTy tmpval_5636 = *(IntTy *) tmpcur_5635;
            CursorTy tmpcur_5637 = tmpcur_5635 + sizeof(IntTy);
            CursorTy jump_3206 = tmpcur_5635 + 8;
            CursorTy jump_3205 = tmpcur_5629 + 8;
            CursorTy loc_2833 = loc_2517 + 1;
            CursorTy loc_2834 = loc_2833 + 8;
            CursorTy loc_2835 = loc_2834 + 8;
            CursorCursorCursorCursorProd tmp_struct_101 =
                                          _copy_PList_v_779(end_r_2518, end_r_2519, loc_2835, tmpcur_5637);
            CursorTy pvrtmp_5638 = tmp_struct_101.field0;
            CursorTy pvrtmp_5639 = tmp_struct_101.field1;
            CursorTy pvrtmp_5640 = tmp_struct_101.field2;
            CursorTy pvrtmp_5641 = tmp_struct_101.field3;

            *(TagTyPacked *) loc_2517 = 1;

            CursorTy writetag_3797 = loc_2517 + 1;

            *(IntTy *) writetag_3797 = tmpval_5634;

            CursorTy writecur_3798 = writetag_3797 + sizeof(IntTy);

            *(IntTy *) writecur_3798 = tmpval_5636;

            CursorTy writecur_3799 = writecur_3798 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_5638, pvrtmp_5639,
                                                   loc_2517, pvrtmp_5641};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5650 = *(CursorTy *) tmpcur_5629;
            CursorTy tmpaftercur_5651 = tmpcur_5629 + 8;
            CursorTy jump_3384 = tmpcur_5629 + 8;
            CursorCursorCursorCursorProd tmp_struct_102 =
                                          _copy_PList_v_779(end_r_2518, end_r_2519, loc_2517, tmpcur_5650);
            CursorTy pvrtmp_5652 = tmp_struct_102.field0;
            CursorTy pvrtmp_5653 = tmp_struct_102.field1;
            CursorTy pvrtmp_5654 = tmp_struct_102.field2;
            CursorTy pvrtmp_5655 = tmp_struct_102.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5652, jump_3384,
                                                   pvrtmp_5654, pvrtmp_5655};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5662 = *(CursorTy *) tmpcur_5629;
            CursorTy tmpaftercur_5663 = tmpcur_5629 + 8;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          _copy_PList_v_779(end_r_2518, end_r_2519, loc_2517, tmpcur_5662);
            CursorTy pvrtmp_5664 = tmp_struct_103.field0;
            CursorTy pvrtmp_5665 = tmp_struct_103.field1;
            CursorTy pvrtmp_5666 = tmp_struct_103.field2;
            CursorTy pvrtmp_5667 = tmp_struct_103.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5664, pvrtmp_5665,
                                                   pvrtmp_5666, pvrtmp_5667};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5628");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_PList_v_779(CursorTy end_r_2522,
                                                            CursorTy end_r_2523,
                                                            CursorTy loc_2521,
                                                            CursorTy arg_1169_1382_1714)
{
    TagTyPacked tmpval_5675 = *(TagTyPacked *) arg_1169_1382_1714;
    CursorTy tmpcur_5676 = arg_1169_1382_1714 + 1;


  switch_5721:
    ;
    switch (tmpval_5675) {

      case 0:
        {
            CursorTy jump_3209 = arg_1169_1382_1714 + 1;

            *(TagTyPacked *) loc_2521 = 0;

            CursorTy writetag_3809 = loc_2521 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2523, jump_3209,
                                                   loc_2521, writetag_3809};
            break;
        }

      case 1:
        {
            IntTy tmpval_5681 = *(IntTy *) tmpcur_5676;
            CursorTy tmpcur_5682 = tmpcur_5676 + sizeof(IntTy);
            IntTy tmpval_5683 = *(IntTy *) tmpcur_5682;
            CursorTy tmpcur_5684 = tmpcur_5682 + sizeof(IntTy);
            CursorTy jump_3212 = tmpcur_5682 + 8;
            CursorTy jump_3211 = tmpcur_5676 + 8;
            CursorTy loc_2850 = loc_2521 + 1;
            CursorTy loc_2851 = loc_2850 + 8;
            CursorTy loc_2852 = loc_2851 + 8;
            CursorCursorCursorCursorProd tmp_struct_107 =
                                          _copy_without_ptrs_PList_v_779(end_r_2522, end_r_2523, loc_2852, tmpcur_5684);
            CursorTy pvrtmp_5685 = tmp_struct_107.field0;
            CursorTy pvrtmp_5686 = tmp_struct_107.field1;
            CursorTy pvrtmp_5687 = tmp_struct_107.field2;
            CursorTy pvrtmp_5688 = tmp_struct_107.field3;

            *(TagTyPacked *) loc_2521 = 1;

            CursorTy writetag_3815 = loc_2521 + 1;

            *(IntTy *) writetag_3815 = tmpval_5681;

            CursorTy writecur_3816 = writetag_3815 + sizeof(IntTy);

            *(IntTy *) writecur_3816 = tmpval_5683;

            CursorTy writecur_3817 = writecur_3816 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_5685, pvrtmp_5686,
                                                   loc_2521, pvrtmp_5688};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5697 = *(CursorTy *) tmpcur_5676;
            CursorTy tmpaftercur_5698 = tmpcur_5676 + 8;
            CursorTy jump_3390 = tmpcur_5676 + 8;
            CursorCursorCursorCursorProd tmp_struct_108 =
                                          _copy_without_ptrs_PList_v_779(end_r_2522, end_r_2523, loc_2521, tmpcur_5697);
            CursorTy pvrtmp_5699 = tmp_struct_108.field0;
            CursorTy pvrtmp_5700 = tmp_struct_108.field1;
            CursorTy pvrtmp_5701 = tmp_struct_108.field2;
            CursorTy pvrtmp_5702 = tmp_struct_108.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5699, jump_3390,
                                                   pvrtmp_5701, pvrtmp_5702};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5709 = *(CursorTy *) tmpcur_5676;
            CursorTy tmpaftercur_5710 = tmpcur_5676 + 8;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          _copy_without_ptrs_PList_v_779(end_r_2522, end_r_2523, loc_2521, tmpcur_5709);
            CursorTy pvrtmp_5711 = tmp_struct_109.field0;
            CursorTy pvrtmp_5712 = tmp_struct_109.field1;
            CursorTy pvrtmp_5713 = tmp_struct_109.field2;
            CursorTy pvrtmp_5714 = tmp_struct_109.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5711, pvrtmp_5712,
                                                   pvrtmp_5713, pvrtmp_5714};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5675");
            exit(1);
        }
    }
}
CursorProd _traverse_PList_v_779(CursorTy end_r_2525,
                                 CursorTy arg_1176_1389_1721)
{
    TagTyPacked tmpval_5722 = *(TagTyPacked *) arg_1176_1389_1721;
    CursorTy tmpcur_5723 = arg_1176_1389_1721 + 1;


  switch_5735:
    ;
    switch (tmpval_5722) {

      case 0:
        {
            CursorTy jump_3215 = arg_1176_1389_1721 + 1;

            return (CursorProd) {jump_3215};
            break;
        }

      case 1:
        {
            IntTy tmpval_5724 = *(IntTy *) tmpcur_5723;
            CursorTy tmpcur_5725 = tmpcur_5723 + sizeof(IntTy);
            IntTy tmpval_5726 = *(IntTy *) tmpcur_5725;
            CursorTy tmpcur_5727 = tmpcur_5725 + sizeof(IntTy);
            CursorTy jump_3218 = tmpcur_5725 + 8;
            CursorTy jump_3217 = tmpcur_5723 + 8;
            CursorProd tmp_struct_110 =
                        _traverse_PList_v_779(end_r_2525, tmpcur_5727);
            CursorTy pvrtmp_5728 = tmp_struct_110.field0;

            return (CursorProd) {pvrtmp_5728};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5729 = *(CursorTy *) tmpcur_5723;
            CursorTy tmpaftercur_5730 = tmpcur_5723 + 8;
            CursorTy jump_3396 = tmpcur_5723 + 8;
            CursorProd tmp_struct_111 =
                        _traverse_PList_v_779(end_r_2525, tmpcur_5729);
            CursorTy pvrtmp_5731 = tmp_struct_111.field0;

            return (CursorProd) {jump_3396};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5732 = *(CursorTy *) tmpcur_5723;
            CursorTy tmpaftercur_5733 = tmpcur_5723 + 8;
            CursorProd tmp_struct_112 =
                        _traverse_PList_v_779(end_r_2525, tmpcur_5732);
            CursorTy pvrtmp_5734 = tmp_struct_112.field0;

            return (CursorProd) {pvrtmp_5734};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5722");
            exit(1);
        }
    }
}
CursorProd _print_PList_v_779(CursorTy end_r_2527, CursorTy arg_1183_1394_1726)
{
    TagTyPacked tmpval_5736 = *(TagTyPacked *) arg_1183_1394_1726;
    CursorTy tmpcur_5737 = arg_1183_1394_1726 + 1;


  switch_5749:
    ;
    switch (tmpval_5736) {

      case 0:
        {
            CursorTy jump_3221 = arg_1183_1394_1726 + 1;
            unsigned char wildcard_1184_1395_1727 = print_symbol(4836);
            unsigned char wildcard_1185_1396_1728 = print_symbol(4834);

            return (CursorProd) {jump_3221};
            break;
        }

      case 1:
        {
            IntTy tmpval_5738 = *(IntTy *) tmpcur_5737;
            CursorTy tmpcur_5739 = tmpcur_5737 + sizeof(IntTy);
            IntTy tmpval_5740 = *(IntTy *) tmpcur_5739;
            CursorTy tmpcur_5741 = tmpcur_5739 + sizeof(IntTy);
            CursorTy jump_3224 = tmpcur_5739 + 8;
            CursorTy jump_3223 = tmpcur_5737 + 8;
            unsigned char wildcard_1192_1400_1732 = print_symbol(4839);
            unsigned char wildcard_1196_1401_1733 = print_symbol(4843);
            unsigned char y_1189_1402_1734 = printf("%lld", tmpval_5738);
            unsigned char wildcard_1195_1403_1735 = print_symbol(4843);
            unsigned char y_1190_1404_1736 = printf("%lld", tmpval_5740);
            unsigned char wildcard_1194_1405_1737 = print_symbol(4843);
            CursorProd tmp_struct_113 =
                        _print_PList_v_779(end_r_2527, tmpcur_5741);
            CursorTy pvrtmp_5742 = tmp_struct_113.field0;
            unsigned char wildcard_1193_1407_1739 = print_symbol(4834);

            return (CursorProd) {pvrtmp_5742};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5743 = *(CursorTy *) tmpcur_5737;
            CursorTy tmpaftercur_5744 = tmpcur_5737 + 8;
            CursorTy jump_3402 = tmpcur_5737 + 8;
            unsigned char wildcard_3405 = print_symbol(4842);
            CursorProd tmp_struct_114 =
                        _print_PList_v_779(end_r_2527, tmpcur_5743);
            CursorTy pvrtmp_5745 = tmp_struct_114.field0;

            return (CursorProd) {jump_3402};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5746 = *(CursorTy *) tmpcur_5737;
            CursorTy tmpaftercur_5747 = tmpcur_5737 + 8;
            unsigned char wildcard_3405 = print_symbol(4841);
            CursorProd tmp_struct_115 =
                        _print_PList_v_779(end_r_2527, tmpcur_5746);
            CursorTy pvrtmp_5748 = tmp_struct_115.field0;

            return (CursorProd) {pvrtmp_5748};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5736");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Maybe_v_788(CursorTy end_r_2530,
                                               CursorTy end_r_2531,
                                               CursorTy loc_2529,
                                               CursorTy arg_1197_1408_1740)
{
    if (loc_2529 + 32 > end_r_2531) {
        ChunkTy new_chunk_118 = alloc_chunk(end_r_2531);
        CursorTy chunk_start_119 = new_chunk_118.chunk_start;
        CursorTy chunk_end_120 = new_chunk_118.chunk_end;

        end_r_2531 = chunk_end_120;
        *(TagTyPacked *) loc_2529 = 255;

        CursorTy redir = loc_2529 + 1;

        *(CursorTy *) redir = chunk_start_119;
        loc_2529 = chunk_start_119;
    }

    TagTyPacked tmpval_5750 = *(TagTyPacked *) arg_1197_1408_1740;
    CursorTy tmpcur_5751 = arg_1197_1408_1740 + 1;


  switch_5786:
    ;
    switch (tmpval_5750) {

      case 0:
        {
            IntTy tmpval_5752 = *(IntTy *) tmpcur_5751;
            CursorTy tmpcur_5753 = tmpcur_5751 + sizeof(IntTy);
            CursorTy jump_3227 = tmpcur_5751 + 8;

            *(TagTyPacked *) loc_2529 = 0;

            CursorTy writetag_3850 = loc_2529 + 1;

            *(IntTy *) writetag_3850 = tmpval_5752;

            CursorTy writecur_3851 = writetag_3850 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_2531, jump_3227,
                                                   loc_2529, writecur_3851};
            break;
        }

      case 1:
        {
            CursorTy jump_3229 = arg_1197_1408_1740 + 1;

            *(TagTyPacked *) loc_2529 = 1;

            CursorTy writetag_3854 = loc_2529 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2531, jump_3229,
                                                   loc_2529, writetag_3854};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5762 = *(CursorTy *) tmpcur_5751;
            CursorTy tmpaftercur_5763 = tmpcur_5751 + 8;
            CursorTy jump_3408 = tmpcur_5751 + 8;
            CursorCursorCursorCursorProd tmp_struct_116 =
                                          _copy_Maybe_v_788(end_r_2530, end_r_2531, loc_2529, tmpcur_5762);
            CursorTy pvrtmp_5764 = tmp_struct_116.field0;
            CursorTy pvrtmp_5765 = tmp_struct_116.field1;
            CursorTy pvrtmp_5766 = tmp_struct_116.field2;
            CursorTy pvrtmp_5767 = tmp_struct_116.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5764, jump_3408,
                                                   pvrtmp_5766, pvrtmp_5767};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5774 = *(CursorTy *) tmpcur_5751;
            CursorTy tmpaftercur_5775 = tmpcur_5751 + 8;
            CursorCursorCursorCursorProd tmp_struct_117 =
                                          _copy_Maybe_v_788(end_r_2530, end_r_2531, loc_2529, tmpcur_5774);
            CursorTy pvrtmp_5776 = tmp_struct_117.field0;
            CursorTy pvrtmp_5777 = tmp_struct_117.field1;
            CursorTy pvrtmp_5778 = tmp_struct_117.field2;
            CursorTy pvrtmp_5779 = tmp_struct_117.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5776, pvrtmp_5777,
                                                   pvrtmp_5778, pvrtmp_5779};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5750");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Maybe_v_788(CursorTy end_r_2534,
                                                            CursorTy end_r_2535,
                                                            CursorTy loc_2533,
                                                            CursorTy arg_1200_1411_1743)
{
    TagTyPacked tmpval_5787 = *(TagTyPacked *) arg_1200_1411_1743;
    CursorTy tmpcur_5788 = arg_1200_1411_1743 + 1;


  switch_5823:
    ;
    switch (tmpval_5787) {

      case 0:
        {
            IntTy tmpval_5789 = *(IntTy *) tmpcur_5788;
            CursorTy tmpcur_5790 = tmpcur_5788 + sizeof(IntTy);
            CursorTy jump_3231 = tmpcur_5788 + 8;

            *(TagTyPacked *) loc_2533 = 0;

            CursorTy writetag_3864 = loc_2533 + 1;

            *(IntTy *) writetag_3864 = tmpval_5789;

            CursorTy writecur_3865 = writetag_3864 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_2535, jump_3231,
                                                   loc_2533, writecur_3865};
            break;
        }

      case 1:
        {
            CursorTy jump_3233 = arg_1200_1411_1743 + 1;

            *(TagTyPacked *) loc_2533 = 1;

            CursorTy writetag_3868 = loc_2533 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2535, jump_3233,
                                                   loc_2533, writetag_3868};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5799 = *(CursorTy *) tmpcur_5788;
            CursorTy tmpaftercur_5800 = tmpcur_5788 + 8;
            CursorTy jump_3414 = tmpcur_5788 + 8;
            CursorCursorCursorCursorProd tmp_struct_121 =
                                          _copy_without_ptrs_Maybe_v_788(end_r_2534, end_r_2535, loc_2533, tmpcur_5799);
            CursorTy pvrtmp_5801 = tmp_struct_121.field0;
            CursorTy pvrtmp_5802 = tmp_struct_121.field1;
            CursorTy pvrtmp_5803 = tmp_struct_121.field2;
            CursorTy pvrtmp_5804 = tmp_struct_121.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5801, jump_3414,
                                                   pvrtmp_5803, pvrtmp_5804};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5811 = *(CursorTy *) tmpcur_5788;
            CursorTy tmpaftercur_5812 = tmpcur_5788 + 8;
            CursorCursorCursorCursorProd tmp_struct_122 =
                                          _copy_without_ptrs_Maybe_v_788(end_r_2534, end_r_2535, loc_2533, tmpcur_5811);
            CursorTy pvrtmp_5813 = tmp_struct_122.field0;
            CursorTy pvrtmp_5814 = tmp_struct_122.field1;
            CursorTy pvrtmp_5815 = tmp_struct_122.field2;
            CursorTy pvrtmp_5816 = tmp_struct_122.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_5813, pvrtmp_5814,
                                                   pvrtmp_5815, pvrtmp_5816};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5787");
            exit(1);
        }
    }
}
CursorProd _traverse_Maybe_v_788(CursorTy end_r_2537,
                                 CursorTy arg_1203_1414_1746)
{
    TagTyPacked tmpval_5824 = *(TagTyPacked *) arg_1203_1414_1746;
    CursorTy tmpcur_5825 = arg_1203_1414_1746 + 1;


  switch_5834:
    ;
    switch (tmpval_5824) {

      case 0:
        {
            IntTy tmpval_5826 = *(IntTy *) tmpcur_5825;
            CursorTy tmpcur_5827 = tmpcur_5825 + sizeof(IntTy);
            CursorTy jump_3235 = tmpcur_5825 + 8;

            return (CursorProd) {jump_3235};
            break;
        }

      case 1:
        {
            CursorTy jump_3237 = arg_1203_1414_1746 + 1;

            return (CursorProd) {jump_3237};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5828 = *(CursorTy *) tmpcur_5825;
            CursorTy tmpaftercur_5829 = tmpcur_5825 + 8;
            CursorTy jump_3420 = tmpcur_5825 + 8;
            CursorProd tmp_struct_123 =
                        _traverse_Maybe_v_788(end_r_2537, tmpcur_5828);
            CursorTy pvrtmp_5830 = tmp_struct_123.field0;

            return (CursorProd) {jump_3420};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5831 = *(CursorTy *) tmpcur_5825;
            CursorTy tmpaftercur_5832 = tmpcur_5825 + 8;
            CursorProd tmp_struct_124 =
                        _traverse_Maybe_v_788(end_r_2537, tmpcur_5831);
            CursorTy pvrtmp_5833 = tmp_struct_124.field0;

            return (CursorProd) {pvrtmp_5833};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5824");
            exit(1);
        }
    }
}
CursorProd _print_Maybe_v_788(CursorTy end_r_2539, CursorTy arg_1206_1416_1748)
{
    TagTyPacked tmpval_5835 = *(TagTyPacked *) arg_1206_1416_1748;
    CursorTy tmpcur_5836 = arg_1206_1416_1748 + 1;


  switch_5845:
    ;
    switch (tmpval_5835) {

      case 0:
        {
            IntTy tmpval_5837 = *(IntTy *) tmpcur_5836;
            CursorTy tmpcur_5838 = tmpcur_5836 + sizeof(IntTy);
            CursorTy jump_3239 = tmpcur_5836 + 8;
            unsigned char wildcard_1209_1418_1750 = print_symbol(4838);
            unsigned char wildcard_1211_1419_1751 = print_symbol(4843);
            unsigned char y_1208_1420_1752 = printf("%lld", tmpval_5837);
            unsigned char wildcard_1210_1421_1753 = print_symbol(4834);

            return (CursorProd) {jump_3239};
            break;
        }

      case 1:
        {
            CursorTy jump_3241 = arg_1206_1416_1748 + 1;
            unsigned char wildcard_1212_1422_1754 = print_symbol(4835);
            unsigned char wildcard_1213_1423_1755 = print_symbol(4834);

            return (CursorProd) {jump_3241};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5839 = *(CursorTy *) tmpcur_5836;
            CursorTy tmpaftercur_5840 = tmpcur_5836 + 8;
            CursorTy jump_3426 = tmpcur_5836 + 8;
            unsigned char wildcard_3429 = print_symbol(4842);
            CursorProd tmp_struct_125 =
                        _print_Maybe_v_788(end_r_2539, tmpcur_5839);
            CursorTy pvrtmp_5841 = tmp_struct_125.field0;

            return (CursorProd) {jump_3426};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5842 = *(CursorTy *) tmpcur_5836;
            CursorTy tmpaftercur_5843 = tmpcur_5836 + 8;
            unsigned char wildcard_3429 = print_symbol(4841);
            CursorProd tmp_struct_126 =
                        _print_Maybe_v_788(end_r_2539, tmpcur_5842);
            CursorTy pvrtmp_5844 = tmp_struct_126.field0;

            return (CursorProd) {pvrtmp_5844};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5835");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_1214(CursorTy end_r_2545, CursorTy end_r_2546,
                                   CursorTy end_r_2547, CursorTy end_r_2548,
                                   CursorTy end_r_2549, CursorTy loc_2544,
                                   IntTy m_144_1215_1424_1756,
                                   IntTy n_145_1216_1425_1757,
                                   CursorTy xs_146_1217_1426_1758,
                                   CursorTy ys_147_1218_1427_1759,
                                   CursorTy zs_148_1219_1428_1760,
                                   CursorTy xs__150_1220_1429_1761,
                                   IntTy x_149_1221_1430_1762)
{
    if (loc_2544 + 32 > end_r_2549) {
        ChunkTy new_chunk_142 = alloc_chunk(end_r_2549);
        CursorTy chunk_start_143 = new_chunk_142.chunk_start;
        CursorTy chunk_end_144 = new_chunk_142.chunk_end;

        end_r_2549 = chunk_end_144;
        *(TagTyPacked *) loc_2544 = 255;

        CursorTy redir = loc_2544 + 1;

        *(CursorTy *) redir = chunk_start_143;
        loc_2544 = chunk_start_143;
    }

    TagTyPacked tmpval_5846 = *(TagTyPacked *) xs__150_1220_1429_1761;
    CursorTy tmpcur_5847 = xs__150_1220_1429_1761 + 1;


  switch_6011:
    ;
    switch (tmpval_5846) {

      case 0:
        {
            CursorTy jump_3243 = xs__150_1220_1429_1761 + 1;
            BoolTy fltIf_1517_1763 =
                    elem_plist_782_1069(end_r_2546, x_149_1221_1430_1762, ys_147_1218_1427_1759);

            if (fltIf_1517_1763) {
                CursorTy loc_2899 = loc_2544 + 1;
                CursorTy loc_2900 = loc_2899 + 8;

                bump_ref_count(end_r_2549, end_r_2547);
                *(TagTyPacked *) loc_2900 = 254;

                CursorTy writetag_3895 = loc_2900 + 1;

                *(CursorTy *) writetag_3895 = zs_148_1219_1428_1760;

                CursorTy writecur_3896 = writetag_3895 + 8;

                *(TagTyPacked *) loc_2544 = 1;

                CursorTy writetag_3898 = loc_2544 + 1;

                *(IntTy *) writetag_3898 = x_149_1221_1430_1762;

                CursorTy writecur_3899 = writetag_3898 + sizeof(IntTy);

                return (CursorCursorCursorProd) {end_r_2549, loc_2544,
                                                 writecur_3896};
            } else {
                bump_ref_count(end_r_2549, end_r_2547);
                *(TagTyPacked *) loc_2544 = 254;

                CursorTy writetag_3902 = loc_2544 + 1;

                *(CursorTy *) writetag_3902 = zs_148_1219_1428_1760;

                CursorTy writecur_3903 = writetag_3902 + 8;

                return (CursorCursorCursorProd) {end_r_2549, loc_2544,
                                                 writecur_3903};
            }
            break;
        }

      case 1:
        {
            RegionTy *region_5858 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3002 = region_5858->reg_heap;
            IntTy sizeof_end_r_3002_5859 = global_init_inf_buf_size;
            CursorTy end_r_3002 = r_3002 + sizeof_end_r_3002_5859;
            RegionTy *region_5860 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3001 = region_5860->reg_heap;
            IntTy sizeof_end_r_3001_5861 = global_init_inf_buf_size;
            CursorTy end_r_3001 = r_3001 + sizeof_end_r_3001_5861;
            RegionTy *region_5862 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3000 = region_5862->reg_heap;
            IntTy sizeof_end_r_3000_5863 = global_init_inf_buf_size;
            CursorTy end_r_3000 = r_3000 + sizeof_end_r_3000_5863;
            RegionTy *region_5864 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2999 = region_5864->reg_heap;
            IntTy sizeof_end_r_2999_5865 = global_init_inf_buf_size;
            CursorTy end_r_2999 = r_2999 + sizeof_end_r_2999_5865;
            RegionTy *region_5866 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2998 = region_5866->reg_heap;
            IntTy sizeof_end_r_2998_5867 = global_init_inf_buf_size;
            CursorTy end_r_2998 = r_2998 + sizeof_end_r_2998_5867;
            RegionTy *region_5868 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2997 = region_5868->reg_heap;
            IntTy sizeof_end_r_2997_5869 = global_init_inf_buf_size;
            CursorTy end_r_2997 = r_2997 + sizeof_end_r_2997_5869;
            RegionTy *region_5870 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2996 = region_5870->reg_heap;
            IntTy sizeof_end_r_2996_5871 = global_init_inf_buf_size;
            CursorTy end_r_2996 = r_2996 + sizeof_end_r_2996_5871;
            RegionTy *region_5872 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2995 = region_5872->reg_heap;
            IntTy sizeof_end_r_2995_5873 = global_init_inf_buf_size;
            CursorTy end_r_2995 = r_2995 + sizeof_end_r_2995_5873;
            RegionTy *region_5874 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2994 = region_5874->reg_heap;
            IntTy sizeof_end_r_2994_5875 = global_init_inf_buf_size;
            CursorTy end_r_2994 = r_2994 + sizeof_end_r_2994_5875;
            RegionTy *region_5876 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2993 = region_5876->reg_heap;
            IntTy sizeof_end_r_2993_5877 = global_init_inf_buf_size;
            CursorTy end_r_2993 = r_2993 + sizeof_end_r_2993_5877;
            RegionTy *region_5878 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2992 = region_5878->reg_heap;
            IntTy sizeof_end_r_2992_5879 = global_init_inf_buf_size;
            CursorTy end_r_2992 = r_2992 + sizeof_end_r_2992_5879;
            RegionTy *region_5880 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2991 = region_5880->reg_heap;
            IntTy sizeof_end_r_2991_5881 = global_init_inf_buf_size;
            CursorTy end_r_2991 = r_2991 + sizeof_end_r_2991_5881;
            RegionTy *region_5882 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2990 = region_5882->reg_heap;
            IntTy sizeof_end_r_2990_5883 = global_init_inf_buf_size;
            CursorTy end_r_2990 = r_2990 + sizeof_end_r_2990_5883;
            RegionTy *region_5884 = alloc_region(global_init_inf_buf_size);
            CursorTy r_2989 = region_5884->reg_heap;
            IntTy sizeof_end_r_2989_5885 = global_init_inf_buf_size;
            CursorTy end_r_2989 = r_2989 + sizeof_end_r_2989_5885;
            IntTy tmpval_5886 = *(IntTy *) tmpcur_5847;
            CursorTy tmpcur_5887 = tmpcur_5847 + sizeof(IntTy);
            CursorTy jump_3245 = tmpcur_5847 + 8;
            IntTy m2_153_1433_1767 = m_144_1215_1424_1756 / 2;
            CursorCursorCursorProd tmp_struct_127 =
                                    take_plist_783(end_r_2545, end_r_3002, r_3002, m2_153_1433_1767, xs_146_1217_1426_1758);
            CursorTy pvrtmp_5888 = tmp_struct_127.field0;
            CursorTy pvrtmp_5889 = tmp_struct_127.field1;
            CursorTy pvrtmp_5890 = tmp_struct_127.field2;
            CursorCursorCursorProd tmp_struct_128 =
                                    drop_plist_784(end_r_2545, end_r_3001, r_3001, m2_153_1433_1767, xs_146_1217_1426_1758);
            CursorTy pvrtmp_5895 = tmp_struct_128.field0;
            CursorTy pvrtmp_5896 = tmp_struct_128.field1;
            CursorTy pvrtmp_5897 = tmp_struct_128.field2;
            CursorCursorCursorCursorCursorProd tmp_struct_129 =
                                                algb(pvrtmp_5888, end_r_2546, end_r_3000, r_3000, pvrtmp_5889, ys_147_1218_1427_1759);
            CursorTy pvrtmp_5902 = tmp_struct_129.field0;
            CursorTy pvrtmp_5903 = tmp_struct_129.field1;
            CursorTy pvrtmp_5904 = tmp_struct_129.field2;
            CursorTy pvrtmp_5905 = tmp_struct_129.field3;
            CursorTy pvrtmp_5906 = tmp_struct_129.field4;

            *(TagTyPacked *) r_2999 = 0;

            CursorTy writetag_3910 = r_2999 + 1;
            CursorCursorCursorCursorProd tmp_struct_130 =
                                          reverse_plist_785(pvrtmp_5895, end_r_2999, end_r_2998, r_2998, pvrtmp_5896, r_2999);
            CursorTy pvrtmp_5913 = tmp_struct_130.field0;
            CursorTy pvrtmp_5914 = tmp_struct_130.field1;
            CursorTy pvrtmp_5915 = tmp_struct_130.field2;
            CursorTy pvrtmp_5916 = tmp_struct_130.field3;

            *(TagTyPacked *) r_2997 = 0;

            CursorTy writetag_3913 = r_2997 + 1;
            CursorCursorCursorCursorProd tmp_struct_131 =
                                          reverse_plist_785(end_r_2546, end_r_2997, end_r_2996, r_2996, ys_147_1218_1427_1759, r_2997);
            CursorTy pvrtmp_5923 = tmp_struct_131.field0;
            CursorTy pvrtmp_5924 = tmp_struct_131.field1;
            CursorTy pvrtmp_5925 = tmp_struct_131.field2;
            CursorTy pvrtmp_5926 = tmp_struct_131.field3;
            CursorCursorCursorCursorCursorProd tmp_struct_132 =
                                                algb(pvrtmp_5913, pvrtmp_5923, end_r_2995, r_2995, pvrtmp_5915, pvrtmp_5925);
            CursorTy pvrtmp_5931 = tmp_struct_132.field0;
            CursorTy pvrtmp_5932 = tmp_struct_132.field1;
            CursorTy pvrtmp_5933 = tmp_struct_132.field2;
            CursorTy pvrtmp_5934 = tmp_struct_132.field3;
            CursorTy pvrtmp_5935 = tmp_struct_132.field4;

            *(TagTyPacked *) r_2994 = 0;

            CursorTy writetag_3917 = r_2994 + 1;
            CursorCursorCursorCursorProd tmp_struct_133 =
                                          reverse_plist_785(pvrtmp_5931, end_r_2994, end_r_2993, r_2993, pvrtmp_5934, r_2994);
            CursorTy pvrtmp_5942 = tmp_struct_133.field0;
            CursorTy pvrtmp_5943 = tmp_struct_133.field1;
            CursorTy pvrtmp_5944 = tmp_struct_133.field2;
            CursorTy pvrtmp_5945 = tmp_struct_133.field3;
            IntTy fltAppE_1522_1778 = 0 - 1;
            CursorCursorCursorProd tmp_struct_134 =
                                    zip_plist_786(pvrtmp_5902, pvrtmp_5942, end_r_2992, r_2992, pvrtmp_5905, pvrtmp_5944);
            CursorTy pvrtmp_5950 = tmp_struct_134.field0;
            CursorTy pvrtmp_5951 = tmp_struct_134.field1;
            CursorTy pvrtmp_5952 = tmp_struct_134.field2;
            CursorInt64Prod tmp_struct_135 =
                             findk(pvrtmp_5950, 0, 0, fltAppE_1522_1778, pvrtmp_5951);
            CursorTy pvrtmp_5957 = tmp_struct_135.field0;
            IntTy pvrtmp_5958 = tmp_struct_135.field1;
            IntTy fltAppE_1524_1781 = m_144_1215_1424_1756 - m2_153_1433_1767;
            IntTy fltAppE_1525_1782 = n_145_1216_1425_1757 - pvrtmp_5958;
            CursorCursorCursorProd tmp_struct_136 =
                                    drop_plist_784(end_r_2546, end_r_2991, r_2991, pvrtmp_5958, ys_147_1218_1427_1759);
            CursorTy pvrtmp_5959 = tmp_struct_136.field0;
            CursorTy pvrtmp_5960 = tmp_struct_136.field1;
            CursorTy pvrtmp_5961 = tmp_struct_136.field2;
            CursorCursorCursorProd tmp_struct_137 =
                                    algc(pvrtmp_5895, pvrtmp_5959, end_r_2547, end_r_2990, r_2990, fltAppE_1524_1781, fltAppE_1525_1782, pvrtmp_5896, pvrtmp_5960, zs_148_1219_1428_1760);
            CursorTy pvrtmp_5966 = tmp_struct_137.field0;
            CursorTy pvrtmp_5967 = tmp_struct_137.field1;
            CursorTy pvrtmp_5968 = tmp_struct_137.field2;
            CursorCursorCursorProd tmp_struct_138 =
                                    take_plist_783(end_r_2546, end_r_2989, r_2989, pvrtmp_5958, ys_147_1218_1427_1759);
            CursorTy pvrtmp_5973 = tmp_struct_138.field0;
            CursorTy pvrtmp_5974 = tmp_struct_138.field1;
            CursorTy pvrtmp_5975 = tmp_struct_138.field2;
            CursorCursorCursorProd tmp_struct_139 =
                                    algc(pvrtmp_5888, pvrtmp_5973, pvrtmp_5966, end_r_2549, loc_2544, m2_153_1433_1767, pvrtmp_5958, pvrtmp_5889, pvrtmp_5974, pvrtmp_5967);
            CursorTy pvrtmp_5980 = tmp_struct_139.field0;
            CursorTy pvrtmp_5981 = tmp_struct_139.field1;
            CursorTy pvrtmp_5982 = tmp_struct_139.field2;

            free_region(end_r_2989);
            free_region(end_r_2990);
            free_region(end_r_2991);
            free_region(end_r_2992);
            free_region(end_r_2993);
            free_region(end_r_2994);
            free_region(end_r_2995);
            free_region(end_r_2996);
            free_region(end_r_2997);
            free_region(end_r_2998);
            free_region(end_r_2999);
            free_region(end_r_3000);
            free_region(end_r_3001);
            free_region(end_r_3002);
            return (CursorCursorCursorProd) {pvrtmp_5980, pvrtmp_5981,
                                             pvrtmp_5982};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5989 = *(CursorTy *) tmpcur_5847;
            CursorTy tmpaftercur_5990 = tmpcur_5847 + 8;
            CursorTy jump_3432 = tmpcur_5847 + 8;
            CursorCursorCursorProd tmp_struct_140 =
                                    caseFn_1214(end_r_2545, end_r_2546, end_r_2547, end_r_2548, end_r_2549, loc_2544, m_144_1215_1424_1756, n_145_1216_1425_1757, xs_146_1217_1426_1758, ys_147_1218_1427_1759, zs_148_1219_1428_1760, tmpcur_5989, x_149_1221_1430_1762);
            CursorTy pvrtmp_5991 = tmp_struct_140.field0;
            CursorTy pvrtmp_5992 = tmp_struct_140.field1;
            CursorTy pvrtmp_5993 = tmp_struct_140.field2;

            return (CursorCursorCursorProd) {pvrtmp_5991, pvrtmp_5992,
                                             pvrtmp_5993};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6000 = *(CursorTy *) tmpcur_5847;
            CursorTy tmpaftercur_6001 = tmpcur_5847 + 8;
            CursorCursorCursorProd tmp_struct_141 =
                                    caseFn_1214(end_r_2545, end_r_2546, end_r_2547, end_r_2548, end_r_2549, loc_2544, m_144_1215_1424_1756, n_145_1216_1425_1757, xs_146_1217_1426_1758, ys_147_1218_1427_1759, zs_148_1219_1428_1760, tmpcur_6000, x_149_1221_1430_1762);
            CursorTy pvrtmp_6002 = tmp_struct_141.field0;
            CursorTy pvrtmp_6003 = tmp_struct_141.field1;
            CursorTy pvrtmp_6004 = tmp_struct_141.field2;

            return (CursorCursorCursorProd) {pvrtmp_6002, pvrtmp_6003,
                                             pvrtmp_6004};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5846");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_1222(CursorTy end_r_2554, CursorTy end_r_2555,
                                   CursorTy end_r_2556, CursorTy end_r_2557,
                                   CursorTy loc_2553,
                                   IntTy m_144_1223_1444_1787,
                                   IntTy n_145_1224_1445_1788,
                                   CursorTy xs_146_1225_1446_1789,
                                   CursorTy ys_147_1226_1447_1790,
                                   CursorTy zs_148_1227_1448_1791)
{
    if (loc_2553 + 32 > end_r_2557) {
        ChunkTy new_chunk_148 = alloc_chunk(end_r_2557);
        CursorTy chunk_start_149 = new_chunk_148.chunk_start;
        CursorTy chunk_end_150 = new_chunk_148.chunk_end;

        end_r_2557 = chunk_end_150;
        *(TagTyPacked *) loc_2553 = 255;

        CursorTy redir = loc_2553 + 1;

        *(CursorTy *) redir = chunk_start_149;
        loc_2553 = chunk_start_149;
    }

    TagTyPacked tmpval_6012 = *(TagTyPacked *) xs_146_1225_1446_1789;
    CursorTy tmpcur_6013 = xs_146_1225_1446_1789 + 1;


  switch_6051:
    ;
    switch (tmpval_6012) {

      case 0:
        {
            CursorTy jump_3254 = xs_146_1225_1446_1789 + 1;

            *(TagTyPacked *) loc_2553 = 0;

            CursorTy writetag_3933 = loc_2553 + 1;

            return (CursorCursorCursorProd) {end_r_2557, loc_2553,
                                             writetag_3933};
            break;
        }

      case 1:
        {
            IntTy tmpval_6018 = *(IntTy *) tmpcur_6013;
            CursorTy tmpcur_6019 = tmpcur_6013 + sizeof(IntTy);
            CursorTy jump_3256 = tmpcur_6013 + 8;
            CursorCursorCursorProd tmp_struct_145 =
                                    caseFn_1214(end_r_2554, end_r_2555, end_r_2556, end_r_2554, end_r_2557, loc_2553, m_144_1223_1444_1787, n_145_1224_1445_1788, xs_146_1225_1446_1789, ys_147_1226_1447_1790, zs_148_1227_1448_1791, tmpcur_6019, tmpval_6018);
            CursorTy pvrtmp_6020 = tmp_struct_145.field0;
            CursorTy pvrtmp_6021 = tmp_struct_145.field1;
            CursorTy pvrtmp_6022 = tmp_struct_145.field2;

            return (CursorCursorCursorProd) {pvrtmp_6020, pvrtmp_6021,
                                             pvrtmp_6022};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6029 = *(CursorTy *) tmpcur_6013;
            CursorTy tmpaftercur_6030 = tmpcur_6013 + 8;
            CursorTy jump_3437 = tmpcur_6013 + 8;
            CursorCursorCursorProd tmp_struct_146 =
                                    caseFn_1222(end_r_2554, end_r_2555, end_r_2556, end_r_2557, loc_2553, m_144_1223_1444_1787, n_145_1224_1445_1788, tmpcur_6029, ys_147_1226_1447_1790, zs_148_1227_1448_1791);
            CursorTy pvrtmp_6031 = tmp_struct_146.field0;
            CursorTy pvrtmp_6032 = tmp_struct_146.field1;
            CursorTy pvrtmp_6033 = tmp_struct_146.field2;

            return (CursorCursorCursorProd) {pvrtmp_6031, pvrtmp_6032,
                                             pvrtmp_6033};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6040 = *(CursorTy *) tmpcur_6013;
            CursorTy tmpaftercur_6041 = tmpcur_6013 + 8;
            CursorCursorCursorProd tmp_struct_147 =
                                    caseFn_1222(end_r_2554, end_r_2555, end_r_2556, end_r_2557, loc_2553, m_144_1223_1444_1787, n_145_1224_1445_1788, tmpcur_6040, ys_147_1226_1447_1790, zs_148_1227_1448_1791);
            CursorTy pvrtmp_6042 = tmp_struct_147.field0;
            CursorTy pvrtmp_6043 = tmp_struct_147.field1;
            CursorTy pvrtmp_6044 = tmp_struct_147.field2;

            return (CursorCursorCursorProd) {pvrtmp_6042, pvrtmp_6043,
                                             pvrtmp_6044};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6012");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_1228(CursorTy end_r_2561, CursorTy end_r_2562,
                                   CursorTy end_r_2563, CursorTy loc_2560,
                                   CursorTy bs_214_1229_1451_1794,
                                   IntTy z_217_1230_1452_1795,
                                   CursorTy zs_218_1231_1453_1796)
{
    if (loc_2560 + 32 > end_r_2563) {
        ChunkTy new_chunk_154 = alloc_chunk(end_r_2563);
        CursorTy chunk_start_155 = new_chunk_154.chunk_start;
        CursorTy chunk_end_156 = new_chunk_154.chunk_end;

        end_r_2563 = chunk_end_156;
        *(TagTyPacked *) loc_2560 = 255;

        CursorTy redir = loc_2560 + 1;

        *(CursorTy *) redir = chunk_start_155;
        loc_2560 = chunk_start_155;
    }

    TagTyPacked tmpval_6052 = *(TagTyPacked *) bs_214_1229_1451_1794;
    CursorTy tmpcur_6053 = bs_214_1229_1451_1794 + 1;


  switch_6093:
    ;
    switch (tmpval_6052) {

      case 0:
        {
            CursorTy jump_3258 = bs_214_1229_1451_1794 + 1;

            *(TagTyPacked *) loc_2560 = 0;

            CursorTy writetag_3945 = loc_2560 + 1;

            return (CursorCursorCursorProd) {end_r_2563, loc_2560,
                                             writetag_3945};
            break;
        }

      case 1:
        {
            IntTy tmpval_6058 = *(IntTy *) tmpcur_6053;
            CursorTy tmpcur_6059 = tmpcur_6053 + sizeof(IntTy);
            CursorTy jump_3260 = tmpcur_6053 + 8;
            CursorTy loc_3028 = loc_2560 + 1;
            CursorTy loc_3029 = loc_3028 + 8;
            CursorTy loc_3030 = loc_3029 + 8;
            CursorCursorCursorProd tmp_struct_151 =
                                    zip_plist_786(end_r_2562, end_r_2561, end_r_2563, loc_3030, zs_218_1231_1453_1796, tmpcur_6059);
            CursorTy pvrtmp_6060 = tmp_struct_151.field0;
            CursorTy pvrtmp_6061 = tmp_struct_151.field1;
            CursorTy pvrtmp_6062 = tmp_struct_151.field2;

            *(TagTyPacked *) loc_2560 = 1;

            CursorTy writetag_3950 = loc_2560 + 1;

            *(IntTy *) writetag_3950 = z_217_1230_1452_1795;

            CursorTy writecur_3951 = writetag_3950 + sizeof(IntTy);

            *(IntTy *) writecur_3951 = tmpval_6058;

            CursorTy writecur_3952 = writecur_3951 + sizeof(IntTy);

            return (CursorCursorCursorProd) {pvrtmp_6060, loc_2560,
                                             pvrtmp_6062};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6071 = *(CursorTy *) tmpcur_6053;
            CursorTy tmpaftercur_6072 = tmpcur_6053 + 8;
            CursorTy jump_3442 = tmpcur_6053 + 8;
            CursorCursorCursorProd tmp_struct_152 =
                                    caseFn_1228(end_r_2561, end_r_2562, end_r_2563, loc_2560, tmpcur_6071, z_217_1230_1452_1795, zs_218_1231_1453_1796);
            CursorTy pvrtmp_6073 = tmp_struct_152.field0;
            CursorTy pvrtmp_6074 = tmp_struct_152.field1;
            CursorTy pvrtmp_6075 = tmp_struct_152.field2;

            return (CursorCursorCursorProd) {pvrtmp_6073, pvrtmp_6074,
                                             pvrtmp_6075};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6082 = *(CursorTy *) tmpcur_6053;
            CursorTy tmpaftercur_6083 = tmpcur_6053 + 8;
            CursorCursorCursorProd tmp_struct_153 =
                                    caseFn_1228(end_r_2561, end_r_2562, end_r_2563, loc_2560, tmpcur_6082, z_217_1230_1452_1795, zs_218_1231_1453_1796);
            CursorTy pvrtmp_6084 = tmp_struct_153.field0;
            CursorTy pvrtmp_6085 = tmp_struct_153.field1;
            CursorTy pvrtmp_6086 = tmp_struct_153.field2;

            return (CursorCursorCursorProd) {pvrtmp_6084, pvrtmp_6085,
                                             pvrtmp_6086};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6052");
            exit(1);
        }
    }
}
CursorCursorCursorProd caseFn_1232(CursorTy end_r_2566, CursorTy end_r_2567,
                                   CursorTy loc_2565,
                                   IntTy n_203_1233_1456_1800,
                                   CursorTy a_204_1234_1457_1801)
{
    if (loc_2565 + 32 > end_r_2567) {
        ChunkTy new_chunk_160 = alloc_chunk(end_r_2567);
        CursorTy chunk_start_161 = new_chunk_160.chunk_start;
        CursorTy chunk_end_162 = new_chunk_160.chunk_end;

        end_r_2567 = chunk_end_162;
        *(TagTyPacked *) loc_2565 = 255;

        CursorTy redir = loc_2565 + 1;

        *(CursorTy *) redir = chunk_start_161;
        loc_2565 = chunk_start_161;
    }

    TagTyPacked tmpval_6094 = *(TagTyPacked *) a_204_1234_1457_1801;
    CursorTy tmpcur_6095 = a_204_1234_1457_1801 + 1;


  switch_6135:
    ;
    switch (tmpval_6094) {

      case 0:
        {
            CursorTy jump_3262 = a_204_1234_1457_1801 + 1;

            *(TagTyPacked *) loc_2565 = 0;

            CursorTy writetag_3962 = loc_2565 + 1;

            return (CursorCursorCursorProd) {end_r_2567, loc_2565,
                                             writetag_3962};
            break;
        }

      case 1:
        {
            IntTy tmpval_6100 = *(IntTy *) tmpcur_6095;
            CursorTy tmpcur_6101 = tmpcur_6095 + sizeof(IntTy);
            CursorTy jump_3264 = tmpcur_6095 + 8;
            IntTy fltAppE_1530_1804 = n_203_1233_1456_1800 - 1;
            CursorTy loc_3044 = loc_2565 + 1;
            CursorTy loc_3045 = loc_3044 + 8;
            CursorCursorCursorProd tmp_struct_157 =
                                    take_plist_783(end_r_2566, end_r_2567, loc_3045, fltAppE_1530_1804, tmpcur_6101);
            CursorTy pvrtmp_6102 = tmp_struct_157.field0;
            CursorTy pvrtmp_6103 = tmp_struct_157.field1;
            CursorTy pvrtmp_6104 = tmp_struct_157.field2;

            *(TagTyPacked *) loc_2565 = 1;

            CursorTy writetag_3967 = loc_2565 + 1;

            *(IntTy *) writetag_3967 = tmpval_6100;

            CursorTy writecur_3968 = writetag_3967 + sizeof(IntTy);

            return (CursorCursorCursorProd) {pvrtmp_6102, loc_2565,
                                             pvrtmp_6104};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6113 = *(CursorTy *) tmpcur_6095;
            CursorTy tmpaftercur_6114 = tmpcur_6095 + 8;
            CursorTy jump_3447 = tmpcur_6095 + 8;
            CursorCursorCursorProd tmp_struct_158 =
                                    caseFn_1232(end_r_2566, end_r_2567, loc_2565, n_203_1233_1456_1800, tmpcur_6113);
            CursorTy pvrtmp_6115 = tmp_struct_158.field0;
            CursorTy pvrtmp_6116 = tmp_struct_158.field1;
            CursorTy pvrtmp_6117 = tmp_struct_158.field2;

            return (CursorCursorCursorProd) {pvrtmp_6115, pvrtmp_6116,
                                             pvrtmp_6117};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6124 = *(CursorTy *) tmpcur_6095;
            CursorTy tmpaftercur_6125 = tmpcur_6095 + 8;
            CursorCursorCursorProd tmp_struct_159 =
                                    caseFn_1232(end_r_2566, end_r_2567, loc_2565, n_203_1233_1456_1800, tmpcur_6124);
            CursorTy pvrtmp_6126 = tmp_struct_159.field0;
            CursorTy pvrtmp_6127 = tmp_struct_159.field1;
            CursorTy pvrtmp_6128 = tmp_struct_159.field2;

            return (CursorCursorCursorProd) {pvrtmp_6126, pvrtmp_6127,
                                             pvrtmp_6128};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6094");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_PList_v_778(CursorTy end_r_2570,
                                                                   CursorTy end_r_2571,
                                                                   CursorTy loc_2569,
                                                                   CursorTy arg_2417)
{
    if (loc_2569 + 32 > end_r_2571) {
        ChunkTy new_chunk_166 = alloc_chunk(end_r_2571);
        CursorTy chunk_start_167 = new_chunk_166.chunk_start;
        CursorTy chunk_end_168 = new_chunk_166.chunk_end;

        end_r_2571 = chunk_end_168;
        *(TagTyPacked *) loc_2569 = 255;

        CursorTy redir = loc_2569 + 1;

        *(CursorTy *) redir = chunk_start_167;
        loc_2569 = chunk_start_167;
    }

    TagTyPacked tmpval_6136 = *(TagTyPacked *) arg_2417;
    CursorTy tmpcur_6137 = arg_2417 + 1;


  switch_6180:
    ;
    switch (tmpval_6136) {

      case 0:
        {
            CursorTy jump_3266 = arg_2417 + 1;

            *(TagTyPacked *) loc_2569 = 0;

            CursorTy writetag_3978 = loc_2569 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2571, jump_3266,
                                                   loc_2569, writetag_3978};
            break;
        }

      case 1:
        {
            IntTy tmpval_6142 = *(IntTy *) tmpcur_6137;
            CursorTy tmpcur_6143 = tmpcur_6137 + sizeof(IntTy);
            CursorTy jump_3268 = tmpcur_6137 + 8;
            CursorTy loc_3057 = loc_2569 + 1;
            CursorTy loc_3058 = loc_3057 + 8;
            CursorCursorCursorCursorProd tmp_struct_163 =
                                          _add_size_and_rel_offsets_PList_v_778(end_r_2570, end_r_2571, loc_3058, tmpcur_6143);
            CursorTy pvrtmp_6144 = tmp_struct_163.field0;
            CursorTy pvrtmp_6145 = tmp_struct_163.field1;
            CursorTy pvrtmp_6146 = tmp_struct_163.field2;
            CursorTy pvrtmp_6147 = tmp_struct_163.field3;

            *(TagTyPacked *) loc_2569 = 1;

            CursorTy writetag_3983 = loc_2569 + 1;

            *(IntTy *) writetag_3983 = tmpval_6142;

            CursorTy writecur_3984 = writetag_3983 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_6144, pvrtmp_6145,
                                                   loc_2569, pvrtmp_6147};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6156 = *(CursorTy *) tmpcur_6137;
            CursorTy tmpaftercur_6157 = tmpcur_6137 + 8;
            CursorTy jump_3452 = tmpcur_6137 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          _add_size_and_rel_offsets_PList_v_778(end_r_2570, end_r_2571, loc_2569, tmpcur_6156);
            CursorTy pvrtmp_6158 = tmp_struct_164.field0;
            CursorTy pvrtmp_6159 = tmp_struct_164.field1;
            CursorTy pvrtmp_6160 = tmp_struct_164.field2;
            CursorTy pvrtmp_6161 = tmp_struct_164.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6158, jump_3452,
                                                   pvrtmp_6160, pvrtmp_6161};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6168 = *(CursorTy *) tmpcur_6137;
            CursorTy tmpaftercur_6169 = tmpcur_6137 + 8;
            CursorCursorCursorCursorProd tmp_struct_165 =
                                          _add_size_and_rel_offsets_PList_v_778(end_r_2570, end_r_2571, loc_2569, tmpcur_6168);
            CursorTy pvrtmp_6170 = tmp_struct_165.field0;
            CursorTy pvrtmp_6171 = tmp_struct_165.field1;
            CursorTy pvrtmp_6172 = tmp_struct_165.field2;
            CursorTy pvrtmp_6173 = tmp_struct_165.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6170, pvrtmp_6171,
                                                   pvrtmp_6172, pvrtmp_6173};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6136");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_PList_v_779(CursorTy end_r_2574,
                                                                   CursorTy end_r_2575,
                                                                   CursorTy loc_2573,
                                                                   CursorTy arg_2422)
{
    if (loc_2573 + 32 > end_r_2575) {
        ChunkTy new_chunk_172 = alloc_chunk(end_r_2575);
        CursorTy chunk_start_173 = new_chunk_172.chunk_start;
        CursorTy chunk_end_174 = new_chunk_172.chunk_end;

        end_r_2575 = chunk_end_174;
        *(TagTyPacked *) loc_2573 = 255;

        CursorTy redir = loc_2573 + 1;

        *(CursorTy *) redir = chunk_start_173;
        loc_2573 = chunk_start_173;
    }

    TagTyPacked tmpval_6181 = *(TagTyPacked *) arg_2422;
    CursorTy tmpcur_6182 = arg_2422 + 1;


  switch_6227:
    ;
    switch (tmpval_6181) {

      case 0:
        {
            CursorTy jump_3271 = arg_2422 + 1;

            *(TagTyPacked *) loc_2573 = 0;

            CursorTy writetag_3994 = loc_2573 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2575, jump_3271,
                                                   loc_2573, writetag_3994};
            break;
        }

      case 1:
        {
            IntTy tmpval_6187 = *(IntTy *) tmpcur_6182;
            CursorTy tmpcur_6188 = tmpcur_6182 + sizeof(IntTy);
            IntTy tmpval_6189 = *(IntTy *) tmpcur_6188;
            CursorTy tmpcur_6190 = tmpcur_6188 + sizeof(IntTy);
            CursorTy jump_3274 = tmpcur_6188 + 8;
            CursorTy jump_3273 = tmpcur_6182 + 8;
            CursorTy loc_3071 = loc_2573 + 1;
            CursorTy loc_3072 = loc_3071 + 8;
            CursorTy loc_3073 = loc_3072 + 8;
            CursorCursorCursorCursorProd tmp_struct_169 =
                                          _add_size_and_rel_offsets_PList_v_779(end_r_2574, end_r_2575, loc_3073, tmpcur_6190);
            CursorTy pvrtmp_6191 = tmp_struct_169.field0;
            CursorTy pvrtmp_6192 = tmp_struct_169.field1;
            CursorTy pvrtmp_6193 = tmp_struct_169.field2;
            CursorTy pvrtmp_6194 = tmp_struct_169.field3;

            *(TagTyPacked *) loc_2573 = 1;

            CursorTy writetag_4000 = loc_2573 + 1;

            *(IntTy *) writetag_4000 = tmpval_6187;

            CursorTy writecur_4001 = writetag_4000 + sizeof(IntTy);

            *(IntTy *) writecur_4001 = tmpval_6189;

            CursorTy writecur_4002 = writecur_4001 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {pvrtmp_6191, pvrtmp_6192,
                                                   loc_2573, pvrtmp_6194};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6203 = *(CursorTy *) tmpcur_6182;
            CursorTy tmpaftercur_6204 = tmpcur_6182 + 8;
            CursorTy jump_3458 = tmpcur_6182 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _add_size_and_rel_offsets_PList_v_779(end_r_2574, end_r_2575, loc_2573, tmpcur_6203);
            CursorTy pvrtmp_6205 = tmp_struct_170.field0;
            CursorTy pvrtmp_6206 = tmp_struct_170.field1;
            CursorTy pvrtmp_6207 = tmp_struct_170.field2;
            CursorTy pvrtmp_6208 = tmp_struct_170.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6205, jump_3458,
                                                   pvrtmp_6207, pvrtmp_6208};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6215 = *(CursorTy *) tmpcur_6182;
            CursorTy tmpaftercur_6216 = tmpcur_6182 + 8;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          _add_size_and_rel_offsets_PList_v_779(end_r_2574, end_r_2575, loc_2573, tmpcur_6215);
            CursorTy pvrtmp_6217 = tmp_struct_171.field0;
            CursorTy pvrtmp_6218 = tmp_struct_171.field1;
            CursorTy pvrtmp_6219 = tmp_struct_171.field2;
            CursorTy pvrtmp_6220 = tmp_struct_171.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6217, pvrtmp_6218,
                                                   pvrtmp_6219, pvrtmp_6220};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6181");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Maybe_v_788(CursorTy end_r_2578,
                                                                   CursorTy end_r_2579,
                                                                   CursorTy loc_2577,
                                                                   CursorTy arg_2429)
{
    if (loc_2577 + 32 > end_r_2579) {
        ChunkTy new_chunk_177 = alloc_chunk(end_r_2579);
        CursorTy chunk_start_178 = new_chunk_177.chunk_start;
        CursorTy chunk_end_179 = new_chunk_177.chunk_end;

        end_r_2579 = chunk_end_179;
        *(TagTyPacked *) loc_2577 = 255;

        CursorTy redir = loc_2577 + 1;

        *(CursorTy *) redir = chunk_start_178;
        loc_2577 = chunk_start_178;
    }

    TagTyPacked tmpval_6228 = *(TagTyPacked *) arg_2429;
    CursorTy tmpcur_6229 = arg_2429 + 1;


  switch_6264:
    ;
    switch (tmpval_6228) {

      case 0:
        {
            IntTy tmpval_6230 = *(IntTy *) tmpcur_6229;
            CursorTy tmpcur_6231 = tmpcur_6229 + sizeof(IntTy);
            CursorTy jump_3277 = tmpcur_6229 + 8;

            *(TagTyPacked *) loc_2577 = 0;

            CursorTy writetag_4013 = loc_2577 + 1;

            *(IntTy *) writetag_4013 = tmpval_6230;

            CursorTy writecur_4014 = writetag_4013 + sizeof(IntTy);

            return (CursorCursorCursorCursorProd) {end_r_2579, jump_3277,
                                                   loc_2577, writecur_4014};
            break;
        }

      case 1:
        {
            CursorTy jump_3279 = arg_2429 + 1;

            *(TagTyPacked *) loc_2577 = 1;

            CursorTy writetag_4017 = loc_2577 + 1;

            return (CursorCursorCursorCursorProd) {end_r_2579, jump_3279,
                                                   loc_2577, writetag_4017};
            break;
        }

      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6240 = *(CursorTy *) tmpcur_6229;
            CursorTy tmpaftercur_6241 = tmpcur_6229 + 8;
            CursorTy jump_3464 = tmpcur_6229 + 8;
            CursorCursorCursorCursorProd tmp_struct_175 =
                                          _add_size_and_rel_offsets_Maybe_v_788(end_r_2578, end_r_2579, loc_2577, tmpcur_6240);
            CursorTy pvrtmp_6242 = tmp_struct_175.field0;
            CursorTy pvrtmp_6243 = tmp_struct_175.field1;
            CursorTy pvrtmp_6244 = tmp_struct_175.field2;
            CursorTy pvrtmp_6245 = tmp_struct_175.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6242, jump_3464,
                                                   pvrtmp_6244, pvrtmp_6245};
            break;
        }

      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6252 = *(CursorTy *) tmpcur_6229;
            CursorTy tmpaftercur_6253 = tmpcur_6229 + 8;
            CursorCursorCursorCursorProd tmp_struct_176 =
                                          _add_size_and_rel_offsets_Maybe_v_788(end_r_2578, end_r_2579, loc_2577, tmpcur_6252);
            CursorTy pvrtmp_6254 = tmp_struct_176.field0;
            CursorTy pvrtmp_6255 = tmp_struct_176.field1;
            CursorTy pvrtmp_6256 = tmp_struct_176.field2;
            CursorTy pvrtmp_6257 = tmp_struct_176.field3;

            return (CursorCursorCursorCursorProd) {pvrtmp_6254, pvrtmp_6255,
                                                   pvrtmp_6256, pvrtmp_6257};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6228");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(4834, ")");
    add_symbol(4835, "(Nothing_v_788");
    add_symbol(4836, "(Nil_v_779");
    add_symbol(4837, "(Nil_v_778");
    add_symbol(4838, "(Just_v_788");
    add_symbol(4839, "(Cons_v_779");
    add_symbol(4840, "(Cons_v_778");
    add_symbol(4841, " ->r ");
    add_symbol(4842, " ->i ");
    add_symbol(4843, " ");

    IntTy n_101_1235_1531 = global_size_param;
    BoolTy fltPrm_1466_1532 = n_101_1235_1531 < 1;
    BoolTy fltPrm_1467_1533 = n_101_1235_1531 == 1;
    BoolTy fltIf_1465_1534 = fltPrm_1466_1532 || fltPrm_1467_1533;

    if (fltIf_1465_1534) {
        Int64Int64Int64Int64Int64Int64Prod tmp_struct_180 =  very_small_opts();
        IntTy pvrtmp_4844 = tmp_struct_180.field0;
        IntTy pvrtmp_4845 = tmp_struct_180.field1;
        IntTy pvrtmp_4846 = tmp_struct_180.field2;
        IntTy pvrtmp_4847 = tmp_struct_180.field3;
        IntTy pvrtmp_4848 = tmp_struct_180.field4;
        IntTy pvrtmp_4849 = tmp_struct_180.field5;
        Int64Int64Int64Prod tmp_struct_181 =  very_small_opts_answer();
        IntTy pvrtmp_4850 = tmp_struct_181.field0;
        IntTy pvrtmp_4851 = tmp_struct_181.field1;
        IntTy pvrtmp_4852 = tmp_struct_181.field2;
        BoolTy tailapp_3281 =
                bench_lcss((Int64Int64Int64Int64Int64Int64Prod) {pvrtmp_4844, pvrtmp_4845, pvrtmp_4846, pvrtmp_4847, pvrtmp_4848, pvrtmp_4849}, (Int64Int64Int64Prod) {pvrtmp_4850, pvrtmp_4851, pvrtmp_4852});

        if (tailapp_3281) {
            printf("#t");
            printf("\n");
            free_symtable();
            return 0;
        } else {
            printf("#f");
            printf("\n");
            free_symtable();
            return 0;
        }
    } else {
        BoolTy fltIf_1470_1537 = n_101_1235_1531 == 2;

        if (fltIf_1470_1537) {
            Int64Int64Int64Int64Int64Int64Prod tmp_struct_182 =  small_opts();
            IntTy pvrtmp_4862 = tmp_struct_182.field0;
            IntTy pvrtmp_4863 = tmp_struct_182.field1;
            IntTy pvrtmp_4864 = tmp_struct_182.field2;
            IntTy pvrtmp_4865 = tmp_struct_182.field3;
            IntTy pvrtmp_4866 = tmp_struct_182.field4;
            IntTy pvrtmp_4867 = tmp_struct_182.field5;
            Int64Int64Int64Prod tmp_struct_183 =  small_opts_answer();
            IntTy pvrtmp_4868 = tmp_struct_183.field0;
            IntTy pvrtmp_4869 = tmp_struct_183.field1;
            IntTy pvrtmp_4870 = tmp_struct_183.field2;
            BoolTy tailapp_3282 =
                    bench_lcss((Int64Int64Int64Int64Int64Int64Prod) {pvrtmp_4862, pvrtmp_4863, pvrtmp_4864, pvrtmp_4865, pvrtmp_4866, pvrtmp_4867}, (Int64Int64Int64Prod) {pvrtmp_4868, pvrtmp_4869, pvrtmp_4870});

            if (tailapp_3282) {
                printf("#t");
                printf("\n");
                free_symtable();
                return 0;
            } else {
                printf("#f");
                printf("\n");
                free_symtable();
                return 0;
            }
        } else {
            BoolTy fltIf_1473_1540 = n_101_1235_1531 == 3;

            if (fltIf_1473_1540) {
                Int64Int64Int64Int64Int64Int64Prod tmp_struct_184 =
                                                    fast_opts();
                IntTy pvrtmp_4880 = tmp_struct_184.field0;
                IntTy pvrtmp_4881 = tmp_struct_184.field1;
                IntTy pvrtmp_4882 = tmp_struct_184.field2;
                IntTy pvrtmp_4883 = tmp_struct_184.field3;
                IntTy pvrtmp_4884 = tmp_struct_184.field4;
                IntTy pvrtmp_4885 = tmp_struct_184.field5;
                Int64Int64Int64Prod tmp_struct_185 =  fast_opts_answer();
                IntTy pvrtmp_4886 = tmp_struct_185.field0;
                IntTy pvrtmp_4887 = tmp_struct_185.field1;
                IntTy pvrtmp_4888 = tmp_struct_185.field2;
                BoolTy tailapp_3283 =
                        bench_lcss((Int64Int64Int64Int64Int64Int64Prod) {pvrtmp_4880, pvrtmp_4881, pvrtmp_4882, pvrtmp_4883, pvrtmp_4884, pvrtmp_4885}, (Int64Int64Int64Prod) {pvrtmp_4886, pvrtmp_4887, pvrtmp_4888});

                if (tailapp_3283) {
                    printf("#t");
                    printf("\n");
                    free_symtable();
                    return 0;
                } else {
                    printf("#f");
                    printf("\n");
                    free_symtable();
                    return 0;
                }
            } else {
                BoolTy fltIf_1476_1543 = n_101_1235_1531 == 4;

                if (fltIf_1476_1543) {
                    Int64Int64Int64Int64Int64Int64Prod tmp_struct_186 =
                                                        norm_opts();
                    IntTy pvrtmp_4898 = tmp_struct_186.field0;
                    IntTy pvrtmp_4899 = tmp_struct_186.field1;
                    IntTy pvrtmp_4900 = tmp_struct_186.field2;
                    IntTy pvrtmp_4901 = tmp_struct_186.field3;
                    IntTy pvrtmp_4902 = tmp_struct_186.field4;
                    IntTy pvrtmp_4903 = tmp_struct_186.field5;
                    Int64Int64Int64Prod tmp_struct_187 =  norm_opts_answer();
                    IntTy pvrtmp_4904 = tmp_struct_187.field0;
                    IntTy pvrtmp_4905 = tmp_struct_187.field1;
                    IntTy pvrtmp_4906 = tmp_struct_187.field2;
                    BoolTy tailapp_3284 =
                            bench_lcss((Int64Int64Int64Int64Int64Int64Prod) {pvrtmp_4898, pvrtmp_4899, pvrtmp_4900, pvrtmp_4901, pvrtmp_4902, pvrtmp_4903}, (Int64Int64Int64Prod) {pvrtmp_4904, pvrtmp_4905, pvrtmp_4906});

                    if (tailapp_3284) {
                        printf("#t");
                        printf("\n");
                        free_symtable();
                        return 0;
                    } else {
                        printf("#f");
                        printf("\n");
                        free_symtable();
                        return 0;
                    }
                } else {
                    Int64Int64Int64Int64Int64Int64Prod tmp_struct_188 =
                                                        slow_opts();
                    IntTy pvrtmp_4916 = tmp_struct_188.field0;
                    IntTy pvrtmp_4917 = tmp_struct_188.field1;
                    IntTy pvrtmp_4918 = tmp_struct_188.field2;
                    IntTy pvrtmp_4919 = tmp_struct_188.field3;
                    IntTy pvrtmp_4920 = tmp_struct_188.field4;
                    IntTy pvrtmp_4921 = tmp_struct_188.field5;
                    Int64Int64Int64Prod tmp_struct_189 =  slow_opts_answer();
                    IntTy pvrtmp_4922 = tmp_struct_189.field0;
                    IntTy pvrtmp_4923 = tmp_struct_189.field1;
                    IntTy pvrtmp_4924 = tmp_struct_189.field2;
                    BoolTy tailapp_3285 =
                            bench_lcss((Int64Int64Int64Int64Int64Int64Prod) {pvrtmp_4916, pvrtmp_4917, pvrtmp_4918, pvrtmp_4919, pvrtmp_4920, pvrtmp_4921}, (Int64Int64Int64Prod) {pvrtmp_4922, pvrtmp_4923, pvrtmp_4924});

                    if (tailapp_3285) {
                        printf("#t");
                        printf("\n");
                        free_symtable();
                        return 0;
                    } else {
                        printf("#f");
                        printf("\n");
                        free_symtable();
                        return 0;
                    }
                }
            }
        }
    }
}
