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

#include "_papi.h"

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
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2914, CursorTy end_r_2915,
                                     CursorTy loc_2913,
                                     CursorTy adt_15_901_1518);
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2918, CursorTy end_r_2919,
                                       CursorTy loc_2917,
                                       CursorTy tags_21_907_1525,
                                       IntTy inVal_22_908_1526);
CursorCursorCursorProd mkCATList(CursorTy end_r_2921, CursorTy loc_2920,
                                 IntTy len_25_911_1531,
                                 IntTy tagLen_26_912_1532,
                                 IntTy strLen_27_913_1533);
CursorCursorCursorProd mkString(CursorTy end_r_2923, CursorTy loc_2922,
                                IntTy len_180_1066_1539);
CursorCursorCursorProd mkContentText(CursorTy end_r_2925, CursorTy loc_2924,
                                     IntTy n_194_1080_1545);
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2927, CursorTy loc_2926,
                                    IntTy len_319_1205_1547);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2930,
                                          CursorTy end_r_2931,
                                          CursorTy loc_2929,
                                          CursorTy arg_623_1229_1552);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2934,
                                                       CursorTy end_r_2935,
                                                       CursorTy loc_2933,
                                                       CursorTy arg_628_1234_1557);
CursorProd _traverse_String(CursorTy end_r_2937, CursorTy arg_633_1239_1562);
CursorProd _print_String(CursorTy end_r_2939, CursorTy arg_638_1243_1566);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2942,
                                           CursorTy end_r_2943,
                                           CursorTy loc_2941,
                                           CursorTy arg_647_1252_1575);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2946,
                                                        CursorTy end_r_2947,
                                                        CursorTy loc_2945,
                                                        CursorTy arg_652_1257_1580);
CursorProd _traverse_Content(CursorTy end_r_2949, CursorTy arg_657_1262_1585);
CursorProd _print_Content(CursorTy end_r_2951, CursorTy arg_662_1267_1590);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2954, CursorTy end_r_2955,
                                       CursorTy loc_2953,
                                       CursorTy arg_671_1276_1599);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2958,
                                                    CursorTy end_r_2959,
                                                    CursorTy loc_2957,
                                                    CursorTy arg_716_1321_1644);
CursorProd _traverse_Adt(CursorTy end_r_2961, CursorTy arg_761_1366_1689);
CursorProd _print_Adt(CursorTy end_r_2963, CursorTy arg_806_1411_1734);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2966,
                                        CursorTy end_r_2967, CursorTy loc_2965,
                                        CursorTy arg_869_1474_1797);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2970,
                                                     CursorTy end_r_2971,
                                                     CursorTy loc_2969,
                                                     CursorTy arg_874_1479_1802);
CursorProd _traverse_Tags(CursorTy end_r_2973, CursorTy arg_879_1484_1807);
CursorProd _print_Tags(CursorTy end_r_2975, CursorTy arg_884_1488_1811);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_2978, CursorTy end_r_2979,
                                 CursorTy loc_2977, CursorTy arg_2710);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_2982, CursorTy end_r_2983,
                                  CursorTy loc_2981, CursorTy arg_2715);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2986,
                                                           CursorTy end_r_2987,
                                                           CursorTy loc_2985,
                                                           CursorTy arg_2720);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2990,
                                                            CursorTy end_r_2991,
                                                            CursorTy loc_2989,
                                                            CursorTy arg_2809);
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2914, CursorTy end_r_2915,
                                     CursorTy loc_2913,
                                     CursorTy adt_15_901_1518)
{
    if (loc_2913 + 32 > end_r_2915) {
        ChunkTy new_chunk_4 = alloc_chunk(end_r_2915);
        CursorTy chunk_start_5 = new_chunk_4.chunk_start;
        CursorTy chunk_end_6 = new_chunk_4.chunk_end;
        
        end_r_2915 = chunk_end_6;
        *(TagTyPacked *) loc_2913 = 255;
        
        CursorTy redir = loc_2913 + 1;
        
        *(CursorTy *) redir = chunk_start_5;
        loc_2913 = chunk_start_5;
    }
    
    CursorTy loc_3020 = loc_2913 + 1;
    CursorTy loc_3021 = loc_3020 + 8;
    CursorTy loc_3022 = loc_3021 + 8;
    TagTyPacked tmpval_6193 = *(TagTyPacked *) adt_15_901_1518;
    CursorTy tmpcur_6194 = adt_15_901_1518 + 1;
    
    
  switch_6250:
    ;
    switch (tmpval_6193) {
        
      case 0:
        {
            CursorTy jump_3946 = adt_15_901_1518 + 1;
            
            *(TagTyPacked *) loc_2913 = 0;
            
            CursorTy writetag_4505 = loc_2913 + 1;
            
            return (CursorCursorCursorProd) {end_r_2915, loc_2913,
                                             writetag_4505};
            break;
        }
        
      case 23:
        {
            RegionTy *region_6199 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3032 = region_6199->reg_heap;
            IntTy sizeof_end_r_3032_6200 = global_init_inf_buf_size;
            CursorTy end_r_3032 = r_3032 + sizeof_end_r_3032_6200;
            CursorTy tmpcur_6201 = *(CursorTy *) tmpcur_6194;
            CursorTy tmpaftercur_6202 = tmpcur_6194 + 8;
            CursorTy tmpcur_6203 = *(CursorTy *) tmpaftercur_6202;
            CursorTy tmpaftercur_6204 = tmpaftercur_6202 + 8;
            CursorTy jump_3949 = tmpaftercur_6202 + 8;
            CursorTy jump_3948 = tmpcur_6194 + 8;
            
            *(TagTyPacked *) loc_3022 = 254;
            
            CursorTy writetag_4510 = loc_3022 + 1;
            
            *(CursorTy *) writetag_4510 = tmpaftercur_6204;
            
            CursorTy writecur_4511 = writetag_4510 + 8;
            CursorCursorCursorCursorProd tmp_struct_0 =
                                          addValTag(end_r_2914, end_r_3032, r_3032, tmpcur_6203, 10);
            CursorTy pvrtmp_6207 = tmp_struct_0.field0;
            CursorTy pvrtmp_6208 = tmp_struct_0.field1;
            CursorTy pvrtmp_6209 = tmp_struct_0.field2;
            CursorTy pvrtmp_6210 = tmp_struct_0.field3;
            CursorCursorCursorProd tmp_struct_1 =
                                    addValTagsAdt(end_r_2914, end_r_2915, writecur_4511, tmpcur_6201);
            CursorTy pvrtmp_6215 = tmp_struct_1.field0;
            CursorTy pvrtmp_6216 = tmp_struct_1.field1;
            CursorTy pvrtmp_6217 = tmp_struct_1.field2;
            
            *(TagTyPacked *) pvrtmp_6217 = 254;
            
            CursorTy writetag_4515 = pvrtmp_6217 + 1;
            
            *(CursorTy *) writetag_4515 = r_3032;
            
            CursorTy writecur_4516 = writetag_4515 + 8;
            
            *(TagTyPacked *) loc_2913 = 23;
            
            CursorTy writetag_4518 = loc_2913 + 1;
            
            *(CursorTy *) writetag_4518 = tmpcur_6201;
            
            CursorTy writecur_4519 = writetag_4518 + 8;
            
            *(CursorTy *) writecur_4519 = pvrtmp_6217;
            
            CursorTy writecur_4520 = writecur_4519 + 8;
            
            return (CursorCursorCursorProd) {pvrtmp_6215, loc_2913,
                                             writecur_4516};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6228 = *(CursorTy *) tmpcur_6194;
            CursorTy tmpaftercur_6229 = tmpcur_6194 + 8;
            CursorTy jump_4258 = tmpcur_6194 + 8;
            CursorCursorCursorProd tmp_struct_2 =
                                    addValTagsAdt(end_r_2914, end_r_2915, loc_2913, tmpcur_6228);
            CursorTy pvrtmp_6230 = tmp_struct_2.field0;
            CursorTy pvrtmp_6231 = tmp_struct_2.field1;
            CursorTy pvrtmp_6232 = tmp_struct_2.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6230, pvrtmp_6231,
                                             pvrtmp_6232};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6239 = *(CursorTy *) tmpcur_6194;
            CursorTy tmpaftercur_6240 = tmpcur_6194 + 8;
            CursorCursorCursorProd tmp_struct_3 =
                                    addValTagsAdt(end_r_2914, end_r_2915, loc_2913, tmpcur_6239);
            CursorTy pvrtmp_6241 = tmp_struct_3.field0;
            CursorTy pvrtmp_6242 = tmp_struct_3.field1;
            CursorTy pvrtmp_6243 = tmp_struct_3.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6241, pvrtmp_6242,
                                             pvrtmp_6243};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6193");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2918, CursorTy end_r_2919,
                                       CursorTy loc_2917,
                                       CursorTy tags_21_907_1525,
                                       IntTy inVal_22_908_1526)
{
    if (loc_2917 + 32 > end_r_2919) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2919);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2919 = chunk_end_12;
        *(TagTyPacked *) loc_2917 = 255;
        
        CursorTy redir = loc_2917 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2917 = chunk_start_11;
    }
    
    CursorTy loc_3041 = loc_2917 + 1;
    CursorTy loc_3042 = loc_3041 + 8;
    TagTyPacked tmpval_6251 = *(TagTyPacked *) tags_21_907_1525;
    CursorTy tmpcur_6252 = tags_21_907_1525 + 1;
    
    
  switch_6295:
    ;
    switch (tmpval_6251) {
        
      case 0:
        {
            CursorTy jump_3952 = tags_21_907_1525 + 1;
            
            *(TagTyPacked *) loc_2917 = 0;
            
            CursorTy writetag_4532 = loc_2917 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2919, jump_3952,
                                                   loc_2917, writetag_4532};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6257 = *(IntTy *) tmpcur_6252;
            CursorTy tmpcur_6258 = tmpcur_6252 + sizeof(IntTy);
            CursorTy jump_3954 = tmpcur_6252 + 8;
            IntTy fltPkd_1506_1529 = tmpval_6257 + inVal_22_908_1526;
            CursorCursorCursorCursorProd tmp_struct_7 =
                                          addValTag(end_r_2918, end_r_2919, loc_3042, tmpcur_6258, inVal_22_908_1526);
            CursorTy pvrtmp_6259 = tmp_struct_7.field0;
            CursorTy pvrtmp_6260 = tmp_struct_7.field1;
            CursorTy pvrtmp_6261 = tmp_struct_7.field2;
            CursorTy pvrtmp_6262 = tmp_struct_7.field3;
            
            *(TagTyPacked *) loc_2917 = 1;
            
            CursorTy writetag_4537 = loc_2917 + 1;
            
            *(IntTy *) writetag_4537 = fltPkd_1506_1529;
            
            CursorTy writecur_4538 = writetag_4537 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6259, pvrtmp_6260,
                                                   loc_2917, pvrtmp_6262};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6271 = *(CursorTy *) tmpcur_6252;
            CursorTy tmpaftercur_6272 = tmpcur_6252 + 8;
            CursorTy jump_4263 = tmpcur_6252 + 8;
            CursorCursorCursorCursorProd tmp_struct_8 =
                                          addValTag(end_r_2918, end_r_2919, loc_2917, tmpcur_6271, inVal_22_908_1526);
            CursorTy pvrtmp_6273 = tmp_struct_8.field0;
            CursorTy pvrtmp_6274 = tmp_struct_8.field1;
            CursorTy pvrtmp_6275 = tmp_struct_8.field2;
            CursorTy pvrtmp_6276 = tmp_struct_8.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6273, jump_4263,
                                                   pvrtmp_6275, pvrtmp_6276};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6283 = *(CursorTy *) tmpcur_6252;
            CursorTy tmpaftercur_6284 = tmpcur_6252 + 8;
            CursorCursorCursorCursorProd tmp_struct_9 =
                                          addValTag(end_r_2918, end_r_2919, loc_2917, tmpcur_6283, inVal_22_908_1526);
            CursorTy pvrtmp_6285 = tmp_struct_9.field0;
            CursorTy pvrtmp_6286 = tmp_struct_9.field1;
            CursorTy pvrtmp_6287 = tmp_struct_9.field2;
            CursorTy pvrtmp_6288 = tmp_struct_9.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6285, pvrtmp_6286,
                                                   pvrtmp_6287, pvrtmp_6288};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6251");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkCATList(CursorTy end_r_2921, CursorTy loc_2920,
                                 IntTy len_25_911_1531,
                                 IntTy tagLen_26_912_1532,
                                 IntTy strLen_27_913_1533)
{
    if (loc_2920 + 32 > end_r_2921) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2921);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2921 = chunk_end_18;
        *(TagTyPacked *) loc_2920 = 255;
        
        CursorTy redir = loc_2920 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2920 = chunk_start_17;
    }
    
    CursorTy loc_3050 = loc_2920 + 1;
    CursorTy loc_3051 = loc_3050 + 8;
    CursorTy loc_3052 = loc_3051 + 8;
    BoolTy fltIf_1508_1534 = len_25_911_1531 <= 0;
    
    if (fltIf_1508_1534) {
        *(TagTyPacked *) loc_2920 = 0;
        
        CursorTy writetag_4547 = loc_2920 + 1;
        
        return (CursorCursorCursorProd) {end_r_2921, loc_2920, writetag_4547};
    } else {
        CursorCursorCursorProd tmp_struct_13 =
                                mkContentText(end_r_2921, loc_3052, strLen_27_913_1533);
        CursorTy pvrtmp_6300 = tmp_struct_13.field0;
        CursorTy pvrtmp_6301 = tmp_struct_13.field1;
        CursorTy pvrtmp_6302 = tmp_struct_13.field2;
        IntTy fltAppE_1509_1536 = len_25_911_1531 - 1;
        CursorCursorCursorProd tmp_struct_14 =
                                mkCATList(pvrtmp_6300, pvrtmp_6302, fltAppE_1509_1536, tagLen_26_912_1532, strLen_27_913_1533);
        CursorTy pvrtmp_6307 = tmp_struct_14.field0;
        CursorTy pvrtmp_6308 = tmp_struct_14.field1;
        CursorTy pvrtmp_6309 = tmp_struct_14.field2;
        CursorCursorCursorProd tmp_struct_15 =
                                mkRandomTags(pvrtmp_6307, pvrtmp_6309, tagLen_26_912_1532);
        CursorTy pvrtmp_6314 = tmp_struct_15.field0;
        CursorTy pvrtmp_6315 = tmp_struct_15.field1;
        CursorTy pvrtmp_6316 = tmp_struct_15.field2;
        
        *(TagTyPacked *) loc_2920 = 23;
        
        CursorTy writetag_4552 = loc_2920 + 1;
        
        *(CursorTy *) writetag_4552 = pvrtmp_6302;
        
        CursorTy writecur_4553 = writetag_4552 + 8;
        
        *(CursorTy *) writecur_4553 = pvrtmp_6309;
        
        CursorTy writecur_4554 = writecur_4553 + 8;
        
        return (CursorCursorCursorProd) {pvrtmp_6314, loc_2920, pvrtmp_6316};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2923, CursorTy loc_2922,
                                IntTy len_180_1066_1539)
{
    if (loc_2922 + 32 > end_r_2923) {
        ChunkTy new_chunk_20 = alloc_chunk(end_r_2923);
        CursorTy chunk_start_21 = new_chunk_20.chunk_start;
        CursorTy chunk_end_22 = new_chunk_20.chunk_end;
        
        end_r_2923 = chunk_end_22;
        *(TagTyPacked *) loc_2922 = 255;
        
        CursorTy redir = loc_2922 + 1;
        
        *(CursorTy *) redir = chunk_start_21;
        loc_2922 = chunk_start_21;
    }
    
    CursorTy loc_3064 = loc_2922 + 1;
    CursorTy loc_3065 = loc_3064 + 8;
    BoolTy fltIf_1510_1540 = len_180_1066_1539 <= 0;
    
    if (fltIf_1510_1540) {
        *(TagTyPacked *) loc_2922 = 0;
        
        CursorTy writetag_4559 = loc_2922 + 1;
        
        return (CursorCursorCursorProd) {end_r_2923, loc_2922, writetag_4559};
    } else {
        IntTy fltPrm_1511_1541 = rand();
        IntTy randomChar_181_1067_1542 = fltPrm_1511_1541 % 128;
        IntTy fltAppE_1512_1543 = len_180_1066_1539 - 1;
        CursorCursorCursorProd tmp_struct_19 =
                                mkString(end_r_2923, loc_3065, fltAppE_1512_1543);
        CursorTy pvrtmp_6329 = tmp_struct_19.field0;
        CursorTy pvrtmp_6330 = tmp_struct_19.field1;
        CursorTy pvrtmp_6331 = tmp_struct_19.field2;
        
        *(TagTyPacked *) loc_2922 = 1;
        
        CursorTy writetag_4562 = loc_2922 + 1;
        
        *(IntTy *) writetag_4562 = randomChar_181_1067_1542;
        
        CursorTy writecur_4563 = writetag_4562 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6329, loc_2922, pvrtmp_6331};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2925, CursorTy loc_2924,
                                     IntTy n_194_1080_1545)
{
    if (loc_2924 + 32 > end_r_2925) {
        ChunkTy new_chunk_24 = alloc_chunk(end_r_2925);
        CursorTy chunk_start_25 = new_chunk_24.chunk_start;
        CursorTy chunk_end_26 = new_chunk_24.chunk_end;
        
        end_r_2925 = chunk_end_26;
        *(TagTyPacked *) loc_2924 = 255;
        
        CursorTy redir = loc_2924 + 1;
        
        *(CursorTy *) redir = chunk_start_25;
        loc_2924 = chunk_start_25;
    }
    
    CursorTy loc_3070 = loc_2924 + 1;
    CursorCursorCursorProd tmp_struct_23 =
                            mkString(end_r_2925, loc_3070, n_194_1080_1545);
    CursorTy pvrtmp_6340 = tmp_struct_23.field0;
    CursorTy pvrtmp_6341 = tmp_struct_23.field1;
    CursorTy pvrtmp_6342 = tmp_struct_23.field2;
    
    *(TagTyPacked *) loc_2924 = 1;
    
    CursorTy writetag_4567 = loc_2924 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_6340, loc_2924, pvrtmp_6342};
}
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2927, CursorTy loc_2926,
                                    IntTy len_319_1205_1547)
{
    if (loc_2926 + 32 > end_r_2927) {
        ChunkTy new_chunk_28 = alloc_chunk(end_r_2927);
        CursorTy chunk_start_29 = new_chunk_28.chunk_start;
        CursorTy chunk_end_30 = new_chunk_28.chunk_end;
        
        end_r_2927 = chunk_end_30;
        *(TagTyPacked *) loc_2926 = 255;
        
        CursorTy redir = loc_2926 + 1;
        
        *(CursorTy *) redir = chunk_start_29;
        loc_2926 = chunk_start_29;
    }
    
    CursorTy loc_3074 = loc_2926 + 1;
    CursorTy loc_3075 = loc_3074 + 8;
    BoolTy fltIf_1514_1548 = len_319_1205_1547 <= 0;
    
    if (fltIf_1514_1548) {
        *(TagTyPacked *) loc_2926 = 0;
        
        CursorTy writetag_4570 = loc_2926 + 1;
        
        return (CursorCursorCursorProd) {end_r_2927, loc_2926, writetag_4570};
    } else {
        IntTy fltAppE_1515_1550 = len_319_1205_1547 - 1;
        CursorCursorCursorProd tmp_struct_27 =
                                mkRandomTags(end_r_2927, loc_3075, fltAppE_1515_1550);
        CursorTy pvrtmp_6355 = tmp_struct_27.field0;
        CursorTy pvrtmp_6356 = tmp_struct_27.field1;
        CursorTy pvrtmp_6357 = tmp_struct_27.field2;
        
        *(TagTyPacked *) loc_2926 = 1;
        
        CursorTy writetag_4573 = loc_2926 + 1;
        
        *(IntTy *) writetag_4573 = 100;
        
        CursorTy writecur_4574 = writetag_4573 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6355, loc_2926, pvrtmp_6357};
    }
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2930,
                                          CursorTy end_r_2931,
                                          CursorTy loc_2929,
                                          CursorTy arg_623_1229_1552)
{
    if (loc_2929 + 32 > end_r_2931) {
        ChunkTy new_chunk_34 = alloc_chunk(end_r_2931);
        CursorTy chunk_start_35 = new_chunk_34.chunk_start;
        CursorTy chunk_end_36 = new_chunk_34.chunk_end;
        
        end_r_2931 = chunk_end_36;
        *(TagTyPacked *) loc_2929 = 255;
        
        CursorTy redir = loc_2929 + 1;
        
        *(CursorTy *) redir = chunk_start_35;
        loc_2929 = chunk_start_35;
    }
    
    CursorTy loc_3085 = loc_2929 + 1;
    CursorTy loc_3086 = loc_3085 + 8;
    TagTyPacked tmpval_6366 = *(TagTyPacked *) arg_623_1229_1552;
    CursorTy tmpcur_6367 = arg_623_1229_1552 + 1;
    
    
  switch_6410:
    ;
    switch (tmpval_6366) {
        
      case 0:
        {
            CursorTy jump_3964 = arg_623_1229_1552 + 1;
            
            *(TagTyPacked *) loc_2929 = 0;
            
            CursorTy writetag_4578 = loc_2929 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2931, jump_3964,
                                                   loc_2929, writetag_4578};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6372 = *(IntTy *) tmpcur_6367;
            CursorTy tmpcur_6373 = tmpcur_6367 + sizeof(IntTy);
            CursorTy jump_3966 = tmpcur_6367 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_String(end_r_2930, end_r_2931, loc_3086, tmpcur_6373);
            CursorTy pvrtmp_6374 = tmp_struct_31.field0;
            CursorTy pvrtmp_6375 = tmp_struct_31.field1;
            CursorTy pvrtmp_6376 = tmp_struct_31.field2;
            CursorTy pvrtmp_6377 = tmp_struct_31.field3;
            
            *(TagTyPacked *) loc_2929 = 1;
            
            CursorTy writetag_4583 = loc_2929 + 1;
            
            *(IntTy *) writetag_4583 = tmpval_6372;
            
            CursorTy writecur_4584 = writetag_4583 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6374, pvrtmp_6375,
                                                   loc_2929, pvrtmp_6377};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6386 = *(CursorTy *) tmpcur_6367;
            CursorTy tmpaftercur_6387 = tmpcur_6367 + 8;
            CursorTy jump_4269 = tmpcur_6367 + 8;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_String(end_r_2930, end_r_2931, loc_2929, tmpcur_6386);
            CursorTy pvrtmp_6388 = tmp_struct_32.field0;
            CursorTy pvrtmp_6389 = tmp_struct_32.field1;
            CursorTy pvrtmp_6390 = tmp_struct_32.field2;
            CursorTy pvrtmp_6391 = tmp_struct_32.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6388, jump_4269,
                                                   pvrtmp_6390, pvrtmp_6391};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6398 = *(CursorTy *) tmpcur_6367;
            CursorTy tmpaftercur_6399 = tmpcur_6367 + 8;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_String(end_r_2930, end_r_2931, loc_2929, tmpcur_6398);
            CursorTy pvrtmp_6400 = tmp_struct_33.field0;
            CursorTy pvrtmp_6401 = tmp_struct_33.field1;
            CursorTy pvrtmp_6402 = tmp_struct_33.field2;
            CursorTy pvrtmp_6403 = tmp_struct_33.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6400, pvrtmp_6401,
                                                   pvrtmp_6402, pvrtmp_6403};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6366");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2934,
                                                       CursorTy end_r_2935,
                                                       CursorTy loc_2933,
                                                       CursorTy arg_628_1234_1557)
{
    CursorTy loc_3098 = loc_2933 + 1;
    CursorTy loc_3099 = loc_3098 + 8;
    TagTyPacked tmpval_6411 = *(TagTyPacked *) arg_628_1234_1557;
    CursorTy tmpcur_6412 = arg_628_1234_1557 + 1;
    
    
  switch_6455:
    ;
    switch (tmpval_6411) {
        
      case 0:
        {
            CursorTy jump_3969 = arg_628_1234_1557 + 1;
            
            *(TagTyPacked *) loc_2933 = 0;
            
            CursorTy writetag_4594 = loc_2933 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2935, jump_3969,
                                                   loc_2933, writetag_4594};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6417 = *(IntTy *) tmpcur_6412;
            CursorTy tmpcur_6418 = tmpcur_6412 + sizeof(IntTy);
            CursorTy jump_3971 = tmpcur_6412 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_String(end_r_2934, end_r_2935, loc_3099, tmpcur_6418);
            CursorTy pvrtmp_6419 = tmp_struct_37.field0;
            CursorTy pvrtmp_6420 = tmp_struct_37.field1;
            CursorTy pvrtmp_6421 = tmp_struct_37.field2;
            CursorTy pvrtmp_6422 = tmp_struct_37.field3;
            
            *(TagTyPacked *) loc_2933 = 1;
            
            CursorTy writetag_4599 = loc_2933 + 1;
            
            *(IntTy *) writetag_4599 = tmpval_6417;
            
            CursorTy writecur_4600 = writetag_4599 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6419, pvrtmp_6420,
                                                   loc_2933, pvrtmp_6422};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6431 = *(CursorTy *) tmpcur_6412;
            CursorTy tmpaftercur_6432 = tmpcur_6412 + 8;
            CursorTy jump_4275 = tmpcur_6412 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_String(end_r_2934, end_r_2935, loc_2933, tmpcur_6431);
            CursorTy pvrtmp_6433 = tmp_struct_38.field0;
            CursorTy pvrtmp_6434 = tmp_struct_38.field1;
            CursorTy pvrtmp_6435 = tmp_struct_38.field2;
            CursorTy pvrtmp_6436 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6433, jump_4275,
                                                   pvrtmp_6435, pvrtmp_6436};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6443 = *(CursorTy *) tmpcur_6412;
            CursorTy tmpaftercur_6444 = tmpcur_6412 + 8;
            CursorCursorCursorCursorProd tmp_struct_39 =
                                          _copy_without_ptrs_String(end_r_2934, end_r_2935, loc_2933, tmpcur_6443);
            CursorTy pvrtmp_6445 = tmp_struct_39.field0;
            CursorTy pvrtmp_6446 = tmp_struct_39.field1;
            CursorTy pvrtmp_6447 = tmp_struct_39.field2;
            CursorTy pvrtmp_6448 = tmp_struct_39.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6445, pvrtmp_6446,
                                                   pvrtmp_6447, pvrtmp_6448};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6411");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2937, CursorTy arg_633_1239_1562)
{
    TagTyPacked tmpval_6456 = *(TagTyPacked *) arg_633_1239_1562;
    CursorTy tmpcur_6457 = arg_633_1239_1562 + 1;
    
    
  switch_6467:
    ;
    switch (tmpval_6456) {
        
      case 0:
        {
            CursorTy jump_3974 = arg_633_1239_1562 + 1;
            
            return (CursorProd) {jump_3974};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6458 = *(IntTy *) tmpcur_6457;
            CursorTy tmpcur_6459 = tmpcur_6457 + sizeof(IntTy);
            CursorTy jump_3976 = tmpcur_6457 + 8;
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2937, tmpcur_6459);
            CursorTy pvrtmp_6460 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_6460};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6461 = *(CursorTy *) tmpcur_6457;
            CursorTy tmpaftercur_6462 = tmpcur_6457 + 8;
            CursorTy jump_4281 = tmpcur_6457 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_String(end_r_2937, tmpcur_6461);
            CursorTy pvrtmp_6463 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_4281};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6464 = *(CursorTy *) tmpcur_6457;
            CursorTy tmpaftercur_6465 = tmpcur_6457 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_String(end_r_2937, tmpcur_6464);
            CursorTy pvrtmp_6466 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_6466};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6456");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2939, CursorTy arg_638_1243_1566)
{
    TagTyPacked tmpval_6468 = *(TagTyPacked *) arg_638_1243_1566;
    CursorTy tmpcur_6469 = arg_638_1243_1566 + 1;
    
    
  switch_6479:
    ;
    switch (tmpval_6468) {
        
      case 0:
        {
            CursorTy jump_3979 = arg_638_1243_1566 + 1;
            unsigned char wildcard_639_1244_1567 = print_symbol(6153);
            unsigned char wildcard_640_1245_1568 = print_symbol(6145);
            
            return (CursorProd) {jump_3979};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6470 = *(IntTy *) tmpcur_6469;
            CursorTy tmpcur_6471 = tmpcur_6469 + sizeof(IntTy);
            CursorTy jump_3981 = tmpcur_6469 + 8;
            unsigned char wildcard_645_1248_1571 = print_symbol(6154);
            unsigned char y_643_1249_1572 = printf("%lld", tmpval_6470);
            CursorProd tmp_struct_43 =  _print_String(end_r_2939, tmpcur_6471);
            CursorTy pvrtmp_6472 = tmp_struct_43.field0;
            unsigned char wildcard_646_1251_1574 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_6472};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6473 = *(CursorTy *) tmpcur_6469;
            CursorTy tmpaftercur_6474 = tmpcur_6469 + 8;
            CursorTy jump_4287 = tmpcur_6469 + 8;
            unsigned char wildcard_4290 = print_symbol(6162);
            CursorProd tmp_struct_44 =  _print_String(end_r_2939, tmpcur_6473);
            CursorTy pvrtmp_6475 = tmp_struct_44.field0;
            
            return (CursorProd) {jump_4287};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6476 = *(CursorTy *) tmpcur_6469;
            CursorTy tmpaftercur_6477 = tmpcur_6469 + 8;
            unsigned char wildcard_4290 = print_symbol(6161);
            CursorProd tmp_struct_45 =  _print_String(end_r_2939, tmpcur_6476);
            CursorTy pvrtmp_6478 = tmp_struct_45.field0;
            
            return (CursorProd) {pvrtmp_6478};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6468");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2942,
                                           CursorTy end_r_2943,
                                           CursorTy loc_2941,
                                           CursorTy arg_647_1252_1575)
{
    if (loc_2941 + 32 > end_r_2943) {
        ChunkTy new_chunk_50 = alloc_chunk(end_r_2943);
        CursorTy chunk_start_51 = new_chunk_50.chunk_start;
        CursorTy chunk_end_52 = new_chunk_50.chunk_end;
        
        end_r_2943 = chunk_end_52;
        *(TagTyPacked *) loc_2941 = 255;
        
        CursorTy redir = loc_2941 + 1;
        
        *(CursorTy *) redir = chunk_start_51;
        loc_2941 = chunk_start_51;
    }
    
    TagTyPacked tmpval_6480 = *(TagTyPacked *) arg_647_1252_1575;
    CursorTy tmpcur_6481 = arg_647_1252_1575 + 1;
    
    
  switch_6530:
    ;
    switch (tmpval_6480) {
        
      case 0:
        {
            CursorTy loc_3121 = loc_2941 + 1;
            CursorCursorCursorCursorProd tmp_struct_46 =
                                          _copy_String(end_r_2942, end_r_2943, loc_3121, tmpcur_6481);
            CursorTy pvrtmp_6482 = tmp_struct_46.field0;
            CursorTy pvrtmp_6483 = tmp_struct_46.field1;
            CursorTy pvrtmp_6484 = tmp_struct_46.field2;
            CursorTy pvrtmp_6485 = tmp_struct_46.field3;
            
            *(TagTyPacked *) loc_2941 = 0;
            
            CursorTy writetag_4631 = loc_2941 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6482, pvrtmp_6483,
                                                   loc_2941, pvrtmp_6485};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3127 = loc_2941 + 1;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_String(end_r_2942, end_r_2943, loc_3127, tmpcur_6481);
            CursorTy pvrtmp_6494 = tmp_struct_47.field0;
            CursorTy pvrtmp_6495 = tmp_struct_47.field1;
            CursorTy pvrtmp_6496 = tmp_struct_47.field2;
            CursorTy pvrtmp_6497 = tmp_struct_47.field3;
            
            *(TagTyPacked *) loc_2941 = 1;
            
            CursorTy writetag_4636 = loc_2941 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6494, pvrtmp_6495,
                                                   loc_2941, pvrtmp_6497};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6506 = *(CursorTy *) tmpcur_6481;
            CursorTy tmpaftercur_6507 = tmpcur_6481 + 8;
            CursorTy jump_4293 = tmpcur_6481 + 8;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Content(end_r_2942, end_r_2943, loc_2941, tmpcur_6506);
            CursorTy pvrtmp_6508 = tmp_struct_48.field0;
            CursorTy pvrtmp_6509 = tmp_struct_48.field1;
            CursorTy pvrtmp_6510 = tmp_struct_48.field2;
            CursorTy pvrtmp_6511 = tmp_struct_48.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6508, jump_4293,
                                                   pvrtmp_6510, pvrtmp_6511};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6518 = *(CursorTy *) tmpcur_6481;
            CursorTy tmpaftercur_6519 = tmpcur_6481 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Content(end_r_2942, end_r_2943, loc_2941, tmpcur_6518);
            CursorTy pvrtmp_6520 = tmp_struct_49.field0;
            CursorTy pvrtmp_6521 = tmp_struct_49.field1;
            CursorTy pvrtmp_6522 = tmp_struct_49.field2;
            CursorTy pvrtmp_6523 = tmp_struct_49.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6520, pvrtmp_6521,
                                                   pvrtmp_6522, pvrtmp_6523};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6480");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2946,
                                                        CursorTy end_r_2947,
                                                        CursorTy loc_2945,
                                                        CursorTy arg_652_1257_1580)
{
    TagTyPacked tmpval_6531 = *(TagTyPacked *) arg_652_1257_1580;
    CursorTy tmpcur_6532 = arg_652_1257_1580 + 1;
    
    
  switch_6581:
    ;
    switch (tmpval_6531) {
        
      case 0:
        {
            CursorTy loc_3135 = loc_2945 + 1;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_without_ptrs_String(end_r_2946, end_r_2947, loc_3135, tmpcur_6532);
            CursorTy pvrtmp_6533 = tmp_struct_53.field0;
            CursorTy pvrtmp_6534 = tmp_struct_53.field1;
            CursorTy pvrtmp_6535 = tmp_struct_53.field2;
            CursorTy pvrtmp_6536 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2945 = 0;
            
            CursorTy writetag_4647 = loc_2945 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6533, pvrtmp_6534,
                                                   loc_2945, pvrtmp_6536};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3141 = loc_2945 + 1;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_without_ptrs_String(end_r_2946, end_r_2947, loc_3141, tmpcur_6532);
            CursorTy pvrtmp_6545 = tmp_struct_54.field0;
            CursorTy pvrtmp_6546 = tmp_struct_54.field1;
            CursorTy pvrtmp_6547 = tmp_struct_54.field2;
            CursorTy pvrtmp_6548 = tmp_struct_54.field3;
            
            *(TagTyPacked *) loc_2945 = 1;
            
            CursorTy writetag_4652 = loc_2945 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6545, pvrtmp_6546,
                                                   loc_2945, pvrtmp_6548};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6557 = *(CursorTy *) tmpcur_6532;
            CursorTy tmpaftercur_6558 = tmpcur_6532 + 8;
            CursorTy jump_4299 = tmpcur_6532 + 8;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_without_ptrs_Content(end_r_2946, end_r_2947, loc_2945, tmpcur_6557);
            CursorTy pvrtmp_6559 = tmp_struct_55.field0;
            CursorTy pvrtmp_6560 = tmp_struct_55.field1;
            CursorTy pvrtmp_6561 = tmp_struct_55.field2;
            CursorTy pvrtmp_6562 = tmp_struct_55.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6559, jump_4299,
                                                   pvrtmp_6561, pvrtmp_6562};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6569 = *(CursorTy *) tmpcur_6532;
            CursorTy tmpaftercur_6570 = tmpcur_6532 + 8;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_without_ptrs_Content(end_r_2946, end_r_2947, loc_2945, tmpcur_6569);
            CursorTy pvrtmp_6571 = tmp_struct_56.field0;
            CursorTy pvrtmp_6572 = tmp_struct_56.field1;
            CursorTy pvrtmp_6573 = tmp_struct_56.field2;
            CursorTy pvrtmp_6574 = tmp_struct_56.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6571, pvrtmp_6572,
                                                   pvrtmp_6573, pvrtmp_6574};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6531");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2949, CursorTy arg_657_1262_1585)
{
    TagTyPacked tmpval_6582 = *(TagTyPacked *) arg_657_1262_1585;
    CursorTy tmpcur_6583 = arg_657_1262_1585 + 1;
    
    
  switch_6592:
    ;
    switch (tmpval_6582) {
        
      case 0:
        {
            CursorProd tmp_struct_57 =
                        _traverse_String(end_r_2949, tmpcur_6583);
            CursorTy pvrtmp_6584 = tmp_struct_57.field0;
            
            return (CursorProd) {pvrtmp_6584};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_58 =
                        _traverse_String(end_r_2949, tmpcur_6583);
            CursorTy pvrtmp_6585 = tmp_struct_58.field0;
            
            return (CursorProd) {pvrtmp_6585};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6586 = *(CursorTy *) tmpcur_6583;
            CursorTy tmpaftercur_6587 = tmpcur_6583 + 8;
            CursorTy jump_4305 = tmpcur_6583 + 8;
            CursorProd tmp_struct_59 =
                        _traverse_Content(end_r_2949, tmpcur_6586);
            CursorTy pvrtmp_6588 = tmp_struct_59.field0;
            
            return (CursorProd) {jump_4305};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6589 = *(CursorTy *) tmpcur_6583;
            CursorTy tmpaftercur_6590 = tmpcur_6583 + 8;
            CursorProd tmp_struct_60 =
                        _traverse_Content(end_r_2949, tmpcur_6589);
            CursorTy pvrtmp_6591 = tmp_struct_60.field0;
            
            return (CursorProd) {pvrtmp_6591};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6582");
            exit(1);
        }
    }
}
CursorProd _print_Content(CursorTy end_r_2951, CursorTy arg_662_1267_1590)
{
    TagTyPacked tmpval_6593 = *(TagTyPacked *) arg_662_1267_1590;
    CursorTy tmpcur_6594 = arg_662_1267_1590 + 1;
    
    
  switch_6603:
    ;
    switch (tmpval_6593) {
        
      case 0:
        {
            unsigned char wildcard_665_1269_1592 = print_symbol(6152);
            CursorProd tmp_struct_61 =  _print_String(end_r_2951, tmpcur_6594);
            CursorTy pvrtmp_6595 = tmp_struct_61.field0;
            unsigned char wildcard_666_1271_1594 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_6595};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_669_1273_1596 = print_symbol(6146);
            CursorProd tmp_struct_62 =  _print_String(end_r_2951, tmpcur_6594);
            CursorTy pvrtmp_6596 = tmp_struct_62.field0;
            unsigned char wildcard_670_1275_1598 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_6596};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6597 = *(CursorTy *) tmpcur_6594;
            CursorTy tmpaftercur_6598 = tmpcur_6594 + 8;
            CursorTy jump_4311 = tmpcur_6594 + 8;
            unsigned char wildcard_4314 = print_symbol(6162);
            CursorProd tmp_struct_63 =  _print_Content(end_r_2951, tmpcur_6597);
            CursorTy pvrtmp_6599 = tmp_struct_63.field0;
            
            return (CursorProd) {jump_4311};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6600 = *(CursorTy *) tmpcur_6594;
            CursorTy tmpaftercur_6601 = tmpcur_6594 + 8;
            unsigned char wildcard_4314 = print_symbol(6161);
            CursorProd tmp_struct_64 =  _print_Content(end_r_2951, tmpcur_6600);
            CursorTy pvrtmp_6602 = tmp_struct_64.field0;
            
            return (CursorProd) {pvrtmp_6602};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6593");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2954, CursorTy end_r_2955,
                                       CursorTy loc_2953,
                                       CursorTy arg_671_1276_1599)
{
    if (loc_2953 + 32 > end_r_2955) {
        ChunkTy new_chunk_89 = alloc_chunk(end_r_2955);
        CursorTy chunk_start_90 = new_chunk_89.chunk_start;
        CursorTy chunk_end_91 = new_chunk_89.chunk_end;
        
        end_r_2955 = chunk_end_91;
        *(TagTyPacked *) loc_2953 = 255;
        
        CursorTy redir = loc_2953 + 1;
        
        *(CursorTy *) redir = chunk_start_90;
        loc_2953 = chunk_start_90;
    }
    
    CursorTy loc_3171 = loc_2953 + 1;
    CursorTy loc_3172 = loc_3171 + 8;
    CursorTy loc_3187 = loc_2953 + 1;
    CursorTy loc_3188 = loc_3187 + 8;
    CursorTy loc_3208 = loc_2953 + 1;
    CursorTy loc_3209 = loc_3208 + 8;
    CursorTy loc_3210 = loc_3209 + 8;
    CursorTy loc_3234 = loc_2953 + 1;
    CursorTy loc_3235 = loc_3234 + 8;
    CursorTy loc_3236 = loc_3235 + 8;
    CursorTy loc_3260 = loc_2953 + 1;
    CursorTy loc_3261 = loc_3260 + 8;
    CursorTy loc_3262 = loc_3261 + 8;
    CursorTy loc_3286 = loc_2953 + 1;
    CursorTy loc_3287 = loc_3286 + 8;
    CursorTy loc_3288 = loc_3287 + 8;
    CursorTy loc_3312 = loc_2953 + 1;
    CursorTy loc_3313 = loc_3312 + 8;
    CursorTy loc_3314 = loc_3313 + 8;
    CursorTy loc_3338 = loc_2953 + 1;
    CursorTy loc_3339 = loc_3338 + 8;
    CursorTy loc_3340 = loc_3339 + 8;
    TagTyPacked tmpval_6604 = *(TagTyPacked *) arg_671_1276_1599;
    CursorTy tmpcur_6605 = arg_671_1276_1599 + 1;
    
    
  switch_6870:
    ;
    switch (tmpval_6604) {
        
      case 0:
        {
            CursorTy jump_4000 = arg_671_1276_1599 + 1;
            
            *(TagTyPacked *) loc_2953 = 0;
            
            CursorTy writetag_4682 = loc_2953 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2955, jump_4000,
                                                   loc_2953, writetag_4682};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6610 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6611 = tmpcur_6605 + 8;
            CursorTy jump_4002 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Content(end_r_2954, end_r_2955, loc_3172, tmpaftercur_6611);
            CursorTy pvrtmp_6612 = tmp_struct_65.field0;
            CursorTy pvrtmp_6613 = tmp_struct_65.field1;
            CursorTy pvrtmp_6614 = tmp_struct_65.field2;
            CursorTy pvrtmp_6615 = tmp_struct_65.field3;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Adt(end_r_2954, pvrtmp_6612, pvrtmp_6615, tmpcur_6610);
            CursorTy pvrtmp_6620 = tmp_struct_66.field0;
            CursorTy pvrtmp_6621 = tmp_struct_66.field1;
            CursorTy pvrtmp_6622 = tmp_struct_66.field2;
            CursorTy pvrtmp_6623 = tmp_struct_66.field3;
            
            *(TagTyPacked *) loc_2953 = 9;
            
            CursorTy writetag_4688 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4688 = pvrtmp_6615;
            
            CursorTy writecur_4689 = writetag_4688 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6620, pvrtmp_6621,
                                                   loc_2953, pvrtmp_6623};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6632 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6633 = tmpcur_6605 + 8;
            CursorTy jump_4006 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2954, end_r_2955, loc_3188, tmpaftercur_6633);
            CursorTy pvrtmp_6634 = tmp_struct_67.field0;
            CursorTy pvrtmp_6635 = tmp_struct_67.field1;
            CursorTy pvrtmp_6636 = tmp_struct_67.field2;
            CursorTy pvrtmp_6637 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Content(end_r_2954, pvrtmp_6634, pvrtmp_6637, tmpcur_6632);
            CursorTy pvrtmp_6642 = tmp_struct_68.field0;
            CursorTy pvrtmp_6643 = tmp_struct_68.field1;
            CursorTy pvrtmp_6644 = tmp_struct_68.field2;
            CursorTy pvrtmp_6645 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2953 = 11;
            
            CursorTy writetag_4697 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4697 = pvrtmp_6637;
            
            CursorTy writecur_4698 = writetag_4697 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6642, pvrtmp_6643,
                                                   loc_2953, pvrtmp_6645};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6654 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6655 = tmpcur_6605 + 8;
            CursorTy tmpcur_6656 = *(CursorTy *) tmpaftercur_6655;
            CursorTy tmpaftercur_6657 = tmpaftercur_6655 + 8;
            CursorTy jump_4011 = tmpaftercur_6655 + 8;
            CursorTy jump_4010 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Tags(end_r_2954, end_r_2955, loc_3210, tmpaftercur_6657);
            CursorTy pvrtmp_6658 = tmp_struct_69.field0;
            CursorTy pvrtmp_6659 = tmp_struct_69.field1;
            CursorTy pvrtmp_6660 = tmp_struct_69.field2;
            CursorTy pvrtmp_6661 = tmp_struct_69.field3;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Content(end_r_2954, pvrtmp_6658, pvrtmp_6661, tmpcur_6654);
            CursorTy pvrtmp_6666 = tmp_struct_70.field0;
            CursorTy pvrtmp_6667 = tmp_struct_70.field1;
            CursorTy pvrtmp_6668 = tmp_struct_70.field2;
            CursorTy pvrtmp_6669 = tmp_struct_70.field3;
            CursorCursorCursorCursorProd tmp_struct_71 =
                                          _copy_Adt(end_r_2954, pvrtmp_6666, pvrtmp_6669, tmpcur_6656);
            CursorTy pvrtmp_6674 = tmp_struct_71.field0;
            CursorTy pvrtmp_6675 = tmp_struct_71.field1;
            CursorTy pvrtmp_6676 = tmp_struct_71.field2;
            CursorTy pvrtmp_6677 = tmp_struct_71.field3;
            
            *(TagTyPacked *) loc_2953 = 13;
            
            CursorTy writetag_4708 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4708 = pvrtmp_6661;
            
            CursorTy writecur_4709 = writetag_4708 + 8;
            
            *(CursorTy *) writecur_4709 = pvrtmp_6669;
            
            CursorTy writecur_4710 = writecur_4709 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6674, pvrtmp_6675,
                                                   loc_2953, pvrtmp_6677};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6686 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6687 = tmpcur_6605 + 8;
            CursorTy tmpcur_6688 = *(CursorTy *) tmpaftercur_6687;
            CursorTy tmpaftercur_6689 = tmpaftercur_6687 + 8;
            CursorTy jump_4017 = tmpaftercur_6687 + 8;
            CursorTy jump_4016 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_72 =
                                          _copy_Adt(end_r_2954, end_r_2955, loc_3236, tmpaftercur_6689);
            CursorTy pvrtmp_6690 = tmp_struct_72.field0;
            CursorTy pvrtmp_6691 = tmp_struct_72.field1;
            CursorTy pvrtmp_6692 = tmp_struct_72.field2;
            CursorTy pvrtmp_6693 = tmp_struct_72.field3;
            CursorCursorCursorCursorProd tmp_struct_73 =
                                          _copy_Content(end_r_2954, pvrtmp_6690, pvrtmp_6693, tmpcur_6686);
            CursorTy pvrtmp_6698 = tmp_struct_73.field0;
            CursorTy pvrtmp_6699 = tmp_struct_73.field1;
            CursorTy pvrtmp_6700 = tmp_struct_73.field2;
            CursorTy pvrtmp_6701 = tmp_struct_73.field3;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_Tags(end_r_2954, pvrtmp_6698, pvrtmp_6701, tmpcur_6688);
            CursorTy pvrtmp_6706 = tmp_struct_74.field0;
            CursorTy pvrtmp_6707 = tmp_struct_74.field1;
            CursorTy pvrtmp_6708 = tmp_struct_74.field2;
            CursorTy pvrtmp_6709 = tmp_struct_74.field3;
            
            *(TagTyPacked *) loc_2953 = 15;
            
            CursorTy writetag_4721 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4721 = pvrtmp_6693;
            
            CursorTy writecur_4722 = writetag_4721 + 8;
            
            *(CursorTy *) writecur_4722 = pvrtmp_6701;
            
            CursorTy writecur_4723 = writecur_4722 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6706, pvrtmp_6707,
                                                   loc_2953, pvrtmp_6709};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6718 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6719 = tmpcur_6605 + 8;
            CursorTy tmpcur_6720 = *(CursorTy *) tmpaftercur_6719;
            CursorTy tmpaftercur_6721 = tmpaftercur_6719 + 8;
            CursorTy jump_4023 = tmpaftercur_6719 + 8;
            CursorTy jump_4022 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_Tags(end_r_2954, end_r_2955, loc_3262, tmpaftercur_6721);
            CursorTy pvrtmp_6722 = tmp_struct_75.field0;
            CursorTy pvrtmp_6723 = tmp_struct_75.field1;
            CursorTy pvrtmp_6724 = tmp_struct_75.field2;
            CursorTy pvrtmp_6725 = tmp_struct_75.field3;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_Adt(end_r_2954, pvrtmp_6722, pvrtmp_6725, tmpcur_6718);
            CursorTy pvrtmp_6730 = tmp_struct_76.field0;
            CursorTy pvrtmp_6731 = tmp_struct_76.field1;
            CursorTy pvrtmp_6732 = tmp_struct_76.field2;
            CursorTy pvrtmp_6733 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_Content(end_r_2954, pvrtmp_6730, pvrtmp_6733, tmpcur_6720);
            CursorTy pvrtmp_6738 = tmp_struct_77.field0;
            CursorTy pvrtmp_6739 = tmp_struct_77.field1;
            CursorTy pvrtmp_6740 = tmp_struct_77.field2;
            CursorTy pvrtmp_6741 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2953 = 17;
            
            CursorTy writetag_4734 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4734 = pvrtmp_6725;
            
            CursorTy writecur_4735 = writetag_4734 + 8;
            
            *(CursorTy *) writecur_4735 = pvrtmp_6733;
            
            CursorTy writecur_4736 = writecur_4735 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6738, pvrtmp_6739,
                                                   loc_2953, pvrtmp_6741};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6750 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6751 = tmpcur_6605 + 8;
            CursorTy tmpcur_6752 = *(CursorTy *) tmpaftercur_6751;
            CursorTy tmpaftercur_6753 = tmpaftercur_6751 + 8;
            CursorTy jump_4029 = tmpaftercur_6751 + 8;
            CursorTy jump_4028 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_Adt(end_r_2954, end_r_2955, loc_3288, tmpaftercur_6753);
            CursorTy pvrtmp_6754 = tmp_struct_78.field0;
            CursorTy pvrtmp_6755 = tmp_struct_78.field1;
            CursorTy pvrtmp_6756 = tmp_struct_78.field2;
            CursorTy pvrtmp_6757 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_Tags(end_r_2954, pvrtmp_6754, pvrtmp_6757, tmpcur_6750);
            CursorTy pvrtmp_6762 = tmp_struct_79.field0;
            CursorTy pvrtmp_6763 = tmp_struct_79.field1;
            CursorTy pvrtmp_6764 = tmp_struct_79.field2;
            CursorTy pvrtmp_6765 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_Content(end_r_2954, pvrtmp_6762, pvrtmp_6765, tmpcur_6752);
            CursorTy pvrtmp_6770 = tmp_struct_80.field0;
            CursorTy pvrtmp_6771 = tmp_struct_80.field1;
            CursorTy pvrtmp_6772 = tmp_struct_80.field2;
            CursorTy pvrtmp_6773 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2953 = 19;
            
            CursorTy writetag_4747 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4747 = pvrtmp_6757;
            
            CursorTy writecur_4748 = writetag_4747 + 8;
            
            *(CursorTy *) writecur_4748 = pvrtmp_6765;
            
            CursorTy writecur_4749 = writecur_4748 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6770, pvrtmp_6771,
                                                   loc_2953, pvrtmp_6773};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6782 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6783 = tmpcur_6605 + 8;
            CursorTy tmpcur_6784 = *(CursorTy *) tmpaftercur_6783;
            CursorTy tmpaftercur_6785 = tmpaftercur_6783 + 8;
            CursorTy jump_4035 = tmpaftercur_6783 + 8;
            CursorTy jump_4034 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_Content(end_r_2954, end_r_2955, loc_3314, tmpaftercur_6785);
            CursorTy pvrtmp_6786 = tmp_struct_81.field0;
            CursorTy pvrtmp_6787 = tmp_struct_81.field1;
            CursorTy pvrtmp_6788 = tmp_struct_81.field2;
            CursorTy pvrtmp_6789 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_Tags(end_r_2954, pvrtmp_6786, pvrtmp_6789, tmpcur_6782);
            CursorTy pvrtmp_6794 = tmp_struct_82.field0;
            CursorTy pvrtmp_6795 = tmp_struct_82.field1;
            CursorTy pvrtmp_6796 = tmp_struct_82.field2;
            CursorTy pvrtmp_6797 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_Adt(end_r_2954, pvrtmp_6794, pvrtmp_6797, tmpcur_6784);
            CursorTy pvrtmp_6802 = tmp_struct_83.field0;
            CursorTy pvrtmp_6803 = tmp_struct_83.field1;
            CursorTy pvrtmp_6804 = tmp_struct_83.field2;
            CursorTy pvrtmp_6805 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2953 = 21;
            
            CursorTy writetag_4760 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4760 = pvrtmp_6789;
            
            CursorTy writecur_4761 = writetag_4760 + 8;
            
            *(CursorTy *) writecur_4761 = pvrtmp_6797;
            
            CursorTy writecur_4762 = writecur_4761 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6802, pvrtmp_6803,
                                                   loc_2953, pvrtmp_6805};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6814 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6815 = tmpcur_6605 + 8;
            CursorTy tmpcur_6816 = *(CursorTy *) tmpaftercur_6815;
            CursorTy tmpaftercur_6817 = tmpaftercur_6815 + 8;
            CursorTy jump_4041 = tmpaftercur_6815 + 8;
            CursorTy jump_4040 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_Content(end_r_2954, end_r_2955, loc_3340, tmpaftercur_6817);
            CursorTy pvrtmp_6818 = tmp_struct_84.field0;
            CursorTy pvrtmp_6819 = tmp_struct_84.field1;
            CursorTy pvrtmp_6820 = tmp_struct_84.field2;
            CursorTy pvrtmp_6821 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_Adt(end_r_2954, pvrtmp_6818, pvrtmp_6821, tmpcur_6814);
            CursorTy pvrtmp_6826 = tmp_struct_85.field0;
            CursorTy pvrtmp_6827 = tmp_struct_85.field1;
            CursorTy pvrtmp_6828 = tmp_struct_85.field2;
            CursorTy pvrtmp_6829 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_Tags(end_r_2954, pvrtmp_6826, pvrtmp_6829, tmpcur_6816);
            CursorTy pvrtmp_6834 = tmp_struct_86.field0;
            CursorTy pvrtmp_6835 = tmp_struct_86.field1;
            CursorTy pvrtmp_6836 = tmp_struct_86.field2;
            CursorTy pvrtmp_6837 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2953 = 23;
            
            CursorTy writetag_4773 = loc_2953 + 1;
            
            *(CursorTy *) writetag_4773 = pvrtmp_6821;
            
            CursorTy writecur_4774 = writetag_4773 + 8;
            
            *(CursorTy *) writecur_4774 = pvrtmp_6829;
            
            CursorTy writecur_4775 = writecur_4774 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6834, pvrtmp_6835,
                                                   loc_2953, pvrtmp_6837};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6846 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6847 = tmpcur_6605 + 8;
            CursorTy jump_4317 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_Adt(end_r_2954, end_r_2955, loc_2953, tmpcur_6846);
            CursorTy pvrtmp_6848 = tmp_struct_87.field0;
            CursorTy pvrtmp_6849 = tmp_struct_87.field1;
            CursorTy pvrtmp_6850 = tmp_struct_87.field2;
            CursorTy pvrtmp_6851 = tmp_struct_87.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6848, jump_4317,
                                                   pvrtmp_6850, pvrtmp_6851};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6858 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6859 = tmpcur_6605 + 8;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_Adt(end_r_2954, end_r_2955, loc_2953, tmpcur_6858);
            CursorTy pvrtmp_6860 = tmp_struct_88.field0;
            CursorTy pvrtmp_6861 = tmp_struct_88.field1;
            CursorTy pvrtmp_6862 = tmp_struct_88.field2;
            CursorTy pvrtmp_6863 = tmp_struct_88.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6860, pvrtmp_6861,
                                                   pvrtmp_6862, pvrtmp_6863};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6604");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2958,
                                                    CursorTy end_r_2959,
                                                    CursorTy loc_2957,
                                                    CursorTy arg_716_1321_1644)
{
    TagTyPacked tmpval_6871 = *(TagTyPacked *) arg_716_1321_1644;
    CursorTy tmpcur_6872 = arg_716_1321_1644 + 1;
    
    
  switch_7137:
    ;
    switch (tmpval_6871) {
        
      case 0:
        {
            CursorTy jump_4046 = arg_716_1321_1644 + 1;
            
            *(TagTyPacked *) loc_2957 = 0;
            
            CursorTy writetag_4787 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2959, jump_4046,
                                                   loc_2957, writetag_4787};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6877 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_6878 = tmpcur_6872 + 8;
            CursorTy jump_4048 = tmpcur_6872 + 8;
            CursorTy loc_3362 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Content(end_r_2958, end_r_2959, loc_3362, tmpaftercur_6878);
            CursorTy pvrtmp_6879 = tmp_struct_92.field0;
            CursorTy pvrtmp_6880 = tmp_struct_92.field1;
            CursorTy pvrtmp_6881 = tmp_struct_92.field2;
            CursorTy pvrtmp_6882 = tmp_struct_92.field3;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Adt(end_r_2958, pvrtmp_6879, pvrtmp_6882, tmpcur_6877);
            CursorTy pvrtmp_6887 = tmp_struct_93.field0;
            CursorTy pvrtmp_6888 = tmp_struct_93.field1;
            CursorTy pvrtmp_6889 = tmp_struct_93.field2;
            CursorTy pvrtmp_6890 = tmp_struct_93.field3;
            
            *(TagTyPacked *) loc_2957 = 1;
            
            CursorTy writetag_4793 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6887, pvrtmp_6888,
                                                   loc_2957, pvrtmp_6890};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6899 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_6900 = tmpcur_6872 + 8;
            CursorTy jump_4052 = tmpcur_6872 + 8;
            CursorTy loc_3375 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2958, end_r_2959, loc_3375, tmpaftercur_6900);
            CursorTy pvrtmp_6901 = tmp_struct_94.field0;
            CursorTy pvrtmp_6902 = tmp_struct_94.field1;
            CursorTy pvrtmp_6903 = tmp_struct_94.field2;
            CursorTy pvrtmp_6904 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Content(end_r_2958, pvrtmp_6901, pvrtmp_6904, tmpcur_6899);
            CursorTy pvrtmp_6909 = tmp_struct_95.field0;
            CursorTy pvrtmp_6910 = tmp_struct_95.field1;
            CursorTy pvrtmp_6911 = tmp_struct_95.field2;
            CursorTy pvrtmp_6912 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2957 = 2;
            
            CursorTy writetag_4801 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6909, pvrtmp_6910,
                                                   loc_2957, pvrtmp_6912};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6921 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_6922 = tmpcur_6872 + 8;
            CursorTy tmpcur_6923 = *(CursorTy *) tmpaftercur_6922;
            CursorTy tmpaftercur_6924 = tmpaftercur_6922 + 8;
            CursorTy jump_4057 = tmpaftercur_6922 + 8;
            CursorTy jump_4056 = tmpcur_6872 + 8;
            CursorTy loc_3393 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Tags(end_r_2958, end_r_2959, loc_3393, tmpaftercur_6924);
            CursorTy pvrtmp_6925 = tmp_struct_96.field0;
            CursorTy pvrtmp_6926 = tmp_struct_96.field1;
            CursorTy pvrtmp_6927 = tmp_struct_96.field2;
            CursorTy pvrtmp_6928 = tmp_struct_96.field3;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Content(end_r_2958, pvrtmp_6925, pvrtmp_6928, tmpcur_6921);
            CursorTy pvrtmp_6933 = tmp_struct_97.field0;
            CursorTy pvrtmp_6934 = tmp_struct_97.field1;
            CursorTy pvrtmp_6935 = tmp_struct_97.field2;
            CursorTy pvrtmp_6936 = tmp_struct_97.field3;
            CursorCursorCursorCursorProd tmp_struct_98 =
                                          _copy_without_ptrs_Adt(end_r_2958, pvrtmp_6933, pvrtmp_6936, tmpcur_6923);
            CursorTy pvrtmp_6941 = tmp_struct_98.field0;
            CursorTy pvrtmp_6942 = tmp_struct_98.field1;
            CursorTy pvrtmp_6943 = tmp_struct_98.field2;
            CursorTy pvrtmp_6944 = tmp_struct_98.field3;
            
            *(TagTyPacked *) loc_2957 = 3;
            
            CursorTy writetag_4811 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6941, pvrtmp_6942,
                                                   loc_2957, pvrtmp_6944};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6953 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_6954 = tmpcur_6872 + 8;
            CursorTy tmpcur_6955 = *(CursorTy *) tmpaftercur_6954;
            CursorTy tmpaftercur_6956 = tmpaftercur_6954 + 8;
            CursorTy jump_4063 = tmpaftercur_6954 + 8;
            CursorTy jump_4062 = tmpcur_6872 + 8;
            CursorTy loc_3413 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_99 =
                                          _copy_without_ptrs_Adt(end_r_2958, end_r_2959, loc_3413, tmpaftercur_6956);
            CursorTy pvrtmp_6957 = tmp_struct_99.field0;
            CursorTy pvrtmp_6958 = tmp_struct_99.field1;
            CursorTy pvrtmp_6959 = tmp_struct_99.field2;
            CursorTy pvrtmp_6960 = tmp_struct_99.field3;
            CursorCursorCursorCursorProd tmp_struct_100 =
                                          _copy_without_ptrs_Content(end_r_2958, pvrtmp_6957, pvrtmp_6960, tmpcur_6953);
            CursorTy pvrtmp_6965 = tmp_struct_100.field0;
            CursorTy pvrtmp_6966 = tmp_struct_100.field1;
            CursorTy pvrtmp_6967 = tmp_struct_100.field2;
            CursorTy pvrtmp_6968 = tmp_struct_100.field3;
            CursorCursorCursorCursorProd tmp_struct_101 =
                                          _copy_without_ptrs_Tags(end_r_2958, pvrtmp_6965, pvrtmp_6968, tmpcur_6955);
            CursorTy pvrtmp_6973 = tmp_struct_101.field0;
            CursorTy pvrtmp_6974 = tmp_struct_101.field1;
            CursorTy pvrtmp_6975 = tmp_struct_101.field2;
            CursorTy pvrtmp_6976 = tmp_struct_101.field3;
            
            *(TagTyPacked *) loc_2957 = 4;
            
            CursorTy writetag_4822 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6973, pvrtmp_6974,
                                                   loc_2957, pvrtmp_6976};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6985 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_6986 = tmpcur_6872 + 8;
            CursorTy tmpcur_6987 = *(CursorTy *) tmpaftercur_6986;
            CursorTy tmpaftercur_6988 = tmpaftercur_6986 + 8;
            CursorTy jump_4069 = tmpaftercur_6986 + 8;
            CursorTy jump_4068 = tmpcur_6872 + 8;
            CursorTy loc_3433 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_102 =
                                          _copy_without_ptrs_Tags(end_r_2958, end_r_2959, loc_3433, tmpaftercur_6988);
            CursorTy pvrtmp_6989 = tmp_struct_102.field0;
            CursorTy pvrtmp_6990 = tmp_struct_102.field1;
            CursorTy pvrtmp_6991 = tmp_struct_102.field2;
            CursorTy pvrtmp_6992 = tmp_struct_102.field3;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          _copy_without_ptrs_Adt(end_r_2958, pvrtmp_6989, pvrtmp_6992, tmpcur_6985);
            CursorTy pvrtmp_6997 = tmp_struct_103.field0;
            CursorTy pvrtmp_6998 = tmp_struct_103.field1;
            CursorTy pvrtmp_6999 = tmp_struct_103.field2;
            CursorTy pvrtmp_7000 = tmp_struct_103.field3;
            CursorCursorCursorCursorProd tmp_struct_104 =
                                          _copy_without_ptrs_Content(end_r_2958, pvrtmp_6997, pvrtmp_7000, tmpcur_6987);
            CursorTy pvrtmp_7005 = tmp_struct_104.field0;
            CursorTy pvrtmp_7006 = tmp_struct_104.field1;
            CursorTy pvrtmp_7007 = tmp_struct_104.field2;
            CursorTy pvrtmp_7008 = tmp_struct_104.field3;
            
            *(TagTyPacked *) loc_2957 = 5;
            
            CursorTy writetag_4833 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7005, pvrtmp_7006,
                                                   loc_2957, pvrtmp_7008};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7017 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_7018 = tmpcur_6872 + 8;
            CursorTy tmpcur_7019 = *(CursorTy *) tmpaftercur_7018;
            CursorTy tmpaftercur_7020 = tmpaftercur_7018 + 8;
            CursorTy jump_4075 = tmpaftercur_7018 + 8;
            CursorTy jump_4074 = tmpcur_6872 + 8;
            CursorTy loc_3453 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_105 =
                                          _copy_without_ptrs_Adt(end_r_2958, end_r_2959, loc_3453, tmpaftercur_7020);
            CursorTy pvrtmp_7021 = tmp_struct_105.field0;
            CursorTy pvrtmp_7022 = tmp_struct_105.field1;
            CursorTy pvrtmp_7023 = tmp_struct_105.field2;
            CursorTy pvrtmp_7024 = tmp_struct_105.field3;
            CursorCursorCursorCursorProd tmp_struct_106 =
                                          _copy_without_ptrs_Tags(end_r_2958, pvrtmp_7021, pvrtmp_7024, tmpcur_7017);
            CursorTy pvrtmp_7029 = tmp_struct_106.field0;
            CursorTy pvrtmp_7030 = tmp_struct_106.field1;
            CursorTy pvrtmp_7031 = tmp_struct_106.field2;
            CursorTy pvrtmp_7032 = tmp_struct_106.field3;
            CursorCursorCursorCursorProd tmp_struct_107 =
                                          _copy_without_ptrs_Content(end_r_2958, pvrtmp_7029, pvrtmp_7032, tmpcur_7019);
            CursorTy pvrtmp_7037 = tmp_struct_107.field0;
            CursorTy pvrtmp_7038 = tmp_struct_107.field1;
            CursorTy pvrtmp_7039 = tmp_struct_107.field2;
            CursorTy pvrtmp_7040 = tmp_struct_107.field3;
            
            *(TagTyPacked *) loc_2957 = 6;
            
            CursorTy writetag_4844 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7037, pvrtmp_7038,
                                                   loc_2957, pvrtmp_7040};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7049 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_7050 = tmpcur_6872 + 8;
            CursorTy tmpcur_7051 = *(CursorTy *) tmpaftercur_7050;
            CursorTy tmpaftercur_7052 = tmpaftercur_7050 + 8;
            CursorTy jump_4081 = tmpaftercur_7050 + 8;
            CursorTy jump_4080 = tmpcur_6872 + 8;
            CursorTy loc_3473 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_108 =
                                          _copy_without_ptrs_Content(end_r_2958, end_r_2959, loc_3473, tmpaftercur_7052);
            CursorTy pvrtmp_7053 = tmp_struct_108.field0;
            CursorTy pvrtmp_7054 = tmp_struct_108.field1;
            CursorTy pvrtmp_7055 = tmp_struct_108.field2;
            CursorTy pvrtmp_7056 = tmp_struct_108.field3;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          _copy_without_ptrs_Tags(end_r_2958, pvrtmp_7053, pvrtmp_7056, tmpcur_7049);
            CursorTy pvrtmp_7061 = tmp_struct_109.field0;
            CursorTy pvrtmp_7062 = tmp_struct_109.field1;
            CursorTy pvrtmp_7063 = tmp_struct_109.field2;
            CursorTy pvrtmp_7064 = tmp_struct_109.field3;
            CursorCursorCursorCursorProd tmp_struct_110 =
                                          _copy_without_ptrs_Adt(end_r_2958, pvrtmp_7061, pvrtmp_7064, tmpcur_7051);
            CursorTy pvrtmp_7069 = tmp_struct_110.field0;
            CursorTy pvrtmp_7070 = tmp_struct_110.field1;
            CursorTy pvrtmp_7071 = tmp_struct_110.field2;
            CursorTy pvrtmp_7072 = tmp_struct_110.field3;
            
            *(TagTyPacked *) loc_2957 = 7;
            
            CursorTy writetag_4855 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7069, pvrtmp_7070,
                                                   loc_2957, pvrtmp_7072};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7081 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_7082 = tmpcur_6872 + 8;
            CursorTy tmpcur_7083 = *(CursorTy *) tmpaftercur_7082;
            CursorTy tmpaftercur_7084 = tmpaftercur_7082 + 8;
            CursorTy jump_4087 = tmpaftercur_7082 + 8;
            CursorTy jump_4086 = tmpcur_6872 + 8;
            CursorTy loc_3493 = loc_2957 + 1;
            CursorCursorCursorCursorProd tmp_struct_111 =
                                          _copy_without_ptrs_Content(end_r_2958, end_r_2959, loc_3493, tmpaftercur_7084);
            CursorTy pvrtmp_7085 = tmp_struct_111.field0;
            CursorTy pvrtmp_7086 = tmp_struct_111.field1;
            CursorTy pvrtmp_7087 = tmp_struct_111.field2;
            CursorTy pvrtmp_7088 = tmp_struct_111.field3;
            CursorCursorCursorCursorProd tmp_struct_112 =
                                          _copy_without_ptrs_Adt(end_r_2958, pvrtmp_7085, pvrtmp_7088, tmpcur_7081);
            CursorTy pvrtmp_7093 = tmp_struct_112.field0;
            CursorTy pvrtmp_7094 = tmp_struct_112.field1;
            CursorTy pvrtmp_7095 = tmp_struct_112.field2;
            CursorTy pvrtmp_7096 = tmp_struct_112.field3;
            CursorCursorCursorCursorProd tmp_struct_113 =
                                          _copy_without_ptrs_Tags(end_r_2958, pvrtmp_7093, pvrtmp_7096, tmpcur_7083);
            CursorTy pvrtmp_7101 = tmp_struct_113.field0;
            CursorTy pvrtmp_7102 = tmp_struct_113.field1;
            CursorTy pvrtmp_7103 = tmp_struct_113.field2;
            CursorTy pvrtmp_7104 = tmp_struct_113.field3;
            
            *(TagTyPacked *) loc_2957 = 8;
            
            CursorTy writetag_4866 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7101, pvrtmp_7102,
                                                   loc_2957, pvrtmp_7104};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7113 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_7114 = tmpcur_6872 + 8;
            CursorTy jump_4323 = tmpcur_6872 + 8;
            CursorCursorCursorCursorProd tmp_struct_114 =
                                          _copy_without_ptrs_Adt(end_r_2958, end_r_2959, loc_2957, tmpcur_7113);
            CursorTy pvrtmp_7115 = tmp_struct_114.field0;
            CursorTy pvrtmp_7116 = tmp_struct_114.field1;
            CursorTy pvrtmp_7117 = tmp_struct_114.field2;
            CursorTy pvrtmp_7118 = tmp_struct_114.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7115, jump_4323,
                                                   pvrtmp_7117, pvrtmp_7118};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7125 = *(CursorTy *) tmpcur_6872;
            CursorTy tmpaftercur_7126 = tmpcur_6872 + 8;
            CursorCursorCursorCursorProd tmp_struct_115 =
                                          _copy_without_ptrs_Adt(end_r_2958, end_r_2959, loc_2957, tmpcur_7125);
            CursorTy pvrtmp_7127 = tmp_struct_115.field0;
            CursorTy pvrtmp_7128 = tmp_struct_115.field1;
            CursorTy pvrtmp_7129 = tmp_struct_115.field2;
            CursorTy pvrtmp_7130 = tmp_struct_115.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7127, pvrtmp_7128,
                                                   pvrtmp_7129, pvrtmp_7130};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6871");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2961, CursorTy arg_761_1366_1689)
{
    TagTyPacked tmpval_7138 = *(TagTyPacked *) arg_761_1366_1689;
    CursorTy tmpcur_7139 = arg_761_1366_1689 + 1;
    
    
  switch_7196:
    ;
    switch (tmpval_7138) {
        
      case 0:
        {
            CursorTy jump_4092 = arg_761_1366_1689 + 1;
            
            return (CursorProd) {jump_4092};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7140 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7141 = tmpcur_7139 + 8;
            CursorTy jump_4094 = tmpcur_7139 + 8;
            CursorProd tmp_struct_116 =
                        _traverse_Content(end_r_2961, tmpaftercur_7141);
            CursorTy pvrtmp_7142 = tmp_struct_116.field0;
            CursorProd tmp_struct_117 =  _traverse_Adt(end_r_2961, tmpcur_7140);
            CursorTy pvrtmp_7143 = tmp_struct_117.field0;
            
            return (CursorProd) {pvrtmp_7143};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7144 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7145 = tmpcur_7139 + 8;
            CursorTy jump_4098 = tmpcur_7139 + 8;
            CursorProd tmp_struct_118 =
                        _traverse_Adt(end_r_2961, tmpaftercur_7145);
            CursorTy pvrtmp_7146 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Content(end_r_2961, tmpcur_7144);
            CursorTy pvrtmp_7147 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_7147};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7148 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7149 = tmpcur_7139 + 8;
            CursorTy tmpcur_7150 = *(CursorTy *) tmpaftercur_7149;
            CursorTy tmpaftercur_7151 = tmpaftercur_7149 + 8;
            CursorTy jump_4103 = tmpaftercur_7149 + 8;
            CursorTy jump_4102 = tmpcur_7139 + 8;
            CursorProd tmp_struct_120 =
                        _traverse_Tags(end_r_2961, tmpaftercur_7151);
            CursorTy pvrtmp_7152 = tmp_struct_120.field0;
            CursorProd tmp_struct_121 =
                        _traverse_Content(end_r_2961, tmpcur_7148);
            CursorTy pvrtmp_7153 = tmp_struct_121.field0;
            CursorProd tmp_struct_122 =  _traverse_Adt(end_r_2961, tmpcur_7150);
            CursorTy pvrtmp_7154 = tmp_struct_122.field0;
            
            return (CursorProd) {pvrtmp_7154};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7155 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7156 = tmpcur_7139 + 8;
            CursorTy tmpcur_7157 = *(CursorTy *) tmpaftercur_7156;
            CursorTy tmpaftercur_7158 = tmpaftercur_7156 + 8;
            CursorTy jump_4109 = tmpaftercur_7156 + 8;
            CursorTy jump_4108 = tmpcur_7139 + 8;
            CursorProd tmp_struct_123 =
                        _traverse_Adt(end_r_2961, tmpaftercur_7158);
            CursorTy pvrtmp_7159 = tmp_struct_123.field0;
            CursorProd tmp_struct_124 =
                        _traverse_Content(end_r_2961, tmpcur_7155);
            CursorTy pvrtmp_7160 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _traverse_Tags(end_r_2961, tmpcur_7157);
            CursorTy pvrtmp_7161 = tmp_struct_125.field0;
            
            return (CursorProd) {pvrtmp_7161};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7162 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7163 = tmpcur_7139 + 8;
            CursorTy tmpcur_7164 = *(CursorTy *) tmpaftercur_7163;
            CursorTy tmpaftercur_7165 = tmpaftercur_7163 + 8;
            CursorTy jump_4115 = tmpaftercur_7163 + 8;
            CursorTy jump_4114 = tmpcur_7139 + 8;
            CursorProd tmp_struct_126 =
                        _traverse_Tags(end_r_2961, tmpaftercur_7165);
            CursorTy pvrtmp_7166 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =  _traverse_Adt(end_r_2961, tmpcur_7162);
            CursorTy pvrtmp_7167 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =
                        _traverse_Content(end_r_2961, tmpcur_7164);
            CursorTy pvrtmp_7168 = tmp_struct_128.field0;
            
            return (CursorProd) {pvrtmp_7168};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7169 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7170 = tmpcur_7139 + 8;
            CursorTy tmpcur_7171 = *(CursorTy *) tmpaftercur_7170;
            CursorTy tmpaftercur_7172 = tmpaftercur_7170 + 8;
            CursorTy jump_4121 = tmpaftercur_7170 + 8;
            CursorTy jump_4120 = tmpcur_7139 + 8;
            CursorProd tmp_struct_129 =
                        _traverse_Adt(end_r_2961, tmpaftercur_7172);
            CursorTy pvrtmp_7173 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _traverse_Tags(end_r_2961, tmpcur_7169);
            CursorTy pvrtmp_7174 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =
                        _traverse_Content(end_r_2961, tmpcur_7171);
            CursorTy pvrtmp_7175 = tmp_struct_131.field0;
            
            return (CursorProd) {pvrtmp_7175};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7176 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7177 = tmpcur_7139 + 8;
            CursorTy tmpcur_7178 = *(CursorTy *) tmpaftercur_7177;
            CursorTy tmpaftercur_7179 = tmpaftercur_7177 + 8;
            CursorTy jump_4127 = tmpaftercur_7177 + 8;
            CursorTy jump_4126 = tmpcur_7139 + 8;
            CursorProd tmp_struct_132 =
                        _traverse_Content(end_r_2961, tmpaftercur_7179);
            CursorTy pvrtmp_7180 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =
                        _traverse_Tags(end_r_2961, tmpcur_7176);
            CursorTy pvrtmp_7181 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =  _traverse_Adt(end_r_2961, tmpcur_7178);
            CursorTy pvrtmp_7182 = tmp_struct_134.field0;
            
            return (CursorProd) {pvrtmp_7182};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7183 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7184 = tmpcur_7139 + 8;
            CursorTy tmpcur_7185 = *(CursorTy *) tmpaftercur_7184;
            CursorTy tmpaftercur_7186 = tmpaftercur_7184 + 8;
            CursorTy jump_4133 = tmpaftercur_7184 + 8;
            CursorTy jump_4132 = tmpcur_7139 + 8;
            CursorProd tmp_struct_135 =
                        _traverse_Content(end_r_2961, tmpaftercur_7186);
            CursorTy pvrtmp_7187 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _traverse_Adt(end_r_2961, tmpcur_7183);
            CursorTy pvrtmp_7188 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _traverse_Tags(end_r_2961, tmpcur_7185);
            CursorTy pvrtmp_7189 = tmp_struct_137.field0;
            
            return (CursorProd) {pvrtmp_7189};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7190 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7191 = tmpcur_7139 + 8;
            CursorTy jump_4329 = tmpcur_7139 + 8;
            CursorProd tmp_struct_138 =  _traverse_Adt(end_r_2961, tmpcur_7190);
            CursorTy pvrtmp_7192 = tmp_struct_138.field0;
            
            return (CursorProd) {jump_4329};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7193 = *(CursorTy *) tmpcur_7139;
            CursorTy tmpaftercur_7194 = tmpcur_7139 + 8;
            CursorProd tmp_struct_139 =  _traverse_Adt(end_r_2961, tmpcur_7193);
            CursorTy pvrtmp_7195 = tmp_struct_139.field0;
            
            return (CursorProd) {pvrtmp_7195};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7138");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2963, CursorTy arg_806_1411_1734)
{
    TagTyPacked tmpval_7197 = *(TagTyPacked *) arg_806_1411_1734;
    CursorTy tmpcur_7198 = arg_806_1411_1734 + 1;
    
    
  switch_7255:
    ;
    switch (tmpval_7197) {
        
      case 0:
        {
            CursorTy jump_4138 = arg_806_1411_1734 + 1;
            unsigned char wildcard_807_1412_1735 = print_symbol(6151);
            unsigned char wildcard_808_1413_1736 = print_symbol(6145);
            
            return (CursorProd) {jump_4138};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7199 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7200 = tmpcur_7198 + 8;
            CursorTy jump_4140 = tmpcur_7198 + 8;
            unsigned char wildcard_813_1416_1739 = print_symbol(6157);
            CursorProd tmp_struct_140 =
                        _print_Content(end_r_2963, tmpaftercur_7200);
            CursorTy pvrtmp_7201 = tmp_struct_140.field0;
            CursorProd tmp_struct_141 =  _print_Adt(end_r_2963, tmpcur_7199);
            CursorTy pvrtmp_7202 = tmp_struct_141.field0;
            unsigned char wildcard_814_1419_1742 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7202};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7203 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7204 = tmpcur_7198 + 8;
            CursorTy jump_4144 = tmpcur_7198 + 8;
            unsigned char wildcard_819_1422_1745 = print_symbol(6160);
            CursorProd tmp_struct_142 =
                        _print_Adt(end_r_2963, tmpaftercur_7204);
            CursorTy pvrtmp_7205 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =
                        _print_Content(end_r_2963, tmpcur_7203);
            CursorTy pvrtmp_7206 = tmp_struct_143.field0;
            unsigned char wildcard_820_1425_1748 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7206};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7207 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7208 = tmpcur_7198 + 8;
            CursorTy tmpcur_7209 = *(CursorTy *) tmpaftercur_7208;
            CursorTy tmpaftercur_7210 = tmpaftercur_7208 + 8;
            CursorTy jump_4149 = tmpaftercur_7208 + 8;
            CursorTy jump_4148 = tmpcur_7198 + 8;
            unsigned char wildcard_827_1429_1752 = print_symbol(6148);
            CursorProd tmp_struct_144 =
                        _print_Tags(end_r_2963, tmpaftercur_7210);
            CursorTy pvrtmp_7211 = tmp_struct_144.field0;
            CursorProd tmp_struct_145 =
                        _print_Content(end_r_2963, tmpcur_7207);
            CursorTy pvrtmp_7212 = tmp_struct_145.field0;
            CursorProd tmp_struct_146 =  _print_Adt(end_r_2963, tmpcur_7209);
            CursorTy pvrtmp_7213 = tmp_struct_146.field0;
            unsigned char wildcard_828_1433_1756 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7213};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7214 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7215 = tmpcur_7198 + 8;
            CursorTy tmpcur_7216 = *(CursorTy *) tmpaftercur_7215;
            CursorTy tmpaftercur_7217 = tmpaftercur_7215 + 8;
            CursorTy jump_4155 = tmpaftercur_7215 + 8;
            CursorTy jump_4154 = tmpcur_7198 + 8;
            unsigned char wildcard_835_1437_1760 = print_symbol(6159);
            CursorProd tmp_struct_147 =
                        _print_Adt(end_r_2963, tmpaftercur_7217);
            CursorTy pvrtmp_7218 = tmp_struct_147.field0;
            CursorProd tmp_struct_148 =
                        _print_Content(end_r_2963, tmpcur_7214);
            CursorTy pvrtmp_7219 = tmp_struct_148.field0;
            CursorProd tmp_struct_149 =  _print_Tags(end_r_2963, tmpcur_7216);
            CursorTy pvrtmp_7220 = tmp_struct_149.field0;
            unsigned char wildcard_836_1441_1764 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7220};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7221 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7222 = tmpcur_7198 + 8;
            CursorTy tmpcur_7223 = *(CursorTy *) tmpaftercur_7222;
            CursorTy tmpaftercur_7224 = tmpaftercur_7222 + 8;
            CursorTy jump_4161 = tmpaftercur_7222 + 8;
            CursorTy jump_4160 = tmpcur_7198 + 8;
            unsigned char wildcard_843_1445_1768 = print_symbol(6149);
            CursorProd tmp_struct_150 =
                        _print_Tags(end_r_2963, tmpaftercur_7224);
            CursorTy pvrtmp_7225 = tmp_struct_150.field0;
            CursorProd tmp_struct_151 =  _print_Adt(end_r_2963, tmpcur_7221);
            CursorTy pvrtmp_7226 = tmp_struct_151.field0;
            CursorProd tmp_struct_152 =
                        _print_Content(end_r_2963, tmpcur_7223);
            CursorTy pvrtmp_7227 = tmp_struct_152.field0;
            unsigned char wildcard_844_1449_1772 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7227};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7228 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7229 = tmpcur_7198 + 8;
            CursorTy tmpcur_7230 = *(CursorTy *) tmpaftercur_7229;
            CursorTy tmpaftercur_7231 = tmpaftercur_7229 + 8;
            CursorTy jump_4167 = tmpaftercur_7229 + 8;
            CursorTy jump_4166 = tmpcur_7198 + 8;
            unsigned char wildcard_851_1453_1776 = print_symbol(6158);
            CursorProd tmp_struct_153 =
                        _print_Adt(end_r_2963, tmpaftercur_7231);
            CursorTy pvrtmp_7232 = tmp_struct_153.field0;
            CursorProd tmp_struct_154 =  _print_Tags(end_r_2963, tmpcur_7228);
            CursorTy pvrtmp_7233 = tmp_struct_154.field0;
            CursorProd tmp_struct_155 =
                        _print_Content(end_r_2963, tmpcur_7230);
            CursorTy pvrtmp_7234 = tmp_struct_155.field0;
            unsigned char wildcard_852_1457_1780 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7234};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7235 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7236 = tmpcur_7198 + 8;
            CursorTy tmpcur_7237 = *(CursorTy *) tmpaftercur_7236;
            CursorTy tmpaftercur_7238 = tmpaftercur_7236 + 8;
            CursorTy jump_4173 = tmpaftercur_7236 + 8;
            CursorTy jump_4172 = tmpcur_7198 + 8;
            unsigned char wildcard_859_1461_1784 = print_symbol(6155);
            CursorProd tmp_struct_156 =
                        _print_Content(end_r_2963, tmpaftercur_7238);
            CursorTy pvrtmp_7239 = tmp_struct_156.field0;
            CursorProd tmp_struct_157 =  _print_Tags(end_r_2963, tmpcur_7235);
            CursorTy pvrtmp_7240 = tmp_struct_157.field0;
            CursorProd tmp_struct_158 =  _print_Adt(end_r_2963, tmpcur_7237);
            CursorTy pvrtmp_7241 = tmp_struct_158.field0;
            unsigned char wildcard_860_1465_1788 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7241};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7242 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7243 = tmpcur_7198 + 8;
            CursorTy tmpcur_7244 = *(CursorTy *) tmpaftercur_7243;
            CursorTy tmpaftercur_7245 = tmpaftercur_7243 + 8;
            CursorTy jump_4179 = tmpaftercur_7243 + 8;
            CursorTy jump_4178 = tmpcur_7198 + 8;
            unsigned char wildcard_867_1469_1792 = print_symbol(6156);
            CursorProd tmp_struct_159 =
                        _print_Content(end_r_2963, tmpaftercur_7245);
            CursorTy pvrtmp_7246 = tmp_struct_159.field0;
            CursorProd tmp_struct_160 =  _print_Adt(end_r_2963, tmpcur_7242);
            CursorTy pvrtmp_7247 = tmp_struct_160.field0;
            CursorProd tmp_struct_161 =  _print_Tags(end_r_2963, tmpcur_7244);
            CursorTy pvrtmp_7248 = tmp_struct_161.field0;
            unsigned char wildcard_868_1473_1796 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7248};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7249 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7250 = tmpcur_7198 + 8;
            CursorTy jump_4335 = tmpcur_7198 + 8;
            unsigned char wildcard_4338 = print_symbol(6162);
            CursorProd tmp_struct_162 =  _print_Adt(end_r_2963, tmpcur_7249);
            CursorTy pvrtmp_7251 = tmp_struct_162.field0;
            
            return (CursorProd) {jump_4335};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7252 = *(CursorTy *) tmpcur_7198;
            CursorTy tmpaftercur_7253 = tmpcur_7198 + 8;
            unsigned char wildcard_4338 = print_symbol(6161);
            CursorProd tmp_struct_163 =  _print_Adt(end_r_2963, tmpcur_7252);
            CursorTy pvrtmp_7254 = tmp_struct_163.field0;
            
            return (CursorProd) {pvrtmp_7254};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7197");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2966,
                                        CursorTy end_r_2967, CursorTy loc_2965,
                                        CursorTy arg_869_1474_1797)
{
    if (loc_2965 + 32 > end_r_2967) {
        ChunkTy new_chunk_167 = alloc_chunk(end_r_2967);
        CursorTy chunk_start_168 = new_chunk_167.chunk_start;
        CursorTy chunk_end_169 = new_chunk_167.chunk_end;
        
        end_r_2967 = chunk_end_169;
        *(TagTyPacked *) loc_2965 = 255;
        
        CursorTy redir = loc_2965 + 1;
        
        *(CursorTy *) redir = chunk_start_168;
        loc_2965 = chunk_start_168;
    }
    
    CursorTy loc_3671 = loc_2965 + 1;
    CursorTy loc_3672 = loc_3671 + 8;
    TagTyPacked tmpval_7256 = *(TagTyPacked *) arg_869_1474_1797;
    CursorTy tmpcur_7257 = arg_869_1474_1797 + 1;
    
    
  switch_7300:
    ;
    switch (tmpval_7256) {
        
      case 0:
        {
            CursorTy jump_4184 = arg_869_1474_1797 + 1;
            
            *(TagTyPacked *) loc_2965 = 0;
            
            CursorTy writetag_4980 = loc_2965 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2967, jump_4184,
                                                   loc_2965, writetag_4980};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7262 = *(IntTy *) tmpcur_7257;
            CursorTy tmpcur_7263 = tmpcur_7257 + sizeof(IntTy);
            CursorTy jump_4186 = tmpcur_7257 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          _copy_Tags(end_r_2966, end_r_2967, loc_3672, tmpcur_7263);
            CursorTy pvrtmp_7264 = tmp_struct_164.field0;
            CursorTy pvrtmp_7265 = tmp_struct_164.field1;
            CursorTy pvrtmp_7266 = tmp_struct_164.field2;
            CursorTy pvrtmp_7267 = tmp_struct_164.field3;
            
            *(TagTyPacked *) loc_2965 = 1;
            
            CursorTy writetag_4985 = loc_2965 + 1;
            
            *(IntTy *) writetag_4985 = tmpval_7262;
            
            CursorTy writecur_4986 = writetag_4985 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7264, pvrtmp_7265,
                                                   loc_2965, pvrtmp_7267};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7276 = *(CursorTy *) tmpcur_7257;
            CursorTy tmpaftercur_7277 = tmpcur_7257 + 8;
            CursorTy jump_4341 = tmpcur_7257 + 8;
            CursorCursorCursorCursorProd tmp_struct_165 =
                                          _copy_Tags(end_r_2966, end_r_2967, loc_2965, tmpcur_7276);
            CursorTy pvrtmp_7278 = tmp_struct_165.field0;
            CursorTy pvrtmp_7279 = tmp_struct_165.field1;
            CursorTy pvrtmp_7280 = tmp_struct_165.field2;
            CursorTy pvrtmp_7281 = tmp_struct_165.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7278, jump_4341,
                                                   pvrtmp_7280, pvrtmp_7281};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7288 = *(CursorTy *) tmpcur_7257;
            CursorTy tmpaftercur_7289 = tmpcur_7257 + 8;
            CursorCursorCursorCursorProd tmp_struct_166 =
                                          _copy_Tags(end_r_2966, end_r_2967, loc_2965, tmpcur_7288);
            CursorTy pvrtmp_7290 = tmp_struct_166.field0;
            CursorTy pvrtmp_7291 = tmp_struct_166.field1;
            CursorTy pvrtmp_7292 = tmp_struct_166.field2;
            CursorTy pvrtmp_7293 = tmp_struct_166.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7290, pvrtmp_7291,
                                                   pvrtmp_7292, pvrtmp_7293};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7256");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2970,
                                                     CursorTy end_r_2971,
                                                     CursorTy loc_2969,
                                                     CursorTy arg_874_1479_1802)
{
    CursorTy loc_3684 = loc_2969 + 1;
    CursorTy loc_3685 = loc_3684 + 8;
    TagTyPacked tmpval_7301 = *(TagTyPacked *) arg_874_1479_1802;
    CursorTy tmpcur_7302 = arg_874_1479_1802 + 1;
    
    
  switch_7345:
    ;
    switch (tmpval_7301) {
        
      case 0:
        {
            CursorTy jump_4189 = arg_874_1479_1802 + 1;
            
            *(TagTyPacked *) loc_2969 = 0;
            
            CursorTy writetag_4996 = loc_2969 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2971, jump_4189,
                                                   loc_2969, writetag_4996};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7307 = *(IntTy *) tmpcur_7302;
            CursorTy tmpcur_7308 = tmpcur_7302 + sizeof(IntTy);
            CursorTy jump_4191 = tmpcur_7302 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _copy_without_ptrs_Tags(end_r_2970, end_r_2971, loc_3685, tmpcur_7308);
            CursorTy pvrtmp_7309 = tmp_struct_170.field0;
            CursorTy pvrtmp_7310 = tmp_struct_170.field1;
            CursorTy pvrtmp_7311 = tmp_struct_170.field2;
            CursorTy pvrtmp_7312 = tmp_struct_170.field3;
            
            *(TagTyPacked *) loc_2969 = 1;
            
            CursorTy writetag_5001 = loc_2969 + 1;
            
            *(IntTy *) writetag_5001 = tmpval_7307;
            
            CursorTy writecur_5002 = writetag_5001 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7309, pvrtmp_7310,
                                                   loc_2969, pvrtmp_7312};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7321 = *(CursorTy *) tmpcur_7302;
            CursorTy tmpaftercur_7322 = tmpcur_7302 + 8;
            CursorTy jump_4347 = tmpcur_7302 + 8;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          _copy_without_ptrs_Tags(end_r_2970, end_r_2971, loc_2969, tmpcur_7321);
            CursorTy pvrtmp_7323 = tmp_struct_171.field0;
            CursorTy pvrtmp_7324 = tmp_struct_171.field1;
            CursorTy pvrtmp_7325 = tmp_struct_171.field2;
            CursorTy pvrtmp_7326 = tmp_struct_171.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7323, jump_4347,
                                                   pvrtmp_7325, pvrtmp_7326};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7333 = *(CursorTy *) tmpcur_7302;
            CursorTy tmpaftercur_7334 = tmpcur_7302 + 8;
            CursorCursorCursorCursorProd tmp_struct_172 =
                                          _copy_without_ptrs_Tags(end_r_2970, end_r_2971, loc_2969, tmpcur_7333);
            CursorTy pvrtmp_7335 = tmp_struct_172.field0;
            CursorTy pvrtmp_7336 = tmp_struct_172.field1;
            CursorTy pvrtmp_7337 = tmp_struct_172.field2;
            CursorTy pvrtmp_7338 = tmp_struct_172.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7335, pvrtmp_7336,
                                                   pvrtmp_7337, pvrtmp_7338};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7301");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_2973, CursorTy arg_879_1484_1807)
{
    TagTyPacked tmpval_7346 = *(TagTyPacked *) arg_879_1484_1807;
    CursorTy tmpcur_7347 = arg_879_1484_1807 + 1;
    
    
  switch_7357:
    ;
    switch (tmpval_7346) {
        
      case 0:
        {
            CursorTy jump_4194 = arg_879_1484_1807 + 1;
            
            return (CursorProd) {jump_4194};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7348 = *(IntTy *) tmpcur_7347;
            CursorTy tmpcur_7349 = tmpcur_7347 + sizeof(IntTy);
            CursorTy jump_4196 = tmpcur_7347 + 8;
            CursorProd tmp_struct_173 =
                        _traverse_Tags(end_r_2973, tmpcur_7349);
            CursorTy pvrtmp_7350 = tmp_struct_173.field0;
            
            return (CursorProd) {pvrtmp_7350};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7351 = *(CursorTy *) tmpcur_7347;
            CursorTy tmpaftercur_7352 = tmpcur_7347 + 8;
            CursorTy jump_4353 = tmpcur_7347 + 8;
            CursorProd tmp_struct_174 =
                        _traverse_Tags(end_r_2973, tmpcur_7351);
            CursorTy pvrtmp_7353 = tmp_struct_174.field0;
            
            return (CursorProd) {jump_4353};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7354 = *(CursorTy *) tmpcur_7347;
            CursorTy tmpaftercur_7355 = tmpcur_7347 + 8;
            CursorProd tmp_struct_175 =
                        _traverse_Tags(end_r_2973, tmpcur_7354);
            CursorTy pvrtmp_7356 = tmp_struct_175.field0;
            
            return (CursorProd) {pvrtmp_7356};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7346");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_2975, CursorTy arg_884_1488_1811)
{
    TagTyPacked tmpval_7358 = *(TagTyPacked *) arg_884_1488_1811;
    CursorTy tmpcur_7359 = arg_884_1488_1811 + 1;
    
    
  switch_7369:
    ;
    switch (tmpval_7358) {
        
      case 0:
        {
            CursorTy jump_4199 = arg_884_1488_1811 + 1;
            unsigned char wildcard_885_1489_1812 = print_symbol(6150);
            unsigned char wildcard_886_1490_1813 = print_symbol(6145);
            
            return (CursorProd) {jump_4199};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7360 = *(IntTy *) tmpcur_7359;
            CursorTy tmpcur_7361 = tmpcur_7359 + sizeof(IntTy);
            CursorTy jump_4201 = tmpcur_7359 + 8;
            unsigned char wildcard_891_1493_1816 = print_symbol(6147);
            unsigned char y_889_1494_1817 = printf("%lld", tmpval_7360);
            CursorProd tmp_struct_176 =  _print_Tags(end_r_2975, tmpcur_7361);
            CursorTy pvrtmp_7362 = tmp_struct_176.field0;
            unsigned char wildcard_892_1496_1819 = print_symbol(6145);
            
            return (CursorProd) {pvrtmp_7362};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7363 = *(CursorTy *) tmpcur_7359;
            CursorTy tmpaftercur_7364 = tmpcur_7359 + 8;
            CursorTy jump_4359 = tmpcur_7359 + 8;
            unsigned char wildcard_4362 = print_symbol(6162);
            CursorProd tmp_struct_177 =  _print_Tags(end_r_2975, tmpcur_7363);
            CursorTy pvrtmp_7365 = tmp_struct_177.field0;
            
            return (CursorProd) {jump_4359};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7366 = *(CursorTy *) tmpcur_7359;
            CursorTy tmpaftercur_7367 = tmpcur_7359 + 8;
            unsigned char wildcard_4362 = print_symbol(6161);
            CursorProd tmp_struct_178 =  _print_Tags(end_r_2975, tmpcur_7366);
            CursorTy pvrtmp_7368 = tmp_struct_178.field0;
            
            return (CursorProd) {pvrtmp_7368};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7358");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_2978,
                                                              CursorTy end_r_2979,
                                                              CursorTy loc_2977,
                                                              CursorTy arg_2710)
{
    if (loc_2977 + 32 > end_r_2979) {
        ChunkTy new_chunk_182 = alloc_chunk(end_r_2979);
        CursorTy chunk_start_183 = new_chunk_182.chunk_start;
        CursorTy chunk_end_184 = new_chunk_182.chunk_end;
        
        end_r_2979 = chunk_end_184;
        *(TagTyPacked *) loc_2977 = 255;
        
        CursorTy redir = loc_2977 + 1;
        
        *(CursorTy *) redir = chunk_start_183;
        loc_2977 = chunk_start_183;
    }
    
    CursorTy loc_3709 = loc_2977 + 1;
    CursorTy loc_3710 = loc_3709 + 8;
    TagTyPacked tmpval_7370 = *(TagTyPacked *) arg_2710;
    CursorTy tmpcur_7371 = arg_2710 + 1;
    
    
  switch_7414:
    ;
    switch (tmpval_7370) {
        
      case 0:
        {
            CursorTy jump_4204 = arg_2710 + 1;
            
            *(TagTyPacked *) loc_2977 = 0;
            
            CursorTy writetag_5032 = loc_2977 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2979, jump_4204,
                                                   loc_2977, writetag_5032};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7376 = *(IntTy *) tmpcur_7371;
            CursorTy tmpcur_7377 = tmpcur_7371 + sizeof(IntTy);
            CursorTy jump_4206 = tmpcur_7371 + 8;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_String(end_r_2978, end_r_2979, loc_3710, tmpcur_7377);
            CursorTy pvrtmp_7378 = tmp_struct_179.field0;
            CursorTy pvrtmp_7379 = tmp_struct_179.field1;
            CursorTy pvrtmp_7380 = tmp_struct_179.field2;
            CursorTy pvrtmp_7381 = tmp_struct_179.field3;
            
            *(TagTyPacked *) loc_2977 = 1;
            
            CursorTy writetag_5037 = loc_2977 + 1;
            
            *(IntTy *) writetag_5037 = tmpval_7376;
            
            CursorTy writecur_5038 = writetag_5037 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7378, pvrtmp_7379,
                                                   loc_2977, pvrtmp_7381};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7390 = *(CursorTy *) tmpcur_7371;
            CursorTy tmpaftercur_7391 = tmpcur_7371 + 8;
            CursorTy jump_4365 = tmpcur_7371 + 8;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_String(end_r_2978, end_r_2979, loc_2977, tmpcur_7390);
            CursorTy pvrtmp_7392 = tmp_struct_180.field0;
            CursorTy pvrtmp_7393 = tmp_struct_180.field1;
            CursorTy pvrtmp_7394 = tmp_struct_180.field2;
            CursorTy pvrtmp_7395 = tmp_struct_180.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7392, jump_4365,
                                                   pvrtmp_7394, pvrtmp_7395};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7402 = *(CursorTy *) tmpcur_7371;
            CursorTy tmpaftercur_7403 = tmpcur_7371 + 8;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_String(end_r_2978, end_r_2979, loc_2977, tmpcur_7402);
            CursorTy pvrtmp_7404 = tmp_struct_181.field0;
            CursorTy pvrtmp_7405 = tmp_struct_181.field1;
            CursorTy pvrtmp_7406 = tmp_struct_181.field2;
            CursorTy pvrtmp_7407 = tmp_struct_181.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7404, pvrtmp_7405,
                                                   pvrtmp_7406, pvrtmp_7407};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7370");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_2982,
                                                               CursorTy end_r_2983,
                                                               CursorTy loc_2981,
                                                               CursorTy arg_2715)
{
    if (loc_2981 + 32 > end_r_2983) {
        ChunkTy new_chunk_189 = alloc_chunk(end_r_2983);
        CursorTy chunk_start_190 = new_chunk_189.chunk_start;
        CursorTy chunk_end_191 = new_chunk_189.chunk_end;
        
        end_r_2983 = chunk_end_191;
        *(TagTyPacked *) loc_2981 = 255;
        
        CursorTy redir = loc_2981 + 1;
        
        *(CursorTy *) redir = chunk_start_190;
        loc_2981 = chunk_start_190;
    }
    
    TagTyPacked tmpval_7415 = *(TagTyPacked *) arg_2715;
    CursorTy tmpcur_7416 = arg_2715 + 1;
    
    
  switch_7465:
    ;
    switch (tmpval_7415) {
        
      case 0:
        {
            CursorTy loc_3720 = loc_2981 + 1;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_String(end_r_2982, end_r_2983, loc_3720, tmpcur_7416);
            CursorTy pvrtmp_7417 = tmp_struct_185.field0;
            CursorTy pvrtmp_7418 = tmp_struct_185.field1;
            CursorTy pvrtmp_7419 = tmp_struct_185.field2;
            CursorTy pvrtmp_7420 = tmp_struct_185.field3;
            
            *(TagTyPacked *) loc_2981 = 0;
            
            CursorTy writetag_5049 = loc_2981 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7417, pvrtmp_7418,
                                                   loc_2981, pvrtmp_7420};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3726 = loc_2981 + 1;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_String(end_r_2982, end_r_2983, loc_3726, tmpcur_7416);
            CursorTy pvrtmp_7429 = tmp_struct_186.field0;
            CursorTy pvrtmp_7430 = tmp_struct_186.field1;
            CursorTy pvrtmp_7431 = tmp_struct_186.field2;
            CursorTy pvrtmp_7432 = tmp_struct_186.field3;
            
            *(TagTyPacked *) loc_2981 = 1;
            
            CursorTy writetag_5054 = loc_2981 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7429, pvrtmp_7430,
                                                   loc_2981, pvrtmp_7432};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7441 = *(CursorTy *) tmpcur_7416;
            CursorTy tmpaftercur_7442 = tmpcur_7416 + 8;
            CursorTy jump_4371 = tmpcur_7416 + 8;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Content(end_r_2982, end_r_2983, loc_2981, tmpcur_7441);
            CursorTy pvrtmp_7443 = tmp_struct_187.field0;
            CursorTy pvrtmp_7444 = tmp_struct_187.field1;
            CursorTy pvrtmp_7445 = tmp_struct_187.field2;
            CursorTy pvrtmp_7446 = tmp_struct_187.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7443, jump_4371,
                                                   pvrtmp_7445, pvrtmp_7446};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7453 = *(CursorTy *) tmpcur_7416;
            CursorTy tmpaftercur_7454 = tmpcur_7416 + 8;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Content(end_r_2982, end_r_2983, loc_2981, tmpcur_7453);
            CursorTy pvrtmp_7455 = tmp_struct_188.field0;
            CursorTy pvrtmp_7456 = tmp_struct_188.field1;
            CursorTy pvrtmp_7457 = tmp_struct_188.field2;
            CursorTy pvrtmp_7458 = tmp_struct_188.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7455, pvrtmp_7456,
                                                   pvrtmp_7457, pvrtmp_7458};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7415");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2986,
                                                           CursorTy end_r_2987,
                                                           CursorTy loc_2985,
                                                           CursorTy arg_2720)
{
    if (loc_2985 + 32 > end_r_2987) {
        ChunkTy new_chunk_216 = alloc_chunk(end_r_2987);
        CursorTy chunk_start_217 = new_chunk_216.chunk_start;
        CursorTy chunk_end_218 = new_chunk_216.chunk_end;
        
        end_r_2987 = chunk_end_218;
        *(TagTyPacked *) loc_2985 = 255;
        
        CursorTy redir = loc_2985 + 1;
        
        *(CursorTy *) redir = chunk_start_217;
        loc_2985 = chunk_start_217;
    }
    
    CursorTy loc_3739 = loc_2985 + 1;
    CursorTy loc_3740 = loc_3739 + 8;
    CursorTy loc_3741 = loc_3740 + 8;
    CursorTy loc_3757 = loc_2985 + 1;
    CursorTy loc_3758 = loc_3757 + 8;
    CursorTy loc_3759 = loc_3758 + 8;
    CursorTy loc_3779 = loc_2985 + 1;
    CursorTy loc_3780 = loc_3779 + 8;
    CursorTy loc_3781 = loc_3780 + 8;
    CursorTy loc_3782 = loc_3781 + 8;
    CursorTy loc_3806 = loc_2985 + 1;
    CursorTy loc_3807 = loc_3806 + 8;
    CursorTy loc_3808 = loc_3807 + 8;
    CursorTy loc_3809 = loc_3808 + 8;
    CursorTy loc_3833 = loc_2985 + 1;
    CursorTy loc_3834 = loc_3833 + 8;
    CursorTy loc_3835 = loc_3834 + 8;
    CursorTy loc_3836 = loc_3835 + 8;
    CursorTy loc_3860 = loc_2985 + 1;
    CursorTy loc_3861 = loc_3860 + 8;
    CursorTy loc_3862 = loc_3861 + 8;
    CursorTy loc_3863 = loc_3862 + 8;
    CursorTy loc_3887 = loc_2985 + 1;
    CursorTy loc_3888 = loc_3887 + 8;
    CursorTy loc_3889 = loc_3888 + 8;
    CursorTy loc_3890 = loc_3889 + 8;
    CursorTy loc_3914 = loc_2985 + 1;
    CursorTy loc_3915 = loc_3914 + 8;
    CursorTy loc_3916 = loc_3915 + 8;
    CursorTy loc_3917 = loc_3916 + 8;
    TagTyPacked tmpval_7466 = *(TagTyPacked *) arg_2720;
    CursorTy tmpcur_7467 = arg_2720 + 1;
    
    
  switch_7704:
    ;
    switch (tmpval_7466) {
        
      case 0:
        {
            CursorTy jump_4213 = arg_2720 + 1;
            
            *(TagTyPacked *) loc_2985 = 0;
            
            CursorTy writetag_5064 = loc_2985 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2987, jump_4213,
                                                   loc_2985, writetag_5064};
            break;
        }
        
      case 1:
        {
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, end_r_2987, loc_3741, tmpcur_7467);
            CursorTy pvrtmp_7472 = tmp_struct_192.field0;
            CursorTy pvrtmp_7473 = tmp_struct_192.field1;
            CursorTy pvrtmp_7474 = tmp_struct_192.field2;
            CursorTy pvrtmp_7475 = tmp_struct_192.field3;
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, pvrtmp_7472, pvrtmp_7475, pvrtmp_7473);
            CursorTy pvrtmp_7480 = tmp_struct_193.field0;
            CursorTy pvrtmp_7481 = tmp_struct_193.field1;
            CursorTy pvrtmp_7482 = tmp_struct_193.field2;
            CursorTy pvrtmp_7483 = tmp_struct_193.field3;
            IntTy sizeof_y_2723__2725 = pvrtmp_7475 - pvrtmp_7474;
            IntTy sizeof_y_2724__2726 = pvrtmp_7483 - pvrtmp_7482;
            IntTy fltPrm_2814 = sizeof_y_2723__2725 + 0;
            IntTy offset__2727 = 0 + fltPrm_2814;
            IntTy fltPrm_2815 = sizeof_y_2723__2725 + sizeof_y_2724__2726;
            IntTy size_dcon_2728 = 9 + fltPrm_2815;
            
            *(TagTyPacked *) loc_2985 = 160;
            
            CursorTy writetag_5069 = loc_2985 + 1;
            
            *(IntTy *) writetag_5069 = size_dcon_2728;
            
            CursorTy writecur_5070 = writetag_5069 + sizeof(IntTy);
            
            *(IntTy *) writecur_5070 = offset__2727;
            
            CursorTy writecur_5071 = writecur_5070 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7480, pvrtmp_7481,
                                                   loc_2985, pvrtmp_7483};
            break;
        }
        
      case 2:
        {
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, end_r_2987, loc_3759, tmpcur_7467);
            CursorTy pvrtmp_7492 = tmp_struct_194.field0;
            CursorTy pvrtmp_7493 = tmp_struct_194.field1;
            CursorTy pvrtmp_7494 = tmp_struct_194.field2;
            CursorTy pvrtmp_7495 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, pvrtmp_7492, pvrtmp_7495, pvrtmp_7493);
            CursorTy pvrtmp_7500 = tmp_struct_195.field0;
            CursorTy pvrtmp_7501 = tmp_struct_195.field1;
            CursorTy pvrtmp_7502 = tmp_struct_195.field2;
            CursorTy pvrtmp_7503 = tmp_struct_195.field3;
            IntTy sizeof_y_2731__2733 = pvrtmp_7495 - pvrtmp_7494;
            IntTy sizeof_y_2732__2734 = pvrtmp_7503 - pvrtmp_7502;
            IntTy fltPrm_2816 = sizeof_y_2731__2733 + 0;
            IntTy offset__2735 = 0 + fltPrm_2816;
            IntTy fltPrm_2817 = sizeof_y_2731__2733 + sizeof_y_2732__2734;
            IntTy size_dcon_2736 = 9 + fltPrm_2817;
            
            *(TagTyPacked *) loc_2985 = 162;
            
            CursorTy writetag_5078 = loc_2985 + 1;
            
            *(IntTy *) writetag_5078 = size_dcon_2736;
            
            CursorTy writecur_5079 = writetag_5078 + sizeof(IntTy);
            
            *(IntTy *) writecur_5079 = offset__2735;
            
            CursorTy writecur_5080 = writecur_5079 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7500, pvrtmp_7501,
                                                   loc_2985, pvrtmp_7503};
            break;
        }
        
      case 3:
        {
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Tags(end_r_2986, end_r_2987, loc_3782, tmpcur_7467);
            CursorTy pvrtmp_7512 = tmp_struct_196.field0;
            CursorTy pvrtmp_7513 = tmp_struct_196.field1;
            CursorTy pvrtmp_7514 = tmp_struct_196.field2;
            CursorTy pvrtmp_7515 = tmp_struct_196.field3;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, pvrtmp_7512, pvrtmp_7515, pvrtmp_7513);
            CursorTy pvrtmp_7520 = tmp_struct_197.field0;
            CursorTy pvrtmp_7521 = tmp_struct_197.field1;
            CursorTy pvrtmp_7522 = tmp_struct_197.field2;
            CursorTy pvrtmp_7523 = tmp_struct_197.field3;
            CursorCursorCursorCursorProd tmp_struct_198 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, pvrtmp_7520, pvrtmp_7523, pvrtmp_7521);
            CursorTy pvrtmp_7528 = tmp_struct_198.field0;
            CursorTy pvrtmp_7529 = tmp_struct_198.field1;
            CursorTy pvrtmp_7530 = tmp_struct_198.field2;
            CursorTy pvrtmp_7531 = tmp_struct_198.field3;
            IntTy sizeof_y_2740__2743 = pvrtmp_7515 - pvrtmp_7514;
            IntTy sizeof_y_2741__2744 = pvrtmp_7523 - pvrtmp_7522;
            IntTy sizeof_y_2742__2745 = pvrtmp_7531 - pvrtmp_7530;
            IntTy fltPrm_2818 = sizeof_y_2740__2743 + 0;
            IntTy offset__2746 = 8 + fltPrm_2818;
            IntTy fltPrm_2819 = sizeof_y_2740__2743 + sizeof_y_2741__2744;
            IntTy offset__2747 = 0 + fltPrm_2819;
            IntTy fltPrm_2821 = sizeof_y_2741__2744 + sizeof_y_2742__2745;
            IntTy fltPrm_2820 = sizeof_y_2740__2743 + fltPrm_2821;
            IntTy size_dcon_2748 = 17 + fltPrm_2820;
            
            *(TagTyPacked *) loc_2985 = 164;
            
            CursorTy writetag_5088 = loc_2985 + 1;
            
            *(IntTy *) writetag_5088 = size_dcon_2748;
            
            CursorTy writecur_5089 = writetag_5088 + sizeof(IntTy);
            
            *(IntTy *) writecur_5089 = offset__2746;
            
            CursorTy writecur_5090 = writecur_5089 + sizeof(IntTy);
            
            *(IntTy *) writecur_5090 = offset__2747;
            
            CursorTy writecur_5091 = writecur_5090 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7528, pvrtmp_7529,
                                                   loc_2985, pvrtmp_7531};
            break;
        }
        
      case 4:
        {
            CursorCursorCursorCursorProd tmp_struct_199 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, end_r_2987, loc_3809, tmpcur_7467);
            CursorTy pvrtmp_7540 = tmp_struct_199.field0;
            CursorTy pvrtmp_7541 = tmp_struct_199.field1;
            CursorTy pvrtmp_7542 = tmp_struct_199.field2;
            CursorTy pvrtmp_7543 = tmp_struct_199.field3;
            CursorCursorCursorCursorProd tmp_struct_200 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, pvrtmp_7540, pvrtmp_7543, pvrtmp_7541);
            CursorTy pvrtmp_7548 = tmp_struct_200.field0;
            CursorTy pvrtmp_7549 = tmp_struct_200.field1;
            CursorTy pvrtmp_7550 = tmp_struct_200.field2;
            CursorTy pvrtmp_7551 = tmp_struct_200.field3;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_2986, pvrtmp_7548, pvrtmp_7551, pvrtmp_7549);
            CursorTy pvrtmp_7556 = tmp_struct_201.field0;
            CursorTy pvrtmp_7557 = tmp_struct_201.field1;
            CursorTy pvrtmp_7558 = tmp_struct_201.field2;
            CursorTy pvrtmp_7559 = tmp_struct_201.field3;
            IntTy sizeof_y_2752__2755 = pvrtmp_7543 - pvrtmp_7542;
            IntTy sizeof_y_2753__2756 = pvrtmp_7551 - pvrtmp_7550;
            IntTy sizeof_y_2754__2757 = pvrtmp_7559 - pvrtmp_7558;
            IntTy fltPrm_2822 = sizeof_y_2752__2755 + 0;
            IntTy offset__2758 = 8 + fltPrm_2822;
            IntTy fltPrm_2823 = sizeof_y_2752__2755 + sizeof_y_2753__2756;
            IntTy offset__2759 = 0 + fltPrm_2823;
            IntTy fltPrm_2825 = sizeof_y_2753__2756 + sizeof_y_2754__2757;
            IntTy fltPrm_2824 = sizeof_y_2752__2755 + fltPrm_2825;
            IntTy size_dcon_2760 = 17 + fltPrm_2824;
            
            *(TagTyPacked *) loc_2985 = 166;
            
            CursorTy writetag_5100 = loc_2985 + 1;
            
            *(IntTy *) writetag_5100 = size_dcon_2760;
            
            CursorTy writecur_5101 = writetag_5100 + sizeof(IntTy);
            
            *(IntTy *) writecur_5101 = offset__2758;
            
            CursorTy writecur_5102 = writecur_5101 + sizeof(IntTy);
            
            *(IntTy *) writecur_5102 = offset__2759;
            
            CursorTy writecur_5103 = writecur_5102 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7556, pvrtmp_7557,
                                                   loc_2985, pvrtmp_7559};
            break;
        }
        
      case 5:
        {
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_2986, end_r_2987, loc_3836, tmpcur_7467);
            CursorTy pvrtmp_7568 = tmp_struct_202.field0;
            CursorTy pvrtmp_7569 = tmp_struct_202.field1;
            CursorTy pvrtmp_7570 = tmp_struct_202.field2;
            CursorTy pvrtmp_7571 = tmp_struct_202.field3;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, pvrtmp_7568, pvrtmp_7571, pvrtmp_7569);
            CursorTy pvrtmp_7576 = tmp_struct_203.field0;
            CursorTy pvrtmp_7577 = tmp_struct_203.field1;
            CursorTy pvrtmp_7578 = tmp_struct_203.field2;
            CursorTy pvrtmp_7579 = tmp_struct_203.field3;
            CursorCursorCursorCursorProd tmp_struct_204 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, pvrtmp_7576, pvrtmp_7579, pvrtmp_7577);
            CursorTy pvrtmp_7584 = tmp_struct_204.field0;
            CursorTy pvrtmp_7585 = tmp_struct_204.field1;
            CursorTy pvrtmp_7586 = tmp_struct_204.field2;
            CursorTy pvrtmp_7587 = tmp_struct_204.field3;
            IntTy sizeof_y_2764__2767 = pvrtmp_7571 - pvrtmp_7570;
            IntTy sizeof_y_2765__2768 = pvrtmp_7579 - pvrtmp_7578;
            IntTy sizeof_y_2766__2769 = pvrtmp_7587 - pvrtmp_7586;
            IntTy fltPrm_2826 = sizeof_y_2764__2767 + 0;
            IntTy offset__2770 = 8 + fltPrm_2826;
            IntTy fltPrm_2827 = sizeof_y_2764__2767 + sizeof_y_2765__2768;
            IntTy offset__2771 = 0 + fltPrm_2827;
            IntTy fltPrm_2829 = sizeof_y_2765__2768 + sizeof_y_2766__2769;
            IntTy fltPrm_2828 = sizeof_y_2764__2767 + fltPrm_2829;
            IntTy size_dcon_2772 = 17 + fltPrm_2828;
            
            *(TagTyPacked *) loc_2985 = 168;
            
            CursorTy writetag_5112 = loc_2985 + 1;
            
            *(IntTy *) writetag_5112 = size_dcon_2772;
            
            CursorTy writecur_5113 = writetag_5112 + sizeof(IntTy);
            
            *(IntTy *) writecur_5113 = offset__2770;
            
            CursorTy writecur_5114 = writecur_5113 + sizeof(IntTy);
            
            *(IntTy *) writecur_5114 = offset__2771;
            
            CursorTy writecur_5115 = writecur_5114 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7584, pvrtmp_7585,
                                                   loc_2985, pvrtmp_7587};
            break;
        }
        
      case 6:
        {
            CursorCursorCursorCursorProd tmp_struct_205 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, end_r_2987, loc_3863, tmpcur_7467);
            CursorTy pvrtmp_7596 = tmp_struct_205.field0;
            CursorTy pvrtmp_7597 = tmp_struct_205.field1;
            CursorTy pvrtmp_7598 = tmp_struct_205.field2;
            CursorTy pvrtmp_7599 = tmp_struct_205.field3;
            CursorCursorCursorCursorProd tmp_struct_206 =
                                          _add_size_and_rel_offsets_Tags(end_r_2986, pvrtmp_7596, pvrtmp_7599, pvrtmp_7597);
            CursorTy pvrtmp_7604 = tmp_struct_206.field0;
            CursorTy pvrtmp_7605 = tmp_struct_206.field1;
            CursorTy pvrtmp_7606 = tmp_struct_206.field2;
            CursorTy pvrtmp_7607 = tmp_struct_206.field3;
            CursorCursorCursorCursorProd tmp_struct_207 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, pvrtmp_7604, pvrtmp_7607, pvrtmp_7605);
            CursorTy pvrtmp_7612 = tmp_struct_207.field0;
            CursorTy pvrtmp_7613 = tmp_struct_207.field1;
            CursorTy pvrtmp_7614 = tmp_struct_207.field2;
            CursorTy pvrtmp_7615 = tmp_struct_207.field3;
            IntTy sizeof_y_2776__2779 = pvrtmp_7599 - pvrtmp_7598;
            IntTy sizeof_y_2777__2780 = pvrtmp_7607 - pvrtmp_7606;
            IntTy sizeof_y_2778__2781 = pvrtmp_7615 - pvrtmp_7614;
            IntTy fltPrm_2830 = sizeof_y_2776__2779 + 0;
            IntTy offset__2782 = 8 + fltPrm_2830;
            IntTy fltPrm_2831 = sizeof_y_2776__2779 + sizeof_y_2777__2780;
            IntTy offset__2783 = 0 + fltPrm_2831;
            IntTy fltPrm_2833 = sizeof_y_2777__2780 + sizeof_y_2778__2781;
            IntTy fltPrm_2832 = sizeof_y_2776__2779 + fltPrm_2833;
            IntTy size_dcon_2784 = 17 + fltPrm_2832;
            
            *(TagTyPacked *) loc_2985 = 170;
            
            CursorTy writetag_5124 = loc_2985 + 1;
            
            *(IntTy *) writetag_5124 = size_dcon_2784;
            
            CursorTy writecur_5125 = writetag_5124 + sizeof(IntTy);
            
            *(IntTy *) writecur_5125 = offset__2782;
            
            CursorTy writecur_5126 = writecur_5125 + sizeof(IntTy);
            
            *(IntTy *) writecur_5126 = offset__2783;
            
            CursorTy writecur_5127 = writecur_5126 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7612, pvrtmp_7613,
                                                   loc_2985, pvrtmp_7615};
            break;
        }
        
      case 7:
        {
            CursorCursorCursorCursorProd tmp_struct_208 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, end_r_2987, loc_3890, tmpcur_7467);
            CursorTy pvrtmp_7624 = tmp_struct_208.field0;
            CursorTy pvrtmp_7625 = tmp_struct_208.field1;
            CursorTy pvrtmp_7626 = tmp_struct_208.field2;
            CursorTy pvrtmp_7627 = tmp_struct_208.field3;
            CursorCursorCursorCursorProd tmp_struct_209 =
                                          _add_size_and_rel_offsets_Tags(end_r_2986, pvrtmp_7624, pvrtmp_7627, pvrtmp_7625);
            CursorTy pvrtmp_7632 = tmp_struct_209.field0;
            CursorTy pvrtmp_7633 = tmp_struct_209.field1;
            CursorTy pvrtmp_7634 = tmp_struct_209.field2;
            CursorTy pvrtmp_7635 = tmp_struct_209.field3;
            CursorCursorCursorCursorProd tmp_struct_210 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, pvrtmp_7632, pvrtmp_7635, pvrtmp_7633);
            CursorTy pvrtmp_7640 = tmp_struct_210.field0;
            CursorTy pvrtmp_7641 = tmp_struct_210.field1;
            CursorTy pvrtmp_7642 = tmp_struct_210.field2;
            CursorTy pvrtmp_7643 = tmp_struct_210.field3;
            IntTy sizeof_y_2788__2791 = pvrtmp_7627 - pvrtmp_7626;
            IntTy sizeof_y_2789__2792 = pvrtmp_7635 - pvrtmp_7634;
            IntTy sizeof_y_2790__2793 = pvrtmp_7643 - pvrtmp_7642;
            IntTy fltPrm_2834 = sizeof_y_2788__2791 + 0;
            IntTy offset__2794 = 8 + fltPrm_2834;
            IntTy fltPrm_2835 = sizeof_y_2788__2791 + sizeof_y_2789__2792;
            IntTy offset__2795 = 0 + fltPrm_2835;
            IntTy fltPrm_2837 = sizeof_y_2789__2792 + sizeof_y_2790__2793;
            IntTy fltPrm_2836 = sizeof_y_2788__2791 + fltPrm_2837;
            IntTy size_dcon_2796 = 17 + fltPrm_2836;
            
            *(TagTyPacked *) loc_2985 = 172;
            
            CursorTy writetag_5136 = loc_2985 + 1;
            
            *(IntTy *) writetag_5136 = size_dcon_2796;
            
            CursorTy writecur_5137 = writetag_5136 + sizeof(IntTy);
            
            *(IntTy *) writecur_5137 = offset__2794;
            
            CursorTy writecur_5138 = writecur_5137 + sizeof(IntTy);
            
            *(IntTy *) writecur_5138 = offset__2795;
            
            CursorTy writecur_5139 = writecur_5138 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7640, pvrtmp_7641,
                                                   loc_2985, pvrtmp_7643};
            break;
        }
        
      case 8:
        {
            CursorCursorCursorCursorProd tmp_struct_211 =
                                          _add_size_and_rel_offsets_Content(end_r_2986, end_r_2987, loc_3917, tmpcur_7467);
            CursorTy pvrtmp_7652 = tmp_struct_211.field0;
            CursorTy pvrtmp_7653 = tmp_struct_211.field1;
            CursorTy pvrtmp_7654 = tmp_struct_211.field2;
            CursorTy pvrtmp_7655 = tmp_struct_211.field3;
            CursorCursorCursorCursorProd tmp_struct_212 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, pvrtmp_7652, pvrtmp_7655, pvrtmp_7653);
            CursorTy pvrtmp_7660 = tmp_struct_212.field0;
            CursorTy pvrtmp_7661 = tmp_struct_212.field1;
            CursorTy pvrtmp_7662 = tmp_struct_212.field2;
            CursorTy pvrtmp_7663 = tmp_struct_212.field3;
            CursorCursorCursorCursorProd tmp_struct_213 =
                                          _add_size_and_rel_offsets_Tags(end_r_2986, pvrtmp_7660, pvrtmp_7663, pvrtmp_7661);
            CursorTy pvrtmp_7668 = tmp_struct_213.field0;
            CursorTy pvrtmp_7669 = tmp_struct_213.field1;
            CursorTy pvrtmp_7670 = tmp_struct_213.field2;
            CursorTy pvrtmp_7671 = tmp_struct_213.field3;
            IntTy sizeof_y_2800__2803 = pvrtmp_7655 - pvrtmp_7654;
            IntTy sizeof_y_2801__2804 = pvrtmp_7663 - pvrtmp_7662;
            IntTy sizeof_y_2802__2805 = pvrtmp_7671 - pvrtmp_7670;
            IntTy fltPrm_2838 = sizeof_y_2800__2803 + 0;
            IntTy offset__2806 = 8 + fltPrm_2838;
            IntTy fltPrm_2839 = sizeof_y_2800__2803 + sizeof_y_2801__2804;
            IntTy offset__2807 = 0 + fltPrm_2839;
            IntTy fltPrm_2841 = sizeof_y_2801__2804 + sizeof_y_2802__2805;
            IntTy fltPrm_2840 = sizeof_y_2800__2803 + fltPrm_2841;
            IntTy size_dcon_2808 = 17 + fltPrm_2840;
            
            *(TagTyPacked *) loc_2985 = 174;
            
            CursorTy writetag_5148 = loc_2985 + 1;
            
            *(IntTy *) writetag_5148 = size_dcon_2808;
            
            CursorTy writecur_5149 = writetag_5148 + sizeof(IntTy);
            
            *(IntTy *) writecur_5149 = offset__2806;
            
            CursorTy writecur_5150 = writecur_5149 + sizeof(IntTy);
            
            *(IntTy *) writecur_5150 = offset__2807;
            
            CursorTy writecur_5151 = writecur_5150 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7668, pvrtmp_7669,
                                                   loc_2985, pvrtmp_7671};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7680 = *(CursorTy *) tmpcur_7467;
            CursorTy tmpaftercur_7681 = tmpcur_7467 + 8;
            CursorTy jump_4377 = tmpcur_7467 + 8;
            CursorCursorCursorCursorProd tmp_struct_214 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, end_r_2987, loc_2985, tmpcur_7680);
            CursorTy pvrtmp_7682 = tmp_struct_214.field0;
            CursorTy pvrtmp_7683 = tmp_struct_214.field1;
            CursorTy pvrtmp_7684 = tmp_struct_214.field2;
            CursorTy pvrtmp_7685 = tmp_struct_214.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7682, jump_4377,
                                                   pvrtmp_7684, pvrtmp_7685};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7692 = *(CursorTy *) tmpcur_7467;
            CursorTy tmpaftercur_7693 = tmpcur_7467 + 8;
            CursorCursorCursorCursorProd tmp_struct_215 =
                                          _add_size_and_rel_offsets_Adt(end_r_2986, end_r_2987, loc_2985, tmpcur_7692);
            CursorTy pvrtmp_7694 = tmp_struct_215.field0;
            CursorTy pvrtmp_7695 = tmp_struct_215.field1;
            CursorTy pvrtmp_7696 = tmp_struct_215.field2;
            CursorTy pvrtmp_7697 = tmp_struct_215.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7694, pvrtmp_7695,
                                                   pvrtmp_7696, pvrtmp_7697};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7466");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2990,
                                                            CursorTy end_r_2991,
                                                            CursorTy loc_2989,
                                                            CursorTy arg_2809)
{
    if (loc_2989 + 32 > end_r_2991) {
        ChunkTy new_chunk_222 = alloc_chunk(end_r_2991);
        CursorTy chunk_start_223 = new_chunk_222.chunk_start;
        CursorTy chunk_end_224 = new_chunk_222.chunk_end;
        
        end_r_2991 = chunk_end_224;
        *(TagTyPacked *) loc_2989 = 255;
        
        CursorTy redir = loc_2989 + 1;
        
        *(CursorTy *) redir = chunk_start_223;
        loc_2989 = chunk_start_223;
    }
    
    CursorTy loc_3937 = loc_2989 + 1;
    CursorTy loc_3938 = loc_3937 + 8;
    TagTyPacked tmpval_7705 = *(TagTyPacked *) arg_2809;
    CursorTy tmpcur_7706 = arg_2809 + 1;
    
    
  switch_7749:
    ;
    switch (tmpval_7705) {
        
      case 0:
        {
            CursorTy jump_4245 = arg_2809 + 1;
            
            *(TagTyPacked *) loc_2989 = 0;
            
            CursorTy writetag_5163 = loc_2989 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2991, jump_4245,
                                                   loc_2989, writetag_5163};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7711 = *(IntTy *) tmpcur_7706;
            CursorTy tmpcur_7712 = tmpcur_7706 + sizeof(IntTy);
            CursorTy jump_4247 = tmpcur_7706 + 8;
            CursorCursorCursorCursorProd tmp_struct_219 =
                                          _add_size_and_rel_offsets_Tags(end_r_2990, end_r_2991, loc_3938, tmpcur_7712);
            CursorTy pvrtmp_7713 = tmp_struct_219.field0;
            CursorTy pvrtmp_7714 = tmp_struct_219.field1;
            CursorTy pvrtmp_7715 = tmp_struct_219.field2;
            CursorTy pvrtmp_7716 = tmp_struct_219.field3;
            
            *(TagTyPacked *) loc_2989 = 1;
            
            CursorTy writetag_5168 = loc_2989 + 1;
            
            *(IntTy *) writetag_5168 = tmpval_7711;
            
            CursorTy writecur_5169 = writetag_5168 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7713, pvrtmp_7714,
                                                   loc_2989, pvrtmp_7716};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7725 = *(CursorTy *) tmpcur_7706;
            CursorTy tmpaftercur_7726 = tmpcur_7706 + 8;
            CursorTy jump_4383 = tmpcur_7706 + 8;
            CursorCursorCursorCursorProd tmp_struct_220 =
                                          _add_size_and_rel_offsets_Tags(end_r_2990, end_r_2991, loc_2989, tmpcur_7725);
            CursorTy pvrtmp_7727 = tmp_struct_220.field0;
            CursorTy pvrtmp_7728 = tmp_struct_220.field1;
            CursorTy pvrtmp_7729 = tmp_struct_220.field2;
            CursorTy pvrtmp_7730 = tmp_struct_220.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7727, jump_4383,
                                                   pvrtmp_7729, pvrtmp_7730};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7737 = *(CursorTy *) tmpcur_7706;
            CursorTy tmpaftercur_7738 = tmpcur_7706 + 8;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          _add_size_and_rel_offsets_Tags(end_r_2990, end_r_2991, loc_2989, tmpcur_7737);
            CursorTy pvrtmp_7739 = tmp_struct_221.field0;
            CursorTy pvrtmp_7740 = tmp_struct_221.field1;
            CursorTy pvrtmp_7741 = tmp_struct_221.field2;
            CursorTy pvrtmp_7742 = tmp_struct_221.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7739, pvrtmp_7740,
                                                   pvrtmp_7741, pvrtmp_7742};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7705");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(6145, ")");
    add_symbol(6146, "(Text ");
    add_symbol(6147, "(Tag ");
    add_symbol(6148, "(TCA ");
    add_symbol(6149, "(TAC ");
    add_symbol(6150, "(Nul ");
    add_symbol(6151, "(Nil ");
    add_symbol(6152, "(Image ");
    add_symbol(6153, "(End ");
    add_symbol(6154, "(Char ");
    add_symbol(6155, "(CTA ");
    add_symbol(6156, "(CAT ");
    add_symbol(6157, "(CA ");
    add_symbol(6158, "(ATC ");
    add_symbol(6159, "(ACT ");
    add_symbol(6160, "(AC ");
    add_symbol(6161, " ->r ");
    add_symbol(6162, " ->i ");
    
    RegionTy *region_6163 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3001 = region_6163->reg_heap;
    IntTy sizeof_end_r_3001_6164 = global_init_inf_buf_size;
    CursorTy end_r_3001 = r_3001 + sizeof_end_r_3001_6164;
    RegionTy *region_6165 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3000 = region_6165->reg_heap;
    IntTy sizeof_end_r_3000_6166 = global_init_inf_buf_size;
    CursorTy end_r_3000 = r_3000 + sizeof_end_r_3000_6166;
    CursorCursorCursorProd tmp_struct_225 =
                            mkCATList(end_r_3001, r_3001, 100000, 10, 2000);
    CursorTy pvrtmp_6167 = tmp_struct_225.field0;
    CursorTy pvrtmp_6168 = tmp_struct_225.field1;
    CursorTy pvrtmp_6169 = tmp_struct_225.field2;
    CursorTy pvrtmp_6183;
    CursorTy pvrtmp_6184;
    CursorTy pvrtmp_6185;
    VectorTy *times_230 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6183;
    struct timespec end_pvrtmp_6183;
    
    start_counters();
    for (long long iters_pvrtmp_6183 = 0; iters_pvrtmp_6183 <
         global_iters_param; iters_pvrtmp_6183++) {
        if (iters_pvrtmp_6183 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6183);
        
        CursorCursorCursorProd tmp_struct_226 =
                                addValTagsAdt(pvrtmp_6167, end_r_3000, r_3000, pvrtmp_6168);
        CursorTy pvrtmp_6174 = tmp_struct_226.field0;
        CursorTy pvrtmp_6175 = tmp_struct_226.field1;
        CursorTy pvrtmp_6176 = tmp_struct_226.field2;
        
        pvrtmp_6183 = pvrtmp_6174;
        pvrtmp_6184 = pvrtmp_6175;
        pvrtmp_6185 = pvrtmp_6176;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6183);
        if (iters_pvrtmp_6183 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_227 = difftimespecs(&begin_pvrtmp_6183,
                                            &end_pvrtmp_6183);
        
        vector_inplace_update(times_230, iters_pvrtmp_6183, &itertime_227);
    }
    read_counters();
    print_counters();
    vector_inplace_sort(times_230, compare_doubles);
    
    double *tmp_231 = (double *) vector_nth(times_230, global_iters_param / 2);
    double selftimed_229 = *tmp_231;
    double batchtime_228 = sum_timing_array(times_230);
    
    print_timing_array(times_230);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_228);
    printf("SELFTIMED: %e\n", selftimed_229);
    printf("'#()");
    printf("\n");
    free_symtable();
    return 0;
}
