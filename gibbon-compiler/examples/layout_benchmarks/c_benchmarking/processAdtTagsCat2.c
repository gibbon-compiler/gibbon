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
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2906, CursorTy end_r_2907,
                                     CursorTy loc_2905,
                                     CursorTy adt_14_900_1516);
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2910, CursorTy end_r_2911,
                                       CursorTy loc_2909,
                                       CursorTy tags_20_906_1522,
                                       IntTy inVal_21_907_1523);
CursorCursorCursorProd mkCATList(CursorTy end_r_2913, CursorTy loc_2912,
                                 IntTy len_24_910_1528,
                                 IntTy tagLen_25_911_1529,
                                 IntTy strLen_26_912_1530);
CursorCursorCursorProd mkString(CursorTy end_r_2915, CursorTy loc_2914,
                                IntTy len_179_1065_1536);
CursorCursorCursorProd mkContentText(CursorTy end_r_2917, CursorTy loc_2916,
                                     IntTy n_193_1079_1542);
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2919, CursorTy loc_2918,
                                    IntTy len_318_1204_1544);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2922,
                                          CursorTy end_r_2923,
                                          CursorTy loc_2921,
                                          CursorTy arg_622_1228_1549);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2926,
                                                       CursorTy end_r_2927,
                                                       CursorTy loc_2925,
                                                       CursorTy arg_627_1233_1554);
CursorProd _traverse_String(CursorTy end_r_2929, CursorTy arg_632_1238_1559);
CursorProd _print_String(CursorTy end_r_2931, CursorTy arg_637_1242_1563);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2934,
                                           CursorTy end_r_2935,
                                           CursorTy loc_2933,
                                           CursorTy arg_646_1251_1572);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2938,
                                                        CursorTy end_r_2939,
                                                        CursorTy loc_2937,
                                                        CursorTy arg_651_1256_1577);
CursorProd _traverse_Content(CursorTy end_r_2941, CursorTy arg_656_1261_1582);
CursorProd _print_Content(CursorTy end_r_2943, CursorTy arg_661_1266_1587);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2946, CursorTy end_r_2947,
                                       CursorTy loc_2945,
                                       CursorTy arg_670_1275_1596);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2950,
                                                    CursorTy end_r_2951,
                                                    CursorTy loc_2949,
                                                    CursorTy arg_715_1320_1641);
CursorProd _traverse_Adt(CursorTy end_r_2953, CursorTy arg_760_1365_1686);
CursorProd _print_Adt(CursorTy end_r_2955, CursorTy arg_805_1410_1731);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2958,
                                        CursorTy end_r_2959, CursorTy loc_2957,
                                        CursorTy arg_868_1473_1794);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2962,
                                                     CursorTy end_r_2963,
                                                     CursorTy loc_2961,
                                                     CursorTy arg_873_1478_1799);
CursorProd _traverse_Tags(CursorTy end_r_2965, CursorTy arg_878_1483_1804);
CursorProd _print_Tags(CursorTy end_r_2967, CursorTy arg_883_1487_1808);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_2970, CursorTy end_r_2971,
                                 CursorTy loc_2969, CursorTy arg_2702);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_2974, CursorTy end_r_2975,
                                  CursorTy loc_2973, CursorTy arg_2707);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2978,
                                                           CursorTy end_r_2979,
                                                           CursorTy loc_2977,
                                                           CursorTy arg_2712);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2982,
                                                            CursorTy end_r_2983,
                                                            CursorTy loc_2981,
                                                            CursorTy arg_2801);
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2906, CursorTy end_r_2907,
                                     CursorTy loc_2905,
                                     CursorTy adt_14_900_1516)
{
    if (loc_2905 + 32 > end_r_2907) {
        ChunkTy new_chunk_4 = alloc_chunk(end_r_2907);
        CursorTy chunk_start_5 = new_chunk_4.chunk_start;
        CursorTy chunk_end_6 = new_chunk_4.chunk_end;
        
        end_r_2907 = chunk_end_6;
        *(TagTyPacked *) loc_2905 = 255;
        
        CursorTy redir = loc_2905 + 1;
        
        *(CursorTy *) redir = chunk_start_5;
        loc_2905 = chunk_start_5;
    }
    
    CursorTy loc_3008 = loc_2905 + 1;
    CursorTy loc_3009 = loc_3008 + 8;
    CursorTy loc_3010 = loc_3009 + 8;
    TagTyPacked tmpval_6177 = *(TagTyPacked *) adt_14_900_1516;
    CursorTy tmpcur_6178 = adt_14_900_1516 + 1;
    
    
  switch_6230:
    ;
    switch (tmpval_6177) {
        
      case 0:
        {
            CursorTy jump_3933 = adt_14_900_1516 + 1;
            
            *(TagTyPacked *) loc_2905 = 0;
            
            CursorTy writetag_4492 = loc_2905 + 1;
            
            return (CursorCursorCursorProd) {end_r_2907, loc_2905,
                                             writetag_4492};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6183 = *(CursorTy *) tmpcur_6178;
            CursorTy tmpaftercur_6184 = tmpcur_6178 + 8;
            CursorTy tmpcur_6185 = *(CursorTy *) tmpaftercur_6184;
            CursorTy tmpaftercur_6186 = tmpaftercur_6184 + 8;
            CursorTy jump_3936 = tmpaftercur_6184 + 8;
            CursorTy jump_3935 = tmpcur_6178 + 8;
            
            *(TagTyPacked *) loc_3010 = 254;
            
            CursorTy writetag_4497 = loc_3010 + 1;
            
            *(CursorTy *) writetag_4497 = tmpaftercur_6186;
            
            CursorTy writecur_4498 = writetag_4497 + 8;
            CursorCursorCursorProd tmp_struct_0 =
                                    addValTagsAdt(end_r_2906, end_r_2907, writecur_4498, tmpcur_6183);
            CursorTy pvrtmp_6189 = tmp_struct_0.field0;
            CursorTy pvrtmp_6190 = tmp_struct_0.field1;
            CursorTy pvrtmp_6191 = tmp_struct_0.field2;
            CursorCursorCursorCursorProd tmp_struct_1 =
                                          addValTag(end_r_2906, pvrtmp_6189, pvrtmp_6191, tmpcur_6185, 10);
            CursorTy pvrtmp_6196 = tmp_struct_1.field0;
            CursorTy pvrtmp_6197 = tmp_struct_1.field1;
            CursorTy pvrtmp_6198 = tmp_struct_1.field2;
            CursorTy pvrtmp_6199 = tmp_struct_1.field3;
            
            *(TagTyPacked *) loc_2905 = 23;
            
            CursorTy writetag_4502 = loc_2905 + 1;
            
            *(CursorTy *) writetag_4502 = tmpcur_6183;
            
            CursorTy writecur_4503 = writetag_4502 + 8;
            
            *(CursorTy *) writecur_4503 = pvrtmp_6191;
            
            CursorTy writecur_4504 = writecur_4503 + 8;
            
            return (CursorCursorCursorProd) {pvrtmp_6196, loc_2905,
                                             pvrtmp_6199};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6208 = *(CursorTy *) tmpcur_6178;
            CursorTy tmpaftercur_6209 = tmpcur_6178 + 8;
            CursorTy jump_4245 = tmpcur_6178 + 8;
            CursorCursorCursorProd tmp_struct_2 =
                                    addValTagsAdt(end_r_2906, end_r_2907, loc_2905, tmpcur_6208);
            CursorTy pvrtmp_6210 = tmp_struct_2.field0;
            CursorTy pvrtmp_6211 = tmp_struct_2.field1;
            CursorTy pvrtmp_6212 = tmp_struct_2.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6210, pvrtmp_6211,
                                             pvrtmp_6212};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6219 = *(CursorTy *) tmpcur_6178;
            CursorTy tmpaftercur_6220 = tmpcur_6178 + 8;
            CursorCursorCursorProd tmp_struct_3 =
                                    addValTagsAdt(end_r_2906, end_r_2907, loc_2905, tmpcur_6219);
            CursorTy pvrtmp_6221 = tmp_struct_3.field0;
            CursorTy pvrtmp_6222 = tmp_struct_3.field1;
            CursorTy pvrtmp_6223 = tmp_struct_3.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6221, pvrtmp_6222,
                                             pvrtmp_6223};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6177");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2910, CursorTy end_r_2911,
                                       CursorTy loc_2909,
                                       CursorTy tags_20_906_1522,
                                       IntTy inVal_21_907_1523)
{
    if (loc_2909 + 32 > end_r_2911) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2911);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2911 = chunk_end_12;
        *(TagTyPacked *) loc_2909 = 255;
        
        CursorTy redir = loc_2909 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2909 = chunk_start_11;
    }
    
    CursorTy loc_3028 = loc_2909 + 1;
    CursorTy loc_3029 = loc_3028 + 8;
    TagTyPacked tmpval_6231 = *(TagTyPacked *) tags_20_906_1522;
    CursorTy tmpcur_6232 = tags_20_906_1522 + 1;
    
    
  switch_6275:
    ;
    switch (tmpval_6231) {
        
      case 0:
        {
            CursorTy jump_3939 = tags_20_906_1522 + 1;
            
            *(TagTyPacked *) loc_2909 = 0;
            
            CursorTy writetag_4516 = loc_2909 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2911, jump_3939,
                                                   loc_2909, writetag_4516};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6237 = *(IntTy *) tmpcur_6232;
            CursorTy tmpcur_6238 = tmpcur_6232 + sizeof(IntTy);
            CursorTy jump_3941 = tmpcur_6232 + 8;
            IntTy fltPkd_1504_1526 = tmpval_6237 + inVal_21_907_1523;
            CursorCursorCursorCursorProd tmp_struct_7 =
                                          addValTag(end_r_2910, end_r_2911, loc_3029, tmpcur_6238, inVal_21_907_1523);
            CursorTy pvrtmp_6239 = tmp_struct_7.field0;
            CursorTy pvrtmp_6240 = tmp_struct_7.field1;
            CursorTy pvrtmp_6241 = tmp_struct_7.field2;
            CursorTy pvrtmp_6242 = tmp_struct_7.field3;
            
            *(TagTyPacked *) loc_2909 = 1;
            
            CursorTy writetag_4521 = loc_2909 + 1;
            
            *(IntTy *) writetag_4521 = fltPkd_1504_1526;
            
            CursorTy writecur_4522 = writetag_4521 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6239, pvrtmp_6240,
                                                   loc_2909, pvrtmp_6242};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6251 = *(CursorTy *) tmpcur_6232;
            CursorTy tmpaftercur_6252 = tmpcur_6232 + 8;
            CursorTy jump_4250 = tmpcur_6232 + 8;
            CursorCursorCursorCursorProd tmp_struct_8 =
                                          addValTag(end_r_2910, end_r_2911, loc_2909, tmpcur_6251, inVal_21_907_1523);
            CursorTy pvrtmp_6253 = tmp_struct_8.field0;
            CursorTy pvrtmp_6254 = tmp_struct_8.field1;
            CursorTy pvrtmp_6255 = tmp_struct_8.field2;
            CursorTy pvrtmp_6256 = tmp_struct_8.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6253, jump_4250,
                                                   pvrtmp_6255, pvrtmp_6256};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6263 = *(CursorTy *) tmpcur_6232;
            CursorTy tmpaftercur_6264 = tmpcur_6232 + 8;
            CursorCursorCursorCursorProd tmp_struct_9 =
                                          addValTag(end_r_2910, end_r_2911, loc_2909, tmpcur_6263, inVal_21_907_1523);
            CursorTy pvrtmp_6265 = tmp_struct_9.field0;
            CursorTy pvrtmp_6266 = tmp_struct_9.field1;
            CursorTy pvrtmp_6267 = tmp_struct_9.field2;
            CursorTy pvrtmp_6268 = tmp_struct_9.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6265, pvrtmp_6266,
                                                   pvrtmp_6267, pvrtmp_6268};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6231");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkCATList(CursorTy end_r_2913, CursorTy loc_2912,
                                 IntTy len_24_910_1528,
                                 IntTy tagLen_25_911_1529,
                                 IntTy strLen_26_912_1530)
{
    if (loc_2912 + 32 > end_r_2913) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2913);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2913 = chunk_end_18;
        *(TagTyPacked *) loc_2912 = 255;
        
        CursorTy redir = loc_2912 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2912 = chunk_start_17;
    }
    
    CursorTy loc_3037 = loc_2912 + 1;
    CursorTy loc_3038 = loc_3037 + 8;
    CursorTy loc_3039 = loc_3038 + 8;
    BoolTy fltIf_1506_1531 = len_24_910_1528 <= 0;
    
    if (fltIf_1506_1531) {
        *(TagTyPacked *) loc_2912 = 0;
        
        CursorTy writetag_4531 = loc_2912 + 1;
        
        return (CursorCursorCursorProd) {end_r_2913, loc_2912, writetag_4531};
    } else {
        CursorCursorCursorProd tmp_struct_13 =
                                mkContentText(end_r_2913, loc_3039, strLen_26_912_1530);
        CursorTy pvrtmp_6280 = tmp_struct_13.field0;
        CursorTy pvrtmp_6281 = tmp_struct_13.field1;
        CursorTy pvrtmp_6282 = tmp_struct_13.field2;
        IntTy fltAppE_1507_1533 = len_24_910_1528 - 1;
        CursorCursorCursorProd tmp_struct_14 =
                                mkCATList(pvrtmp_6280, pvrtmp_6282, fltAppE_1507_1533, tagLen_25_911_1529, strLen_26_912_1530);
        CursorTy pvrtmp_6287 = tmp_struct_14.field0;
        CursorTy pvrtmp_6288 = tmp_struct_14.field1;
        CursorTy pvrtmp_6289 = tmp_struct_14.field2;
        CursorCursorCursorProd tmp_struct_15 =
                                mkRandomTags(pvrtmp_6287, pvrtmp_6289, tagLen_25_911_1529);
        CursorTy pvrtmp_6294 = tmp_struct_15.field0;
        CursorTy pvrtmp_6295 = tmp_struct_15.field1;
        CursorTy pvrtmp_6296 = tmp_struct_15.field2;
        
        *(TagTyPacked *) loc_2912 = 23;
        
        CursorTy writetag_4536 = loc_2912 + 1;
        
        *(CursorTy *) writetag_4536 = pvrtmp_6282;
        
        CursorTy writecur_4537 = writetag_4536 + 8;
        
        *(CursorTy *) writecur_4537 = pvrtmp_6289;
        
        CursorTy writecur_4538 = writecur_4537 + 8;
        
        return (CursorCursorCursorProd) {pvrtmp_6294, loc_2912, pvrtmp_6296};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2915, CursorTy loc_2914,
                                IntTy len_179_1065_1536)
{
    if (loc_2914 + 32 > end_r_2915) {
        ChunkTy new_chunk_20 = alloc_chunk(end_r_2915);
        CursorTy chunk_start_21 = new_chunk_20.chunk_start;
        CursorTy chunk_end_22 = new_chunk_20.chunk_end;
        
        end_r_2915 = chunk_end_22;
        *(TagTyPacked *) loc_2914 = 255;
        
        CursorTy redir = loc_2914 + 1;
        
        *(CursorTy *) redir = chunk_start_21;
        loc_2914 = chunk_start_21;
    }
    
    CursorTy loc_3051 = loc_2914 + 1;
    CursorTy loc_3052 = loc_3051 + 8;
    BoolTy fltIf_1508_1537 = len_179_1065_1536 <= 0;
    
    if (fltIf_1508_1537) {
        *(TagTyPacked *) loc_2914 = 0;
        
        CursorTy writetag_4543 = loc_2914 + 1;
        
        return (CursorCursorCursorProd) {end_r_2915, loc_2914, writetag_4543};
    } else {
        IntTy fltPrm_1509_1538 = rand();
        IntTy randomChar_180_1066_1539 = fltPrm_1509_1538 % 128;
        IntTy fltAppE_1510_1540 = len_179_1065_1536 - 1;
        CursorCursorCursorProd tmp_struct_19 =
                                mkString(end_r_2915, loc_3052, fltAppE_1510_1540);
        CursorTy pvrtmp_6309 = tmp_struct_19.field0;
        CursorTy pvrtmp_6310 = tmp_struct_19.field1;
        CursorTy pvrtmp_6311 = tmp_struct_19.field2;
        
        *(TagTyPacked *) loc_2914 = 1;
        
        CursorTy writetag_4546 = loc_2914 + 1;
        
        *(IntTy *) writetag_4546 = randomChar_180_1066_1539;
        
        CursorTy writecur_4547 = writetag_4546 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6309, loc_2914, pvrtmp_6311};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2917, CursorTy loc_2916,
                                     IntTy n_193_1079_1542)
{
    if (loc_2916 + 32 > end_r_2917) {
        ChunkTy new_chunk_24 = alloc_chunk(end_r_2917);
        CursorTy chunk_start_25 = new_chunk_24.chunk_start;
        CursorTy chunk_end_26 = new_chunk_24.chunk_end;
        
        end_r_2917 = chunk_end_26;
        *(TagTyPacked *) loc_2916 = 255;
        
        CursorTy redir = loc_2916 + 1;
        
        *(CursorTy *) redir = chunk_start_25;
        loc_2916 = chunk_start_25;
    }
    
    CursorTy loc_3057 = loc_2916 + 1;
    CursorCursorCursorProd tmp_struct_23 =
                            mkString(end_r_2917, loc_3057, n_193_1079_1542);
    CursorTy pvrtmp_6320 = tmp_struct_23.field0;
    CursorTy pvrtmp_6321 = tmp_struct_23.field1;
    CursorTy pvrtmp_6322 = tmp_struct_23.field2;
    
    *(TagTyPacked *) loc_2916 = 1;
    
    CursorTy writetag_4551 = loc_2916 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_6320, loc_2916, pvrtmp_6322};
}
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2919, CursorTy loc_2918,
                                    IntTy len_318_1204_1544)
{
    if (loc_2918 + 32 > end_r_2919) {
        ChunkTy new_chunk_28 = alloc_chunk(end_r_2919);
        CursorTy chunk_start_29 = new_chunk_28.chunk_start;
        CursorTy chunk_end_30 = new_chunk_28.chunk_end;
        
        end_r_2919 = chunk_end_30;
        *(TagTyPacked *) loc_2918 = 255;
        
        CursorTy redir = loc_2918 + 1;
        
        *(CursorTy *) redir = chunk_start_29;
        loc_2918 = chunk_start_29;
    }
    
    CursorTy loc_3061 = loc_2918 + 1;
    CursorTy loc_3062 = loc_3061 + 8;
    BoolTy fltIf_1512_1545 = len_318_1204_1544 <= 0;
    
    if (fltIf_1512_1545) {
        *(TagTyPacked *) loc_2918 = 0;
        
        CursorTy writetag_4554 = loc_2918 + 1;
        
        return (CursorCursorCursorProd) {end_r_2919, loc_2918, writetag_4554};
    } else {
        IntTy fltAppE_1513_1547 = len_318_1204_1544 - 1;
        CursorCursorCursorProd tmp_struct_27 =
                                mkRandomTags(end_r_2919, loc_3062, fltAppE_1513_1547);
        CursorTy pvrtmp_6335 = tmp_struct_27.field0;
        CursorTy pvrtmp_6336 = tmp_struct_27.field1;
        CursorTy pvrtmp_6337 = tmp_struct_27.field2;
        
        *(TagTyPacked *) loc_2918 = 1;
        
        CursorTy writetag_4557 = loc_2918 + 1;
        
        *(IntTy *) writetag_4557 = 100;
        
        CursorTy writecur_4558 = writetag_4557 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6335, loc_2918, pvrtmp_6337};
    }
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2922,
                                          CursorTy end_r_2923,
                                          CursorTy loc_2921,
                                          CursorTy arg_622_1228_1549)
{
    if (loc_2921 + 32 > end_r_2923) {
        ChunkTy new_chunk_34 = alloc_chunk(end_r_2923);
        CursorTy chunk_start_35 = new_chunk_34.chunk_start;
        CursorTy chunk_end_36 = new_chunk_34.chunk_end;
        
        end_r_2923 = chunk_end_36;
        *(TagTyPacked *) loc_2921 = 255;
        
        CursorTy redir = loc_2921 + 1;
        
        *(CursorTy *) redir = chunk_start_35;
        loc_2921 = chunk_start_35;
    }
    
    CursorTy loc_3072 = loc_2921 + 1;
    CursorTy loc_3073 = loc_3072 + 8;
    TagTyPacked tmpval_6346 = *(TagTyPacked *) arg_622_1228_1549;
    CursorTy tmpcur_6347 = arg_622_1228_1549 + 1;
    
    
  switch_6390:
    ;
    switch (tmpval_6346) {
        
      case 0:
        {
            CursorTy jump_3951 = arg_622_1228_1549 + 1;
            
            *(TagTyPacked *) loc_2921 = 0;
            
            CursorTy writetag_4562 = loc_2921 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2923, jump_3951,
                                                   loc_2921, writetag_4562};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6352 = *(IntTy *) tmpcur_6347;
            CursorTy tmpcur_6353 = tmpcur_6347 + sizeof(IntTy);
            CursorTy jump_3953 = tmpcur_6347 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_String(end_r_2922, end_r_2923, loc_3073, tmpcur_6353);
            CursorTy pvrtmp_6354 = tmp_struct_31.field0;
            CursorTy pvrtmp_6355 = tmp_struct_31.field1;
            CursorTy pvrtmp_6356 = tmp_struct_31.field2;
            CursorTy pvrtmp_6357 = tmp_struct_31.field3;
            
            *(TagTyPacked *) loc_2921 = 1;
            
            CursorTy writetag_4567 = loc_2921 + 1;
            
            *(IntTy *) writetag_4567 = tmpval_6352;
            
            CursorTy writecur_4568 = writetag_4567 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6354, pvrtmp_6355,
                                                   loc_2921, pvrtmp_6357};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6366 = *(CursorTy *) tmpcur_6347;
            CursorTy tmpaftercur_6367 = tmpcur_6347 + 8;
            CursorTy jump_4256 = tmpcur_6347 + 8;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_String(end_r_2922, end_r_2923, loc_2921, tmpcur_6366);
            CursorTy pvrtmp_6368 = tmp_struct_32.field0;
            CursorTy pvrtmp_6369 = tmp_struct_32.field1;
            CursorTy pvrtmp_6370 = tmp_struct_32.field2;
            CursorTy pvrtmp_6371 = tmp_struct_32.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6368, jump_4256,
                                                   pvrtmp_6370, pvrtmp_6371};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6378 = *(CursorTy *) tmpcur_6347;
            CursorTy tmpaftercur_6379 = tmpcur_6347 + 8;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_String(end_r_2922, end_r_2923, loc_2921, tmpcur_6378);
            CursorTy pvrtmp_6380 = tmp_struct_33.field0;
            CursorTy pvrtmp_6381 = tmp_struct_33.field1;
            CursorTy pvrtmp_6382 = tmp_struct_33.field2;
            CursorTy pvrtmp_6383 = tmp_struct_33.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6380, pvrtmp_6381,
                                                   pvrtmp_6382, pvrtmp_6383};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6346");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2926,
                                                       CursorTy end_r_2927,
                                                       CursorTy loc_2925,
                                                       CursorTy arg_627_1233_1554)
{
    CursorTy loc_3085 = loc_2925 + 1;
    CursorTy loc_3086 = loc_3085 + 8;
    TagTyPacked tmpval_6391 = *(TagTyPacked *) arg_627_1233_1554;
    CursorTy tmpcur_6392 = arg_627_1233_1554 + 1;
    
    
  switch_6435:
    ;
    switch (tmpval_6391) {
        
      case 0:
        {
            CursorTy jump_3956 = arg_627_1233_1554 + 1;
            
            *(TagTyPacked *) loc_2925 = 0;
            
            CursorTy writetag_4578 = loc_2925 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2927, jump_3956,
                                                   loc_2925, writetag_4578};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6397 = *(IntTy *) tmpcur_6392;
            CursorTy tmpcur_6398 = tmpcur_6392 + sizeof(IntTy);
            CursorTy jump_3958 = tmpcur_6392 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_String(end_r_2926, end_r_2927, loc_3086, tmpcur_6398);
            CursorTy pvrtmp_6399 = tmp_struct_37.field0;
            CursorTy pvrtmp_6400 = tmp_struct_37.field1;
            CursorTy pvrtmp_6401 = tmp_struct_37.field2;
            CursorTy pvrtmp_6402 = tmp_struct_37.field3;
            
            *(TagTyPacked *) loc_2925 = 1;
            
            CursorTy writetag_4583 = loc_2925 + 1;
            
            *(IntTy *) writetag_4583 = tmpval_6397;
            
            CursorTy writecur_4584 = writetag_4583 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6399, pvrtmp_6400,
                                                   loc_2925, pvrtmp_6402};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6411 = *(CursorTy *) tmpcur_6392;
            CursorTy tmpaftercur_6412 = tmpcur_6392 + 8;
            CursorTy jump_4262 = tmpcur_6392 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_String(end_r_2926, end_r_2927, loc_2925, tmpcur_6411);
            CursorTy pvrtmp_6413 = tmp_struct_38.field0;
            CursorTy pvrtmp_6414 = tmp_struct_38.field1;
            CursorTy pvrtmp_6415 = tmp_struct_38.field2;
            CursorTy pvrtmp_6416 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6413, jump_4262,
                                                   pvrtmp_6415, pvrtmp_6416};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6423 = *(CursorTy *) tmpcur_6392;
            CursorTy tmpaftercur_6424 = tmpcur_6392 + 8;
            CursorCursorCursorCursorProd tmp_struct_39 =
                                          _copy_without_ptrs_String(end_r_2926, end_r_2927, loc_2925, tmpcur_6423);
            CursorTy pvrtmp_6425 = tmp_struct_39.field0;
            CursorTy pvrtmp_6426 = tmp_struct_39.field1;
            CursorTy pvrtmp_6427 = tmp_struct_39.field2;
            CursorTy pvrtmp_6428 = tmp_struct_39.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6425, pvrtmp_6426,
                                                   pvrtmp_6427, pvrtmp_6428};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6391");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2929, CursorTy arg_632_1238_1559)
{
    TagTyPacked tmpval_6436 = *(TagTyPacked *) arg_632_1238_1559;
    CursorTy tmpcur_6437 = arg_632_1238_1559 + 1;
    
    
  switch_6447:
    ;
    switch (tmpval_6436) {
        
      case 0:
        {
            CursorTy jump_3961 = arg_632_1238_1559 + 1;
            
            return (CursorProd) {jump_3961};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6438 = *(IntTy *) tmpcur_6437;
            CursorTy tmpcur_6439 = tmpcur_6437 + sizeof(IntTy);
            CursorTy jump_3963 = tmpcur_6437 + 8;
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2929, tmpcur_6439);
            CursorTy pvrtmp_6440 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_6440};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6441 = *(CursorTy *) tmpcur_6437;
            CursorTy tmpaftercur_6442 = tmpcur_6437 + 8;
            CursorTy jump_4268 = tmpcur_6437 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_String(end_r_2929, tmpcur_6441);
            CursorTy pvrtmp_6443 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_4268};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6444 = *(CursorTy *) tmpcur_6437;
            CursorTy tmpaftercur_6445 = tmpcur_6437 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_String(end_r_2929, tmpcur_6444);
            CursorTy pvrtmp_6446 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_6446};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6436");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2931, CursorTy arg_637_1242_1563)
{
    TagTyPacked tmpval_6448 = *(TagTyPacked *) arg_637_1242_1563;
    CursorTy tmpcur_6449 = arg_637_1242_1563 + 1;
    
    
  switch_6459:
    ;
    switch (tmpval_6448) {
        
      case 0:
        {
            CursorTy jump_3966 = arg_637_1242_1563 + 1;
            unsigned char wildcard_638_1243_1564 = print_symbol(6137);
            unsigned char wildcard_639_1244_1565 = print_symbol(6129);
            
            return (CursorProd) {jump_3966};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6450 = *(IntTy *) tmpcur_6449;
            CursorTy tmpcur_6451 = tmpcur_6449 + sizeof(IntTy);
            CursorTy jump_3968 = tmpcur_6449 + 8;
            unsigned char wildcard_644_1247_1568 = print_symbol(6138);
            unsigned char y_642_1248_1569 = printf("%lld", tmpval_6450);
            CursorProd tmp_struct_43 =  _print_String(end_r_2931, tmpcur_6451);
            CursorTy pvrtmp_6452 = tmp_struct_43.field0;
            unsigned char wildcard_645_1250_1571 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_6452};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6453 = *(CursorTy *) tmpcur_6449;
            CursorTy tmpaftercur_6454 = tmpcur_6449 + 8;
            CursorTy jump_4274 = tmpcur_6449 + 8;
            unsigned char wildcard_4277 = print_symbol(6146);
            CursorProd tmp_struct_44 =  _print_String(end_r_2931, tmpcur_6453);
            CursorTy pvrtmp_6455 = tmp_struct_44.field0;
            
            return (CursorProd) {jump_4274};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6456 = *(CursorTy *) tmpcur_6449;
            CursorTy tmpaftercur_6457 = tmpcur_6449 + 8;
            unsigned char wildcard_4277 = print_symbol(6145);
            CursorProd tmp_struct_45 =  _print_String(end_r_2931, tmpcur_6456);
            CursorTy pvrtmp_6458 = tmp_struct_45.field0;
            
            return (CursorProd) {pvrtmp_6458};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6448");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2934,
                                           CursorTy end_r_2935,
                                           CursorTy loc_2933,
                                           CursorTy arg_646_1251_1572)
{
    if (loc_2933 + 32 > end_r_2935) {
        ChunkTy new_chunk_50 = alloc_chunk(end_r_2935);
        CursorTy chunk_start_51 = new_chunk_50.chunk_start;
        CursorTy chunk_end_52 = new_chunk_50.chunk_end;
        
        end_r_2935 = chunk_end_52;
        *(TagTyPacked *) loc_2933 = 255;
        
        CursorTy redir = loc_2933 + 1;
        
        *(CursorTy *) redir = chunk_start_51;
        loc_2933 = chunk_start_51;
    }
    
    TagTyPacked tmpval_6460 = *(TagTyPacked *) arg_646_1251_1572;
    CursorTy tmpcur_6461 = arg_646_1251_1572 + 1;
    
    
  switch_6510:
    ;
    switch (tmpval_6460) {
        
      case 0:
        {
            CursorTy loc_3108 = loc_2933 + 1;
            CursorCursorCursorCursorProd tmp_struct_46 =
                                          _copy_String(end_r_2934, end_r_2935, loc_3108, tmpcur_6461);
            CursorTy pvrtmp_6462 = tmp_struct_46.field0;
            CursorTy pvrtmp_6463 = tmp_struct_46.field1;
            CursorTy pvrtmp_6464 = tmp_struct_46.field2;
            CursorTy pvrtmp_6465 = tmp_struct_46.field3;
            
            *(TagTyPacked *) loc_2933 = 0;
            
            CursorTy writetag_4615 = loc_2933 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6462, pvrtmp_6463,
                                                   loc_2933, pvrtmp_6465};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3114 = loc_2933 + 1;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_String(end_r_2934, end_r_2935, loc_3114, tmpcur_6461);
            CursorTy pvrtmp_6474 = tmp_struct_47.field0;
            CursorTy pvrtmp_6475 = tmp_struct_47.field1;
            CursorTy pvrtmp_6476 = tmp_struct_47.field2;
            CursorTy pvrtmp_6477 = tmp_struct_47.field3;
            
            *(TagTyPacked *) loc_2933 = 1;
            
            CursorTy writetag_4620 = loc_2933 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6474, pvrtmp_6475,
                                                   loc_2933, pvrtmp_6477};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6486 = *(CursorTy *) tmpcur_6461;
            CursorTy tmpaftercur_6487 = tmpcur_6461 + 8;
            CursorTy jump_4280 = tmpcur_6461 + 8;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Content(end_r_2934, end_r_2935, loc_2933, tmpcur_6486);
            CursorTy pvrtmp_6488 = tmp_struct_48.field0;
            CursorTy pvrtmp_6489 = tmp_struct_48.field1;
            CursorTy pvrtmp_6490 = tmp_struct_48.field2;
            CursorTy pvrtmp_6491 = tmp_struct_48.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6488, jump_4280,
                                                   pvrtmp_6490, pvrtmp_6491};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6498 = *(CursorTy *) tmpcur_6461;
            CursorTy tmpaftercur_6499 = tmpcur_6461 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Content(end_r_2934, end_r_2935, loc_2933, tmpcur_6498);
            CursorTy pvrtmp_6500 = tmp_struct_49.field0;
            CursorTy pvrtmp_6501 = tmp_struct_49.field1;
            CursorTy pvrtmp_6502 = tmp_struct_49.field2;
            CursorTy pvrtmp_6503 = tmp_struct_49.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6500, pvrtmp_6501,
                                                   pvrtmp_6502, pvrtmp_6503};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6460");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2938,
                                                        CursorTy end_r_2939,
                                                        CursorTy loc_2937,
                                                        CursorTy arg_651_1256_1577)
{
    TagTyPacked tmpval_6511 = *(TagTyPacked *) arg_651_1256_1577;
    CursorTy tmpcur_6512 = arg_651_1256_1577 + 1;
    
    
  switch_6561:
    ;
    switch (tmpval_6511) {
        
      case 0:
        {
            CursorTy loc_3122 = loc_2937 + 1;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_without_ptrs_String(end_r_2938, end_r_2939, loc_3122, tmpcur_6512);
            CursorTy pvrtmp_6513 = tmp_struct_53.field0;
            CursorTy pvrtmp_6514 = tmp_struct_53.field1;
            CursorTy pvrtmp_6515 = tmp_struct_53.field2;
            CursorTy pvrtmp_6516 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2937 = 0;
            
            CursorTy writetag_4631 = loc_2937 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6513, pvrtmp_6514,
                                                   loc_2937, pvrtmp_6516};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3128 = loc_2937 + 1;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_without_ptrs_String(end_r_2938, end_r_2939, loc_3128, tmpcur_6512);
            CursorTy pvrtmp_6525 = tmp_struct_54.field0;
            CursorTy pvrtmp_6526 = tmp_struct_54.field1;
            CursorTy pvrtmp_6527 = tmp_struct_54.field2;
            CursorTy pvrtmp_6528 = tmp_struct_54.field3;
            
            *(TagTyPacked *) loc_2937 = 1;
            
            CursorTy writetag_4636 = loc_2937 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6525, pvrtmp_6526,
                                                   loc_2937, pvrtmp_6528};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6537 = *(CursorTy *) tmpcur_6512;
            CursorTy tmpaftercur_6538 = tmpcur_6512 + 8;
            CursorTy jump_4286 = tmpcur_6512 + 8;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_without_ptrs_Content(end_r_2938, end_r_2939, loc_2937, tmpcur_6537);
            CursorTy pvrtmp_6539 = tmp_struct_55.field0;
            CursorTy pvrtmp_6540 = tmp_struct_55.field1;
            CursorTy pvrtmp_6541 = tmp_struct_55.field2;
            CursorTy pvrtmp_6542 = tmp_struct_55.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6539, jump_4286,
                                                   pvrtmp_6541, pvrtmp_6542};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6549 = *(CursorTy *) tmpcur_6512;
            CursorTy tmpaftercur_6550 = tmpcur_6512 + 8;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_without_ptrs_Content(end_r_2938, end_r_2939, loc_2937, tmpcur_6549);
            CursorTy pvrtmp_6551 = tmp_struct_56.field0;
            CursorTy pvrtmp_6552 = tmp_struct_56.field1;
            CursorTy pvrtmp_6553 = tmp_struct_56.field2;
            CursorTy pvrtmp_6554 = tmp_struct_56.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6551, pvrtmp_6552,
                                                   pvrtmp_6553, pvrtmp_6554};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6511");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2941, CursorTy arg_656_1261_1582)
{
    TagTyPacked tmpval_6562 = *(TagTyPacked *) arg_656_1261_1582;
    CursorTy tmpcur_6563 = arg_656_1261_1582 + 1;
    
    
  switch_6572:
    ;
    switch (tmpval_6562) {
        
      case 0:
        {
            CursorProd tmp_struct_57 =
                        _traverse_String(end_r_2941, tmpcur_6563);
            CursorTy pvrtmp_6564 = tmp_struct_57.field0;
            
            return (CursorProd) {pvrtmp_6564};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_58 =
                        _traverse_String(end_r_2941, tmpcur_6563);
            CursorTy pvrtmp_6565 = tmp_struct_58.field0;
            
            return (CursorProd) {pvrtmp_6565};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6566 = *(CursorTy *) tmpcur_6563;
            CursorTy tmpaftercur_6567 = tmpcur_6563 + 8;
            CursorTy jump_4292 = tmpcur_6563 + 8;
            CursorProd tmp_struct_59 =
                        _traverse_Content(end_r_2941, tmpcur_6566);
            CursorTy pvrtmp_6568 = tmp_struct_59.field0;
            
            return (CursorProd) {jump_4292};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6569 = *(CursorTy *) tmpcur_6563;
            CursorTy tmpaftercur_6570 = tmpcur_6563 + 8;
            CursorProd tmp_struct_60 =
                        _traverse_Content(end_r_2941, tmpcur_6569);
            CursorTy pvrtmp_6571 = tmp_struct_60.field0;
            
            return (CursorProd) {pvrtmp_6571};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6562");
            exit(1);
        }
    }
}
CursorProd _print_Content(CursorTy end_r_2943, CursorTy arg_661_1266_1587)
{
    TagTyPacked tmpval_6573 = *(TagTyPacked *) arg_661_1266_1587;
    CursorTy tmpcur_6574 = arg_661_1266_1587 + 1;
    
    
  switch_6583:
    ;
    switch (tmpval_6573) {
        
      case 0:
        {
            unsigned char wildcard_664_1268_1589 = print_symbol(6136);
            CursorProd tmp_struct_61 =  _print_String(end_r_2943, tmpcur_6574);
            CursorTy pvrtmp_6575 = tmp_struct_61.field0;
            unsigned char wildcard_665_1270_1591 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_6575};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_668_1272_1593 = print_symbol(6130);
            CursorProd tmp_struct_62 =  _print_String(end_r_2943, tmpcur_6574);
            CursorTy pvrtmp_6576 = tmp_struct_62.field0;
            unsigned char wildcard_669_1274_1595 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_6576};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6577 = *(CursorTy *) tmpcur_6574;
            CursorTy tmpaftercur_6578 = tmpcur_6574 + 8;
            CursorTy jump_4298 = tmpcur_6574 + 8;
            unsigned char wildcard_4301 = print_symbol(6146);
            CursorProd tmp_struct_63 =  _print_Content(end_r_2943, tmpcur_6577);
            CursorTy pvrtmp_6579 = tmp_struct_63.field0;
            
            return (CursorProd) {jump_4298};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6580 = *(CursorTy *) tmpcur_6574;
            CursorTy tmpaftercur_6581 = tmpcur_6574 + 8;
            unsigned char wildcard_4301 = print_symbol(6145);
            CursorProd tmp_struct_64 =  _print_Content(end_r_2943, tmpcur_6580);
            CursorTy pvrtmp_6582 = tmp_struct_64.field0;
            
            return (CursorProd) {pvrtmp_6582};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6573");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2946, CursorTy end_r_2947,
                                       CursorTy loc_2945,
                                       CursorTy arg_670_1275_1596)
{
    if (loc_2945 + 32 > end_r_2947) {
        ChunkTy new_chunk_89 = alloc_chunk(end_r_2947);
        CursorTy chunk_start_90 = new_chunk_89.chunk_start;
        CursorTy chunk_end_91 = new_chunk_89.chunk_end;
        
        end_r_2947 = chunk_end_91;
        *(TagTyPacked *) loc_2945 = 255;
        
        CursorTy redir = loc_2945 + 1;
        
        *(CursorTy *) redir = chunk_start_90;
        loc_2945 = chunk_start_90;
    }
    
    CursorTy loc_3158 = loc_2945 + 1;
    CursorTy loc_3159 = loc_3158 + 8;
    CursorTy loc_3174 = loc_2945 + 1;
    CursorTy loc_3175 = loc_3174 + 8;
    CursorTy loc_3195 = loc_2945 + 1;
    CursorTy loc_3196 = loc_3195 + 8;
    CursorTy loc_3197 = loc_3196 + 8;
    CursorTy loc_3221 = loc_2945 + 1;
    CursorTy loc_3222 = loc_3221 + 8;
    CursorTy loc_3223 = loc_3222 + 8;
    CursorTy loc_3247 = loc_2945 + 1;
    CursorTy loc_3248 = loc_3247 + 8;
    CursorTy loc_3249 = loc_3248 + 8;
    CursorTy loc_3273 = loc_2945 + 1;
    CursorTy loc_3274 = loc_3273 + 8;
    CursorTy loc_3275 = loc_3274 + 8;
    CursorTy loc_3299 = loc_2945 + 1;
    CursorTy loc_3300 = loc_3299 + 8;
    CursorTy loc_3301 = loc_3300 + 8;
    CursorTy loc_3325 = loc_2945 + 1;
    CursorTy loc_3326 = loc_3325 + 8;
    CursorTy loc_3327 = loc_3326 + 8;
    TagTyPacked tmpval_6584 = *(TagTyPacked *) arg_670_1275_1596;
    CursorTy tmpcur_6585 = arg_670_1275_1596 + 1;
    
    
  switch_6850:
    ;
    switch (tmpval_6584) {
        
      case 0:
        {
            CursorTy jump_3987 = arg_670_1275_1596 + 1;
            
            *(TagTyPacked *) loc_2945 = 0;
            
            CursorTy writetag_4666 = loc_2945 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2947, jump_3987,
                                                   loc_2945, writetag_4666};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6590 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6591 = tmpcur_6585 + 8;
            CursorTy jump_3989 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Content(end_r_2946, end_r_2947, loc_3159, tmpaftercur_6591);
            CursorTy pvrtmp_6592 = tmp_struct_65.field0;
            CursorTy pvrtmp_6593 = tmp_struct_65.field1;
            CursorTy pvrtmp_6594 = tmp_struct_65.field2;
            CursorTy pvrtmp_6595 = tmp_struct_65.field3;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Adt(end_r_2946, pvrtmp_6592, pvrtmp_6595, tmpcur_6590);
            CursorTy pvrtmp_6600 = tmp_struct_66.field0;
            CursorTy pvrtmp_6601 = tmp_struct_66.field1;
            CursorTy pvrtmp_6602 = tmp_struct_66.field2;
            CursorTy pvrtmp_6603 = tmp_struct_66.field3;
            
            *(TagTyPacked *) loc_2945 = 9;
            
            CursorTy writetag_4672 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4672 = pvrtmp_6595;
            
            CursorTy writecur_4673 = writetag_4672 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6600, pvrtmp_6601,
                                                   loc_2945, pvrtmp_6603};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6612 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6613 = tmpcur_6585 + 8;
            CursorTy jump_3993 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2946, end_r_2947, loc_3175, tmpaftercur_6613);
            CursorTy pvrtmp_6614 = tmp_struct_67.field0;
            CursorTy pvrtmp_6615 = tmp_struct_67.field1;
            CursorTy pvrtmp_6616 = tmp_struct_67.field2;
            CursorTy pvrtmp_6617 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Content(end_r_2946, pvrtmp_6614, pvrtmp_6617, tmpcur_6612);
            CursorTy pvrtmp_6622 = tmp_struct_68.field0;
            CursorTy pvrtmp_6623 = tmp_struct_68.field1;
            CursorTy pvrtmp_6624 = tmp_struct_68.field2;
            CursorTy pvrtmp_6625 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2945 = 11;
            
            CursorTy writetag_4681 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4681 = pvrtmp_6617;
            
            CursorTy writecur_4682 = writetag_4681 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6622, pvrtmp_6623,
                                                   loc_2945, pvrtmp_6625};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6634 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6635 = tmpcur_6585 + 8;
            CursorTy tmpcur_6636 = *(CursorTy *) tmpaftercur_6635;
            CursorTy tmpaftercur_6637 = tmpaftercur_6635 + 8;
            CursorTy jump_3998 = tmpaftercur_6635 + 8;
            CursorTy jump_3997 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Tags(end_r_2946, end_r_2947, loc_3197, tmpaftercur_6637);
            CursorTy pvrtmp_6638 = tmp_struct_69.field0;
            CursorTy pvrtmp_6639 = tmp_struct_69.field1;
            CursorTy pvrtmp_6640 = tmp_struct_69.field2;
            CursorTy pvrtmp_6641 = tmp_struct_69.field3;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Content(end_r_2946, pvrtmp_6638, pvrtmp_6641, tmpcur_6634);
            CursorTy pvrtmp_6646 = tmp_struct_70.field0;
            CursorTy pvrtmp_6647 = tmp_struct_70.field1;
            CursorTy pvrtmp_6648 = tmp_struct_70.field2;
            CursorTy pvrtmp_6649 = tmp_struct_70.field3;
            CursorCursorCursorCursorProd tmp_struct_71 =
                                          _copy_Adt(end_r_2946, pvrtmp_6646, pvrtmp_6649, tmpcur_6636);
            CursorTy pvrtmp_6654 = tmp_struct_71.field0;
            CursorTy pvrtmp_6655 = tmp_struct_71.field1;
            CursorTy pvrtmp_6656 = tmp_struct_71.field2;
            CursorTy pvrtmp_6657 = tmp_struct_71.field3;
            
            *(TagTyPacked *) loc_2945 = 13;
            
            CursorTy writetag_4692 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4692 = pvrtmp_6641;
            
            CursorTy writecur_4693 = writetag_4692 + 8;
            
            *(CursorTy *) writecur_4693 = pvrtmp_6649;
            
            CursorTy writecur_4694 = writecur_4693 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6654, pvrtmp_6655,
                                                   loc_2945, pvrtmp_6657};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6666 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6667 = tmpcur_6585 + 8;
            CursorTy tmpcur_6668 = *(CursorTy *) tmpaftercur_6667;
            CursorTy tmpaftercur_6669 = tmpaftercur_6667 + 8;
            CursorTy jump_4004 = tmpaftercur_6667 + 8;
            CursorTy jump_4003 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_72 =
                                          _copy_Adt(end_r_2946, end_r_2947, loc_3223, tmpaftercur_6669);
            CursorTy pvrtmp_6670 = tmp_struct_72.field0;
            CursorTy pvrtmp_6671 = tmp_struct_72.field1;
            CursorTy pvrtmp_6672 = tmp_struct_72.field2;
            CursorTy pvrtmp_6673 = tmp_struct_72.field3;
            CursorCursorCursorCursorProd tmp_struct_73 =
                                          _copy_Content(end_r_2946, pvrtmp_6670, pvrtmp_6673, tmpcur_6666);
            CursorTy pvrtmp_6678 = tmp_struct_73.field0;
            CursorTy pvrtmp_6679 = tmp_struct_73.field1;
            CursorTy pvrtmp_6680 = tmp_struct_73.field2;
            CursorTy pvrtmp_6681 = tmp_struct_73.field3;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_Tags(end_r_2946, pvrtmp_6678, pvrtmp_6681, tmpcur_6668);
            CursorTy pvrtmp_6686 = tmp_struct_74.field0;
            CursorTy pvrtmp_6687 = tmp_struct_74.field1;
            CursorTy pvrtmp_6688 = tmp_struct_74.field2;
            CursorTy pvrtmp_6689 = tmp_struct_74.field3;
            
            *(TagTyPacked *) loc_2945 = 15;
            
            CursorTy writetag_4705 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4705 = pvrtmp_6673;
            
            CursorTy writecur_4706 = writetag_4705 + 8;
            
            *(CursorTy *) writecur_4706 = pvrtmp_6681;
            
            CursorTy writecur_4707 = writecur_4706 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6686, pvrtmp_6687,
                                                   loc_2945, pvrtmp_6689};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6698 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6699 = tmpcur_6585 + 8;
            CursorTy tmpcur_6700 = *(CursorTy *) tmpaftercur_6699;
            CursorTy tmpaftercur_6701 = tmpaftercur_6699 + 8;
            CursorTy jump_4010 = tmpaftercur_6699 + 8;
            CursorTy jump_4009 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_Tags(end_r_2946, end_r_2947, loc_3249, tmpaftercur_6701);
            CursorTy pvrtmp_6702 = tmp_struct_75.field0;
            CursorTy pvrtmp_6703 = tmp_struct_75.field1;
            CursorTy pvrtmp_6704 = tmp_struct_75.field2;
            CursorTy pvrtmp_6705 = tmp_struct_75.field3;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_Adt(end_r_2946, pvrtmp_6702, pvrtmp_6705, tmpcur_6698);
            CursorTy pvrtmp_6710 = tmp_struct_76.field0;
            CursorTy pvrtmp_6711 = tmp_struct_76.field1;
            CursorTy pvrtmp_6712 = tmp_struct_76.field2;
            CursorTy pvrtmp_6713 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_Content(end_r_2946, pvrtmp_6710, pvrtmp_6713, tmpcur_6700);
            CursorTy pvrtmp_6718 = tmp_struct_77.field0;
            CursorTy pvrtmp_6719 = tmp_struct_77.field1;
            CursorTy pvrtmp_6720 = tmp_struct_77.field2;
            CursorTy pvrtmp_6721 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2945 = 17;
            
            CursorTy writetag_4718 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4718 = pvrtmp_6705;
            
            CursorTy writecur_4719 = writetag_4718 + 8;
            
            *(CursorTy *) writecur_4719 = pvrtmp_6713;
            
            CursorTy writecur_4720 = writecur_4719 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6718, pvrtmp_6719,
                                                   loc_2945, pvrtmp_6721};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6730 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6731 = tmpcur_6585 + 8;
            CursorTy tmpcur_6732 = *(CursorTy *) tmpaftercur_6731;
            CursorTy tmpaftercur_6733 = tmpaftercur_6731 + 8;
            CursorTy jump_4016 = tmpaftercur_6731 + 8;
            CursorTy jump_4015 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_Adt(end_r_2946, end_r_2947, loc_3275, tmpaftercur_6733);
            CursorTy pvrtmp_6734 = tmp_struct_78.field0;
            CursorTy pvrtmp_6735 = tmp_struct_78.field1;
            CursorTy pvrtmp_6736 = tmp_struct_78.field2;
            CursorTy pvrtmp_6737 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_Tags(end_r_2946, pvrtmp_6734, pvrtmp_6737, tmpcur_6730);
            CursorTy pvrtmp_6742 = tmp_struct_79.field0;
            CursorTy pvrtmp_6743 = tmp_struct_79.field1;
            CursorTy pvrtmp_6744 = tmp_struct_79.field2;
            CursorTy pvrtmp_6745 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_Content(end_r_2946, pvrtmp_6742, pvrtmp_6745, tmpcur_6732);
            CursorTy pvrtmp_6750 = tmp_struct_80.field0;
            CursorTy pvrtmp_6751 = tmp_struct_80.field1;
            CursorTy pvrtmp_6752 = tmp_struct_80.field2;
            CursorTy pvrtmp_6753 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2945 = 19;
            
            CursorTy writetag_4731 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4731 = pvrtmp_6737;
            
            CursorTy writecur_4732 = writetag_4731 + 8;
            
            *(CursorTy *) writecur_4732 = pvrtmp_6745;
            
            CursorTy writecur_4733 = writecur_4732 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6750, pvrtmp_6751,
                                                   loc_2945, pvrtmp_6753};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6762 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6763 = tmpcur_6585 + 8;
            CursorTy tmpcur_6764 = *(CursorTy *) tmpaftercur_6763;
            CursorTy tmpaftercur_6765 = tmpaftercur_6763 + 8;
            CursorTy jump_4022 = tmpaftercur_6763 + 8;
            CursorTy jump_4021 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_Content(end_r_2946, end_r_2947, loc_3301, tmpaftercur_6765);
            CursorTy pvrtmp_6766 = tmp_struct_81.field0;
            CursorTy pvrtmp_6767 = tmp_struct_81.field1;
            CursorTy pvrtmp_6768 = tmp_struct_81.field2;
            CursorTy pvrtmp_6769 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_Tags(end_r_2946, pvrtmp_6766, pvrtmp_6769, tmpcur_6762);
            CursorTy pvrtmp_6774 = tmp_struct_82.field0;
            CursorTy pvrtmp_6775 = tmp_struct_82.field1;
            CursorTy pvrtmp_6776 = tmp_struct_82.field2;
            CursorTy pvrtmp_6777 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_Adt(end_r_2946, pvrtmp_6774, pvrtmp_6777, tmpcur_6764);
            CursorTy pvrtmp_6782 = tmp_struct_83.field0;
            CursorTy pvrtmp_6783 = tmp_struct_83.field1;
            CursorTy pvrtmp_6784 = tmp_struct_83.field2;
            CursorTy pvrtmp_6785 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2945 = 21;
            
            CursorTy writetag_4744 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4744 = pvrtmp_6769;
            
            CursorTy writecur_4745 = writetag_4744 + 8;
            
            *(CursorTy *) writecur_4745 = pvrtmp_6777;
            
            CursorTy writecur_4746 = writecur_4745 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6782, pvrtmp_6783,
                                                   loc_2945, pvrtmp_6785};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6794 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6795 = tmpcur_6585 + 8;
            CursorTy tmpcur_6796 = *(CursorTy *) tmpaftercur_6795;
            CursorTy tmpaftercur_6797 = tmpaftercur_6795 + 8;
            CursorTy jump_4028 = tmpaftercur_6795 + 8;
            CursorTy jump_4027 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_Content(end_r_2946, end_r_2947, loc_3327, tmpaftercur_6797);
            CursorTy pvrtmp_6798 = tmp_struct_84.field0;
            CursorTy pvrtmp_6799 = tmp_struct_84.field1;
            CursorTy pvrtmp_6800 = tmp_struct_84.field2;
            CursorTy pvrtmp_6801 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_Adt(end_r_2946, pvrtmp_6798, pvrtmp_6801, tmpcur_6794);
            CursorTy pvrtmp_6806 = tmp_struct_85.field0;
            CursorTy pvrtmp_6807 = tmp_struct_85.field1;
            CursorTy pvrtmp_6808 = tmp_struct_85.field2;
            CursorTy pvrtmp_6809 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_Tags(end_r_2946, pvrtmp_6806, pvrtmp_6809, tmpcur_6796);
            CursorTy pvrtmp_6814 = tmp_struct_86.field0;
            CursorTy pvrtmp_6815 = tmp_struct_86.field1;
            CursorTy pvrtmp_6816 = tmp_struct_86.field2;
            CursorTy pvrtmp_6817 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2945 = 23;
            
            CursorTy writetag_4757 = loc_2945 + 1;
            
            *(CursorTy *) writetag_4757 = pvrtmp_6801;
            
            CursorTy writecur_4758 = writetag_4757 + 8;
            
            *(CursorTy *) writecur_4758 = pvrtmp_6809;
            
            CursorTy writecur_4759 = writecur_4758 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6814, pvrtmp_6815,
                                                   loc_2945, pvrtmp_6817};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6826 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6827 = tmpcur_6585 + 8;
            CursorTy jump_4304 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_Adt(end_r_2946, end_r_2947, loc_2945, tmpcur_6826);
            CursorTy pvrtmp_6828 = tmp_struct_87.field0;
            CursorTy pvrtmp_6829 = tmp_struct_87.field1;
            CursorTy pvrtmp_6830 = tmp_struct_87.field2;
            CursorTy pvrtmp_6831 = tmp_struct_87.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6828, jump_4304,
                                                   pvrtmp_6830, pvrtmp_6831};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6838 = *(CursorTy *) tmpcur_6585;
            CursorTy tmpaftercur_6839 = tmpcur_6585 + 8;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_Adt(end_r_2946, end_r_2947, loc_2945, tmpcur_6838);
            CursorTy pvrtmp_6840 = tmp_struct_88.field0;
            CursorTy pvrtmp_6841 = tmp_struct_88.field1;
            CursorTy pvrtmp_6842 = tmp_struct_88.field2;
            CursorTy pvrtmp_6843 = tmp_struct_88.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6840, pvrtmp_6841,
                                                   pvrtmp_6842, pvrtmp_6843};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6584");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2950,
                                                    CursorTy end_r_2951,
                                                    CursorTy loc_2949,
                                                    CursorTy arg_715_1320_1641)
{
    TagTyPacked tmpval_6851 = *(TagTyPacked *) arg_715_1320_1641;
    CursorTy tmpcur_6852 = arg_715_1320_1641 + 1;
    
    
  switch_7117:
    ;
    switch (tmpval_6851) {
        
      case 0:
        {
            CursorTy jump_4033 = arg_715_1320_1641 + 1;
            
            *(TagTyPacked *) loc_2949 = 0;
            
            CursorTy writetag_4771 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2951, jump_4033,
                                                   loc_2949, writetag_4771};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6857 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_6858 = tmpcur_6852 + 8;
            CursorTy jump_4035 = tmpcur_6852 + 8;
            CursorTy loc_3349 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Content(end_r_2950, end_r_2951, loc_3349, tmpaftercur_6858);
            CursorTy pvrtmp_6859 = tmp_struct_92.field0;
            CursorTy pvrtmp_6860 = tmp_struct_92.field1;
            CursorTy pvrtmp_6861 = tmp_struct_92.field2;
            CursorTy pvrtmp_6862 = tmp_struct_92.field3;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Adt(end_r_2950, pvrtmp_6859, pvrtmp_6862, tmpcur_6857);
            CursorTy pvrtmp_6867 = tmp_struct_93.field0;
            CursorTy pvrtmp_6868 = tmp_struct_93.field1;
            CursorTy pvrtmp_6869 = tmp_struct_93.field2;
            CursorTy pvrtmp_6870 = tmp_struct_93.field3;
            
            *(TagTyPacked *) loc_2949 = 1;
            
            CursorTy writetag_4777 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6867, pvrtmp_6868,
                                                   loc_2949, pvrtmp_6870};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6879 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_6880 = tmpcur_6852 + 8;
            CursorTy jump_4039 = tmpcur_6852 + 8;
            CursorTy loc_3362 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2950, end_r_2951, loc_3362, tmpaftercur_6880);
            CursorTy pvrtmp_6881 = tmp_struct_94.field0;
            CursorTy pvrtmp_6882 = tmp_struct_94.field1;
            CursorTy pvrtmp_6883 = tmp_struct_94.field2;
            CursorTy pvrtmp_6884 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Content(end_r_2950, pvrtmp_6881, pvrtmp_6884, tmpcur_6879);
            CursorTy pvrtmp_6889 = tmp_struct_95.field0;
            CursorTy pvrtmp_6890 = tmp_struct_95.field1;
            CursorTy pvrtmp_6891 = tmp_struct_95.field2;
            CursorTy pvrtmp_6892 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2949 = 2;
            
            CursorTy writetag_4785 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6889, pvrtmp_6890,
                                                   loc_2949, pvrtmp_6892};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6901 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_6902 = tmpcur_6852 + 8;
            CursorTy tmpcur_6903 = *(CursorTy *) tmpaftercur_6902;
            CursorTy tmpaftercur_6904 = tmpaftercur_6902 + 8;
            CursorTy jump_4044 = tmpaftercur_6902 + 8;
            CursorTy jump_4043 = tmpcur_6852 + 8;
            CursorTy loc_3380 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Tags(end_r_2950, end_r_2951, loc_3380, tmpaftercur_6904);
            CursorTy pvrtmp_6905 = tmp_struct_96.field0;
            CursorTy pvrtmp_6906 = tmp_struct_96.field1;
            CursorTy pvrtmp_6907 = tmp_struct_96.field2;
            CursorTy pvrtmp_6908 = tmp_struct_96.field3;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Content(end_r_2950, pvrtmp_6905, pvrtmp_6908, tmpcur_6901);
            CursorTy pvrtmp_6913 = tmp_struct_97.field0;
            CursorTy pvrtmp_6914 = tmp_struct_97.field1;
            CursorTy pvrtmp_6915 = tmp_struct_97.field2;
            CursorTy pvrtmp_6916 = tmp_struct_97.field3;
            CursorCursorCursorCursorProd tmp_struct_98 =
                                          _copy_without_ptrs_Adt(end_r_2950, pvrtmp_6913, pvrtmp_6916, tmpcur_6903);
            CursorTy pvrtmp_6921 = tmp_struct_98.field0;
            CursorTy pvrtmp_6922 = tmp_struct_98.field1;
            CursorTy pvrtmp_6923 = tmp_struct_98.field2;
            CursorTy pvrtmp_6924 = tmp_struct_98.field3;
            
            *(TagTyPacked *) loc_2949 = 3;
            
            CursorTy writetag_4795 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6921, pvrtmp_6922,
                                                   loc_2949, pvrtmp_6924};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6933 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_6934 = tmpcur_6852 + 8;
            CursorTy tmpcur_6935 = *(CursorTy *) tmpaftercur_6934;
            CursorTy tmpaftercur_6936 = tmpaftercur_6934 + 8;
            CursorTy jump_4050 = tmpaftercur_6934 + 8;
            CursorTy jump_4049 = tmpcur_6852 + 8;
            CursorTy loc_3400 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_99 =
                                          _copy_without_ptrs_Adt(end_r_2950, end_r_2951, loc_3400, tmpaftercur_6936);
            CursorTy pvrtmp_6937 = tmp_struct_99.field0;
            CursorTy pvrtmp_6938 = tmp_struct_99.field1;
            CursorTy pvrtmp_6939 = tmp_struct_99.field2;
            CursorTy pvrtmp_6940 = tmp_struct_99.field3;
            CursorCursorCursorCursorProd tmp_struct_100 =
                                          _copy_without_ptrs_Content(end_r_2950, pvrtmp_6937, pvrtmp_6940, tmpcur_6933);
            CursorTy pvrtmp_6945 = tmp_struct_100.field0;
            CursorTy pvrtmp_6946 = tmp_struct_100.field1;
            CursorTy pvrtmp_6947 = tmp_struct_100.field2;
            CursorTy pvrtmp_6948 = tmp_struct_100.field3;
            CursorCursorCursorCursorProd tmp_struct_101 =
                                          _copy_without_ptrs_Tags(end_r_2950, pvrtmp_6945, pvrtmp_6948, tmpcur_6935);
            CursorTy pvrtmp_6953 = tmp_struct_101.field0;
            CursorTy pvrtmp_6954 = tmp_struct_101.field1;
            CursorTy pvrtmp_6955 = tmp_struct_101.field2;
            CursorTy pvrtmp_6956 = tmp_struct_101.field3;
            
            *(TagTyPacked *) loc_2949 = 4;
            
            CursorTy writetag_4806 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6953, pvrtmp_6954,
                                                   loc_2949, pvrtmp_6956};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6965 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_6966 = tmpcur_6852 + 8;
            CursorTy tmpcur_6967 = *(CursorTy *) tmpaftercur_6966;
            CursorTy tmpaftercur_6968 = tmpaftercur_6966 + 8;
            CursorTy jump_4056 = tmpaftercur_6966 + 8;
            CursorTy jump_4055 = tmpcur_6852 + 8;
            CursorTy loc_3420 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_102 =
                                          _copy_without_ptrs_Tags(end_r_2950, end_r_2951, loc_3420, tmpaftercur_6968);
            CursorTy pvrtmp_6969 = tmp_struct_102.field0;
            CursorTy pvrtmp_6970 = tmp_struct_102.field1;
            CursorTy pvrtmp_6971 = tmp_struct_102.field2;
            CursorTy pvrtmp_6972 = tmp_struct_102.field3;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          _copy_without_ptrs_Adt(end_r_2950, pvrtmp_6969, pvrtmp_6972, tmpcur_6965);
            CursorTy pvrtmp_6977 = tmp_struct_103.field0;
            CursorTy pvrtmp_6978 = tmp_struct_103.field1;
            CursorTy pvrtmp_6979 = tmp_struct_103.field2;
            CursorTy pvrtmp_6980 = tmp_struct_103.field3;
            CursorCursorCursorCursorProd tmp_struct_104 =
                                          _copy_without_ptrs_Content(end_r_2950, pvrtmp_6977, pvrtmp_6980, tmpcur_6967);
            CursorTy pvrtmp_6985 = tmp_struct_104.field0;
            CursorTy pvrtmp_6986 = tmp_struct_104.field1;
            CursorTy pvrtmp_6987 = tmp_struct_104.field2;
            CursorTy pvrtmp_6988 = tmp_struct_104.field3;
            
            *(TagTyPacked *) loc_2949 = 5;
            
            CursorTy writetag_4817 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6985, pvrtmp_6986,
                                                   loc_2949, pvrtmp_6988};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6997 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_6998 = tmpcur_6852 + 8;
            CursorTy tmpcur_6999 = *(CursorTy *) tmpaftercur_6998;
            CursorTy tmpaftercur_7000 = tmpaftercur_6998 + 8;
            CursorTy jump_4062 = tmpaftercur_6998 + 8;
            CursorTy jump_4061 = tmpcur_6852 + 8;
            CursorTy loc_3440 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_105 =
                                          _copy_without_ptrs_Adt(end_r_2950, end_r_2951, loc_3440, tmpaftercur_7000);
            CursorTy pvrtmp_7001 = tmp_struct_105.field0;
            CursorTy pvrtmp_7002 = tmp_struct_105.field1;
            CursorTy pvrtmp_7003 = tmp_struct_105.field2;
            CursorTy pvrtmp_7004 = tmp_struct_105.field3;
            CursorCursorCursorCursorProd tmp_struct_106 =
                                          _copy_without_ptrs_Tags(end_r_2950, pvrtmp_7001, pvrtmp_7004, tmpcur_6997);
            CursorTy pvrtmp_7009 = tmp_struct_106.field0;
            CursorTy pvrtmp_7010 = tmp_struct_106.field1;
            CursorTy pvrtmp_7011 = tmp_struct_106.field2;
            CursorTy pvrtmp_7012 = tmp_struct_106.field3;
            CursorCursorCursorCursorProd tmp_struct_107 =
                                          _copy_without_ptrs_Content(end_r_2950, pvrtmp_7009, pvrtmp_7012, tmpcur_6999);
            CursorTy pvrtmp_7017 = tmp_struct_107.field0;
            CursorTy pvrtmp_7018 = tmp_struct_107.field1;
            CursorTy pvrtmp_7019 = tmp_struct_107.field2;
            CursorTy pvrtmp_7020 = tmp_struct_107.field3;
            
            *(TagTyPacked *) loc_2949 = 6;
            
            CursorTy writetag_4828 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7017, pvrtmp_7018,
                                                   loc_2949, pvrtmp_7020};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7029 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_7030 = tmpcur_6852 + 8;
            CursorTy tmpcur_7031 = *(CursorTy *) tmpaftercur_7030;
            CursorTy tmpaftercur_7032 = tmpaftercur_7030 + 8;
            CursorTy jump_4068 = tmpaftercur_7030 + 8;
            CursorTy jump_4067 = tmpcur_6852 + 8;
            CursorTy loc_3460 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_108 =
                                          _copy_without_ptrs_Content(end_r_2950, end_r_2951, loc_3460, tmpaftercur_7032);
            CursorTy pvrtmp_7033 = tmp_struct_108.field0;
            CursorTy pvrtmp_7034 = tmp_struct_108.field1;
            CursorTy pvrtmp_7035 = tmp_struct_108.field2;
            CursorTy pvrtmp_7036 = tmp_struct_108.field3;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          _copy_without_ptrs_Tags(end_r_2950, pvrtmp_7033, pvrtmp_7036, tmpcur_7029);
            CursorTy pvrtmp_7041 = tmp_struct_109.field0;
            CursorTy pvrtmp_7042 = tmp_struct_109.field1;
            CursorTy pvrtmp_7043 = tmp_struct_109.field2;
            CursorTy pvrtmp_7044 = tmp_struct_109.field3;
            CursorCursorCursorCursorProd tmp_struct_110 =
                                          _copy_without_ptrs_Adt(end_r_2950, pvrtmp_7041, pvrtmp_7044, tmpcur_7031);
            CursorTy pvrtmp_7049 = tmp_struct_110.field0;
            CursorTy pvrtmp_7050 = tmp_struct_110.field1;
            CursorTy pvrtmp_7051 = tmp_struct_110.field2;
            CursorTy pvrtmp_7052 = tmp_struct_110.field3;
            
            *(TagTyPacked *) loc_2949 = 7;
            
            CursorTy writetag_4839 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7049, pvrtmp_7050,
                                                   loc_2949, pvrtmp_7052};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7061 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_7062 = tmpcur_6852 + 8;
            CursorTy tmpcur_7063 = *(CursorTy *) tmpaftercur_7062;
            CursorTy tmpaftercur_7064 = tmpaftercur_7062 + 8;
            CursorTy jump_4074 = tmpaftercur_7062 + 8;
            CursorTy jump_4073 = tmpcur_6852 + 8;
            CursorTy loc_3480 = loc_2949 + 1;
            CursorCursorCursorCursorProd tmp_struct_111 =
                                          _copy_without_ptrs_Content(end_r_2950, end_r_2951, loc_3480, tmpaftercur_7064);
            CursorTy pvrtmp_7065 = tmp_struct_111.field0;
            CursorTy pvrtmp_7066 = tmp_struct_111.field1;
            CursorTy pvrtmp_7067 = tmp_struct_111.field2;
            CursorTy pvrtmp_7068 = tmp_struct_111.field3;
            CursorCursorCursorCursorProd tmp_struct_112 =
                                          _copy_without_ptrs_Adt(end_r_2950, pvrtmp_7065, pvrtmp_7068, tmpcur_7061);
            CursorTy pvrtmp_7073 = tmp_struct_112.field0;
            CursorTy pvrtmp_7074 = tmp_struct_112.field1;
            CursorTy pvrtmp_7075 = tmp_struct_112.field2;
            CursorTy pvrtmp_7076 = tmp_struct_112.field3;
            CursorCursorCursorCursorProd tmp_struct_113 =
                                          _copy_without_ptrs_Tags(end_r_2950, pvrtmp_7073, pvrtmp_7076, tmpcur_7063);
            CursorTy pvrtmp_7081 = tmp_struct_113.field0;
            CursorTy pvrtmp_7082 = tmp_struct_113.field1;
            CursorTy pvrtmp_7083 = tmp_struct_113.field2;
            CursorTy pvrtmp_7084 = tmp_struct_113.field3;
            
            *(TagTyPacked *) loc_2949 = 8;
            
            CursorTy writetag_4850 = loc_2949 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7081, pvrtmp_7082,
                                                   loc_2949, pvrtmp_7084};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7093 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_7094 = tmpcur_6852 + 8;
            CursorTy jump_4310 = tmpcur_6852 + 8;
            CursorCursorCursorCursorProd tmp_struct_114 =
                                          _copy_without_ptrs_Adt(end_r_2950, end_r_2951, loc_2949, tmpcur_7093);
            CursorTy pvrtmp_7095 = tmp_struct_114.field0;
            CursorTy pvrtmp_7096 = tmp_struct_114.field1;
            CursorTy pvrtmp_7097 = tmp_struct_114.field2;
            CursorTy pvrtmp_7098 = tmp_struct_114.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7095, jump_4310,
                                                   pvrtmp_7097, pvrtmp_7098};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7105 = *(CursorTy *) tmpcur_6852;
            CursorTy tmpaftercur_7106 = tmpcur_6852 + 8;
            CursorCursorCursorCursorProd tmp_struct_115 =
                                          _copy_without_ptrs_Adt(end_r_2950, end_r_2951, loc_2949, tmpcur_7105);
            CursorTy pvrtmp_7107 = tmp_struct_115.field0;
            CursorTy pvrtmp_7108 = tmp_struct_115.field1;
            CursorTy pvrtmp_7109 = tmp_struct_115.field2;
            CursorTy pvrtmp_7110 = tmp_struct_115.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7107, pvrtmp_7108,
                                                   pvrtmp_7109, pvrtmp_7110};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6851");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2953, CursorTy arg_760_1365_1686)
{
    TagTyPacked tmpval_7118 = *(TagTyPacked *) arg_760_1365_1686;
    CursorTy tmpcur_7119 = arg_760_1365_1686 + 1;
    
    
  switch_7176:
    ;
    switch (tmpval_7118) {
        
      case 0:
        {
            CursorTy jump_4079 = arg_760_1365_1686 + 1;
            
            return (CursorProd) {jump_4079};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7120 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7121 = tmpcur_7119 + 8;
            CursorTy jump_4081 = tmpcur_7119 + 8;
            CursorProd tmp_struct_116 =
                        _traverse_Content(end_r_2953, tmpaftercur_7121);
            CursorTy pvrtmp_7122 = tmp_struct_116.field0;
            CursorProd tmp_struct_117 =  _traverse_Adt(end_r_2953, tmpcur_7120);
            CursorTy pvrtmp_7123 = tmp_struct_117.field0;
            
            return (CursorProd) {pvrtmp_7123};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7124 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7125 = tmpcur_7119 + 8;
            CursorTy jump_4085 = tmpcur_7119 + 8;
            CursorProd tmp_struct_118 =
                        _traverse_Adt(end_r_2953, tmpaftercur_7125);
            CursorTy pvrtmp_7126 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Content(end_r_2953, tmpcur_7124);
            CursorTy pvrtmp_7127 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_7127};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7128 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7129 = tmpcur_7119 + 8;
            CursorTy tmpcur_7130 = *(CursorTy *) tmpaftercur_7129;
            CursorTy tmpaftercur_7131 = tmpaftercur_7129 + 8;
            CursorTy jump_4090 = tmpaftercur_7129 + 8;
            CursorTy jump_4089 = tmpcur_7119 + 8;
            CursorProd tmp_struct_120 =
                        _traverse_Tags(end_r_2953, tmpaftercur_7131);
            CursorTy pvrtmp_7132 = tmp_struct_120.field0;
            CursorProd tmp_struct_121 =
                        _traverse_Content(end_r_2953, tmpcur_7128);
            CursorTy pvrtmp_7133 = tmp_struct_121.field0;
            CursorProd tmp_struct_122 =  _traverse_Adt(end_r_2953, tmpcur_7130);
            CursorTy pvrtmp_7134 = tmp_struct_122.field0;
            
            return (CursorProd) {pvrtmp_7134};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7135 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7136 = tmpcur_7119 + 8;
            CursorTy tmpcur_7137 = *(CursorTy *) tmpaftercur_7136;
            CursorTy tmpaftercur_7138 = tmpaftercur_7136 + 8;
            CursorTy jump_4096 = tmpaftercur_7136 + 8;
            CursorTy jump_4095 = tmpcur_7119 + 8;
            CursorProd tmp_struct_123 =
                        _traverse_Adt(end_r_2953, tmpaftercur_7138);
            CursorTy pvrtmp_7139 = tmp_struct_123.field0;
            CursorProd tmp_struct_124 =
                        _traverse_Content(end_r_2953, tmpcur_7135);
            CursorTy pvrtmp_7140 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _traverse_Tags(end_r_2953, tmpcur_7137);
            CursorTy pvrtmp_7141 = tmp_struct_125.field0;
            
            return (CursorProd) {pvrtmp_7141};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7142 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7143 = tmpcur_7119 + 8;
            CursorTy tmpcur_7144 = *(CursorTy *) tmpaftercur_7143;
            CursorTy tmpaftercur_7145 = tmpaftercur_7143 + 8;
            CursorTy jump_4102 = tmpaftercur_7143 + 8;
            CursorTy jump_4101 = tmpcur_7119 + 8;
            CursorProd tmp_struct_126 =
                        _traverse_Tags(end_r_2953, tmpaftercur_7145);
            CursorTy pvrtmp_7146 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =  _traverse_Adt(end_r_2953, tmpcur_7142);
            CursorTy pvrtmp_7147 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =
                        _traverse_Content(end_r_2953, tmpcur_7144);
            CursorTy pvrtmp_7148 = tmp_struct_128.field0;
            
            return (CursorProd) {pvrtmp_7148};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7149 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7150 = tmpcur_7119 + 8;
            CursorTy tmpcur_7151 = *(CursorTy *) tmpaftercur_7150;
            CursorTy tmpaftercur_7152 = tmpaftercur_7150 + 8;
            CursorTy jump_4108 = tmpaftercur_7150 + 8;
            CursorTy jump_4107 = tmpcur_7119 + 8;
            CursorProd tmp_struct_129 =
                        _traverse_Adt(end_r_2953, tmpaftercur_7152);
            CursorTy pvrtmp_7153 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _traverse_Tags(end_r_2953, tmpcur_7149);
            CursorTy pvrtmp_7154 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =
                        _traverse_Content(end_r_2953, tmpcur_7151);
            CursorTy pvrtmp_7155 = tmp_struct_131.field0;
            
            return (CursorProd) {pvrtmp_7155};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7156 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7157 = tmpcur_7119 + 8;
            CursorTy tmpcur_7158 = *(CursorTy *) tmpaftercur_7157;
            CursorTy tmpaftercur_7159 = tmpaftercur_7157 + 8;
            CursorTy jump_4114 = tmpaftercur_7157 + 8;
            CursorTy jump_4113 = tmpcur_7119 + 8;
            CursorProd tmp_struct_132 =
                        _traverse_Content(end_r_2953, tmpaftercur_7159);
            CursorTy pvrtmp_7160 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =
                        _traverse_Tags(end_r_2953, tmpcur_7156);
            CursorTy pvrtmp_7161 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =  _traverse_Adt(end_r_2953, tmpcur_7158);
            CursorTy pvrtmp_7162 = tmp_struct_134.field0;
            
            return (CursorProd) {pvrtmp_7162};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7163 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7164 = tmpcur_7119 + 8;
            CursorTy tmpcur_7165 = *(CursorTy *) tmpaftercur_7164;
            CursorTy tmpaftercur_7166 = tmpaftercur_7164 + 8;
            CursorTy jump_4120 = tmpaftercur_7164 + 8;
            CursorTy jump_4119 = tmpcur_7119 + 8;
            CursorProd tmp_struct_135 =
                        _traverse_Content(end_r_2953, tmpaftercur_7166);
            CursorTy pvrtmp_7167 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _traverse_Adt(end_r_2953, tmpcur_7163);
            CursorTy pvrtmp_7168 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _traverse_Tags(end_r_2953, tmpcur_7165);
            CursorTy pvrtmp_7169 = tmp_struct_137.field0;
            
            return (CursorProd) {pvrtmp_7169};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7170 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7171 = tmpcur_7119 + 8;
            CursorTy jump_4316 = tmpcur_7119 + 8;
            CursorProd tmp_struct_138 =  _traverse_Adt(end_r_2953, tmpcur_7170);
            CursorTy pvrtmp_7172 = tmp_struct_138.field0;
            
            return (CursorProd) {jump_4316};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7173 = *(CursorTy *) tmpcur_7119;
            CursorTy tmpaftercur_7174 = tmpcur_7119 + 8;
            CursorProd tmp_struct_139 =  _traverse_Adt(end_r_2953, tmpcur_7173);
            CursorTy pvrtmp_7175 = tmp_struct_139.field0;
            
            return (CursorProd) {pvrtmp_7175};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7118");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2955, CursorTy arg_805_1410_1731)
{
    TagTyPacked tmpval_7177 = *(TagTyPacked *) arg_805_1410_1731;
    CursorTy tmpcur_7178 = arg_805_1410_1731 + 1;
    
    
  switch_7235:
    ;
    switch (tmpval_7177) {
        
      case 0:
        {
            CursorTy jump_4125 = arg_805_1410_1731 + 1;
            unsigned char wildcard_806_1411_1732 = print_symbol(6135);
            unsigned char wildcard_807_1412_1733 = print_symbol(6129);
            
            return (CursorProd) {jump_4125};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7179 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7180 = tmpcur_7178 + 8;
            CursorTy jump_4127 = tmpcur_7178 + 8;
            unsigned char wildcard_812_1415_1736 = print_symbol(6141);
            CursorProd tmp_struct_140 =
                        _print_Content(end_r_2955, tmpaftercur_7180);
            CursorTy pvrtmp_7181 = tmp_struct_140.field0;
            CursorProd tmp_struct_141 =  _print_Adt(end_r_2955, tmpcur_7179);
            CursorTy pvrtmp_7182 = tmp_struct_141.field0;
            unsigned char wildcard_813_1418_1739 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7182};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7183 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7184 = tmpcur_7178 + 8;
            CursorTy jump_4131 = tmpcur_7178 + 8;
            unsigned char wildcard_818_1421_1742 = print_symbol(6144);
            CursorProd tmp_struct_142 =
                        _print_Adt(end_r_2955, tmpaftercur_7184);
            CursorTy pvrtmp_7185 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =
                        _print_Content(end_r_2955, tmpcur_7183);
            CursorTy pvrtmp_7186 = tmp_struct_143.field0;
            unsigned char wildcard_819_1424_1745 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7186};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7187 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7188 = tmpcur_7178 + 8;
            CursorTy tmpcur_7189 = *(CursorTy *) tmpaftercur_7188;
            CursorTy tmpaftercur_7190 = tmpaftercur_7188 + 8;
            CursorTy jump_4136 = tmpaftercur_7188 + 8;
            CursorTy jump_4135 = tmpcur_7178 + 8;
            unsigned char wildcard_826_1428_1749 = print_symbol(6132);
            CursorProd tmp_struct_144 =
                        _print_Tags(end_r_2955, tmpaftercur_7190);
            CursorTy pvrtmp_7191 = tmp_struct_144.field0;
            CursorProd tmp_struct_145 =
                        _print_Content(end_r_2955, tmpcur_7187);
            CursorTy pvrtmp_7192 = tmp_struct_145.field0;
            CursorProd tmp_struct_146 =  _print_Adt(end_r_2955, tmpcur_7189);
            CursorTy pvrtmp_7193 = tmp_struct_146.field0;
            unsigned char wildcard_827_1432_1753 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7193};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7194 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7195 = tmpcur_7178 + 8;
            CursorTy tmpcur_7196 = *(CursorTy *) tmpaftercur_7195;
            CursorTy tmpaftercur_7197 = tmpaftercur_7195 + 8;
            CursorTy jump_4142 = tmpaftercur_7195 + 8;
            CursorTy jump_4141 = tmpcur_7178 + 8;
            unsigned char wildcard_834_1436_1757 = print_symbol(6143);
            CursorProd tmp_struct_147 =
                        _print_Adt(end_r_2955, tmpaftercur_7197);
            CursorTy pvrtmp_7198 = tmp_struct_147.field0;
            CursorProd tmp_struct_148 =
                        _print_Content(end_r_2955, tmpcur_7194);
            CursorTy pvrtmp_7199 = tmp_struct_148.field0;
            CursorProd tmp_struct_149 =  _print_Tags(end_r_2955, tmpcur_7196);
            CursorTy pvrtmp_7200 = tmp_struct_149.field0;
            unsigned char wildcard_835_1440_1761 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7200};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7201 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7202 = tmpcur_7178 + 8;
            CursorTy tmpcur_7203 = *(CursorTy *) tmpaftercur_7202;
            CursorTy tmpaftercur_7204 = tmpaftercur_7202 + 8;
            CursorTy jump_4148 = tmpaftercur_7202 + 8;
            CursorTy jump_4147 = tmpcur_7178 + 8;
            unsigned char wildcard_842_1444_1765 = print_symbol(6133);
            CursorProd tmp_struct_150 =
                        _print_Tags(end_r_2955, tmpaftercur_7204);
            CursorTy pvrtmp_7205 = tmp_struct_150.field0;
            CursorProd tmp_struct_151 =  _print_Adt(end_r_2955, tmpcur_7201);
            CursorTy pvrtmp_7206 = tmp_struct_151.field0;
            CursorProd tmp_struct_152 =
                        _print_Content(end_r_2955, tmpcur_7203);
            CursorTy pvrtmp_7207 = tmp_struct_152.field0;
            unsigned char wildcard_843_1448_1769 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7207};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7208 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7209 = tmpcur_7178 + 8;
            CursorTy tmpcur_7210 = *(CursorTy *) tmpaftercur_7209;
            CursorTy tmpaftercur_7211 = tmpaftercur_7209 + 8;
            CursorTy jump_4154 = tmpaftercur_7209 + 8;
            CursorTy jump_4153 = tmpcur_7178 + 8;
            unsigned char wildcard_850_1452_1773 = print_symbol(6142);
            CursorProd tmp_struct_153 =
                        _print_Adt(end_r_2955, tmpaftercur_7211);
            CursorTy pvrtmp_7212 = tmp_struct_153.field0;
            CursorProd tmp_struct_154 =  _print_Tags(end_r_2955, tmpcur_7208);
            CursorTy pvrtmp_7213 = tmp_struct_154.field0;
            CursorProd tmp_struct_155 =
                        _print_Content(end_r_2955, tmpcur_7210);
            CursorTy pvrtmp_7214 = tmp_struct_155.field0;
            unsigned char wildcard_851_1456_1777 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7214};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7215 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7216 = tmpcur_7178 + 8;
            CursorTy tmpcur_7217 = *(CursorTy *) tmpaftercur_7216;
            CursorTy tmpaftercur_7218 = tmpaftercur_7216 + 8;
            CursorTy jump_4160 = tmpaftercur_7216 + 8;
            CursorTy jump_4159 = tmpcur_7178 + 8;
            unsigned char wildcard_858_1460_1781 = print_symbol(6139);
            CursorProd tmp_struct_156 =
                        _print_Content(end_r_2955, tmpaftercur_7218);
            CursorTy pvrtmp_7219 = tmp_struct_156.field0;
            CursorProd tmp_struct_157 =  _print_Tags(end_r_2955, tmpcur_7215);
            CursorTy pvrtmp_7220 = tmp_struct_157.field0;
            CursorProd tmp_struct_158 =  _print_Adt(end_r_2955, tmpcur_7217);
            CursorTy pvrtmp_7221 = tmp_struct_158.field0;
            unsigned char wildcard_859_1464_1785 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7221};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7222 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7223 = tmpcur_7178 + 8;
            CursorTy tmpcur_7224 = *(CursorTy *) tmpaftercur_7223;
            CursorTy tmpaftercur_7225 = tmpaftercur_7223 + 8;
            CursorTy jump_4166 = tmpaftercur_7223 + 8;
            CursorTy jump_4165 = tmpcur_7178 + 8;
            unsigned char wildcard_866_1468_1789 = print_symbol(6140);
            CursorProd tmp_struct_159 =
                        _print_Content(end_r_2955, tmpaftercur_7225);
            CursorTy pvrtmp_7226 = tmp_struct_159.field0;
            CursorProd tmp_struct_160 =  _print_Adt(end_r_2955, tmpcur_7222);
            CursorTy pvrtmp_7227 = tmp_struct_160.field0;
            CursorProd tmp_struct_161 =  _print_Tags(end_r_2955, tmpcur_7224);
            CursorTy pvrtmp_7228 = tmp_struct_161.field0;
            unsigned char wildcard_867_1472_1793 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7228};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7229 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7230 = tmpcur_7178 + 8;
            CursorTy jump_4322 = tmpcur_7178 + 8;
            unsigned char wildcard_4325 = print_symbol(6146);
            CursorProd tmp_struct_162 =  _print_Adt(end_r_2955, tmpcur_7229);
            CursorTy pvrtmp_7231 = tmp_struct_162.field0;
            
            return (CursorProd) {jump_4322};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7232 = *(CursorTy *) tmpcur_7178;
            CursorTy tmpaftercur_7233 = tmpcur_7178 + 8;
            unsigned char wildcard_4325 = print_symbol(6145);
            CursorProd tmp_struct_163 =  _print_Adt(end_r_2955, tmpcur_7232);
            CursorTy pvrtmp_7234 = tmp_struct_163.field0;
            
            return (CursorProd) {pvrtmp_7234};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7177");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2958,
                                        CursorTy end_r_2959, CursorTy loc_2957,
                                        CursorTy arg_868_1473_1794)
{
    if (loc_2957 + 32 > end_r_2959) {
        ChunkTy new_chunk_167 = alloc_chunk(end_r_2959);
        CursorTy chunk_start_168 = new_chunk_167.chunk_start;
        CursorTy chunk_end_169 = new_chunk_167.chunk_end;
        
        end_r_2959 = chunk_end_169;
        *(TagTyPacked *) loc_2957 = 255;
        
        CursorTy redir = loc_2957 + 1;
        
        *(CursorTy *) redir = chunk_start_168;
        loc_2957 = chunk_start_168;
    }
    
    CursorTy loc_3658 = loc_2957 + 1;
    CursorTy loc_3659 = loc_3658 + 8;
    TagTyPacked tmpval_7236 = *(TagTyPacked *) arg_868_1473_1794;
    CursorTy tmpcur_7237 = arg_868_1473_1794 + 1;
    
    
  switch_7280:
    ;
    switch (tmpval_7236) {
        
      case 0:
        {
            CursorTy jump_4171 = arg_868_1473_1794 + 1;
            
            *(TagTyPacked *) loc_2957 = 0;
            
            CursorTy writetag_4964 = loc_2957 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2959, jump_4171,
                                                   loc_2957, writetag_4964};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7242 = *(IntTy *) tmpcur_7237;
            CursorTy tmpcur_7243 = tmpcur_7237 + sizeof(IntTy);
            CursorTy jump_4173 = tmpcur_7237 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          _copy_Tags(end_r_2958, end_r_2959, loc_3659, tmpcur_7243);
            CursorTy pvrtmp_7244 = tmp_struct_164.field0;
            CursorTy pvrtmp_7245 = tmp_struct_164.field1;
            CursorTy pvrtmp_7246 = tmp_struct_164.field2;
            CursorTy pvrtmp_7247 = tmp_struct_164.field3;
            
            *(TagTyPacked *) loc_2957 = 1;
            
            CursorTy writetag_4969 = loc_2957 + 1;
            
            *(IntTy *) writetag_4969 = tmpval_7242;
            
            CursorTy writecur_4970 = writetag_4969 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7244, pvrtmp_7245,
                                                   loc_2957, pvrtmp_7247};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7256 = *(CursorTy *) tmpcur_7237;
            CursorTy tmpaftercur_7257 = tmpcur_7237 + 8;
            CursorTy jump_4328 = tmpcur_7237 + 8;
            CursorCursorCursorCursorProd tmp_struct_165 =
                                          _copy_Tags(end_r_2958, end_r_2959, loc_2957, tmpcur_7256);
            CursorTy pvrtmp_7258 = tmp_struct_165.field0;
            CursorTy pvrtmp_7259 = tmp_struct_165.field1;
            CursorTy pvrtmp_7260 = tmp_struct_165.field2;
            CursorTy pvrtmp_7261 = tmp_struct_165.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7258, jump_4328,
                                                   pvrtmp_7260, pvrtmp_7261};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7268 = *(CursorTy *) tmpcur_7237;
            CursorTy tmpaftercur_7269 = tmpcur_7237 + 8;
            CursorCursorCursorCursorProd tmp_struct_166 =
                                          _copy_Tags(end_r_2958, end_r_2959, loc_2957, tmpcur_7268);
            CursorTy pvrtmp_7270 = tmp_struct_166.field0;
            CursorTy pvrtmp_7271 = tmp_struct_166.field1;
            CursorTy pvrtmp_7272 = tmp_struct_166.field2;
            CursorTy pvrtmp_7273 = tmp_struct_166.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7270, pvrtmp_7271,
                                                   pvrtmp_7272, pvrtmp_7273};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7236");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2962,
                                                     CursorTy end_r_2963,
                                                     CursorTy loc_2961,
                                                     CursorTy arg_873_1478_1799)
{
    CursorTy loc_3671 = loc_2961 + 1;
    CursorTy loc_3672 = loc_3671 + 8;
    TagTyPacked tmpval_7281 = *(TagTyPacked *) arg_873_1478_1799;
    CursorTy tmpcur_7282 = arg_873_1478_1799 + 1;
    
    
  switch_7325:
    ;
    switch (tmpval_7281) {
        
      case 0:
        {
            CursorTy jump_4176 = arg_873_1478_1799 + 1;
            
            *(TagTyPacked *) loc_2961 = 0;
            
            CursorTy writetag_4980 = loc_2961 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2963, jump_4176,
                                                   loc_2961, writetag_4980};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7287 = *(IntTy *) tmpcur_7282;
            CursorTy tmpcur_7288 = tmpcur_7282 + sizeof(IntTy);
            CursorTy jump_4178 = tmpcur_7282 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _copy_without_ptrs_Tags(end_r_2962, end_r_2963, loc_3672, tmpcur_7288);
            CursorTy pvrtmp_7289 = tmp_struct_170.field0;
            CursorTy pvrtmp_7290 = tmp_struct_170.field1;
            CursorTy pvrtmp_7291 = tmp_struct_170.field2;
            CursorTy pvrtmp_7292 = tmp_struct_170.field3;
            
            *(TagTyPacked *) loc_2961 = 1;
            
            CursorTy writetag_4985 = loc_2961 + 1;
            
            *(IntTy *) writetag_4985 = tmpval_7287;
            
            CursorTy writecur_4986 = writetag_4985 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7289, pvrtmp_7290,
                                                   loc_2961, pvrtmp_7292};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7301 = *(CursorTy *) tmpcur_7282;
            CursorTy tmpaftercur_7302 = tmpcur_7282 + 8;
            CursorTy jump_4334 = tmpcur_7282 + 8;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          _copy_without_ptrs_Tags(end_r_2962, end_r_2963, loc_2961, tmpcur_7301);
            CursorTy pvrtmp_7303 = tmp_struct_171.field0;
            CursorTy pvrtmp_7304 = tmp_struct_171.field1;
            CursorTy pvrtmp_7305 = tmp_struct_171.field2;
            CursorTy pvrtmp_7306 = tmp_struct_171.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7303, jump_4334,
                                                   pvrtmp_7305, pvrtmp_7306};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7313 = *(CursorTy *) tmpcur_7282;
            CursorTy tmpaftercur_7314 = tmpcur_7282 + 8;
            CursorCursorCursorCursorProd tmp_struct_172 =
                                          _copy_without_ptrs_Tags(end_r_2962, end_r_2963, loc_2961, tmpcur_7313);
            CursorTy pvrtmp_7315 = tmp_struct_172.field0;
            CursorTy pvrtmp_7316 = tmp_struct_172.field1;
            CursorTy pvrtmp_7317 = tmp_struct_172.field2;
            CursorTy pvrtmp_7318 = tmp_struct_172.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7315, pvrtmp_7316,
                                                   pvrtmp_7317, pvrtmp_7318};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7281");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_2965, CursorTy arg_878_1483_1804)
{
    TagTyPacked tmpval_7326 = *(TagTyPacked *) arg_878_1483_1804;
    CursorTy tmpcur_7327 = arg_878_1483_1804 + 1;
    
    
  switch_7337:
    ;
    switch (tmpval_7326) {
        
      case 0:
        {
            CursorTy jump_4181 = arg_878_1483_1804 + 1;
            
            return (CursorProd) {jump_4181};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7328 = *(IntTy *) tmpcur_7327;
            CursorTy tmpcur_7329 = tmpcur_7327 + sizeof(IntTy);
            CursorTy jump_4183 = tmpcur_7327 + 8;
            CursorProd tmp_struct_173 =
                        _traverse_Tags(end_r_2965, tmpcur_7329);
            CursorTy pvrtmp_7330 = tmp_struct_173.field0;
            
            return (CursorProd) {pvrtmp_7330};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7331 = *(CursorTy *) tmpcur_7327;
            CursorTy tmpaftercur_7332 = tmpcur_7327 + 8;
            CursorTy jump_4340 = tmpcur_7327 + 8;
            CursorProd tmp_struct_174 =
                        _traverse_Tags(end_r_2965, tmpcur_7331);
            CursorTy pvrtmp_7333 = tmp_struct_174.field0;
            
            return (CursorProd) {jump_4340};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7334 = *(CursorTy *) tmpcur_7327;
            CursorTy tmpaftercur_7335 = tmpcur_7327 + 8;
            CursorProd tmp_struct_175 =
                        _traverse_Tags(end_r_2965, tmpcur_7334);
            CursorTy pvrtmp_7336 = tmp_struct_175.field0;
            
            return (CursorProd) {pvrtmp_7336};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7326");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_2967, CursorTy arg_883_1487_1808)
{
    TagTyPacked tmpval_7338 = *(TagTyPacked *) arg_883_1487_1808;
    CursorTy tmpcur_7339 = arg_883_1487_1808 + 1;
    
    
  switch_7349:
    ;
    switch (tmpval_7338) {
        
      case 0:
        {
            CursorTy jump_4186 = arg_883_1487_1808 + 1;
            unsigned char wildcard_884_1488_1809 = print_symbol(6134);
            unsigned char wildcard_885_1489_1810 = print_symbol(6129);
            
            return (CursorProd) {jump_4186};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7340 = *(IntTy *) tmpcur_7339;
            CursorTy tmpcur_7341 = tmpcur_7339 + sizeof(IntTy);
            CursorTy jump_4188 = tmpcur_7339 + 8;
            unsigned char wildcard_890_1492_1813 = print_symbol(6131);
            unsigned char y_888_1493_1814 = printf("%lld", tmpval_7340);
            CursorProd tmp_struct_176 =  _print_Tags(end_r_2967, tmpcur_7341);
            CursorTy pvrtmp_7342 = tmp_struct_176.field0;
            unsigned char wildcard_891_1495_1816 = print_symbol(6129);
            
            return (CursorProd) {pvrtmp_7342};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7343 = *(CursorTy *) tmpcur_7339;
            CursorTy tmpaftercur_7344 = tmpcur_7339 + 8;
            CursorTy jump_4346 = tmpcur_7339 + 8;
            unsigned char wildcard_4349 = print_symbol(6146);
            CursorProd tmp_struct_177 =  _print_Tags(end_r_2967, tmpcur_7343);
            CursorTy pvrtmp_7345 = tmp_struct_177.field0;
            
            return (CursorProd) {jump_4346};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7346 = *(CursorTy *) tmpcur_7339;
            CursorTy tmpaftercur_7347 = tmpcur_7339 + 8;
            unsigned char wildcard_4349 = print_symbol(6145);
            CursorProd tmp_struct_178 =  _print_Tags(end_r_2967, tmpcur_7346);
            CursorTy pvrtmp_7348 = tmp_struct_178.field0;
            
            return (CursorProd) {pvrtmp_7348};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7338");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_2970,
                                                              CursorTy end_r_2971,
                                                              CursorTy loc_2969,
                                                              CursorTy arg_2702)
{
    if (loc_2969 + 32 > end_r_2971) {
        ChunkTy new_chunk_182 = alloc_chunk(end_r_2971);
        CursorTy chunk_start_183 = new_chunk_182.chunk_start;
        CursorTy chunk_end_184 = new_chunk_182.chunk_end;
        
        end_r_2971 = chunk_end_184;
        *(TagTyPacked *) loc_2969 = 255;
        
        CursorTy redir = loc_2969 + 1;
        
        *(CursorTy *) redir = chunk_start_183;
        loc_2969 = chunk_start_183;
    }
    
    CursorTy loc_3696 = loc_2969 + 1;
    CursorTy loc_3697 = loc_3696 + 8;
    TagTyPacked tmpval_7350 = *(TagTyPacked *) arg_2702;
    CursorTy tmpcur_7351 = arg_2702 + 1;
    
    
  switch_7394:
    ;
    switch (tmpval_7350) {
        
      case 0:
        {
            CursorTy jump_4191 = arg_2702 + 1;
            
            *(TagTyPacked *) loc_2969 = 0;
            
            CursorTy writetag_5016 = loc_2969 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2971, jump_4191,
                                                   loc_2969, writetag_5016};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7356 = *(IntTy *) tmpcur_7351;
            CursorTy tmpcur_7357 = tmpcur_7351 + sizeof(IntTy);
            CursorTy jump_4193 = tmpcur_7351 + 8;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_String(end_r_2970, end_r_2971, loc_3697, tmpcur_7357);
            CursorTy pvrtmp_7358 = tmp_struct_179.field0;
            CursorTy pvrtmp_7359 = tmp_struct_179.field1;
            CursorTy pvrtmp_7360 = tmp_struct_179.field2;
            CursorTy pvrtmp_7361 = tmp_struct_179.field3;
            
            *(TagTyPacked *) loc_2969 = 1;
            
            CursorTy writetag_5021 = loc_2969 + 1;
            
            *(IntTy *) writetag_5021 = tmpval_7356;
            
            CursorTy writecur_5022 = writetag_5021 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7358, pvrtmp_7359,
                                                   loc_2969, pvrtmp_7361};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7370 = *(CursorTy *) tmpcur_7351;
            CursorTy tmpaftercur_7371 = tmpcur_7351 + 8;
            CursorTy jump_4352 = tmpcur_7351 + 8;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_String(end_r_2970, end_r_2971, loc_2969, tmpcur_7370);
            CursorTy pvrtmp_7372 = tmp_struct_180.field0;
            CursorTy pvrtmp_7373 = tmp_struct_180.field1;
            CursorTy pvrtmp_7374 = tmp_struct_180.field2;
            CursorTy pvrtmp_7375 = tmp_struct_180.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7372, jump_4352,
                                                   pvrtmp_7374, pvrtmp_7375};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7382 = *(CursorTy *) tmpcur_7351;
            CursorTy tmpaftercur_7383 = tmpcur_7351 + 8;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_String(end_r_2970, end_r_2971, loc_2969, tmpcur_7382);
            CursorTy pvrtmp_7384 = tmp_struct_181.field0;
            CursorTy pvrtmp_7385 = tmp_struct_181.field1;
            CursorTy pvrtmp_7386 = tmp_struct_181.field2;
            CursorTy pvrtmp_7387 = tmp_struct_181.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7384, pvrtmp_7385,
                                                   pvrtmp_7386, pvrtmp_7387};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7350");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_2974,
                                                               CursorTy end_r_2975,
                                                               CursorTy loc_2973,
                                                               CursorTy arg_2707)
{
    if (loc_2973 + 32 > end_r_2975) {
        ChunkTy new_chunk_189 = alloc_chunk(end_r_2975);
        CursorTy chunk_start_190 = new_chunk_189.chunk_start;
        CursorTy chunk_end_191 = new_chunk_189.chunk_end;
        
        end_r_2975 = chunk_end_191;
        *(TagTyPacked *) loc_2973 = 255;
        
        CursorTy redir = loc_2973 + 1;
        
        *(CursorTy *) redir = chunk_start_190;
        loc_2973 = chunk_start_190;
    }
    
    TagTyPacked tmpval_7395 = *(TagTyPacked *) arg_2707;
    CursorTy tmpcur_7396 = arg_2707 + 1;
    
    
  switch_7445:
    ;
    switch (tmpval_7395) {
        
      case 0:
        {
            CursorTy loc_3707 = loc_2973 + 1;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_String(end_r_2974, end_r_2975, loc_3707, tmpcur_7396);
            CursorTy pvrtmp_7397 = tmp_struct_185.field0;
            CursorTy pvrtmp_7398 = tmp_struct_185.field1;
            CursorTy pvrtmp_7399 = tmp_struct_185.field2;
            CursorTy pvrtmp_7400 = tmp_struct_185.field3;
            
            *(TagTyPacked *) loc_2973 = 0;
            
            CursorTy writetag_5033 = loc_2973 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7397, pvrtmp_7398,
                                                   loc_2973, pvrtmp_7400};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3713 = loc_2973 + 1;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_String(end_r_2974, end_r_2975, loc_3713, tmpcur_7396);
            CursorTy pvrtmp_7409 = tmp_struct_186.field0;
            CursorTy pvrtmp_7410 = tmp_struct_186.field1;
            CursorTy pvrtmp_7411 = tmp_struct_186.field2;
            CursorTy pvrtmp_7412 = tmp_struct_186.field3;
            
            *(TagTyPacked *) loc_2973 = 1;
            
            CursorTy writetag_5038 = loc_2973 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7409, pvrtmp_7410,
                                                   loc_2973, pvrtmp_7412};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7421 = *(CursorTy *) tmpcur_7396;
            CursorTy tmpaftercur_7422 = tmpcur_7396 + 8;
            CursorTy jump_4358 = tmpcur_7396 + 8;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Content(end_r_2974, end_r_2975, loc_2973, tmpcur_7421);
            CursorTy pvrtmp_7423 = tmp_struct_187.field0;
            CursorTy pvrtmp_7424 = tmp_struct_187.field1;
            CursorTy pvrtmp_7425 = tmp_struct_187.field2;
            CursorTy pvrtmp_7426 = tmp_struct_187.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7423, jump_4358,
                                                   pvrtmp_7425, pvrtmp_7426};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7433 = *(CursorTy *) tmpcur_7396;
            CursorTy tmpaftercur_7434 = tmpcur_7396 + 8;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Content(end_r_2974, end_r_2975, loc_2973, tmpcur_7433);
            CursorTy pvrtmp_7435 = tmp_struct_188.field0;
            CursorTy pvrtmp_7436 = tmp_struct_188.field1;
            CursorTy pvrtmp_7437 = tmp_struct_188.field2;
            CursorTy pvrtmp_7438 = tmp_struct_188.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7435, pvrtmp_7436,
                                                   pvrtmp_7437, pvrtmp_7438};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7395");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2978,
                                                           CursorTy end_r_2979,
                                                           CursorTy loc_2977,
                                                           CursorTy arg_2712)
{
    if (loc_2977 + 32 > end_r_2979) {
        ChunkTy new_chunk_216 = alloc_chunk(end_r_2979);
        CursorTy chunk_start_217 = new_chunk_216.chunk_start;
        CursorTy chunk_end_218 = new_chunk_216.chunk_end;
        
        end_r_2979 = chunk_end_218;
        *(TagTyPacked *) loc_2977 = 255;
        
        CursorTy redir = loc_2977 + 1;
        
        *(CursorTy *) redir = chunk_start_217;
        loc_2977 = chunk_start_217;
    }
    
    CursorTy loc_3726 = loc_2977 + 1;
    CursorTy loc_3727 = loc_3726 + 8;
    CursorTy loc_3728 = loc_3727 + 8;
    CursorTy loc_3744 = loc_2977 + 1;
    CursorTy loc_3745 = loc_3744 + 8;
    CursorTy loc_3746 = loc_3745 + 8;
    CursorTy loc_3766 = loc_2977 + 1;
    CursorTy loc_3767 = loc_3766 + 8;
    CursorTy loc_3768 = loc_3767 + 8;
    CursorTy loc_3769 = loc_3768 + 8;
    CursorTy loc_3793 = loc_2977 + 1;
    CursorTy loc_3794 = loc_3793 + 8;
    CursorTy loc_3795 = loc_3794 + 8;
    CursorTy loc_3796 = loc_3795 + 8;
    CursorTy loc_3820 = loc_2977 + 1;
    CursorTy loc_3821 = loc_3820 + 8;
    CursorTy loc_3822 = loc_3821 + 8;
    CursorTy loc_3823 = loc_3822 + 8;
    CursorTy loc_3847 = loc_2977 + 1;
    CursorTy loc_3848 = loc_3847 + 8;
    CursorTy loc_3849 = loc_3848 + 8;
    CursorTy loc_3850 = loc_3849 + 8;
    CursorTy loc_3874 = loc_2977 + 1;
    CursorTy loc_3875 = loc_3874 + 8;
    CursorTy loc_3876 = loc_3875 + 8;
    CursorTy loc_3877 = loc_3876 + 8;
    CursorTy loc_3901 = loc_2977 + 1;
    CursorTy loc_3902 = loc_3901 + 8;
    CursorTy loc_3903 = loc_3902 + 8;
    CursorTy loc_3904 = loc_3903 + 8;
    TagTyPacked tmpval_7446 = *(TagTyPacked *) arg_2712;
    CursorTy tmpcur_7447 = arg_2712 + 1;
    
    
  switch_7684:
    ;
    switch (tmpval_7446) {
        
      case 0:
        {
            CursorTy jump_4200 = arg_2712 + 1;
            
            *(TagTyPacked *) loc_2977 = 0;
            
            CursorTy writetag_5048 = loc_2977 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2979, jump_4200,
                                                   loc_2977, writetag_5048};
            break;
        }
        
      case 1:
        {
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, end_r_2979, loc_3728, tmpcur_7447);
            CursorTy pvrtmp_7452 = tmp_struct_192.field0;
            CursorTy pvrtmp_7453 = tmp_struct_192.field1;
            CursorTy pvrtmp_7454 = tmp_struct_192.field2;
            CursorTy pvrtmp_7455 = tmp_struct_192.field3;
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, pvrtmp_7452, pvrtmp_7455, pvrtmp_7453);
            CursorTy pvrtmp_7460 = tmp_struct_193.field0;
            CursorTy pvrtmp_7461 = tmp_struct_193.field1;
            CursorTy pvrtmp_7462 = tmp_struct_193.field2;
            CursorTy pvrtmp_7463 = tmp_struct_193.field3;
            IntTy sizeof_y_2715__2717 = pvrtmp_7455 - pvrtmp_7454;
            IntTy sizeof_y_2716__2718 = pvrtmp_7463 - pvrtmp_7462;
            IntTy fltPrm_2806 = sizeof_y_2715__2717 + 0;
            IntTy offset__2719 = 0 + fltPrm_2806;
            IntTy fltPrm_2807 = sizeof_y_2715__2717 + sizeof_y_2716__2718;
            IntTy size_dcon_2720 = 9 + fltPrm_2807;
            
            *(TagTyPacked *) loc_2977 = 160;
            
            CursorTy writetag_5053 = loc_2977 + 1;
            
            *(IntTy *) writetag_5053 = size_dcon_2720;
            
            CursorTy writecur_5054 = writetag_5053 + sizeof(IntTy);
            
            *(IntTy *) writecur_5054 = offset__2719;
            
            CursorTy writecur_5055 = writecur_5054 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7460, pvrtmp_7461,
                                                   loc_2977, pvrtmp_7463};
            break;
        }
        
      case 2:
        {
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, end_r_2979, loc_3746, tmpcur_7447);
            CursorTy pvrtmp_7472 = tmp_struct_194.field0;
            CursorTy pvrtmp_7473 = tmp_struct_194.field1;
            CursorTy pvrtmp_7474 = tmp_struct_194.field2;
            CursorTy pvrtmp_7475 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, pvrtmp_7472, pvrtmp_7475, pvrtmp_7473);
            CursorTy pvrtmp_7480 = tmp_struct_195.field0;
            CursorTy pvrtmp_7481 = tmp_struct_195.field1;
            CursorTy pvrtmp_7482 = tmp_struct_195.field2;
            CursorTy pvrtmp_7483 = tmp_struct_195.field3;
            IntTy sizeof_y_2723__2725 = pvrtmp_7475 - pvrtmp_7474;
            IntTy sizeof_y_2724__2726 = pvrtmp_7483 - pvrtmp_7482;
            IntTy fltPrm_2808 = sizeof_y_2723__2725 + 0;
            IntTy offset__2727 = 0 + fltPrm_2808;
            IntTy fltPrm_2809 = sizeof_y_2723__2725 + sizeof_y_2724__2726;
            IntTy size_dcon_2728 = 9 + fltPrm_2809;
            
            *(TagTyPacked *) loc_2977 = 162;
            
            CursorTy writetag_5062 = loc_2977 + 1;
            
            *(IntTy *) writetag_5062 = size_dcon_2728;
            
            CursorTy writecur_5063 = writetag_5062 + sizeof(IntTy);
            
            *(IntTy *) writecur_5063 = offset__2727;
            
            CursorTy writecur_5064 = writecur_5063 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7480, pvrtmp_7481,
                                                   loc_2977, pvrtmp_7483};
            break;
        }
        
      case 3:
        {
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Tags(end_r_2978, end_r_2979, loc_3769, tmpcur_7447);
            CursorTy pvrtmp_7492 = tmp_struct_196.field0;
            CursorTy pvrtmp_7493 = tmp_struct_196.field1;
            CursorTy pvrtmp_7494 = tmp_struct_196.field2;
            CursorTy pvrtmp_7495 = tmp_struct_196.field3;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, pvrtmp_7492, pvrtmp_7495, pvrtmp_7493);
            CursorTy pvrtmp_7500 = tmp_struct_197.field0;
            CursorTy pvrtmp_7501 = tmp_struct_197.field1;
            CursorTy pvrtmp_7502 = tmp_struct_197.field2;
            CursorTy pvrtmp_7503 = tmp_struct_197.field3;
            CursorCursorCursorCursorProd tmp_struct_198 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, pvrtmp_7500, pvrtmp_7503, pvrtmp_7501);
            CursorTy pvrtmp_7508 = tmp_struct_198.field0;
            CursorTy pvrtmp_7509 = tmp_struct_198.field1;
            CursorTy pvrtmp_7510 = tmp_struct_198.field2;
            CursorTy pvrtmp_7511 = tmp_struct_198.field3;
            IntTy sizeof_y_2732__2735 = pvrtmp_7495 - pvrtmp_7494;
            IntTy sizeof_y_2733__2736 = pvrtmp_7503 - pvrtmp_7502;
            IntTy sizeof_y_2734__2737 = pvrtmp_7511 - pvrtmp_7510;
            IntTy fltPrm_2810 = sizeof_y_2732__2735 + 0;
            IntTy offset__2738 = 8 + fltPrm_2810;
            IntTy fltPrm_2811 = sizeof_y_2732__2735 + sizeof_y_2733__2736;
            IntTy offset__2739 = 0 + fltPrm_2811;
            IntTy fltPrm_2813 = sizeof_y_2733__2736 + sizeof_y_2734__2737;
            IntTy fltPrm_2812 = sizeof_y_2732__2735 + fltPrm_2813;
            IntTy size_dcon_2740 = 17 + fltPrm_2812;
            
            *(TagTyPacked *) loc_2977 = 164;
            
            CursorTy writetag_5072 = loc_2977 + 1;
            
            *(IntTy *) writetag_5072 = size_dcon_2740;
            
            CursorTy writecur_5073 = writetag_5072 + sizeof(IntTy);
            
            *(IntTy *) writecur_5073 = offset__2738;
            
            CursorTy writecur_5074 = writecur_5073 + sizeof(IntTy);
            
            *(IntTy *) writecur_5074 = offset__2739;
            
            CursorTy writecur_5075 = writecur_5074 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7508, pvrtmp_7509,
                                                   loc_2977, pvrtmp_7511};
            break;
        }
        
      case 4:
        {
            CursorCursorCursorCursorProd tmp_struct_199 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, end_r_2979, loc_3796, tmpcur_7447);
            CursorTy pvrtmp_7520 = tmp_struct_199.field0;
            CursorTy pvrtmp_7521 = tmp_struct_199.field1;
            CursorTy pvrtmp_7522 = tmp_struct_199.field2;
            CursorTy pvrtmp_7523 = tmp_struct_199.field3;
            CursorCursorCursorCursorProd tmp_struct_200 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, pvrtmp_7520, pvrtmp_7523, pvrtmp_7521);
            CursorTy pvrtmp_7528 = tmp_struct_200.field0;
            CursorTy pvrtmp_7529 = tmp_struct_200.field1;
            CursorTy pvrtmp_7530 = tmp_struct_200.field2;
            CursorTy pvrtmp_7531 = tmp_struct_200.field3;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_2978, pvrtmp_7528, pvrtmp_7531, pvrtmp_7529);
            CursorTy pvrtmp_7536 = tmp_struct_201.field0;
            CursorTy pvrtmp_7537 = tmp_struct_201.field1;
            CursorTy pvrtmp_7538 = tmp_struct_201.field2;
            CursorTy pvrtmp_7539 = tmp_struct_201.field3;
            IntTy sizeof_y_2744__2747 = pvrtmp_7523 - pvrtmp_7522;
            IntTy sizeof_y_2745__2748 = pvrtmp_7531 - pvrtmp_7530;
            IntTy sizeof_y_2746__2749 = pvrtmp_7539 - pvrtmp_7538;
            IntTy fltPrm_2814 = sizeof_y_2744__2747 + 0;
            IntTy offset__2750 = 8 + fltPrm_2814;
            IntTy fltPrm_2815 = sizeof_y_2744__2747 + sizeof_y_2745__2748;
            IntTy offset__2751 = 0 + fltPrm_2815;
            IntTy fltPrm_2817 = sizeof_y_2745__2748 + sizeof_y_2746__2749;
            IntTy fltPrm_2816 = sizeof_y_2744__2747 + fltPrm_2817;
            IntTy size_dcon_2752 = 17 + fltPrm_2816;
            
            *(TagTyPacked *) loc_2977 = 166;
            
            CursorTy writetag_5084 = loc_2977 + 1;
            
            *(IntTy *) writetag_5084 = size_dcon_2752;
            
            CursorTy writecur_5085 = writetag_5084 + sizeof(IntTy);
            
            *(IntTy *) writecur_5085 = offset__2750;
            
            CursorTy writecur_5086 = writecur_5085 + sizeof(IntTy);
            
            *(IntTy *) writecur_5086 = offset__2751;
            
            CursorTy writecur_5087 = writecur_5086 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7536, pvrtmp_7537,
                                                   loc_2977, pvrtmp_7539};
            break;
        }
        
      case 5:
        {
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_2978, end_r_2979, loc_3823, tmpcur_7447);
            CursorTy pvrtmp_7548 = tmp_struct_202.field0;
            CursorTy pvrtmp_7549 = tmp_struct_202.field1;
            CursorTy pvrtmp_7550 = tmp_struct_202.field2;
            CursorTy pvrtmp_7551 = tmp_struct_202.field3;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, pvrtmp_7548, pvrtmp_7551, pvrtmp_7549);
            CursorTy pvrtmp_7556 = tmp_struct_203.field0;
            CursorTy pvrtmp_7557 = tmp_struct_203.field1;
            CursorTy pvrtmp_7558 = tmp_struct_203.field2;
            CursorTy pvrtmp_7559 = tmp_struct_203.field3;
            CursorCursorCursorCursorProd tmp_struct_204 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, pvrtmp_7556, pvrtmp_7559, pvrtmp_7557);
            CursorTy pvrtmp_7564 = tmp_struct_204.field0;
            CursorTy pvrtmp_7565 = tmp_struct_204.field1;
            CursorTy pvrtmp_7566 = tmp_struct_204.field2;
            CursorTy pvrtmp_7567 = tmp_struct_204.field3;
            IntTy sizeof_y_2756__2759 = pvrtmp_7551 - pvrtmp_7550;
            IntTy sizeof_y_2757__2760 = pvrtmp_7559 - pvrtmp_7558;
            IntTy sizeof_y_2758__2761 = pvrtmp_7567 - pvrtmp_7566;
            IntTy fltPrm_2818 = sizeof_y_2756__2759 + 0;
            IntTy offset__2762 = 8 + fltPrm_2818;
            IntTy fltPrm_2819 = sizeof_y_2756__2759 + sizeof_y_2757__2760;
            IntTy offset__2763 = 0 + fltPrm_2819;
            IntTy fltPrm_2821 = sizeof_y_2757__2760 + sizeof_y_2758__2761;
            IntTy fltPrm_2820 = sizeof_y_2756__2759 + fltPrm_2821;
            IntTy size_dcon_2764 = 17 + fltPrm_2820;
            
            *(TagTyPacked *) loc_2977 = 168;
            
            CursorTy writetag_5096 = loc_2977 + 1;
            
            *(IntTy *) writetag_5096 = size_dcon_2764;
            
            CursorTy writecur_5097 = writetag_5096 + sizeof(IntTy);
            
            *(IntTy *) writecur_5097 = offset__2762;
            
            CursorTy writecur_5098 = writecur_5097 + sizeof(IntTy);
            
            *(IntTy *) writecur_5098 = offset__2763;
            
            CursorTy writecur_5099 = writecur_5098 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7564, pvrtmp_7565,
                                                   loc_2977, pvrtmp_7567};
            break;
        }
        
      case 6:
        {
            CursorCursorCursorCursorProd tmp_struct_205 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, end_r_2979, loc_3850, tmpcur_7447);
            CursorTy pvrtmp_7576 = tmp_struct_205.field0;
            CursorTy pvrtmp_7577 = tmp_struct_205.field1;
            CursorTy pvrtmp_7578 = tmp_struct_205.field2;
            CursorTy pvrtmp_7579 = tmp_struct_205.field3;
            CursorCursorCursorCursorProd tmp_struct_206 =
                                          _add_size_and_rel_offsets_Tags(end_r_2978, pvrtmp_7576, pvrtmp_7579, pvrtmp_7577);
            CursorTy pvrtmp_7584 = tmp_struct_206.field0;
            CursorTy pvrtmp_7585 = tmp_struct_206.field1;
            CursorTy pvrtmp_7586 = tmp_struct_206.field2;
            CursorTy pvrtmp_7587 = tmp_struct_206.field3;
            CursorCursorCursorCursorProd tmp_struct_207 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, pvrtmp_7584, pvrtmp_7587, pvrtmp_7585);
            CursorTy pvrtmp_7592 = tmp_struct_207.field0;
            CursorTy pvrtmp_7593 = tmp_struct_207.field1;
            CursorTy pvrtmp_7594 = tmp_struct_207.field2;
            CursorTy pvrtmp_7595 = tmp_struct_207.field3;
            IntTy sizeof_y_2768__2771 = pvrtmp_7579 - pvrtmp_7578;
            IntTy sizeof_y_2769__2772 = pvrtmp_7587 - pvrtmp_7586;
            IntTy sizeof_y_2770__2773 = pvrtmp_7595 - pvrtmp_7594;
            IntTy fltPrm_2822 = sizeof_y_2768__2771 + 0;
            IntTy offset__2774 = 8 + fltPrm_2822;
            IntTy fltPrm_2823 = sizeof_y_2768__2771 + sizeof_y_2769__2772;
            IntTy offset__2775 = 0 + fltPrm_2823;
            IntTy fltPrm_2825 = sizeof_y_2769__2772 + sizeof_y_2770__2773;
            IntTy fltPrm_2824 = sizeof_y_2768__2771 + fltPrm_2825;
            IntTy size_dcon_2776 = 17 + fltPrm_2824;
            
            *(TagTyPacked *) loc_2977 = 170;
            
            CursorTy writetag_5108 = loc_2977 + 1;
            
            *(IntTy *) writetag_5108 = size_dcon_2776;
            
            CursorTy writecur_5109 = writetag_5108 + sizeof(IntTy);
            
            *(IntTy *) writecur_5109 = offset__2774;
            
            CursorTy writecur_5110 = writecur_5109 + sizeof(IntTy);
            
            *(IntTy *) writecur_5110 = offset__2775;
            
            CursorTy writecur_5111 = writecur_5110 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7592, pvrtmp_7593,
                                                   loc_2977, pvrtmp_7595};
            break;
        }
        
      case 7:
        {
            CursorCursorCursorCursorProd tmp_struct_208 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, end_r_2979, loc_3877, tmpcur_7447);
            CursorTy pvrtmp_7604 = tmp_struct_208.field0;
            CursorTy pvrtmp_7605 = tmp_struct_208.field1;
            CursorTy pvrtmp_7606 = tmp_struct_208.field2;
            CursorTy pvrtmp_7607 = tmp_struct_208.field3;
            CursorCursorCursorCursorProd tmp_struct_209 =
                                          _add_size_and_rel_offsets_Tags(end_r_2978, pvrtmp_7604, pvrtmp_7607, pvrtmp_7605);
            CursorTy pvrtmp_7612 = tmp_struct_209.field0;
            CursorTy pvrtmp_7613 = tmp_struct_209.field1;
            CursorTy pvrtmp_7614 = tmp_struct_209.field2;
            CursorTy pvrtmp_7615 = tmp_struct_209.field3;
            CursorCursorCursorCursorProd tmp_struct_210 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, pvrtmp_7612, pvrtmp_7615, pvrtmp_7613);
            CursorTy pvrtmp_7620 = tmp_struct_210.field0;
            CursorTy pvrtmp_7621 = tmp_struct_210.field1;
            CursorTy pvrtmp_7622 = tmp_struct_210.field2;
            CursorTy pvrtmp_7623 = tmp_struct_210.field3;
            IntTy sizeof_y_2780__2783 = pvrtmp_7607 - pvrtmp_7606;
            IntTy sizeof_y_2781__2784 = pvrtmp_7615 - pvrtmp_7614;
            IntTy sizeof_y_2782__2785 = pvrtmp_7623 - pvrtmp_7622;
            IntTy fltPrm_2826 = sizeof_y_2780__2783 + 0;
            IntTy offset__2786 = 8 + fltPrm_2826;
            IntTy fltPrm_2827 = sizeof_y_2780__2783 + sizeof_y_2781__2784;
            IntTy offset__2787 = 0 + fltPrm_2827;
            IntTy fltPrm_2829 = sizeof_y_2781__2784 + sizeof_y_2782__2785;
            IntTy fltPrm_2828 = sizeof_y_2780__2783 + fltPrm_2829;
            IntTy size_dcon_2788 = 17 + fltPrm_2828;
            
            *(TagTyPacked *) loc_2977 = 172;
            
            CursorTy writetag_5120 = loc_2977 + 1;
            
            *(IntTy *) writetag_5120 = size_dcon_2788;
            
            CursorTy writecur_5121 = writetag_5120 + sizeof(IntTy);
            
            *(IntTy *) writecur_5121 = offset__2786;
            
            CursorTy writecur_5122 = writecur_5121 + sizeof(IntTy);
            
            *(IntTy *) writecur_5122 = offset__2787;
            
            CursorTy writecur_5123 = writecur_5122 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7620, pvrtmp_7621,
                                                   loc_2977, pvrtmp_7623};
            break;
        }
        
      case 8:
        {
            CursorCursorCursorCursorProd tmp_struct_211 =
                                          _add_size_and_rel_offsets_Content(end_r_2978, end_r_2979, loc_3904, tmpcur_7447);
            CursorTy pvrtmp_7632 = tmp_struct_211.field0;
            CursorTy pvrtmp_7633 = tmp_struct_211.field1;
            CursorTy pvrtmp_7634 = tmp_struct_211.field2;
            CursorTy pvrtmp_7635 = tmp_struct_211.field3;
            CursorCursorCursorCursorProd tmp_struct_212 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, pvrtmp_7632, pvrtmp_7635, pvrtmp_7633);
            CursorTy pvrtmp_7640 = tmp_struct_212.field0;
            CursorTy pvrtmp_7641 = tmp_struct_212.field1;
            CursorTy pvrtmp_7642 = tmp_struct_212.field2;
            CursorTy pvrtmp_7643 = tmp_struct_212.field3;
            CursorCursorCursorCursorProd tmp_struct_213 =
                                          _add_size_and_rel_offsets_Tags(end_r_2978, pvrtmp_7640, pvrtmp_7643, pvrtmp_7641);
            CursorTy pvrtmp_7648 = tmp_struct_213.field0;
            CursorTy pvrtmp_7649 = tmp_struct_213.field1;
            CursorTy pvrtmp_7650 = tmp_struct_213.field2;
            CursorTy pvrtmp_7651 = tmp_struct_213.field3;
            IntTy sizeof_y_2792__2795 = pvrtmp_7635 - pvrtmp_7634;
            IntTy sizeof_y_2793__2796 = pvrtmp_7643 - pvrtmp_7642;
            IntTy sizeof_y_2794__2797 = pvrtmp_7651 - pvrtmp_7650;
            IntTy fltPrm_2830 = sizeof_y_2792__2795 + 0;
            IntTy offset__2798 = 8 + fltPrm_2830;
            IntTy fltPrm_2831 = sizeof_y_2792__2795 + sizeof_y_2793__2796;
            IntTy offset__2799 = 0 + fltPrm_2831;
            IntTy fltPrm_2833 = sizeof_y_2793__2796 + sizeof_y_2794__2797;
            IntTy fltPrm_2832 = sizeof_y_2792__2795 + fltPrm_2833;
            IntTy size_dcon_2800 = 17 + fltPrm_2832;
            
            *(TagTyPacked *) loc_2977 = 174;
            
            CursorTy writetag_5132 = loc_2977 + 1;
            
            *(IntTy *) writetag_5132 = size_dcon_2800;
            
            CursorTy writecur_5133 = writetag_5132 + sizeof(IntTy);
            
            *(IntTy *) writecur_5133 = offset__2798;
            
            CursorTy writecur_5134 = writecur_5133 + sizeof(IntTy);
            
            *(IntTy *) writecur_5134 = offset__2799;
            
            CursorTy writecur_5135 = writecur_5134 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7648, pvrtmp_7649,
                                                   loc_2977, pvrtmp_7651};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7660 = *(CursorTy *) tmpcur_7447;
            CursorTy tmpaftercur_7661 = tmpcur_7447 + 8;
            CursorTy jump_4364 = tmpcur_7447 + 8;
            CursorCursorCursorCursorProd tmp_struct_214 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, end_r_2979, loc_2977, tmpcur_7660);
            CursorTy pvrtmp_7662 = tmp_struct_214.field0;
            CursorTy pvrtmp_7663 = tmp_struct_214.field1;
            CursorTy pvrtmp_7664 = tmp_struct_214.field2;
            CursorTy pvrtmp_7665 = tmp_struct_214.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7662, jump_4364,
                                                   pvrtmp_7664, pvrtmp_7665};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7672 = *(CursorTy *) tmpcur_7447;
            CursorTy tmpaftercur_7673 = tmpcur_7447 + 8;
            CursorCursorCursorCursorProd tmp_struct_215 =
                                          _add_size_and_rel_offsets_Adt(end_r_2978, end_r_2979, loc_2977, tmpcur_7672);
            CursorTy pvrtmp_7674 = tmp_struct_215.field0;
            CursorTy pvrtmp_7675 = tmp_struct_215.field1;
            CursorTy pvrtmp_7676 = tmp_struct_215.field2;
            CursorTy pvrtmp_7677 = tmp_struct_215.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7674, pvrtmp_7675,
                                                   pvrtmp_7676, pvrtmp_7677};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7446");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2982,
                                                            CursorTy end_r_2983,
                                                            CursorTy loc_2981,
                                                            CursorTy arg_2801)
{
    if (loc_2981 + 32 > end_r_2983) {
        ChunkTy new_chunk_222 = alloc_chunk(end_r_2983);
        CursorTy chunk_start_223 = new_chunk_222.chunk_start;
        CursorTy chunk_end_224 = new_chunk_222.chunk_end;
        
        end_r_2983 = chunk_end_224;
        *(TagTyPacked *) loc_2981 = 255;
        
        CursorTy redir = loc_2981 + 1;
        
        *(CursorTy *) redir = chunk_start_223;
        loc_2981 = chunk_start_223;
    }
    
    CursorTy loc_3924 = loc_2981 + 1;
    CursorTy loc_3925 = loc_3924 + 8;
    TagTyPacked tmpval_7685 = *(TagTyPacked *) arg_2801;
    CursorTy tmpcur_7686 = arg_2801 + 1;
    
    
  switch_7729:
    ;
    switch (tmpval_7685) {
        
      case 0:
        {
            CursorTy jump_4232 = arg_2801 + 1;
            
            *(TagTyPacked *) loc_2981 = 0;
            
            CursorTy writetag_5147 = loc_2981 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2983, jump_4232,
                                                   loc_2981, writetag_5147};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7691 = *(IntTy *) tmpcur_7686;
            CursorTy tmpcur_7692 = tmpcur_7686 + sizeof(IntTy);
            CursorTy jump_4234 = tmpcur_7686 + 8;
            CursorCursorCursorCursorProd tmp_struct_219 =
                                          _add_size_and_rel_offsets_Tags(end_r_2982, end_r_2983, loc_3925, tmpcur_7692);
            CursorTy pvrtmp_7693 = tmp_struct_219.field0;
            CursorTy pvrtmp_7694 = tmp_struct_219.field1;
            CursorTy pvrtmp_7695 = tmp_struct_219.field2;
            CursorTy pvrtmp_7696 = tmp_struct_219.field3;
            
            *(TagTyPacked *) loc_2981 = 1;
            
            CursorTy writetag_5152 = loc_2981 + 1;
            
            *(IntTy *) writetag_5152 = tmpval_7691;
            
            CursorTy writecur_5153 = writetag_5152 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7693, pvrtmp_7694,
                                                   loc_2981, pvrtmp_7696};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7705 = *(CursorTy *) tmpcur_7686;
            CursorTy tmpaftercur_7706 = tmpcur_7686 + 8;
            CursorTy jump_4370 = tmpcur_7686 + 8;
            CursorCursorCursorCursorProd tmp_struct_220 =
                                          _add_size_and_rel_offsets_Tags(end_r_2982, end_r_2983, loc_2981, tmpcur_7705);
            CursorTy pvrtmp_7707 = tmp_struct_220.field0;
            CursorTy pvrtmp_7708 = tmp_struct_220.field1;
            CursorTy pvrtmp_7709 = tmp_struct_220.field2;
            CursorTy pvrtmp_7710 = tmp_struct_220.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7707, jump_4370,
                                                   pvrtmp_7709, pvrtmp_7710};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7717 = *(CursorTy *) tmpcur_7686;
            CursorTy tmpaftercur_7718 = tmpcur_7686 + 8;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          _add_size_and_rel_offsets_Tags(end_r_2982, end_r_2983, loc_2981, tmpcur_7717);
            CursorTy pvrtmp_7719 = tmp_struct_221.field0;
            CursorTy pvrtmp_7720 = tmp_struct_221.field1;
            CursorTy pvrtmp_7721 = tmp_struct_221.field2;
            CursorTy pvrtmp_7722 = tmp_struct_221.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7719, pvrtmp_7720,
                                                   pvrtmp_7721, pvrtmp_7722};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7685");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(6129, ")");
    add_symbol(6130, "(Text ");
    add_symbol(6131, "(Tag ");
    add_symbol(6132, "(TCA ");
    add_symbol(6133, "(TAC ");
    add_symbol(6134, "(Nul ");
    add_symbol(6135, "(Nil ");
    add_symbol(6136, "(Image ");
    add_symbol(6137, "(End ");
    add_symbol(6138, "(Char ");
    add_symbol(6139, "(CTA ");
    add_symbol(6140, "(CAT ");
    add_symbol(6141, "(CA ");
    add_symbol(6142, "(ATC ");
    add_symbol(6143, "(ACT ");
    add_symbol(6144, "(AC ");
    add_symbol(6145, " ->r ");
    add_symbol(6146, " ->i ");
    
    RegionTy *region_6147 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2993 = region_6147->reg_heap;
    IntTy sizeof_end_r_2993_6148 = global_init_inf_buf_size;
    CursorTy end_r_2993 = r_2993 + sizeof_end_r_2993_6148;
    RegionTy *region_6149 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2992 = region_6149->reg_heap;
    IntTy sizeof_end_r_2992_6150 = global_init_inf_buf_size;
    CursorTy end_r_2992 = r_2992 + sizeof_end_r_2992_6150;
    CursorCursorCursorProd tmp_struct_225 =
                            mkCATList(end_r_2993, r_2993, 100000, 10, 2000);
    CursorTy pvrtmp_6151 = tmp_struct_225.field0;
    CursorTy pvrtmp_6152 = tmp_struct_225.field1;
    CursorTy pvrtmp_6153 = tmp_struct_225.field2;
    CursorTy pvrtmp_6167;
    CursorTy pvrtmp_6168;
    CursorTy pvrtmp_6169;
    VectorTy *times_230 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6167;
    struct timespec end_pvrtmp_6167;
    
    start_counters();
    for (long long iters_pvrtmp_6167 = 0; iters_pvrtmp_6167 <
         global_iters_param; iters_pvrtmp_6167++) {
        if (iters_pvrtmp_6167 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6167);
        
        CursorCursorCursorProd tmp_struct_226 =
                                addValTagsAdt(pvrtmp_6151, end_r_2992, r_2992, pvrtmp_6152);
        CursorTy pvrtmp_6158 = tmp_struct_226.field0;
        CursorTy pvrtmp_6159 = tmp_struct_226.field1;
        CursorTy pvrtmp_6160 = tmp_struct_226.field2;
        
        pvrtmp_6167 = pvrtmp_6158;
        pvrtmp_6168 = pvrtmp_6159;
        pvrtmp_6169 = pvrtmp_6160;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6167);
        if (iters_pvrtmp_6167 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_227 = difftimespecs(&begin_pvrtmp_6167,
                                            &end_pvrtmp_6167);
        
        vector_inplace_update(times_230, iters_pvrtmp_6167, &itertime_227);
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
