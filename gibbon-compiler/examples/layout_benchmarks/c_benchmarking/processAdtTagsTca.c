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
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2920, CursorTy end_r_2921,
                                     CursorTy loc_2919,
                                     CursorTy adt_16_902_1520);
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2924, CursorTy end_r_2925,
                                       CursorTy loc_2923,
                                       CursorTy tags_22_908_1528,
                                       IntTy inVal_23_909_1529);
CursorCursorCursorProd mkTCAList(CursorTy end_r_2927, CursorTy loc_2926,
                                 IntTy len_26_912_1534,
                                 IntTy tagLen_27_913_1535,
                                 IntTy strLen_28_914_1536);
CursorCursorCursorProd mkString(CursorTy end_r_2929, CursorTy loc_2928,
                                IntTy len_181_1067_1542);
CursorCursorCursorProd mkContentText(CursorTy end_r_2931, CursorTy loc_2930,
                                     IntTy n_195_1081_1548);
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2933, CursorTy loc_2932,
                                    IntTy len_320_1206_1550);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2936,
                                          CursorTy end_r_2937,
                                          CursorTy loc_2935,
                                          CursorTy arg_624_1230_1555);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2940,
                                                       CursorTy end_r_2941,
                                                       CursorTy loc_2939,
                                                       CursorTy arg_629_1235_1560);
CursorProd _traverse_String(CursorTy end_r_2943, CursorTy arg_634_1240_1565);
CursorProd _print_String(CursorTy end_r_2945, CursorTy arg_639_1244_1569);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2948,
                                           CursorTy end_r_2949,
                                           CursorTy loc_2947,
                                           CursorTy arg_648_1253_1578);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2952,
                                                        CursorTy end_r_2953,
                                                        CursorTy loc_2951,
                                                        CursorTy arg_653_1258_1583);
CursorProd _traverse_Content(CursorTy end_r_2955, CursorTy arg_658_1263_1588);
CursorProd _print_Content(CursorTy end_r_2957, CursorTy arg_663_1268_1593);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2960, CursorTy end_r_2961,
                                       CursorTy loc_2959,
                                       CursorTy arg_672_1277_1602);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2964,
                                                    CursorTy end_r_2965,
                                                    CursorTy loc_2963,
                                                    CursorTy arg_717_1322_1647);
CursorProd _traverse_Adt(CursorTy end_r_2967, CursorTy arg_762_1367_1692);
CursorProd _print_Adt(CursorTy end_r_2969, CursorTy arg_807_1412_1737);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2972,
                                        CursorTy end_r_2973, CursorTy loc_2971,
                                        CursorTy arg_870_1475_1800);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2976,
                                                     CursorTy end_r_2977,
                                                     CursorTy loc_2975,
                                                     CursorTy arg_875_1480_1805);
CursorProd _traverse_Tags(CursorTy end_r_2979, CursorTy arg_880_1485_1810);
CursorProd _print_Tags(CursorTy end_r_2981, CursorTy arg_885_1489_1814);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_2984, CursorTy end_r_2985,
                                 CursorTy loc_2983, CursorTy arg_2716);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_2988, CursorTy end_r_2989,
                                  CursorTy loc_2987, CursorTy arg_2721);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2992,
                                                           CursorTy end_r_2993,
                                                           CursorTy loc_2991,
                                                           CursorTy arg_2726);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2996,
                                                            CursorTy end_r_2997,
                                                            CursorTy loc_2995,
                                                            CursorTy arg_2815);
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2920, CursorTy end_r_2921,
                                     CursorTy loc_2919,
                                     CursorTy adt_16_902_1520)
{
    if (loc_2919 + 32 > end_r_2921) {
        ChunkTy new_chunk_4 = alloc_chunk(end_r_2921);
        CursorTy chunk_start_5 = new_chunk_4.chunk_start;
        CursorTy chunk_end_6 = new_chunk_4.chunk_end;
        
        end_r_2921 = chunk_end_6;
        *(TagTyPacked *) loc_2919 = 255;
        
        CursorTy redir = loc_2919 + 1;
        
        *(CursorTy *) redir = chunk_start_5;
        loc_2919 = chunk_start_5;
    }
    
    CursorTy loc_3029 = loc_2919 + 1;
    CursorTy loc_3030 = loc_3029 + 8;
    CursorTy loc_3031 = loc_3030 + 8;
    TagTyPacked tmpval_6202 = *(TagTyPacked *) adt_16_902_1520;
    CursorTy tmpcur_6203 = adt_16_902_1520 + 1;
    
    
  switch_6259:
    ;
    switch (tmpval_6202) {
        
      case 0:
        {
            CursorTy jump_3955 = adt_16_902_1520 + 1;
            
            *(TagTyPacked *) loc_2919 = 0;
            
            CursorTy writetag_4514 = loc_2919 + 1;
            
            return (CursorCursorCursorProd) {end_r_2921, loc_2919,
                                             writetag_4514};
            break;
        }
        
      case 13:
        {
            RegionTy *region_6208 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3041 = region_6208->reg_heap;
            IntTy sizeof_end_r_3041_6209 = global_init_inf_buf_size;
            CursorTy end_r_3041 = r_3041 + sizeof_end_r_3041_6209;
            CursorTy tmpcur_6210 = *(CursorTy *) tmpcur_6203;
            CursorTy tmpaftercur_6211 = tmpcur_6203 + 8;
            CursorTy tmpcur_6212 = *(CursorTy *) tmpaftercur_6211;
            CursorTy tmpaftercur_6213 = tmpaftercur_6211 + 8;
            CursorTy jump_3958 = tmpaftercur_6211 + 8;
            CursorTy jump_3957 = tmpcur_6203 + 8;
            CursorCursorCursorCursorProd tmp_struct_0 =
                                          addValTag(end_r_2920, end_r_2921, loc_3031, tmpaftercur_6213, 10);
            CursorTy pvrtmp_6214 = tmp_struct_0.field0;
            CursorTy pvrtmp_6215 = tmp_struct_0.field1;
            CursorTy pvrtmp_6216 = tmp_struct_0.field2;
            CursorTy pvrtmp_6217 = tmp_struct_0.field3;
            CursorCursorCursorProd tmp_struct_1 =
                                    addValTagsAdt(end_r_2920, end_r_3041, r_3041, tmpcur_6212);
            CursorTy pvrtmp_6222 = tmp_struct_1.field0;
            CursorTy pvrtmp_6223 = tmp_struct_1.field1;
            CursorTy pvrtmp_6224 = tmp_struct_1.field2;
            
            *(TagTyPacked *) pvrtmp_6217 = 254;
            
            CursorTy writetag_4521 = pvrtmp_6217 + 1;
            
            *(CursorTy *) writetag_4521 = tmpcur_6210;
            
            CursorTy writecur_4522 = writetag_4521 + 8;
            
            *(TagTyPacked *) writecur_4522 = 254;
            
            CursorTy writetag_4524 = writecur_4522 + 1;
            
            *(CursorTy *) writetag_4524 = r_3041;
            
            CursorTy writecur_4525 = writetag_4524 + 8;
            
            *(TagTyPacked *) loc_2919 = 13;
            
            CursorTy writetag_4527 = loc_2919 + 1;
            
            *(CursorTy *) writetag_4527 = pvrtmp_6217;
            
            CursorTy writecur_4528 = writetag_4527 + 8;
            
            *(CursorTy *) writecur_4528 = writecur_4522;
            
            CursorTy writecur_4529 = writecur_4528 + 8;
            
            return (CursorCursorCursorProd) {pvrtmp_6214, loc_2919,
                                             writecur_4525};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6237 = *(CursorTy *) tmpcur_6203;
            CursorTy tmpaftercur_6238 = tmpcur_6203 + 8;
            CursorTy jump_4267 = tmpcur_6203 + 8;
            CursorCursorCursorProd tmp_struct_2 =
                                    addValTagsAdt(end_r_2920, end_r_2921, loc_2919, tmpcur_6237);
            CursorTy pvrtmp_6239 = tmp_struct_2.field0;
            CursorTy pvrtmp_6240 = tmp_struct_2.field1;
            CursorTy pvrtmp_6241 = tmp_struct_2.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6239, pvrtmp_6240,
                                             pvrtmp_6241};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6248 = *(CursorTy *) tmpcur_6203;
            CursorTy tmpaftercur_6249 = tmpcur_6203 + 8;
            CursorCursorCursorProd tmp_struct_3 =
                                    addValTagsAdt(end_r_2920, end_r_2921, loc_2919, tmpcur_6248);
            CursorTy pvrtmp_6250 = tmp_struct_3.field0;
            CursorTy pvrtmp_6251 = tmp_struct_3.field1;
            CursorTy pvrtmp_6252 = tmp_struct_3.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6250, pvrtmp_6251,
                                             pvrtmp_6252};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6202");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2924, CursorTy end_r_2925,
                                       CursorTy loc_2923,
                                       CursorTy tags_22_908_1528,
                                       IntTy inVal_23_909_1529)
{
    if (loc_2923 + 32 > end_r_2925) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2925);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2925 = chunk_end_12;
        *(TagTyPacked *) loc_2923 = 255;
        
        CursorTy redir = loc_2923 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2923 = chunk_start_11;
    }
    
    CursorTy loc_3050 = loc_2923 + 1;
    CursorTy loc_3051 = loc_3050 + 8;
    TagTyPacked tmpval_6260 = *(TagTyPacked *) tags_22_908_1528;
    CursorTy tmpcur_6261 = tags_22_908_1528 + 1;
    
    
  switch_6304:
    ;
    switch (tmpval_6260) {
        
      case 0:
        {
            CursorTy jump_3961 = tags_22_908_1528 + 1;
            
            *(TagTyPacked *) loc_2923 = 0;
            
            CursorTy writetag_4541 = loc_2923 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2925, jump_3961,
                                                   loc_2923, writetag_4541};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6266 = *(IntTy *) tmpcur_6261;
            CursorTy tmpcur_6267 = tmpcur_6261 + sizeof(IntTy);
            CursorTy jump_3963 = tmpcur_6261 + 8;
            IntTy fltPkd_1508_1532 = tmpval_6266 + inVal_23_909_1529;
            CursorCursorCursorCursorProd tmp_struct_7 =
                                          addValTag(end_r_2924, end_r_2925, loc_3051, tmpcur_6267, inVal_23_909_1529);
            CursorTy pvrtmp_6268 = tmp_struct_7.field0;
            CursorTy pvrtmp_6269 = tmp_struct_7.field1;
            CursorTy pvrtmp_6270 = tmp_struct_7.field2;
            CursorTy pvrtmp_6271 = tmp_struct_7.field3;
            
            *(TagTyPacked *) loc_2923 = 1;
            
            CursorTy writetag_4546 = loc_2923 + 1;
            
            *(IntTy *) writetag_4546 = fltPkd_1508_1532;
            
            CursorTy writecur_4547 = writetag_4546 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6268, pvrtmp_6269,
                                                   loc_2923, pvrtmp_6271};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6280 = *(CursorTy *) tmpcur_6261;
            CursorTy tmpaftercur_6281 = tmpcur_6261 + 8;
            CursorTy jump_4272 = tmpcur_6261 + 8;
            CursorCursorCursorCursorProd tmp_struct_8 =
                                          addValTag(end_r_2924, end_r_2925, loc_2923, tmpcur_6280, inVal_23_909_1529);
            CursorTy pvrtmp_6282 = tmp_struct_8.field0;
            CursorTy pvrtmp_6283 = tmp_struct_8.field1;
            CursorTy pvrtmp_6284 = tmp_struct_8.field2;
            CursorTy pvrtmp_6285 = tmp_struct_8.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6282, jump_4272,
                                                   pvrtmp_6284, pvrtmp_6285};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6292 = *(CursorTy *) tmpcur_6261;
            CursorTy tmpaftercur_6293 = tmpcur_6261 + 8;
            CursorCursorCursorCursorProd tmp_struct_9 =
                                          addValTag(end_r_2924, end_r_2925, loc_2923, tmpcur_6292, inVal_23_909_1529);
            CursorTy pvrtmp_6294 = tmp_struct_9.field0;
            CursorTy pvrtmp_6295 = tmp_struct_9.field1;
            CursorTy pvrtmp_6296 = tmp_struct_9.field2;
            CursorTy pvrtmp_6297 = tmp_struct_9.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6294, pvrtmp_6295,
                                                   pvrtmp_6296, pvrtmp_6297};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6260");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkTCAList(CursorTy end_r_2927, CursorTy loc_2926,
                                 IntTy len_26_912_1534,
                                 IntTy tagLen_27_913_1535,
                                 IntTy strLen_28_914_1536)
{
    if (loc_2926 + 32 > end_r_2927) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2927);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2927 = chunk_end_18;
        *(TagTyPacked *) loc_2926 = 255;
        
        CursorTy redir = loc_2926 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2926 = chunk_start_17;
    }
    
    CursorTy loc_3059 = loc_2926 + 1;
    CursorTy loc_3060 = loc_3059 + 8;
    CursorTy loc_3061 = loc_3060 + 8;
    BoolTy fltIf_1510_1537 = len_26_912_1534 <= 0;
    
    if (fltIf_1510_1537) {
        *(TagTyPacked *) loc_2926 = 0;
        
        CursorTy writetag_4556 = loc_2926 + 1;
        
        return (CursorCursorCursorProd) {end_r_2927, loc_2926, writetag_4556};
    } else {
        CursorCursorCursorProd tmp_struct_13 =
                                mkRandomTags(end_r_2927, loc_3061, tagLen_27_913_1535);
        CursorTy pvrtmp_6309 = tmp_struct_13.field0;
        CursorTy pvrtmp_6310 = tmp_struct_13.field1;
        CursorTy pvrtmp_6311 = tmp_struct_13.field2;
        CursorCursorCursorProd tmp_struct_14 =
                                mkContentText(pvrtmp_6309, pvrtmp_6311, strLen_28_914_1536);
        CursorTy pvrtmp_6316 = tmp_struct_14.field0;
        CursorTy pvrtmp_6317 = tmp_struct_14.field1;
        CursorTy pvrtmp_6318 = tmp_struct_14.field2;
        IntTy fltAppE_1511_1540 = len_26_912_1534 - 1;
        CursorCursorCursorProd tmp_struct_15 =
                                mkTCAList(pvrtmp_6316, pvrtmp_6318, fltAppE_1511_1540, tagLen_27_913_1535, strLen_28_914_1536);
        CursorTy pvrtmp_6323 = tmp_struct_15.field0;
        CursorTy pvrtmp_6324 = tmp_struct_15.field1;
        CursorTy pvrtmp_6325 = tmp_struct_15.field2;
        
        *(TagTyPacked *) loc_2926 = 13;
        
        CursorTy writetag_4561 = loc_2926 + 1;
        
        *(CursorTy *) writetag_4561 = pvrtmp_6311;
        
        CursorTy writecur_4562 = writetag_4561 + 8;
        
        *(CursorTy *) writecur_4562 = pvrtmp_6318;
        
        CursorTy writecur_4563 = writecur_4562 + 8;
        
        return (CursorCursorCursorProd) {pvrtmp_6323, loc_2926, pvrtmp_6325};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2929, CursorTy loc_2928,
                                IntTy len_181_1067_1542)
{
    if (loc_2928 + 32 > end_r_2929) {
        ChunkTy new_chunk_20 = alloc_chunk(end_r_2929);
        CursorTy chunk_start_21 = new_chunk_20.chunk_start;
        CursorTy chunk_end_22 = new_chunk_20.chunk_end;
        
        end_r_2929 = chunk_end_22;
        *(TagTyPacked *) loc_2928 = 255;
        
        CursorTy redir = loc_2928 + 1;
        
        *(CursorTy *) redir = chunk_start_21;
        loc_2928 = chunk_start_21;
    }
    
    CursorTy loc_3073 = loc_2928 + 1;
    CursorTy loc_3074 = loc_3073 + 8;
    BoolTy fltIf_1512_1543 = len_181_1067_1542 <= 0;
    
    if (fltIf_1512_1543) {
        *(TagTyPacked *) loc_2928 = 0;
        
        CursorTy writetag_4568 = loc_2928 + 1;
        
        return (CursorCursorCursorProd) {end_r_2929, loc_2928, writetag_4568};
    } else {
        IntTy fltPrm_1513_1544 = rand();
        IntTy randomChar_182_1068_1545 = fltPrm_1513_1544 % 128;
        IntTy fltAppE_1514_1546 = len_181_1067_1542 - 1;
        CursorCursorCursorProd tmp_struct_19 =
                                mkString(end_r_2929, loc_3074, fltAppE_1514_1546);
        CursorTy pvrtmp_6338 = tmp_struct_19.field0;
        CursorTy pvrtmp_6339 = tmp_struct_19.field1;
        CursorTy pvrtmp_6340 = tmp_struct_19.field2;
        
        *(TagTyPacked *) loc_2928 = 1;
        
        CursorTy writetag_4571 = loc_2928 + 1;
        
        *(IntTy *) writetag_4571 = randomChar_182_1068_1545;
        
        CursorTy writecur_4572 = writetag_4571 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6338, loc_2928, pvrtmp_6340};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2931, CursorTy loc_2930,
                                     IntTy n_195_1081_1548)
{
    if (loc_2930 + 32 > end_r_2931) {
        ChunkTy new_chunk_24 = alloc_chunk(end_r_2931);
        CursorTy chunk_start_25 = new_chunk_24.chunk_start;
        CursorTy chunk_end_26 = new_chunk_24.chunk_end;
        
        end_r_2931 = chunk_end_26;
        *(TagTyPacked *) loc_2930 = 255;
        
        CursorTy redir = loc_2930 + 1;
        
        *(CursorTy *) redir = chunk_start_25;
        loc_2930 = chunk_start_25;
    }
    
    CursorTy loc_3079 = loc_2930 + 1;
    CursorCursorCursorProd tmp_struct_23 =
                            mkString(end_r_2931, loc_3079, n_195_1081_1548);
    CursorTy pvrtmp_6349 = tmp_struct_23.field0;
    CursorTy pvrtmp_6350 = tmp_struct_23.field1;
    CursorTy pvrtmp_6351 = tmp_struct_23.field2;
    
    *(TagTyPacked *) loc_2930 = 1;
    
    CursorTy writetag_4576 = loc_2930 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_6349, loc_2930, pvrtmp_6351};
}
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2933, CursorTy loc_2932,
                                    IntTy len_320_1206_1550)
{
    if (loc_2932 + 32 > end_r_2933) {
        ChunkTy new_chunk_28 = alloc_chunk(end_r_2933);
        CursorTy chunk_start_29 = new_chunk_28.chunk_start;
        CursorTy chunk_end_30 = new_chunk_28.chunk_end;
        
        end_r_2933 = chunk_end_30;
        *(TagTyPacked *) loc_2932 = 255;
        
        CursorTy redir = loc_2932 + 1;
        
        *(CursorTy *) redir = chunk_start_29;
        loc_2932 = chunk_start_29;
    }
    
    CursorTy loc_3083 = loc_2932 + 1;
    CursorTy loc_3084 = loc_3083 + 8;
    BoolTy fltIf_1516_1551 = len_320_1206_1550 <= 0;
    
    if (fltIf_1516_1551) {
        *(TagTyPacked *) loc_2932 = 0;
        
        CursorTy writetag_4579 = loc_2932 + 1;
        
        return (CursorCursorCursorProd) {end_r_2933, loc_2932, writetag_4579};
    } else {
        IntTy fltAppE_1517_1553 = len_320_1206_1550 - 1;
        CursorCursorCursorProd tmp_struct_27 =
                                mkRandomTags(end_r_2933, loc_3084, fltAppE_1517_1553);
        CursorTy pvrtmp_6364 = tmp_struct_27.field0;
        CursorTy pvrtmp_6365 = tmp_struct_27.field1;
        CursorTy pvrtmp_6366 = tmp_struct_27.field2;
        
        *(TagTyPacked *) loc_2932 = 1;
        
        CursorTy writetag_4582 = loc_2932 + 1;
        
        *(IntTy *) writetag_4582 = 100;
        
        CursorTy writecur_4583 = writetag_4582 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6364, loc_2932, pvrtmp_6366};
    }
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2936,
                                          CursorTy end_r_2937,
                                          CursorTy loc_2935,
                                          CursorTy arg_624_1230_1555)
{
    if (loc_2935 + 32 > end_r_2937) {
        ChunkTy new_chunk_34 = alloc_chunk(end_r_2937);
        CursorTy chunk_start_35 = new_chunk_34.chunk_start;
        CursorTy chunk_end_36 = new_chunk_34.chunk_end;
        
        end_r_2937 = chunk_end_36;
        *(TagTyPacked *) loc_2935 = 255;
        
        CursorTy redir = loc_2935 + 1;
        
        *(CursorTy *) redir = chunk_start_35;
        loc_2935 = chunk_start_35;
    }
    
    CursorTy loc_3094 = loc_2935 + 1;
    CursorTy loc_3095 = loc_3094 + 8;
    TagTyPacked tmpval_6375 = *(TagTyPacked *) arg_624_1230_1555;
    CursorTy tmpcur_6376 = arg_624_1230_1555 + 1;
    
    
  switch_6419:
    ;
    switch (tmpval_6375) {
        
      case 0:
        {
            CursorTy jump_3973 = arg_624_1230_1555 + 1;
            
            *(TagTyPacked *) loc_2935 = 0;
            
            CursorTy writetag_4587 = loc_2935 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2937, jump_3973,
                                                   loc_2935, writetag_4587};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6381 = *(IntTy *) tmpcur_6376;
            CursorTy tmpcur_6382 = tmpcur_6376 + sizeof(IntTy);
            CursorTy jump_3975 = tmpcur_6376 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_String(end_r_2936, end_r_2937, loc_3095, tmpcur_6382);
            CursorTy pvrtmp_6383 = tmp_struct_31.field0;
            CursorTy pvrtmp_6384 = tmp_struct_31.field1;
            CursorTy pvrtmp_6385 = tmp_struct_31.field2;
            CursorTy pvrtmp_6386 = tmp_struct_31.field3;
            
            *(TagTyPacked *) loc_2935 = 1;
            
            CursorTy writetag_4592 = loc_2935 + 1;
            
            *(IntTy *) writetag_4592 = tmpval_6381;
            
            CursorTy writecur_4593 = writetag_4592 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6383, pvrtmp_6384,
                                                   loc_2935, pvrtmp_6386};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6395 = *(CursorTy *) tmpcur_6376;
            CursorTy tmpaftercur_6396 = tmpcur_6376 + 8;
            CursorTy jump_4278 = tmpcur_6376 + 8;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_String(end_r_2936, end_r_2937, loc_2935, tmpcur_6395);
            CursorTy pvrtmp_6397 = tmp_struct_32.field0;
            CursorTy pvrtmp_6398 = tmp_struct_32.field1;
            CursorTy pvrtmp_6399 = tmp_struct_32.field2;
            CursorTy pvrtmp_6400 = tmp_struct_32.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6397, jump_4278,
                                                   pvrtmp_6399, pvrtmp_6400};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6407 = *(CursorTy *) tmpcur_6376;
            CursorTy tmpaftercur_6408 = tmpcur_6376 + 8;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_String(end_r_2936, end_r_2937, loc_2935, tmpcur_6407);
            CursorTy pvrtmp_6409 = tmp_struct_33.field0;
            CursorTy pvrtmp_6410 = tmp_struct_33.field1;
            CursorTy pvrtmp_6411 = tmp_struct_33.field2;
            CursorTy pvrtmp_6412 = tmp_struct_33.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6409, pvrtmp_6410,
                                                   pvrtmp_6411, pvrtmp_6412};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6375");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2940,
                                                       CursorTy end_r_2941,
                                                       CursorTy loc_2939,
                                                       CursorTy arg_629_1235_1560)
{
    CursorTy loc_3107 = loc_2939 + 1;
    CursorTy loc_3108 = loc_3107 + 8;
    TagTyPacked tmpval_6420 = *(TagTyPacked *) arg_629_1235_1560;
    CursorTy tmpcur_6421 = arg_629_1235_1560 + 1;
    
    
  switch_6464:
    ;
    switch (tmpval_6420) {
        
      case 0:
        {
            CursorTy jump_3978 = arg_629_1235_1560 + 1;
            
            *(TagTyPacked *) loc_2939 = 0;
            
            CursorTy writetag_4603 = loc_2939 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2941, jump_3978,
                                                   loc_2939, writetag_4603};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6426 = *(IntTy *) tmpcur_6421;
            CursorTy tmpcur_6427 = tmpcur_6421 + sizeof(IntTy);
            CursorTy jump_3980 = tmpcur_6421 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_String(end_r_2940, end_r_2941, loc_3108, tmpcur_6427);
            CursorTy pvrtmp_6428 = tmp_struct_37.field0;
            CursorTy pvrtmp_6429 = tmp_struct_37.field1;
            CursorTy pvrtmp_6430 = tmp_struct_37.field2;
            CursorTy pvrtmp_6431 = tmp_struct_37.field3;
            
            *(TagTyPacked *) loc_2939 = 1;
            
            CursorTy writetag_4608 = loc_2939 + 1;
            
            *(IntTy *) writetag_4608 = tmpval_6426;
            
            CursorTy writecur_4609 = writetag_4608 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6428, pvrtmp_6429,
                                                   loc_2939, pvrtmp_6431};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6440 = *(CursorTy *) tmpcur_6421;
            CursorTy tmpaftercur_6441 = tmpcur_6421 + 8;
            CursorTy jump_4284 = tmpcur_6421 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_String(end_r_2940, end_r_2941, loc_2939, tmpcur_6440);
            CursorTy pvrtmp_6442 = tmp_struct_38.field0;
            CursorTy pvrtmp_6443 = tmp_struct_38.field1;
            CursorTy pvrtmp_6444 = tmp_struct_38.field2;
            CursorTy pvrtmp_6445 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6442, jump_4284,
                                                   pvrtmp_6444, pvrtmp_6445};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6452 = *(CursorTy *) tmpcur_6421;
            CursorTy tmpaftercur_6453 = tmpcur_6421 + 8;
            CursorCursorCursorCursorProd tmp_struct_39 =
                                          _copy_without_ptrs_String(end_r_2940, end_r_2941, loc_2939, tmpcur_6452);
            CursorTy pvrtmp_6454 = tmp_struct_39.field0;
            CursorTy pvrtmp_6455 = tmp_struct_39.field1;
            CursorTy pvrtmp_6456 = tmp_struct_39.field2;
            CursorTy pvrtmp_6457 = tmp_struct_39.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6454, pvrtmp_6455,
                                                   pvrtmp_6456, pvrtmp_6457};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6420");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2943, CursorTy arg_634_1240_1565)
{
    TagTyPacked tmpval_6465 = *(TagTyPacked *) arg_634_1240_1565;
    CursorTy tmpcur_6466 = arg_634_1240_1565 + 1;
    
    
  switch_6476:
    ;
    switch (tmpval_6465) {
        
      case 0:
        {
            CursorTy jump_3983 = arg_634_1240_1565 + 1;
            
            return (CursorProd) {jump_3983};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6467 = *(IntTy *) tmpcur_6466;
            CursorTy tmpcur_6468 = tmpcur_6466 + sizeof(IntTy);
            CursorTy jump_3985 = tmpcur_6466 + 8;
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2943, tmpcur_6468);
            CursorTy pvrtmp_6469 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_6469};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6470 = *(CursorTy *) tmpcur_6466;
            CursorTy tmpaftercur_6471 = tmpcur_6466 + 8;
            CursorTy jump_4290 = tmpcur_6466 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_String(end_r_2943, tmpcur_6470);
            CursorTy pvrtmp_6472 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_4290};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6473 = *(CursorTy *) tmpcur_6466;
            CursorTy tmpaftercur_6474 = tmpcur_6466 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_String(end_r_2943, tmpcur_6473);
            CursorTy pvrtmp_6475 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_6475};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6465");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2945, CursorTy arg_639_1244_1569)
{
    TagTyPacked tmpval_6477 = *(TagTyPacked *) arg_639_1244_1569;
    CursorTy tmpcur_6478 = arg_639_1244_1569 + 1;
    
    
  switch_6488:
    ;
    switch (tmpval_6477) {
        
      case 0:
        {
            CursorTy jump_3988 = arg_639_1244_1569 + 1;
            unsigned char wildcard_640_1245_1570 = print_symbol(6162);
            unsigned char wildcard_641_1246_1571 = print_symbol(6154);
            
            return (CursorProd) {jump_3988};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6479 = *(IntTy *) tmpcur_6478;
            CursorTy tmpcur_6480 = tmpcur_6478 + sizeof(IntTy);
            CursorTy jump_3990 = tmpcur_6478 + 8;
            unsigned char wildcard_646_1249_1574 = print_symbol(6163);
            unsigned char y_644_1250_1575 = printf("%lld", tmpval_6479);
            CursorProd tmp_struct_43 =  _print_String(end_r_2945, tmpcur_6480);
            CursorTy pvrtmp_6481 = tmp_struct_43.field0;
            unsigned char wildcard_647_1252_1577 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_6481};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6482 = *(CursorTy *) tmpcur_6478;
            CursorTy tmpaftercur_6483 = tmpcur_6478 + 8;
            CursorTy jump_4296 = tmpcur_6478 + 8;
            unsigned char wildcard_4299 = print_symbol(6171);
            CursorProd tmp_struct_44 =  _print_String(end_r_2945, tmpcur_6482);
            CursorTy pvrtmp_6484 = tmp_struct_44.field0;
            
            return (CursorProd) {jump_4296};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6485 = *(CursorTy *) tmpcur_6478;
            CursorTy tmpaftercur_6486 = tmpcur_6478 + 8;
            unsigned char wildcard_4299 = print_symbol(6170);
            CursorProd tmp_struct_45 =  _print_String(end_r_2945, tmpcur_6485);
            CursorTy pvrtmp_6487 = tmp_struct_45.field0;
            
            return (CursorProd) {pvrtmp_6487};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6477");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2948,
                                           CursorTy end_r_2949,
                                           CursorTy loc_2947,
                                           CursorTy arg_648_1253_1578)
{
    if (loc_2947 + 32 > end_r_2949) {
        ChunkTy new_chunk_50 = alloc_chunk(end_r_2949);
        CursorTy chunk_start_51 = new_chunk_50.chunk_start;
        CursorTy chunk_end_52 = new_chunk_50.chunk_end;
        
        end_r_2949 = chunk_end_52;
        *(TagTyPacked *) loc_2947 = 255;
        
        CursorTy redir = loc_2947 + 1;
        
        *(CursorTy *) redir = chunk_start_51;
        loc_2947 = chunk_start_51;
    }
    
    TagTyPacked tmpval_6489 = *(TagTyPacked *) arg_648_1253_1578;
    CursorTy tmpcur_6490 = arg_648_1253_1578 + 1;
    
    
  switch_6539:
    ;
    switch (tmpval_6489) {
        
      case 0:
        {
            CursorTy loc_3130 = loc_2947 + 1;
            CursorCursorCursorCursorProd tmp_struct_46 =
                                          _copy_String(end_r_2948, end_r_2949, loc_3130, tmpcur_6490);
            CursorTy pvrtmp_6491 = tmp_struct_46.field0;
            CursorTy pvrtmp_6492 = tmp_struct_46.field1;
            CursorTy pvrtmp_6493 = tmp_struct_46.field2;
            CursorTy pvrtmp_6494 = tmp_struct_46.field3;
            
            *(TagTyPacked *) loc_2947 = 0;
            
            CursorTy writetag_4640 = loc_2947 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6491, pvrtmp_6492,
                                                   loc_2947, pvrtmp_6494};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3136 = loc_2947 + 1;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_String(end_r_2948, end_r_2949, loc_3136, tmpcur_6490);
            CursorTy pvrtmp_6503 = tmp_struct_47.field0;
            CursorTy pvrtmp_6504 = tmp_struct_47.field1;
            CursorTy pvrtmp_6505 = tmp_struct_47.field2;
            CursorTy pvrtmp_6506 = tmp_struct_47.field3;
            
            *(TagTyPacked *) loc_2947 = 1;
            
            CursorTy writetag_4645 = loc_2947 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6503, pvrtmp_6504,
                                                   loc_2947, pvrtmp_6506};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6515 = *(CursorTy *) tmpcur_6490;
            CursorTy tmpaftercur_6516 = tmpcur_6490 + 8;
            CursorTy jump_4302 = tmpcur_6490 + 8;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Content(end_r_2948, end_r_2949, loc_2947, tmpcur_6515);
            CursorTy pvrtmp_6517 = tmp_struct_48.field0;
            CursorTy pvrtmp_6518 = tmp_struct_48.field1;
            CursorTy pvrtmp_6519 = tmp_struct_48.field2;
            CursorTy pvrtmp_6520 = tmp_struct_48.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6517, jump_4302,
                                                   pvrtmp_6519, pvrtmp_6520};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6527 = *(CursorTy *) tmpcur_6490;
            CursorTy tmpaftercur_6528 = tmpcur_6490 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Content(end_r_2948, end_r_2949, loc_2947, tmpcur_6527);
            CursorTy pvrtmp_6529 = tmp_struct_49.field0;
            CursorTy pvrtmp_6530 = tmp_struct_49.field1;
            CursorTy pvrtmp_6531 = tmp_struct_49.field2;
            CursorTy pvrtmp_6532 = tmp_struct_49.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6529, pvrtmp_6530,
                                                   pvrtmp_6531, pvrtmp_6532};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6489");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2952,
                                                        CursorTy end_r_2953,
                                                        CursorTy loc_2951,
                                                        CursorTy arg_653_1258_1583)
{
    TagTyPacked tmpval_6540 = *(TagTyPacked *) arg_653_1258_1583;
    CursorTy tmpcur_6541 = arg_653_1258_1583 + 1;
    
    
  switch_6590:
    ;
    switch (tmpval_6540) {
        
      case 0:
        {
            CursorTy loc_3144 = loc_2951 + 1;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_without_ptrs_String(end_r_2952, end_r_2953, loc_3144, tmpcur_6541);
            CursorTy pvrtmp_6542 = tmp_struct_53.field0;
            CursorTy pvrtmp_6543 = tmp_struct_53.field1;
            CursorTy pvrtmp_6544 = tmp_struct_53.field2;
            CursorTy pvrtmp_6545 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2951 = 0;
            
            CursorTy writetag_4656 = loc_2951 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6542, pvrtmp_6543,
                                                   loc_2951, pvrtmp_6545};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3150 = loc_2951 + 1;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_without_ptrs_String(end_r_2952, end_r_2953, loc_3150, tmpcur_6541);
            CursorTy pvrtmp_6554 = tmp_struct_54.field0;
            CursorTy pvrtmp_6555 = tmp_struct_54.field1;
            CursorTy pvrtmp_6556 = tmp_struct_54.field2;
            CursorTy pvrtmp_6557 = tmp_struct_54.field3;
            
            *(TagTyPacked *) loc_2951 = 1;
            
            CursorTy writetag_4661 = loc_2951 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6554, pvrtmp_6555,
                                                   loc_2951, pvrtmp_6557};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6566 = *(CursorTy *) tmpcur_6541;
            CursorTy tmpaftercur_6567 = tmpcur_6541 + 8;
            CursorTy jump_4308 = tmpcur_6541 + 8;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_without_ptrs_Content(end_r_2952, end_r_2953, loc_2951, tmpcur_6566);
            CursorTy pvrtmp_6568 = tmp_struct_55.field0;
            CursorTy pvrtmp_6569 = tmp_struct_55.field1;
            CursorTy pvrtmp_6570 = tmp_struct_55.field2;
            CursorTy pvrtmp_6571 = tmp_struct_55.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6568, jump_4308,
                                                   pvrtmp_6570, pvrtmp_6571};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6578 = *(CursorTy *) tmpcur_6541;
            CursorTy tmpaftercur_6579 = tmpcur_6541 + 8;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_without_ptrs_Content(end_r_2952, end_r_2953, loc_2951, tmpcur_6578);
            CursorTy pvrtmp_6580 = tmp_struct_56.field0;
            CursorTy pvrtmp_6581 = tmp_struct_56.field1;
            CursorTy pvrtmp_6582 = tmp_struct_56.field2;
            CursorTy pvrtmp_6583 = tmp_struct_56.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6580, pvrtmp_6581,
                                                   pvrtmp_6582, pvrtmp_6583};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6540");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2955, CursorTy arg_658_1263_1588)
{
    TagTyPacked tmpval_6591 = *(TagTyPacked *) arg_658_1263_1588;
    CursorTy tmpcur_6592 = arg_658_1263_1588 + 1;
    
    
  switch_6601:
    ;
    switch (tmpval_6591) {
        
      case 0:
        {
            CursorProd tmp_struct_57 =
                        _traverse_String(end_r_2955, tmpcur_6592);
            CursorTy pvrtmp_6593 = tmp_struct_57.field0;
            
            return (CursorProd) {pvrtmp_6593};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_58 =
                        _traverse_String(end_r_2955, tmpcur_6592);
            CursorTy pvrtmp_6594 = tmp_struct_58.field0;
            
            return (CursorProd) {pvrtmp_6594};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6595 = *(CursorTy *) tmpcur_6592;
            CursorTy tmpaftercur_6596 = tmpcur_6592 + 8;
            CursorTy jump_4314 = tmpcur_6592 + 8;
            CursorProd tmp_struct_59 =
                        _traverse_Content(end_r_2955, tmpcur_6595);
            CursorTy pvrtmp_6597 = tmp_struct_59.field0;
            
            return (CursorProd) {jump_4314};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6598 = *(CursorTy *) tmpcur_6592;
            CursorTy tmpaftercur_6599 = tmpcur_6592 + 8;
            CursorProd tmp_struct_60 =
                        _traverse_Content(end_r_2955, tmpcur_6598);
            CursorTy pvrtmp_6600 = tmp_struct_60.field0;
            
            return (CursorProd) {pvrtmp_6600};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6591");
            exit(1);
        }
    }
}
CursorProd _print_Content(CursorTy end_r_2957, CursorTy arg_663_1268_1593)
{
    TagTyPacked tmpval_6602 = *(TagTyPacked *) arg_663_1268_1593;
    CursorTy tmpcur_6603 = arg_663_1268_1593 + 1;
    
    
  switch_6612:
    ;
    switch (tmpval_6602) {
        
      case 0:
        {
            unsigned char wildcard_666_1270_1595 = print_symbol(6161);
            CursorProd tmp_struct_61 =  _print_String(end_r_2957, tmpcur_6603);
            CursorTy pvrtmp_6604 = tmp_struct_61.field0;
            unsigned char wildcard_667_1272_1597 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_6604};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_670_1274_1599 = print_symbol(6155);
            CursorProd tmp_struct_62 =  _print_String(end_r_2957, tmpcur_6603);
            CursorTy pvrtmp_6605 = tmp_struct_62.field0;
            unsigned char wildcard_671_1276_1601 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_6605};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6606 = *(CursorTy *) tmpcur_6603;
            CursorTy tmpaftercur_6607 = tmpcur_6603 + 8;
            CursorTy jump_4320 = tmpcur_6603 + 8;
            unsigned char wildcard_4323 = print_symbol(6171);
            CursorProd tmp_struct_63 =  _print_Content(end_r_2957, tmpcur_6606);
            CursorTy pvrtmp_6608 = tmp_struct_63.field0;
            
            return (CursorProd) {jump_4320};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6609 = *(CursorTy *) tmpcur_6603;
            CursorTy tmpaftercur_6610 = tmpcur_6603 + 8;
            unsigned char wildcard_4323 = print_symbol(6170);
            CursorProd tmp_struct_64 =  _print_Content(end_r_2957, tmpcur_6609);
            CursorTy pvrtmp_6611 = tmp_struct_64.field0;
            
            return (CursorProd) {pvrtmp_6611};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6602");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2960, CursorTy end_r_2961,
                                       CursorTy loc_2959,
                                       CursorTy arg_672_1277_1602)
{
    if (loc_2959 + 32 > end_r_2961) {
        ChunkTy new_chunk_89 = alloc_chunk(end_r_2961);
        CursorTy chunk_start_90 = new_chunk_89.chunk_start;
        CursorTy chunk_end_91 = new_chunk_89.chunk_end;
        
        end_r_2961 = chunk_end_91;
        *(TagTyPacked *) loc_2959 = 255;
        
        CursorTy redir = loc_2959 + 1;
        
        *(CursorTy *) redir = chunk_start_90;
        loc_2959 = chunk_start_90;
    }
    
    CursorTy loc_3180 = loc_2959 + 1;
    CursorTy loc_3181 = loc_3180 + 8;
    CursorTy loc_3196 = loc_2959 + 1;
    CursorTy loc_3197 = loc_3196 + 8;
    CursorTy loc_3217 = loc_2959 + 1;
    CursorTy loc_3218 = loc_3217 + 8;
    CursorTy loc_3219 = loc_3218 + 8;
    CursorTy loc_3243 = loc_2959 + 1;
    CursorTy loc_3244 = loc_3243 + 8;
    CursorTy loc_3245 = loc_3244 + 8;
    CursorTy loc_3269 = loc_2959 + 1;
    CursorTy loc_3270 = loc_3269 + 8;
    CursorTy loc_3271 = loc_3270 + 8;
    CursorTy loc_3295 = loc_2959 + 1;
    CursorTy loc_3296 = loc_3295 + 8;
    CursorTy loc_3297 = loc_3296 + 8;
    CursorTy loc_3321 = loc_2959 + 1;
    CursorTy loc_3322 = loc_3321 + 8;
    CursorTy loc_3323 = loc_3322 + 8;
    CursorTy loc_3347 = loc_2959 + 1;
    CursorTy loc_3348 = loc_3347 + 8;
    CursorTy loc_3349 = loc_3348 + 8;
    TagTyPacked tmpval_6613 = *(TagTyPacked *) arg_672_1277_1602;
    CursorTy tmpcur_6614 = arg_672_1277_1602 + 1;
    
    
  switch_6879:
    ;
    switch (tmpval_6613) {
        
      case 0:
        {
            CursorTy jump_4009 = arg_672_1277_1602 + 1;
            
            *(TagTyPacked *) loc_2959 = 0;
            
            CursorTy writetag_4691 = loc_2959 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2961, jump_4009,
                                                   loc_2959, writetag_4691};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6619 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6620 = tmpcur_6614 + 8;
            CursorTy jump_4011 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Content(end_r_2960, end_r_2961, loc_3181, tmpaftercur_6620);
            CursorTy pvrtmp_6621 = tmp_struct_65.field0;
            CursorTy pvrtmp_6622 = tmp_struct_65.field1;
            CursorTy pvrtmp_6623 = tmp_struct_65.field2;
            CursorTy pvrtmp_6624 = tmp_struct_65.field3;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Adt(end_r_2960, pvrtmp_6621, pvrtmp_6624, tmpcur_6619);
            CursorTy pvrtmp_6629 = tmp_struct_66.field0;
            CursorTy pvrtmp_6630 = tmp_struct_66.field1;
            CursorTy pvrtmp_6631 = tmp_struct_66.field2;
            CursorTy pvrtmp_6632 = tmp_struct_66.field3;
            
            *(TagTyPacked *) loc_2959 = 9;
            
            CursorTy writetag_4697 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4697 = pvrtmp_6624;
            
            CursorTy writecur_4698 = writetag_4697 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6629, pvrtmp_6630,
                                                   loc_2959, pvrtmp_6632};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6641 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6642 = tmpcur_6614 + 8;
            CursorTy jump_4015 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2960, end_r_2961, loc_3197, tmpaftercur_6642);
            CursorTy pvrtmp_6643 = tmp_struct_67.field0;
            CursorTy pvrtmp_6644 = tmp_struct_67.field1;
            CursorTy pvrtmp_6645 = tmp_struct_67.field2;
            CursorTy pvrtmp_6646 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Content(end_r_2960, pvrtmp_6643, pvrtmp_6646, tmpcur_6641);
            CursorTy pvrtmp_6651 = tmp_struct_68.field0;
            CursorTy pvrtmp_6652 = tmp_struct_68.field1;
            CursorTy pvrtmp_6653 = tmp_struct_68.field2;
            CursorTy pvrtmp_6654 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2959 = 11;
            
            CursorTy writetag_4706 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4706 = pvrtmp_6646;
            
            CursorTy writecur_4707 = writetag_4706 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6651, pvrtmp_6652,
                                                   loc_2959, pvrtmp_6654};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6663 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6664 = tmpcur_6614 + 8;
            CursorTy tmpcur_6665 = *(CursorTy *) tmpaftercur_6664;
            CursorTy tmpaftercur_6666 = tmpaftercur_6664 + 8;
            CursorTy jump_4020 = tmpaftercur_6664 + 8;
            CursorTy jump_4019 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Tags(end_r_2960, end_r_2961, loc_3219, tmpaftercur_6666);
            CursorTy pvrtmp_6667 = tmp_struct_69.field0;
            CursorTy pvrtmp_6668 = tmp_struct_69.field1;
            CursorTy pvrtmp_6669 = tmp_struct_69.field2;
            CursorTy pvrtmp_6670 = tmp_struct_69.field3;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Content(end_r_2960, pvrtmp_6667, pvrtmp_6670, tmpcur_6663);
            CursorTy pvrtmp_6675 = tmp_struct_70.field0;
            CursorTy pvrtmp_6676 = tmp_struct_70.field1;
            CursorTy pvrtmp_6677 = tmp_struct_70.field2;
            CursorTy pvrtmp_6678 = tmp_struct_70.field3;
            CursorCursorCursorCursorProd tmp_struct_71 =
                                          _copy_Adt(end_r_2960, pvrtmp_6675, pvrtmp_6678, tmpcur_6665);
            CursorTy pvrtmp_6683 = tmp_struct_71.field0;
            CursorTy pvrtmp_6684 = tmp_struct_71.field1;
            CursorTy pvrtmp_6685 = tmp_struct_71.field2;
            CursorTy pvrtmp_6686 = tmp_struct_71.field3;
            
            *(TagTyPacked *) loc_2959 = 13;
            
            CursorTy writetag_4717 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4717 = pvrtmp_6670;
            
            CursorTy writecur_4718 = writetag_4717 + 8;
            
            *(CursorTy *) writecur_4718 = pvrtmp_6678;
            
            CursorTy writecur_4719 = writecur_4718 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6683, pvrtmp_6684,
                                                   loc_2959, pvrtmp_6686};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6695 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6696 = tmpcur_6614 + 8;
            CursorTy tmpcur_6697 = *(CursorTy *) tmpaftercur_6696;
            CursorTy tmpaftercur_6698 = tmpaftercur_6696 + 8;
            CursorTy jump_4026 = tmpaftercur_6696 + 8;
            CursorTy jump_4025 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_72 =
                                          _copy_Adt(end_r_2960, end_r_2961, loc_3245, tmpaftercur_6698);
            CursorTy pvrtmp_6699 = tmp_struct_72.field0;
            CursorTy pvrtmp_6700 = tmp_struct_72.field1;
            CursorTy pvrtmp_6701 = tmp_struct_72.field2;
            CursorTy pvrtmp_6702 = tmp_struct_72.field3;
            CursorCursorCursorCursorProd tmp_struct_73 =
                                          _copy_Content(end_r_2960, pvrtmp_6699, pvrtmp_6702, tmpcur_6695);
            CursorTy pvrtmp_6707 = tmp_struct_73.field0;
            CursorTy pvrtmp_6708 = tmp_struct_73.field1;
            CursorTy pvrtmp_6709 = tmp_struct_73.field2;
            CursorTy pvrtmp_6710 = tmp_struct_73.field3;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_Tags(end_r_2960, pvrtmp_6707, pvrtmp_6710, tmpcur_6697);
            CursorTy pvrtmp_6715 = tmp_struct_74.field0;
            CursorTy pvrtmp_6716 = tmp_struct_74.field1;
            CursorTy pvrtmp_6717 = tmp_struct_74.field2;
            CursorTy pvrtmp_6718 = tmp_struct_74.field3;
            
            *(TagTyPacked *) loc_2959 = 15;
            
            CursorTy writetag_4730 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4730 = pvrtmp_6702;
            
            CursorTy writecur_4731 = writetag_4730 + 8;
            
            *(CursorTy *) writecur_4731 = pvrtmp_6710;
            
            CursorTy writecur_4732 = writecur_4731 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6715, pvrtmp_6716,
                                                   loc_2959, pvrtmp_6718};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6727 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6728 = tmpcur_6614 + 8;
            CursorTy tmpcur_6729 = *(CursorTy *) tmpaftercur_6728;
            CursorTy tmpaftercur_6730 = tmpaftercur_6728 + 8;
            CursorTy jump_4032 = tmpaftercur_6728 + 8;
            CursorTy jump_4031 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_Tags(end_r_2960, end_r_2961, loc_3271, tmpaftercur_6730);
            CursorTy pvrtmp_6731 = tmp_struct_75.field0;
            CursorTy pvrtmp_6732 = tmp_struct_75.field1;
            CursorTy pvrtmp_6733 = tmp_struct_75.field2;
            CursorTy pvrtmp_6734 = tmp_struct_75.field3;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_Adt(end_r_2960, pvrtmp_6731, pvrtmp_6734, tmpcur_6727);
            CursorTy pvrtmp_6739 = tmp_struct_76.field0;
            CursorTy pvrtmp_6740 = tmp_struct_76.field1;
            CursorTy pvrtmp_6741 = tmp_struct_76.field2;
            CursorTy pvrtmp_6742 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_Content(end_r_2960, pvrtmp_6739, pvrtmp_6742, tmpcur_6729);
            CursorTy pvrtmp_6747 = tmp_struct_77.field0;
            CursorTy pvrtmp_6748 = tmp_struct_77.field1;
            CursorTy pvrtmp_6749 = tmp_struct_77.field2;
            CursorTy pvrtmp_6750 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2959 = 17;
            
            CursorTy writetag_4743 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4743 = pvrtmp_6734;
            
            CursorTy writecur_4744 = writetag_4743 + 8;
            
            *(CursorTy *) writecur_4744 = pvrtmp_6742;
            
            CursorTy writecur_4745 = writecur_4744 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6747, pvrtmp_6748,
                                                   loc_2959, pvrtmp_6750};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6759 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6760 = tmpcur_6614 + 8;
            CursorTy tmpcur_6761 = *(CursorTy *) tmpaftercur_6760;
            CursorTy tmpaftercur_6762 = tmpaftercur_6760 + 8;
            CursorTy jump_4038 = tmpaftercur_6760 + 8;
            CursorTy jump_4037 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_Adt(end_r_2960, end_r_2961, loc_3297, tmpaftercur_6762);
            CursorTy pvrtmp_6763 = tmp_struct_78.field0;
            CursorTy pvrtmp_6764 = tmp_struct_78.field1;
            CursorTy pvrtmp_6765 = tmp_struct_78.field2;
            CursorTy pvrtmp_6766 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_Tags(end_r_2960, pvrtmp_6763, pvrtmp_6766, tmpcur_6759);
            CursorTy pvrtmp_6771 = tmp_struct_79.field0;
            CursorTy pvrtmp_6772 = tmp_struct_79.field1;
            CursorTy pvrtmp_6773 = tmp_struct_79.field2;
            CursorTy pvrtmp_6774 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_Content(end_r_2960, pvrtmp_6771, pvrtmp_6774, tmpcur_6761);
            CursorTy pvrtmp_6779 = tmp_struct_80.field0;
            CursorTy pvrtmp_6780 = tmp_struct_80.field1;
            CursorTy pvrtmp_6781 = tmp_struct_80.field2;
            CursorTy pvrtmp_6782 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2959 = 19;
            
            CursorTy writetag_4756 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4756 = pvrtmp_6766;
            
            CursorTy writecur_4757 = writetag_4756 + 8;
            
            *(CursorTy *) writecur_4757 = pvrtmp_6774;
            
            CursorTy writecur_4758 = writecur_4757 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6779, pvrtmp_6780,
                                                   loc_2959, pvrtmp_6782};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6791 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6792 = tmpcur_6614 + 8;
            CursorTy tmpcur_6793 = *(CursorTy *) tmpaftercur_6792;
            CursorTy tmpaftercur_6794 = tmpaftercur_6792 + 8;
            CursorTy jump_4044 = tmpaftercur_6792 + 8;
            CursorTy jump_4043 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_Content(end_r_2960, end_r_2961, loc_3323, tmpaftercur_6794);
            CursorTy pvrtmp_6795 = tmp_struct_81.field0;
            CursorTy pvrtmp_6796 = tmp_struct_81.field1;
            CursorTy pvrtmp_6797 = tmp_struct_81.field2;
            CursorTy pvrtmp_6798 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_Tags(end_r_2960, pvrtmp_6795, pvrtmp_6798, tmpcur_6791);
            CursorTy pvrtmp_6803 = tmp_struct_82.field0;
            CursorTy pvrtmp_6804 = tmp_struct_82.field1;
            CursorTy pvrtmp_6805 = tmp_struct_82.field2;
            CursorTy pvrtmp_6806 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_Adt(end_r_2960, pvrtmp_6803, pvrtmp_6806, tmpcur_6793);
            CursorTy pvrtmp_6811 = tmp_struct_83.field0;
            CursorTy pvrtmp_6812 = tmp_struct_83.field1;
            CursorTy pvrtmp_6813 = tmp_struct_83.field2;
            CursorTy pvrtmp_6814 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2959 = 21;
            
            CursorTy writetag_4769 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4769 = pvrtmp_6798;
            
            CursorTy writecur_4770 = writetag_4769 + 8;
            
            *(CursorTy *) writecur_4770 = pvrtmp_6806;
            
            CursorTy writecur_4771 = writecur_4770 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6811, pvrtmp_6812,
                                                   loc_2959, pvrtmp_6814};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6823 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6824 = tmpcur_6614 + 8;
            CursorTy tmpcur_6825 = *(CursorTy *) tmpaftercur_6824;
            CursorTy tmpaftercur_6826 = tmpaftercur_6824 + 8;
            CursorTy jump_4050 = tmpaftercur_6824 + 8;
            CursorTy jump_4049 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_Content(end_r_2960, end_r_2961, loc_3349, tmpaftercur_6826);
            CursorTy pvrtmp_6827 = tmp_struct_84.field0;
            CursorTy pvrtmp_6828 = tmp_struct_84.field1;
            CursorTy pvrtmp_6829 = tmp_struct_84.field2;
            CursorTy pvrtmp_6830 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_Adt(end_r_2960, pvrtmp_6827, pvrtmp_6830, tmpcur_6823);
            CursorTy pvrtmp_6835 = tmp_struct_85.field0;
            CursorTy pvrtmp_6836 = tmp_struct_85.field1;
            CursorTy pvrtmp_6837 = tmp_struct_85.field2;
            CursorTy pvrtmp_6838 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_Tags(end_r_2960, pvrtmp_6835, pvrtmp_6838, tmpcur_6825);
            CursorTy pvrtmp_6843 = tmp_struct_86.field0;
            CursorTy pvrtmp_6844 = tmp_struct_86.field1;
            CursorTy pvrtmp_6845 = tmp_struct_86.field2;
            CursorTy pvrtmp_6846 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2959 = 23;
            
            CursorTy writetag_4782 = loc_2959 + 1;
            
            *(CursorTy *) writetag_4782 = pvrtmp_6830;
            
            CursorTy writecur_4783 = writetag_4782 + 8;
            
            *(CursorTy *) writecur_4783 = pvrtmp_6838;
            
            CursorTy writecur_4784 = writecur_4783 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6843, pvrtmp_6844,
                                                   loc_2959, pvrtmp_6846};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6855 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6856 = tmpcur_6614 + 8;
            CursorTy jump_4326 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_Adt(end_r_2960, end_r_2961, loc_2959, tmpcur_6855);
            CursorTy pvrtmp_6857 = tmp_struct_87.field0;
            CursorTy pvrtmp_6858 = tmp_struct_87.field1;
            CursorTy pvrtmp_6859 = tmp_struct_87.field2;
            CursorTy pvrtmp_6860 = tmp_struct_87.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6857, jump_4326,
                                                   pvrtmp_6859, pvrtmp_6860};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6867 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6868 = tmpcur_6614 + 8;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_Adt(end_r_2960, end_r_2961, loc_2959, tmpcur_6867);
            CursorTy pvrtmp_6869 = tmp_struct_88.field0;
            CursorTy pvrtmp_6870 = tmp_struct_88.field1;
            CursorTy pvrtmp_6871 = tmp_struct_88.field2;
            CursorTy pvrtmp_6872 = tmp_struct_88.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6869, pvrtmp_6870,
                                                   pvrtmp_6871, pvrtmp_6872};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6613");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2964,
                                                    CursorTy end_r_2965,
                                                    CursorTy loc_2963,
                                                    CursorTy arg_717_1322_1647)
{
    TagTyPacked tmpval_6880 = *(TagTyPacked *) arg_717_1322_1647;
    CursorTy tmpcur_6881 = arg_717_1322_1647 + 1;
    
    
  switch_7146:
    ;
    switch (tmpval_6880) {
        
      case 0:
        {
            CursorTy jump_4055 = arg_717_1322_1647 + 1;
            
            *(TagTyPacked *) loc_2963 = 0;
            
            CursorTy writetag_4796 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2965, jump_4055,
                                                   loc_2963, writetag_4796};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6886 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_6887 = tmpcur_6881 + 8;
            CursorTy jump_4057 = tmpcur_6881 + 8;
            CursorTy loc_3371 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Content(end_r_2964, end_r_2965, loc_3371, tmpaftercur_6887);
            CursorTy pvrtmp_6888 = tmp_struct_92.field0;
            CursorTy pvrtmp_6889 = tmp_struct_92.field1;
            CursorTy pvrtmp_6890 = tmp_struct_92.field2;
            CursorTy pvrtmp_6891 = tmp_struct_92.field3;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Adt(end_r_2964, pvrtmp_6888, pvrtmp_6891, tmpcur_6886);
            CursorTy pvrtmp_6896 = tmp_struct_93.field0;
            CursorTy pvrtmp_6897 = tmp_struct_93.field1;
            CursorTy pvrtmp_6898 = tmp_struct_93.field2;
            CursorTy pvrtmp_6899 = tmp_struct_93.field3;
            
            *(TagTyPacked *) loc_2963 = 1;
            
            CursorTy writetag_4802 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6896, pvrtmp_6897,
                                                   loc_2963, pvrtmp_6899};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6908 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_6909 = tmpcur_6881 + 8;
            CursorTy jump_4061 = tmpcur_6881 + 8;
            CursorTy loc_3384 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2964, end_r_2965, loc_3384, tmpaftercur_6909);
            CursorTy pvrtmp_6910 = tmp_struct_94.field0;
            CursorTy pvrtmp_6911 = tmp_struct_94.field1;
            CursorTy pvrtmp_6912 = tmp_struct_94.field2;
            CursorTy pvrtmp_6913 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Content(end_r_2964, pvrtmp_6910, pvrtmp_6913, tmpcur_6908);
            CursorTy pvrtmp_6918 = tmp_struct_95.field0;
            CursorTy pvrtmp_6919 = tmp_struct_95.field1;
            CursorTy pvrtmp_6920 = tmp_struct_95.field2;
            CursorTy pvrtmp_6921 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2963 = 2;
            
            CursorTy writetag_4810 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6918, pvrtmp_6919,
                                                   loc_2963, pvrtmp_6921};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6930 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_6931 = tmpcur_6881 + 8;
            CursorTy tmpcur_6932 = *(CursorTy *) tmpaftercur_6931;
            CursorTy tmpaftercur_6933 = tmpaftercur_6931 + 8;
            CursorTy jump_4066 = tmpaftercur_6931 + 8;
            CursorTy jump_4065 = tmpcur_6881 + 8;
            CursorTy loc_3402 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Tags(end_r_2964, end_r_2965, loc_3402, tmpaftercur_6933);
            CursorTy pvrtmp_6934 = tmp_struct_96.field0;
            CursorTy pvrtmp_6935 = tmp_struct_96.field1;
            CursorTy pvrtmp_6936 = tmp_struct_96.field2;
            CursorTy pvrtmp_6937 = tmp_struct_96.field3;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Content(end_r_2964, pvrtmp_6934, pvrtmp_6937, tmpcur_6930);
            CursorTy pvrtmp_6942 = tmp_struct_97.field0;
            CursorTy pvrtmp_6943 = tmp_struct_97.field1;
            CursorTy pvrtmp_6944 = tmp_struct_97.field2;
            CursorTy pvrtmp_6945 = tmp_struct_97.field3;
            CursorCursorCursorCursorProd tmp_struct_98 =
                                          _copy_without_ptrs_Adt(end_r_2964, pvrtmp_6942, pvrtmp_6945, tmpcur_6932);
            CursorTy pvrtmp_6950 = tmp_struct_98.field0;
            CursorTy pvrtmp_6951 = tmp_struct_98.field1;
            CursorTy pvrtmp_6952 = tmp_struct_98.field2;
            CursorTy pvrtmp_6953 = tmp_struct_98.field3;
            
            *(TagTyPacked *) loc_2963 = 3;
            
            CursorTy writetag_4820 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6950, pvrtmp_6951,
                                                   loc_2963, pvrtmp_6953};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6962 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_6963 = tmpcur_6881 + 8;
            CursorTy tmpcur_6964 = *(CursorTy *) tmpaftercur_6963;
            CursorTy tmpaftercur_6965 = tmpaftercur_6963 + 8;
            CursorTy jump_4072 = tmpaftercur_6963 + 8;
            CursorTy jump_4071 = tmpcur_6881 + 8;
            CursorTy loc_3422 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_99 =
                                          _copy_without_ptrs_Adt(end_r_2964, end_r_2965, loc_3422, tmpaftercur_6965);
            CursorTy pvrtmp_6966 = tmp_struct_99.field0;
            CursorTy pvrtmp_6967 = tmp_struct_99.field1;
            CursorTy pvrtmp_6968 = tmp_struct_99.field2;
            CursorTy pvrtmp_6969 = tmp_struct_99.field3;
            CursorCursorCursorCursorProd tmp_struct_100 =
                                          _copy_without_ptrs_Content(end_r_2964, pvrtmp_6966, pvrtmp_6969, tmpcur_6962);
            CursorTy pvrtmp_6974 = tmp_struct_100.field0;
            CursorTy pvrtmp_6975 = tmp_struct_100.field1;
            CursorTy pvrtmp_6976 = tmp_struct_100.field2;
            CursorTy pvrtmp_6977 = tmp_struct_100.field3;
            CursorCursorCursorCursorProd tmp_struct_101 =
                                          _copy_without_ptrs_Tags(end_r_2964, pvrtmp_6974, pvrtmp_6977, tmpcur_6964);
            CursorTy pvrtmp_6982 = tmp_struct_101.field0;
            CursorTy pvrtmp_6983 = tmp_struct_101.field1;
            CursorTy pvrtmp_6984 = tmp_struct_101.field2;
            CursorTy pvrtmp_6985 = tmp_struct_101.field3;
            
            *(TagTyPacked *) loc_2963 = 4;
            
            CursorTy writetag_4831 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6982, pvrtmp_6983,
                                                   loc_2963, pvrtmp_6985};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6994 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_6995 = tmpcur_6881 + 8;
            CursorTy tmpcur_6996 = *(CursorTy *) tmpaftercur_6995;
            CursorTy tmpaftercur_6997 = tmpaftercur_6995 + 8;
            CursorTy jump_4078 = tmpaftercur_6995 + 8;
            CursorTy jump_4077 = tmpcur_6881 + 8;
            CursorTy loc_3442 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_102 =
                                          _copy_without_ptrs_Tags(end_r_2964, end_r_2965, loc_3442, tmpaftercur_6997);
            CursorTy pvrtmp_6998 = tmp_struct_102.field0;
            CursorTy pvrtmp_6999 = tmp_struct_102.field1;
            CursorTy pvrtmp_7000 = tmp_struct_102.field2;
            CursorTy pvrtmp_7001 = tmp_struct_102.field3;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          _copy_without_ptrs_Adt(end_r_2964, pvrtmp_6998, pvrtmp_7001, tmpcur_6994);
            CursorTy pvrtmp_7006 = tmp_struct_103.field0;
            CursorTy pvrtmp_7007 = tmp_struct_103.field1;
            CursorTy pvrtmp_7008 = tmp_struct_103.field2;
            CursorTy pvrtmp_7009 = tmp_struct_103.field3;
            CursorCursorCursorCursorProd tmp_struct_104 =
                                          _copy_without_ptrs_Content(end_r_2964, pvrtmp_7006, pvrtmp_7009, tmpcur_6996);
            CursorTy pvrtmp_7014 = tmp_struct_104.field0;
            CursorTy pvrtmp_7015 = tmp_struct_104.field1;
            CursorTy pvrtmp_7016 = tmp_struct_104.field2;
            CursorTy pvrtmp_7017 = tmp_struct_104.field3;
            
            *(TagTyPacked *) loc_2963 = 5;
            
            CursorTy writetag_4842 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7014, pvrtmp_7015,
                                                   loc_2963, pvrtmp_7017};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7026 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_7027 = tmpcur_6881 + 8;
            CursorTy tmpcur_7028 = *(CursorTy *) tmpaftercur_7027;
            CursorTy tmpaftercur_7029 = tmpaftercur_7027 + 8;
            CursorTy jump_4084 = tmpaftercur_7027 + 8;
            CursorTy jump_4083 = tmpcur_6881 + 8;
            CursorTy loc_3462 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_105 =
                                          _copy_without_ptrs_Adt(end_r_2964, end_r_2965, loc_3462, tmpaftercur_7029);
            CursorTy pvrtmp_7030 = tmp_struct_105.field0;
            CursorTy pvrtmp_7031 = tmp_struct_105.field1;
            CursorTy pvrtmp_7032 = tmp_struct_105.field2;
            CursorTy pvrtmp_7033 = tmp_struct_105.field3;
            CursorCursorCursorCursorProd tmp_struct_106 =
                                          _copy_without_ptrs_Tags(end_r_2964, pvrtmp_7030, pvrtmp_7033, tmpcur_7026);
            CursorTy pvrtmp_7038 = tmp_struct_106.field0;
            CursorTy pvrtmp_7039 = tmp_struct_106.field1;
            CursorTy pvrtmp_7040 = tmp_struct_106.field2;
            CursorTy pvrtmp_7041 = tmp_struct_106.field3;
            CursorCursorCursorCursorProd tmp_struct_107 =
                                          _copy_without_ptrs_Content(end_r_2964, pvrtmp_7038, pvrtmp_7041, tmpcur_7028);
            CursorTy pvrtmp_7046 = tmp_struct_107.field0;
            CursorTy pvrtmp_7047 = tmp_struct_107.field1;
            CursorTy pvrtmp_7048 = tmp_struct_107.field2;
            CursorTy pvrtmp_7049 = tmp_struct_107.field3;
            
            *(TagTyPacked *) loc_2963 = 6;
            
            CursorTy writetag_4853 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7046, pvrtmp_7047,
                                                   loc_2963, pvrtmp_7049};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7058 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_7059 = tmpcur_6881 + 8;
            CursorTy tmpcur_7060 = *(CursorTy *) tmpaftercur_7059;
            CursorTy tmpaftercur_7061 = tmpaftercur_7059 + 8;
            CursorTy jump_4090 = tmpaftercur_7059 + 8;
            CursorTy jump_4089 = tmpcur_6881 + 8;
            CursorTy loc_3482 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_108 =
                                          _copy_without_ptrs_Content(end_r_2964, end_r_2965, loc_3482, tmpaftercur_7061);
            CursorTy pvrtmp_7062 = tmp_struct_108.field0;
            CursorTy pvrtmp_7063 = tmp_struct_108.field1;
            CursorTy pvrtmp_7064 = tmp_struct_108.field2;
            CursorTy pvrtmp_7065 = tmp_struct_108.field3;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          _copy_without_ptrs_Tags(end_r_2964, pvrtmp_7062, pvrtmp_7065, tmpcur_7058);
            CursorTy pvrtmp_7070 = tmp_struct_109.field0;
            CursorTy pvrtmp_7071 = tmp_struct_109.field1;
            CursorTy pvrtmp_7072 = tmp_struct_109.field2;
            CursorTy pvrtmp_7073 = tmp_struct_109.field3;
            CursorCursorCursorCursorProd tmp_struct_110 =
                                          _copy_without_ptrs_Adt(end_r_2964, pvrtmp_7070, pvrtmp_7073, tmpcur_7060);
            CursorTy pvrtmp_7078 = tmp_struct_110.field0;
            CursorTy pvrtmp_7079 = tmp_struct_110.field1;
            CursorTy pvrtmp_7080 = tmp_struct_110.field2;
            CursorTy pvrtmp_7081 = tmp_struct_110.field3;
            
            *(TagTyPacked *) loc_2963 = 7;
            
            CursorTy writetag_4864 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7078, pvrtmp_7079,
                                                   loc_2963, pvrtmp_7081};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7090 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_7091 = tmpcur_6881 + 8;
            CursorTy tmpcur_7092 = *(CursorTy *) tmpaftercur_7091;
            CursorTy tmpaftercur_7093 = tmpaftercur_7091 + 8;
            CursorTy jump_4096 = tmpaftercur_7091 + 8;
            CursorTy jump_4095 = tmpcur_6881 + 8;
            CursorTy loc_3502 = loc_2963 + 1;
            CursorCursorCursorCursorProd tmp_struct_111 =
                                          _copy_without_ptrs_Content(end_r_2964, end_r_2965, loc_3502, tmpaftercur_7093);
            CursorTy pvrtmp_7094 = tmp_struct_111.field0;
            CursorTy pvrtmp_7095 = tmp_struct_111.field1;
            CursorTy pvrtmp_7096 = tmp_struct_111.field2;
            CursorTy pvrtmp_7097 = tmp_struct_111.field3;
            CursorCursorCursorCursorProd tmp_struct_112 =
                                          _copy_without_ptrs_Adt(end_r_2964, pvrtmp_7094, pvrtmp_7097, tmpcur_7090);
            CursorTy pvrtmp_7102 = tmp_struct_112.field0;
            CursorTy pvrtmp_7103 = tmp_struct_112.field1;
            CursorTy pvrtmp_7104 = tmp_struct_112.field2;
            CursorTy pvrtmp_7105 = tmp_struct_112.field3;
            CursorCursorCursorCursorProd tmp_struct_113 =
                                          _copy_without_ptrs_Tags(end_r_2964, pvrtmp_7102, pvrtmp_7105, tmpcur_7092);
            CursorTy pvrtmp_7110 = tmp_struct_113.field0;
            CursorTy pvrtmp_7111 = tmp_struct_113.field1;
            CursorTy pvrtmp_7112 = tmp_struct_113.field2;
            CursorTy pvrtmp_7113 = tmp_struct_113.field3;
            
            *(TagTyPacked *) loc_2963 = 8;
            
            CursorTy writetag_4875 = loc_2963 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7110, pvrtmp_7111,
                                                   loc_2963, pvrtmp_7113};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7122 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_7123 = tmpcur_6881 + 8;
            CursorTy jump_4332 = tmpcur_6881 + 8;
            CursorCursorCursorCursorProd tmp_struct_114 =
                                          _copy_without_ptrs_Adt(end_r_2964, end_r_2965, loc_2963, tmpcur_7122);
            CursorTy pvrtmp_7124 = tmp_struct_114.field0;
            CursorTy pvrtmp_7125 = tmp_struct_114.field1;
            CursorTy pvrtmp_7126 = tmp_struct_114.field2;
            CursorTy pvrtmp_7127 = tmp_struct_114.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7124, jump_4332,
                                                   pvrtmp_7126, pvrtmp_7127};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7134 = *(CursorTy *) tmpcur_6881;
            CursorTy tmpaftercur_7135 = tmpcur_6881 + 8;
            CursorCursorCursorCursorProd tmp_struct_115 =
                                          _copy_without_ptrs_Adt(end_r_2964, end_r_2965, loc_2963, tmpcur_7134);
            CursorTy pvrtmp_7136 = tmp_struct_115.field0;
            CursorTy pvrtmp_7137 = tmp_struct_115.field1;
            CursorTy pvrtmp_7138 = tmp_struct_115.field2;
            CursorTy pvrtmp_7139 = tmp_struct_115.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7136, pvrtmp_7137,
                                                   pvrtmp_7138, pvrtmp_7139};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6880");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2967, CursorTy arg_762_1367_1692)
{
    TagTyPacked tmpval_7147 = *(TagTyPacked *) arg_762_1367_1692;
    CursorTy tmpcur_7148 = arg_762_1367_1692 + 1;
    
    
  switch_7205:
    ;
    switch (tmpval_7147) {
        
      case 0:
        {
            CursorTy jump_4101 = arg_762_1367_1692 + 1;
            
            return (CursorProd) {jump_4101};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7149 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7150 = tmpcur_7148 + 8;
            CursorTy jump_4103 = tmpcur_7148 + 8;
            CursorProd tmp_struct_116 =
                        _traverse_Content(end_r_2967, tmpaftercur_7150);
            CursorTy pvrtmp_7151 = tmp_struct_116.field0;
            CursorProd tmp_struct_117 =  _traverse_Adt(end_r_2967, tmpcur_7149);
            CursorTy pvrtmp_7152 = tmp_struct_117.field0;
            
            return (CursorProd) {pvrtmp_7152};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7153 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7154 = tmpcur_7148 + 8;
            CursorTy jump_4107 = tmpcur_7148 + 8;
            CursorProd tmp_struct_118 =
                        _traverse_Adt(end_r_2967, tmpaftercur_7154);
            CursorTy pvrtmp_7155 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Content(end_r_2967, tmpcur_7153);
            CursorTy pvrtmp_7156 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_7156};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7157 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7158 = tmpcur_7148 + 8;
            CursorTy tmpcur_7159 = *(CursorTy *) tmpaftercur_7158;
            CursorTy tmpaftercur_7160 = tmpaftercur_7158 + 8;
            CursorTy jump_4112 = tmpaftercur_7158 + 8;
            CursorTy jump_4111 = tmpcur_7148 + 8;
            CursorProd tmp_struct_120 =
                        _traverse_Tags(end_r_2967, tmpaftercur_7160);
            CursorTy pvrtmp_7161 = tmp_struct_120.field0;
            CursorProd tmp_struct_121 =
                        _traverse_Content(end_r_2967, tmpcur_7157);
            CursorTy pvrtmp_7162 = tmp_struct_121.field0;
            CursorProd tmp_struct_122 =  _traverse_Adt(end_r_2967, tmpcur_7159);
            CursorTy pvrtmp_7163 = tmp_struct_122.field0;
            
            return (CursorProd) {pvrtmp_7163};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7164 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7165 = tmpcur_7148 + 8;
            CursorTy tmpcur_7166 = *(CursorTy *) tmpaftercur_7165;
            CursorTy tmpaftercur_7167 = tmpaftercur_7165 + 8;
            CursorTy jump_4118 = tmpaftercur_7165 + 8;
            CursorTy jump_4117 = tmpcur_7148 + 8;
            CursorProd tmp_struct_123 =
                        _traverse_Adt(end_r_2967, tmpaftercur_7167);
            CursorTy pvrtmp_7168 = tmp_struct_123.field0;
            CursorProd tmp_struct_124 =
                        _traverse_Content(end_r_2967, tmpcur_7164);
            CursorTy pvrtmp_7169 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _traverse_Tags(end_r_2967, tmpcur_7166);
            CursorTy pvrtmp_7170 = tmp_struct_125.field0;
            
            return (CursorProd) {pvrtmp_7170};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7171 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7172 = tmpcur_7148 + 8;
            CursorTy tmpcur_7173 = *(CursorTy *) tmpaftercur_7172;
            CursorTy tmpaftercur_7174 = tmpaftercur_7172 + 8;
            CursorTy jump_4124 = tmpaftercur_7172 + 8;
            CursorTy jump_4123 = tmpcur_7148 + 8;
            CursorProd tmp_struct_126 =
                        _traverse_Tags(end_r_2967, tmpaftercur_7174);
            CursorTy pvrtmp_7175 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =  _traverse_Adt(end_r_2967, tmpcur_7171);
            CursorTy pvrtmp_7176 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =
                        _traverse_Content(end_r_2967, tmpcur_7173);
            CursorTy pvrtmp_7177 = tmp_struct_128.field0;
            
            return (CursorProd) {pvrtmp_7177};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7178 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7179 = tmpcur_7148 + 8;
            CursorTy tmpcur_7180 = *(CursorTy *) tmpaftercur_7179;
            CursorTy tmpaftercur_7181 = tmpaftercur_7179 + 8;
            CursorTy jump_4130 = tmpaftercur_7179 + 8;
            CursorTy jump_4129 = tmpcur_7148 + 8;
            CursorProd tmp_struct_129 =
                        _traverse_Adt(end_r_2967, tmpaftercur_7181);
            CursorTy pvrtmp_7182 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _traverse_Tags(end_r_2967, tmpcur_7178);
            CursorTy pvrtmp_7183 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =
                        _traverse_Content(end_r_2967, tmpcur_7180);
            CursorTy pvrtmp_7184 = tmp_struct_131.field0;
            
            return (CursorProd) {pvrtmp_7184};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7185 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7186 = tmpcur_7148 + 8;
            CursorTy tmpcur_7187 = *(CursorTy *) tmpaftercur_7186;
            CursorTy tmpaftercur_7188 = tmpaftercur_7186 + 8;
            CursorTy jump_4136 = tmpaftercur_7186 + 8;
            CursorTy jump_4135 = tmpcur_7148 + 8;
            CursorProd tmp_struct_132 =
                        _traverse_Content(end_r_2967, tmpaftercur_7188);
            CursorTy pvrtmp_7189 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =
                        _traverse_Tags(end_r_2967, tmpcur_7185);
            CursorTy pvrtmp_7190 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =  _traverse_Adt(end_r_2967, tmpcur_7187);
            CursorTy pvrtmp_7191 = tmp_struct_134.field0;
            
            return (CursorProd) {pvrtmp_7191};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7192 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7193 = tmpcur_7148 + 8;
            CursorTy tmpcur_7194 = *(CursorTy *) tmpaftercur_7193;
            CursorTy tmpaftercur_7195 = tmpaftercur_7193 + 8;
            CursorTy jump_4142 = tmpaftercur_7193 + 8;
            CursorTy jump_4141 = tmpcur_7148 + 8;
            CursorProd tmp_struct_135 =
                        _traverse_Content(end_r_2967, tmpaftercur_7195);
            CursorTy pvrtmp_7196 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _traverse_Adt(end_r_2967, tmpcur_7192);
            CursorTy pvrtmp_7197 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _traverse_Tags(end_r_2967, tmpcur_7194);
            CursorTy pvrtmp_7198 = tmp_struct_137.field0;
            
            return (CursorProd) {pvrtmp_7198};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7199 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7200 = tmpcur_7148 + 8;
            CursorTy jump_4338 = tmpcur_7148 + 8;
            CursorProd tmp_struct_138 =  _traverse_Adt(end_r_2967, tmpcur_7199);
            CursorTy pvrtmp_7201 = tmp_struct_138.field0;
            
            return (CursorProd) {jump_4338};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7202 = *(CursorTy *) tmpcur_7148;
            CursorTy tmpaftercur_7203 = tmpcur_7148 + 8;
            CursorProd tmp_struct_139 =  _traverse_Adt(end_r_2967, tmpcur_7202);
            CursorTy pvrtmp_7204 = tmp_struct_139.field0;
            
            return (CursorProd) {pvrtmp_7204};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7147");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2969, CursorTy arg_807_1412_1737)
{
    TagTyPacked tmpval_7206 = *(TagTyPacked *) arg_807_1412_1737;
    CursorTy tmpcur_7207 = arg_807_1412_1737 + 1;
    
    
  switch_7264:
    ;
    switch (tmpval_7206) {
        
      case 0:
        {
            CursorTy jump_4147 = arg_807_1412_1737 + 1;
            unsigned char wildcard_808_1413_1738 = print_symbol(6160);
            unsigned char wildcard_809_1414_1739 = print_symbol(6154);
            
            return (CursorProd) {jump_4147};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7208 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7209 = tmpcur_7207 + 8;
            CursorTy jump_4149 = tmpcur_7207 + 8;
            unsigned char wildcard_814_1417_1742 = print_symbol(6166);
            CursorProd tmp_struct_140 =
                        _print_Content(end_r_2969, tmpaftercur_7209);
            CursorTy pvrtmp_7210 = tmp_struct_140.field0;
            CursorProd tmp_struct_141 =  _print_Adt(end_r_2969, tmpcur_7208);
            CursorTy pvrtmp_7211 = tmp_struct_141.field0;
            unsigned char wildcard_815_1420_1745 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7211};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7212 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7213 = tmpcur_7207 + 8;
            CursorTy jump_4153 = tmpcur_7207 + 8;
            unsigned char wildcard_820_1423_1748 = print_symbol(6169);
            CursorProd tmp_struct_142 =
                        _print_Adt(end_r_2969, tmpaftercur_7213);
            CursorTy pvrtmp_7214 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =
                        _print_Content(end_r_2969, tmpcur_7212);
            CursorTy pvrtmp_7215 = tmp_struct_143.field0;
            unsigned char wildcard_821_1426_1751 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7215};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7216 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7217 = tmpcur_7207 + 8;
            CursorTy tmpcur_7218 = *(CursorTy *) tmpaftercur_7217;
            CursorTy tmpaftercur_7219 = tmpaftercur_7217 + 8;
            CursorTy jump_4158 = tmpaftercur_7217 + 8;
            CursorTy jump_4157 = tmpcur_7207 + 8;
            unsigned char wildcard_828_1430_1755 = print_symbol(6157);
            CursorProd tmp_struct_144 =
                        _print_Tags(end_r_2969, tmpaftercur_7219);
            CursorTy pvrtmp_7220 = tmp_struct_144.field0;
            CursorProd tmp_struct_145 =
                        _print_Content(end_r_2969, tmpcur_7216);
            CursorTy pvrtmp_7221 = tmp_struct_145.field0;
            CursorProd tmp_struct_146 =  _print_Adt(end_r_2969, tmpcur_7218);
            CursorTy pvrtmp_7222 = tmp_struct_146.field0;
            unsigned char wildcard_829_1434_1759 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7222};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7223 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7224 = tmpcur_7207 + 8;
            CursorTy tmpcur_7225 = *(CursorTy *) tmpaftercur_7224;
            CursorTy tmpaftercur_7226 = tmpaftercur_7224 + 8;
            CursorTy jump_4164 = tmpaftercur_7224 + 8;
            CursorTy jump_4163 = tmpcur_7207 + 8;
            unsigned char wildcard_836_1438_1763 = print_symbol(6168);
            CursorProd tmp_struct_147 =
                        _print_Adt(end_r_2969, tmpaftercur_7226);
            CursorTy pvrtmp_7227 = tmp_struct_147.field0;
            CursorProd tmp_struct_148 =
                        _print_Content(end_r_2969, tmpcur_7223);
            CursorTy pvrtmp_7228 = tmp_struct_148.field0;
            CursorProd tmp_struct_149 =  _print_Tags(end_r_2969, tmpcur_7225);
            CursorTy pvrtmp_7229 = tmp_struct_149.field0;
            unsigned char wildcard_837_1442_1767 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7229};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7230 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7231 = tmpcur_7207 + 8;
            CursorTy tmpcur_7232 = *(CursorTy *) tmpaftercur_7231;
            CursorTy tmpaftercur_7233 = tmpaftercur_7231 + 8;
            CursorTy jump_4170 = tmpaftercur_7231 + 8;
            CursorTy jump_4169 = tmpcur_7207 + 8;
            unsigned char wildcard_844_1446_1771 = print_symbol(6158);
            CursorProd tmp_struct_150 =
                        _print_Tags(end_r_2969, tmpaftercur_7233);
            CursorTy pvrtmp_7234 = tmp_struct_150.field0;
            CursorProd tmp_struct_151 =  _print_Adt(end_r_2969, tmpcur_7230);
            CursorTy pvrtmp_7235 = tmp_struct_151.field0;
            CursorProd tmp_struct_152 =
                        _print_Content(end_r_2969, tmpcur_7232);
            CursorTy pvrtmp_7236 = tmp_struct_152.field0;
            unsigned char wildcard_845_1450_1775 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7236};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7237 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7238 = tmpcur_7207 + 8;
            CursorTy tmpcur_7239 = *(CursorTy *) tmpaftercur_7238;
            CursorTy tmpaftercur_7240 = tmpaftercur_7238 + 8;
            CursorTy jump_4176 = tmpaftercur_7238 + 8;
            CursorTy jump_4175 = tmpcur_7207 + 8;
            unsigned char wildcard_852_1454_1779 = print_symbol(6167);
            CursorProd tmp_struct_153 =
                        _print_Adt(end_r_2969, tmpaftercur_7240);
            CursorTy pvrtmp_7241 = tmp_struct_153.field0;
            CursorProd tmp_struct_154 =  _print_Tags(end_r_2969, tmpcur_7237);
            CursorTy pvrtmp_7242 = tmp_struct_154.field0;
            CursorProd tmp_struct_155 =
                        _print_Content(end_r_2969, tmpcur_7239);
            CursorTy pvrtmp_7243 = tmp_struct_155.field0;
            unsigned char wildcard_853_1458_1783 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7243};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7244 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7245 = tmpcur_7207 + 8;
            CursorTy tmpcur_7246 = *(CursorTy *) tmpaftercur_7245;
            CursorTy tmpaftercur_7247 = tmpaftercur_7245 + 8;
            CursorTy jump_4182 = tmpaftercur_7245 + 8;
            CursorTy jump_4181 = tmpcur_7207 + 8;
            unsigned char wildcard_860_1462_1787 = print_symbol(6164);
            CursorProd tmp_struct_156 =
                        _print_Content(end_r_2969, tmpaftercur_7247);
            CursorTy pvrtmp_7248 = tmp_struct_156.field0;
            CursorProd tmp_struct_157 =  _print_Tags(end_r_2969, tmpcur_7244);
            CursorTy pvrtmp_7249 = tmp_struct_157.field0;
            CursorProd tmp_struct_158 =  _print_Adt(end_r_2969, tmpcur_7246);
            CursorTy pvrtmp_7250 = tmp_struct_158.field0;
            unsigned char wildcard_861_1466_1791 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7250};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7251 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7252 = tmpcur_7207 + 8;
            CursorTy tmpcur_7253 = *(CursorTy *) tmpaftercur_7252;
            CursorTy tmpaftercur_7254 = tmpaftercur_7252 + 8;
            CursorTy jump_4188 = tmpaftercur_7252 + 8;
            CursorTy jump_4187 = tmpcur_7207 + 8;
            unsigned char wildcard_868_1470_1795 = print_symbol(6165);
            CursorProd tmp_struct_159 =
                        _print_Content(end_r_2969, tmpaftercur_7254);
            CursorTy pvrtmp_7255 = tmp_struct_159.field0;
            CursorProd tmp_struct_160 =  _print_Adt(end_r_2969, tmpcur_7251);
            CursorTy pvrtmp_7256 = tmp_struct_160.field0;
            CursorProd tmp_struct_161 =  _print_Tags(end_r_2969, tmpcur_7253);
            CursorTy pvrtmp_7257 = tmp_struct_161.field0;
            unsigned char wildcard_869_1474_1799 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7257};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7258 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7259 = tmpcur_7207 + 8;
            CursorTy jump_4344 = tmpcur_7207 + 8;
            unsigned char wildcard_4347 = print_symbol(6171);
            CursorProd tmp_struct_162 =  _print_Adt(end_r_2969, tmpcur_7258);
            CursorTy pvrtmp_7260 = tmp_struct_162.field0;
            
            return (CursorProd) {jump_4344};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7261 = *(CursorTy *) tmpcur_7207;
            CursorTy tmpaftercur_7262 = tmpcur_7207 + 8;
            unsigned char wildcard_4347 = print_symbol(6170);
            CursorProd tmp_struct_163 =  _print_Adt(end_r_2969, tmpcur_7261);
            CursorTy pvrtmp_7263 = tmp_struct_163.field0;
            
            return (CursorProd) {pvrtmp_7263};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7206");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2972,
                                        CursorTy end_r_2973, CursorTy loc_2971,
                                        CursorTy arg_870_1475_1800)
{
    if (loc_2971 + 32 > end_r_2973) {
        ChunkTy new_chunk_167 = alloc_chunk(end_r_2973);
        CursorTy chunk_start_168 = new_chunk_167.chunk_start;
        CursorTy chunk_end_169 = new_chunk_167.chunk_end;
        
        end_r_2973 = chunk_end_169;
        *(TagTyPacked *) loc_2971 = 255;
        
        CursorTy redir = loc_2971 + 1;
        
        *(CursorTy *) redir = chunk_start_168;
        loc_2971 = chunk_start_168;
    }
    
    CursorTy loc_3680 = loc_2971 + 1;
    CursorTy loc_3681 = loc_3680 + 8;
    TagTyPacked tmpval_7265 = *(TagTyPacked *) arg_870_1475_1800;
    CursorTy tmpcur_7266 = arg_870_1475_1800 + 1;
    
    
  switch_7309:
    ;
    switch (tmpval_7265) {
        
      case 0:
        {
            CursorTy jump_4193 = arg_870_1475_1800 + 1;
            
            *(TagTyPacked *) loc_2971 = 0;
            
            CursorTy writetag_4989 = loc_2971 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2973, jump_4193,
                                                   loc_2971, writetag_4989};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7271 = *(IntTy *) tmpcur_7266;
            CursorTy tmpcur_7272 = tmpcur_7266 + sizeof(IntTy);
            CursorTy jump_4195 = tmpcur_7266 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          _copy_Tags(end_r_2972, end_r_2973, loc_3681, tmpcur_7272);
            CursorTy pvrtmp_7273 = tmp_struct_164.field0;
            CursorTy pvrtmp_7274 = tmp_struct_164.field1;
            CursorTy pvrtmp_7275 = tmp_struct_164.field2;
            CursorTy pvrtmp_7276 = tmp_struct_164.field3;
            
            *(TagTyPacked *) loc_2971 = 1;
            
            CursorTy writetag_4994 = loc_2971 + 1;
            
            *(IntTy *) writetag_4994 = tmpval_7271;
            
            CursorTy writecur_4995 = writetag_4994 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7273, pvrtmp_7274,
                                                   loc_2971, pvrtmp_7276};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7285 = *(CursorTy *) tmpcur_7266;
            CursorTy tmpaftercur_7286 = tmpcur_7266 + 8;
            CursorTy jump_4350 = tmpcur_7266 + 8;
            CursorCursorCursorCursorProd tmp_struct_165 =
                                          _copy_Tags(end_r_2972, end_r_2973, loc_2971, tmpcur_7285);
            CursorTy pvrtmp_7287 = tmp_struct_165.field0;
            CursorTy pvrtmp_7288 = tmp_struct_165.field1;
            CursorTy pvrtmp_7289 = tmp_struct_165.field2;
            CursorTy pvrtmp_7290 = tmp_struct_165.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7287, jump_4350,
                                                   pvrtmp_7289, pvrtmp_7290};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7297 = *(CursorTy *) tmpcur_7266;
            CursorTy tmpaftercur_7298 = tmpcur_7266 + 8;
            CursorCursorCursorCursorProd tmp_struct_166 =
                                          _copy_Tags(end_r_2972, end_r_2973, loc_2971, tmpcur_7297);
            CursorTy pvrtmp_7299 = tmp_struct_166.field0;
            CursorTy pvrtmp_7300 = tmp_struct_166.field1;
            CursorTy pvrtmp_7301 = tmp_struct_166.field2;
            CursorTy pvrtmp_7302 = tmp_struct_166.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7299, pvrtmp_7300,
                                                   pvrtmp_7301, pvrtmp_7302};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7265");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2976,
                                                     CursorTy end_r_2977,
                                                     CursorTy loc_2975,
                                                     CursorTy arg_875_1480_1805)
{
    CursorTy loc_3693 = loc_2975 + 1;
    CursorTy loc_3694 = loc_3693 + 8;
    TagTyPacked tmpval_7310 = *(TagTyPacked *) arg_875_1480_1805;
    CursorTy tmpcur_7311 = arg_875_1480_1805 + 1;
    
    
  switch_7354:
    ;
    switch (tmpval_7310) {
        
      case 0:
        {
            CursorTy jump_4198 = arg_875_1480_1805 + 1;
            
            *(TagTyPacked *) loc_2975 = 0;
            
            CursorTy writetag_5005 = loc_2975 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2977, jump_4198,
                                                   loc_2975, writetag_5005};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7316 = *(IntTy *) tmpcur_7311;
            CursorTy tmpcur_7317 = tmpcur_7311 + sizeof(IntTy);
            CursorTy jump_4200 = tmpcur_7311 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _copy_without_ptrs_Tags(end_r_2976, end_r_2977, loc_3694, tmpcur_7317);
            CursorTy pvrtmp_7318 = tmp_struct_170.field0;
            CursorTy pvrtmp_7319 = tmp_struct_170.field1;
            CursorTy pvrtmp_7320 = tmp_struct_170.field2;
            CursorTy pvrtmp_7321 = tmp_struct_170.field3;
            
            *(TagTyPacked *) loc_2975 = 1;
            
            CursorTy writetag_5010 = loc_2975 + 1;
            
            *(IntTy *) writetag_5010 = tmpval_7316;
            
            CursorTy writecur_5011 = writetag_5010 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7318, pvrtmp_7319,
                                                   loc_2975, pvrtmp_7321};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7330 = *(CursorTy *) tmpcur_7311;
            CursorTy tmpaftercur_7331 = tmpcur_7311 + 8;
            CursorTy jump_4356 = tmpcur_7311 + 8;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          _copy_without_ptrs_Tags(end_r_2976, end_r_2977, loc_2975, tmpcur_7330);
            CursorTy pvrtmp_7332 = tmp_struct_171.field0;
            CursorTy pvrtmp_7333 = tmp_struct_171.field1;
            CursorTy pvrtmp_7334 = tmp_struct_171.field2;
            CursorTy pvrtmp_7335 = tmp_struct_171.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7332, jump_4356,
                                                   pvrtmp_7334, pvrtmp_7335};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7342 = *(CursorTy *) tmpcur_7311;
            CursorTy tmpaftercur_7343 = tmpcur_7311 + 8;
            CursorCursorCursorCursorProd tmp_struct_172 =
                                          _copy_without_ptrs_Tags(end_r_2976, end_r_2977, loc_2975, tmpcur_7342);
            CursorTy pvrtmp_7344 = tmp_struct_172.field0;
            CursorTy pvrtmp_7345 = tmp_struct_172.field1;
            CursorTy pvrtmp_7346 = tmp_struct_172.field2;
            CursorTy pvrtmp_7347 = tmp_struct_172.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7344, pvrtmp_7345,
                                                   pvrtmp_7346, pvrtmp_7347};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7310");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_2979, CursorTy arg_880_1485_1810)
{
    TagTyPacked tmpval_7355 = *(TagTyPacked *) arg_880_1485_1810;
    CursorTy tmpcur_7356 = arg_880_1485_1810 + 1;
    
    
  switch_7366:
    ;
    switch (tmpval_7355) {
        
      case 0:
        {
            CursorTy jump_4203 = arg_880_1485_1810 + 1;
            
            return (CursorProd) {jump_4203};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7357 = *(IntTy *) tmpcur_7356;
            CursorTy tmpcur_7358 = tmpcur_7356 + sizeof(IntTy);
            CursorTy jump_4205 = tmpcur_7356 + 8;
            CursorProd tmp_struct_173 =
                        _traverse_Tags(end_r_2979, tmpcur_7358);
            CursorTy pvrtmp_7359 = tmp_struct_173.field0;
            
            return (CursorProd) {pvrtmp_7359};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7360 = *(CursorTy *) tmpcur_7356;
            CursorTy tmpaftercur_7361 = tmpcur_7356 + 8;
            CursorTy jump_4362 = tmpcur_7356 + 8;
            CursorProd tmp_struct_174 =
                        _traverse_Tags(end_r_2979, tmpcur_7360);
            CursorTy pvrtmp_7362 = tmp_struct_174.field0;
            
            return (CursorProd) {jump_4362};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7363 = *(CursorTy *) tmpcur_7356;
            CursorTy tmpaftercur_7364 = tmpcur_7356 + 8;
            CursorProd tmp_struct_175 =
                        _traverse_Tags(end_r_2979, tmpcur_7363);
            CursorTy pvrtmp_7365 = tmp_struct_175.field0;
            
            return (CursorProd) {pvrtmp_7365};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7355");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_2981, CursorTy arg_885_1489_1814)
{
    TagTyPacked tmpval_7367 = *(TagTyPacked *) arg_885_1489_1814;
    CursorTy tmpcur_7368 = arg_885_1489_1814 + 1;
    
    
  switch_7378:
    ;
    switch (tmpval_7367) {
        
      case 0:
        {
            CursorTy jump_4208 = arg_885_1489_1814 + 1;
            unsigned char wildcard_886_1490_1815 = print_symbol(6159);
            unsigned char wildcard_887_1491_1816 = print_symbol(6154);
            
            return (CursorProd) {jump_4208};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7369 = *(IntTy *) tmpcur_7368;
            CursorTy tmpcur_7370 = tmpcur_7368 + sizeof(IntTy);
            CursorTy jump_4210 = tmpcur_7368 + 8;
            unsigned char wildcard_892_1494_1819 = print_symbol(6156);
            unsigned char y_890_1495_1820 = printf("%lld", tmpval_7369);
            CursorProd tmp_struct_176 =  _print_Tags(end_r_2981, tmpcur_7370);
            CursorTy pvrtmp_7371 = tmp_struct_176.field0;
            unsigned char wildcard_893_1497_1822 = print_symbol(6154);
            
            return (CursorProd) {pvrtmp_7371};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7372 = *(CursorTy *) tmpcur_7368;
            CursorTy tmpaftercur_7373 = tmpcur_7368 + 8;
            CursorTy jump_4368 = tmpcur_7368 + 8;
            unsigned char wildcard_4371 = print_symbol(6171);
            CursorProd tmp_struct_177 =  _print_Tags(end_r_2981, tmpcur_7372);
            CursorTy pvrtmp_7374 = tmp_struct_177.field0;
            
            return (CursorProd) {jump_4368};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7375 = *(CursorTy *) tmpcur_7368;
            CursorTy tmpaftercur_7376 = tmpcur_7368 + 8;
            unsigned char wildcard_4371 = print_symbol(6170);
            CursorProd tmp_struct_178 =  _print_Tags(end_r_2981, tmpcur_7375);
            CursorTy pvrtmp_7377 = tmp_struct_178.field0;
            
            return (CursorProd) {pvrtmp_7377};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7367");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_2984,
                                                              CursorTy end_r_2985,
                                                              CursorTy loc_2983,
                                                              CursorTy arg_2716)
{
    if (loc_2983 + 32 > end_r_2985) {
        ChunkTy new_chunk_182 = alloc_chunk(end_r_2985);
        CursorTy chunk_start_183 = new_chunk_182.chunk_start;
        CursorTy chunk_end_184 = new_chunk_182.chunk_end;
        
        end_r_2985 = chunk_end_184;
        *(TagTyPacked *) loc_2983 = 255;
        
        CursorTy redir = loc_2983 + 1;
        
        *(CursorTy *) redir = chunk_start_183;
        loc_2983 = chunk_start_183;
    }
    
    CursorTy loc_3718 = loc_2983 + 1;
    CursorTy loc_3719 = loc_3718 + 8;
    TagTyPacked tmpval_7379 = *(TagTyPacked *) arg_2716;
    CursorTy tmpcur_7380 = arg_2716 + 1;
    
    
  switch_7423:
    ;
    switch (tmpval_7379) {
        
      case 0:
        {
            CursorTy jump_4213 = arg_2716 + 1;
            
            *(TagTyPacked *) loc_2983 = 0;
            
            CursorTy writetag_5041 = loc_2983 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2985, jump_4213,
                                                   loc_2983, writetag_5041};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7385 = *(IntTy *) tmpcur_7380;
            CursorTy tmpcur_7386 = tmpcur_7380 + sizeof(IntTy);
            CursorTy jump_4215 = tmpcur_7380 + 8;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_String(end_r_2984, end_r_2985, loc_3719, tmpcur_7386);
            CursorTy pvrtmp_7387 = tmp_struct_179.field0;
            CursorTy pvrtmp_7388 = tmp_struct_179.field1;
            CursorTy pvrtmp_7389 = tmp_struct_179.field2;
            CursorTy pvrtmp_7390 = tmp_struct_179.field3;
            
            *(TagTyPacked *) loc_2983 = 1;
            
            CursorTy writetag_5046 = loc_2983 + 1;
            
            *(IntTy *) writetag_5046 = tmpval_7385;
            
            CursorTy writecur_5047 = writetag_5046 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7387, pvrtmp_7388,
                                                   loc_2983, pvrtmp_7390};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7399 = *(CursorTy *) tmpcur_7380;
            CursorTy tmpaftercur_7400 = tmpcur_7380 + 8;
            CursorTy jump_4374 = tmpcur_7380 + 8;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_String(end_r_2984, end_r_2985, loc_2983, tmpcur_7399);
            CursorTy pvrtmp_7401 = tmp_struct_180.field0;
            CursorTy pvrtmp_7402 = tmp_struct_180.field1;
            CursorTy pvrtmp_7403 = tmp_struct_180.field2;
            CursorTy pvrtmp_7404 = tmp_struct_180.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7401, jump_4374,
                                                   pvrtmp_7403, pvrtmp_7404};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7411 = *(CursorTy *) tmpcur_7380;
            CursorTy tmpaftercur_7412 = tmpcur_7380 + 8;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_String(end_r_2984, end_r_2985, loc_2983, tmpcur_7411);
            CursorTy pvrtmp_7413 = tmp_struct_181.field0;
            CursorTy pvrtmp_7414 = tmp_struct_181.field1;
            CursorTy pvrtmp_7415 = tmp_struct_181.field2;
            CursorTy pvrtmp_7416 = tmp_struct_181.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7413, pvrtmp_7414,
                                                   pvrtmp_7415, pvrtmp_7416};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7379");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_2988,
                                                               CursorTy end_r_2989,
                                                               CursorTy loc_2987,
                                                               CursorTy arg_2721)
{
    if (loc_2987 + 32 > end_r_2989) {
        ChunkTy new_chunk_189 = alloc_chunk(end_r_2989);
        CursorTy chunk_start_190 = new_chunk_189.chunk_start;
        CursorTy chunk_end_191 = new_chunk_189.chunk_end;
        
        end_r_2989 = chunk_end_191;
        *(TagTyPacked *) loc_2987 = 255;
        
        CursorTy redir = loc_2987 + 1;
        
        *(CursorTy *) redir = chunk_start_190;
        loc_2987 = chunk_start_190;
    }
    
    TagTyPacked tmpval_7424 = *(TagTyPacked *) arg_2721;
    CursorTy tmpcur_7425 = arg_2721 + 1;
    
    
  switch_7474:
    ;
    switch (tmpval_7424) {
        
      case 0:
        {
            CursorTy loc_3729 = loc_2987 + 1;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_String(end_r_2988, end_r_2989, loc_3729, tmpcur_7425);
            CursorTy pvrtmp_7426 = tmp_struct_185.field0;
            CursorTy pvrtmp_7427 = tmp_struct_185.field1;
            CursorTy pvrtmp_7428 = tmp_struct_185.field2;
            CursorTy pvrtmp_7429 = tmp_struct_185.field3;
            
            *(TagTyPacked *) loc_2987 = 0;
            
            CursorTy writetag_5058 = loc_2987 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7426, pvrtmp_7427,
                                                   loc_2987, pvrtmp_7429};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3735 = loc_2987 + 1;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_String(end_r_2988, end_r_2989, loc_3735, tmpcur_7425);
            CursorTy pvrtmp_7438 = tmp_struct_186.field0;
            CursorTy pvrtmp_7439 = tmp_struct_186.field1;
            CursorTy pvrtmp_7440 = tmp_struct_186.field2;
            CursorTy pvrtmp_7441 = tmp_struct_186.field3;
            
            *(TagTyPacked *) loc_2987 = 1;
            
            CursorTy writetag_5063 = loc_2987 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7438, pvrtmp_7439,
                                                   loc_2987, pvrtmp_7441};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7450 = *(CursorTy *) tmpcur_7425;
            CursorTy tmpaftercur_7451 = tmpcur_7425 + 8;
            CursorTy jump_4380 = tmpcur_7425 + 8;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Content(end_r_2988, end_r_2989, loc_2987, tmpcur_7450);
            CursorTy pvrtmp_7452 = tmp_struct_187.field0;
            CursorTy pvrtmp_7453 = tmp_struct_187.field1;
            CursorTy pvrtmp_7454 = tmp_struct_187.field2;
            CursorTy pvrtmp_7455 = tmp_struct_187.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7452, jump_4380,
                                                   pvrtmp_7454, pvrtmp_7455};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7462 = *(CursorTy *) tmpcur_7425;
            CursorTy tmpaftercur_7463 = tmpcur_7425 + 8;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Content(end_r_2988, end_r_2989, loc_2987, tmpcur_7462);
            CursorTy pvrtmp_7464 = tmp_struct_188.field0;
            CursorTy pvrtmp_7465 = tmp_struct_188.field1;
            CursorTy pvrtmp_7466 = tmp_struct_188.field2;
            CursorTy pvrtmp_7467 = tmp_struct_188.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7464, pvrtmp_7465,
                                                   pvrtmp_7466, pvrtmp_7467};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7424");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2992,
                                                           CursorTy end_r_2993,
                                                           CursorTy loc_2991,
                                                           CursorTy arg_2726)
{
    if (loc_2991 + 32 > end_r_2993) {
        ChunkTy new_chunk_216 = alloc_chunk(end_r_2993);
        CursorTy chunk_start_217 = new_chunk_216.chunk_start;
        CursorTy chunk_end_218 = new_chunk_216.chunk_end;
        
        end_r_2993 = chunk_end_218;
        *(TagTyPacked *) loc_2991 = 255;
        
        CursorTy redir = loc_2991 + 1;
        
        *(CursorTy *) redir = chunk_start_217;
        loc_2991 = chunk_start_217;
    }
    
    CursorTy loc_3748 = loc_2991 + 1;
    CursorTy loc_3749 = loc_3748 + 8;
    CursorTy loc_3750 = loc_3749 + 8;
    CursorTy loc_3766 = loc_2991 + 1;
    CursorTy loc_3767 = loc_3766 + 8;
    CursorTy loc_3768 = loc_3767 + 8;
    CursorTy loc_3788 = loc_2991 + 1;
    CursorTy loc_3789 = loc_3788 + 8;
    CursorTy loc_3790 = loc_3789 + 8;
    CursorTy loc_3791 = loc_3790 + 8;
    CursorTy loc_3815 = loc_2991 + 1;
    CursorTy loc_3816 = loc_3815 + 8;
    CursorTy loc_3817 = loc_3816 + 8;
    CursorTy loc_3818 = loc_3817 + 8;
    CursorTy loc_3842 = loc_2991 + 1;
    CursorTy loc_3843 = loc_3842 + 8;
    CursorTy loc_3844 = loc_3843 + 8;
    CursorTy loc_3845 = loc_3844 + 8;
    CursorTy loc_3869 = loc_2991 + 1;
    CursorTy loc_3870 = loc_3869 + 8;
    CursorTy loc_3871 = loc_3870 + 8;
    CursorTy loc_3872 = loc_3871 + 8;
    CursorTy loc_3896 = loc_2991 + 1;
    CursorTy loc_3897 = loc_3896 + 8;
    CursorTy loc_3898 = loc_3897 + 8;
    CursorTy loc_3899 = loc_3898 + 8;
    CursorTy loc_3923 = loc_2991 + 1;
    CursorTy loc_3924 = loc_3923 + 8;
    CursorTy loc_3925 = loc_3924 + 8;
    CursorTy loc_3926 = loc_3925 + 8;
    TagTyPacked tmpval_7475 = *(TagTyPacked *) arg_2726;
    CursorTy tmpcur_7476 = arg_2726 + 1;
    
    
  switch_7713:
    ;
    switch (tmpval_7475) {
        
      case 0:
        {
            CursorTy jump_4222 = arg_2726 + 1;
            
            *(TagTyPacked *) loc_2991 = 0;
            
            CursorTy writetag_5073 = loc_2991 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2993, jump_4222,
                                                   loc_2991, writetag_5073};
            break;
        }
        
      case 1:
        {
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, end_r_2993, loc_3750, tmpcur_7476);
            CursorTy pvrtmp_7481 = tmp_struct_192.field0;
            CursorTy pvrtmp_7482 = tmp_struct_192.field1;
            CursorTy pvrtmp_7483 = tmp_struct_192.field2;
            CursorTy pvrtmp_7484 = tmp_struct_192.field3;
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, pvrtmp_7481, pvrtmp_7484, pvrtmp_7482);
            CursorTy pvrtmp_7489 = tmp_struct_193.field0;
            CursorTy pvrtmp_7490 = tmp_struct_193.field1;
            CursorTy pvrtmp_7491 = tmp_struct_193.field2;
            CursorTy pvrtmp_7492 = tmp_struct_193.field3;
            IntTy sizeof_y_2729__2731 = pvrtmp_7484 - pvrtmp_7483;
            IntTy sizeof_y_2730__2732 = pvrtmp_7492 - pvrtmp_7491;
            IntTy fltPrm_2820 = sizeof_y_2729__2731 + 0;
            IntTy offset__2733 = 0 + fltPrm_2820;
            IntTy fltPrm_2821 = sizeof_y_2729__2731 + sizeof_y_2730__2732;
            IntTy size_dcon_2734 = 9 + fltPrm_2821;
            
            *(TagTyPacked *) loc_2991 = 160;
            
            CursorTy writetag_5078 = loc_2991 + 1;
            
            *(IntTy *) writetag_5078 = size_dcon_2734;
            
            CursorTy writecur_5079 = writetag_5078 + sizeof(IntTy);
            
            *(IntTy *) writecur_5079 = offset__2733;
            
            CursorTy writecur_5080 = writecur_5079 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7489, pvrtmp_7490,
                                                   loc_2991, pvrtmp_7492};
            break;
        }
        
      case 2:
        {
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, end_r_2993, loc_3768, tmpcur_7476);
            CursorTy pvrtmp_7501 = tmp_struct_194.field0;
            CursorTy pvrtmp_7502 = tmp_struct_194.field1;
            CursorTy pvrtmp_7503 = tmp_struct_194.field2;
            CursorTy pvrtmp_7504 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, pvrtmp_7501, pvrtmp_7504, pvrtmp_7502);
            CursorTy pvrtmp_7509 = tmp_struct_195.field0;
            CursorTy pvrtmp_7510 = tmp_struct_195.field1;
            CursorTy pvrtmp_7511 = tmp_struct_195.field2;
            CursorTy pvrtmp_7512 = tmp_struct_195.field3;
            IntTy sizeof_y_2737__2739 = pvrtmp_7504 - pvrtmp_7503;
            IntTy sizeof_y_2738__2740 = pvrtmp_7512 - pvrtmp_7511;
            IntTy fltPrm_2822 = sizeof_y_2737__2739 + 0;
            IntTy offset__2741 = 0 + fltPrm_2822;
            IntTy fltPrm_2823 = sizeof_y_2737__2739 + sizeof_y_2738__2740;
            IntTy size_dcon_2742 = 9 + fltPrm_2823;
            
            *(TagTyPacked *) loc_2991 = 162;
            
            CursorTy writetag_5087 = loc_2991 + 1;
            
            *(IntTy *) writetag_5087 = size_dcon_2742;
            
            CursorTy writecur_5088 = writetag_5087 + sizeof(IntTy);
            
            *(IntTy *) writecur_5088 = offset__2741;
            
            CursorTy writecur_5089 = writecur_5088 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7509, pvrtmp_7510,
                                                   loc_2991, pvrtmp_7512};
            break;
        }
        
      case 3:
        {
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Tags(end_r_2992, end_r_2993, loc_3791, tmpcur_7476);
            CursorTy pvrtmp_7521 = tmp_struct_196.field0;
            CursorTy pvrtmp_7522 = tmp_struct_196.field1;
            CursorTy pvrtmp_7523 = tmp_struct_196.field2;
            CursorTy pvrtmp_7524 = tmp_struct_196.field3;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, pvrtmp_7521, pvrtmp_7524, pvrtmp_7522);
            CursorTy pvrtmp_7529 = tmp_struct_197.field0;
            CursorTy pvrtmp_7530 = tmp_struct_197.field1;
            CursorTy pvrtmp_7531 = tmp_struct_197.field2;
            CursorTy pvrtmp_7532 = tmp_struct_197.field3;
            CursorCursorCursorCursorProd tmp_struct_198 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, pvrtmp_7529, pvrtmp_7532, pvrtmp_7530);
            CursorTy pvrtmp_7537 = tmp_struct_198.field0;
            CursorTy pvrtmp_7538 = tmp_struct_198.field1;
            CursorTy pvrtmp_7539 = tmp_struct_198.field2;
            CursorTy pvrtmp_7540 = tmp_struct_198.field3;
            IntTy sizeof_y_2746__2749 = pvrtmp_7524 - pvrtmp_7523;
            IntTy sizeof_y_2747__2750 = pvrtmp_7532 - pvrtmp_7531;
            IntTy sizeof_y_2748__2751 = pvrtmp_7540 - pvrtmp_7539;
            IntTy fltPrm_2824 = sizeof_y_2746__2749 + 0;
            IntTy offset__2752 = 8 + fltPrm_2824;
            IntTy fltPrm_2825 = sizeof_y_2746__2749 + sizeof_y_2747__2750;
            IntTy offset__2753 = 0 + fltPrm_2825;
            IntTy fltPrm_2827 = sizeof_y_2747__2750 + sizeof_y_2748__2751;
            IntTy fltPrm_2826 = sizeof_y_2746__2749 + fltPrm_2827;
            IntTy size_dcon_2754 = 17 + fltPrm_2826;
            
            *(TagTyPacked *) loc_2991 = 164;
            
            CursorTy writetag_5097 = loc_2991 + 1;
            
            *(IntTy *) writetag_5097 = size_dcon_2754;
            
            CursorTy writecur_5098 = writetag_5097 + sizeof(IntTy);
            
            *(IntTy *) writecur_5098 = offset__2752;
            
            CursorTy writecur_5099 = writecur_5098 + sizeof(IntTy);
            
            *(IntTy *) writecur_5099 = offset__2753;
            
            CursorTy writecur_5100 = writecur_5099 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7537, pvrtmp_7538,
                                                   loc_2991, pvrtmp_7540};
            break;
        }
        
      case 4:
        {
            CursorCursorCursorCursorProd tmp_struct_199 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, end_r_2993, loc_3818, tmpcur_7476);
            CursorTy pvrtmp_7549 = tmp_struct_199.field0;
            CursorTy pvrtmp_7550 = tmp_struct_199.field1;
            CursorTy pvrtmp_7551 = tmp_struct_199.field2;
            CursorTy pvrtmp_7552 = tmp_struct_199.field3;
            CursorCursorCursorCursorProd tmp_struct_200 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, pvrtmp_7549, pvrtmp_7552, pvrtmp_7550);
            CursorTy pvrtmp_7557 = tmp_struct_200.field0;
            CursorTy pvrtmp_7558 = tmp_struct_200.field1;
            CursorTy pvrtmp_7559 = tmp_struct_200.field2;
            CursorTy pvrtmp_7560 = tmp_struct_200.field3;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_2992, pvrtmp_7557, pvrtmp_7560, pvrtmp_7558);
            CursorTy pvrtmp_7565 = tmp_struct_201.field0;
            CursorTy pvrtmp_7566 = tmp_struct_201.field1;
            CursorTy pvrtmp_7567 = tmp_struct_201.field2;
            CursorTy pvrtmp_7568 = tmp_struct_201.field3;
            IntTy sizeof_y_2758__2761 = pvrtmp_7552 - pvrtmp_7551;
            IntTy sizeof_y_2759__2762 = pvrtmp_7560 - pvrtmp_7559;
            IntTy sizeof_y_2760__2763 = pvrtmp_7568 - pvrtmp_7567;
            IntTy fltPrm_2828 = sizeof_y_2758__2761 + 0;
            IntTy offset__2764 = 8 + fltPrm_2828;
            IntTy fltPrm_2829 = sizeof_y_2758__2761 + sizeof_y_2759__2762;
            IntTy offset__2765 = 0 + fltPrm_2829;
            IntTy fltPrm_2831 = sizeof_y_2759__2762 + sizeof_y_2760__2763;
            IntTy fltPrm_2830 = sizeof_y_2758__2761 + fltPrm_2831;
            IntTy size_dcon_2766 = 17 + fltPrm_2830;
            
            *(TagTyPacked *) loc_2991 = 166;
            
            CursorTy writetag_5109 = loc_2991 + 1;
            
            *(IntTy *) writetag_5109 = size_dcon_2766;
            
            CursorTy writecur_5110 = writetag_5109 + sizeof(IntTy);
            
            *(IntTy *) writecur_5110 = offset__2764;
            
            CursorTy writecur_5111 = writecur_5110 + sizeof(IntTy);
            
            *(IntTy *) writecur_5111 = offset__2765;
            
            CursorTy writecur_5112 = writecur_5111 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7565, pvrtmp_7566,
                                                   loc_2991, pvrtmp_7568};
            break;
        }
        
      case 5:
        {
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_2992, end_r_2993, loc_3845, tmpcur_7476);
            CursorTy pvrtmp_7577 = tmp_struct_202.field0;
            CursorTy pvrtmp_7578 = tmp_struct_202.field1;
            CursorTy pvrtmp_7579 = tmp_struct_202.field2;
            CursorTy pvrtmp_7580 = tmp_struct_202.field3;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, pvrtmp_7577, pvrtmp_7580, pvrtmp_7578);
            CursorTy pvrtmp_7585 = tmp_struct_203.field0;
            CursorTy pvrtmp_7586 = tmp_struct_203.field1;
            CursorTy pvrtmp_7587 = tmp_struct_203.field2;
            CursorTy pvrtmp_7588 = tmp_struct_203.field3;
            CursorCursorCursorCursorProd tmp_struct_204 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, pvrtmp_7585, pvrtmp_7588, pvrtmp_7586);
            CursorTy pvrtmp_7593 = tmp_struct_204.field0;
            CursorTy pvrtmp_7594 = tmp_struct_204.field1;
            CursorTy pvrtmp_7595 = tmp_struct_204.field2;
            CursorTy pvrtmp_7596 = tmp_struct_204.field3;
            IntTy sizeof_y_2770__2773 = pvrtmp_7580 - pvrtmp_7579;
            IntTy sizeof_y_2771__2774 = pvrtmp_7588 - pvrtmp_7587;
            IntTy sizeof_y_2772__2775 = pvrtmp_7596 - pvrtmp_7595;
            IntTy fltPrm_2832 = sizeof_y_2770__2773 + 0;
            IntTy offset__2776 = 8 + fltPrm_2832;
            IntTy fltPrm_2833 = sizeof_y_2770__2773 + sizeof_y_2771__2774;
            IntTy offset__2777 = 0 + fltPrm_2833;
            IntTy fltPrm_2835 = sizeof_y_2771__2774 + sizeof_y_2772__2775;
            IntTy fltPrm_2834 = sizeof_y_2770__2773 + fltPrm_2835;
            IntTy size_dcon_2778 = 17 + fltPrm_2834;
            
            *(TagTyPacked *) loc_2991 = 168;
            
            CursorTy writetag_5121 = loc_2991 + 1;
            
            *(IntTy *) writetag_5121 = size_dcon_2778;
            
            CursorTy writecur_5122 = writetag_5121 + sizeof(IntTy);
            
            *(IntTy *) writecur_5122 = offset__2776;
            
            CursorTy writecur_5123 = writecur_5122 + sizeof(IntTy);
            
            *(IntTy *) writecur_5123 = offset__2777;
            
            CursorTy writecur_5124 = writecur_5123 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7593, pvrtmp_7594,
                                                   loc_2991, pvrtmp_7596};
            break;
        }
        
      case 6:
        {
            CursorCursorCursorCursorProd tmp_struct_205 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, end_r_2993, loc_3872, tmpcur_7476);
            CursorTy pvrtmp_7605 = tmp_struct_205.field0;
            CursorTy pvrtmp_7606 = tmp_struct_205.field1;
            CursorTy pvrtmp_7607 = tmp_struct_205.field2;
            CursorTy pvrtmp_7608 = tmp_struct_205.field3;
            CursorCursorCursorCursorProd tmp_struct_206 =
                                          _add_size_and_rel_offsets_Tags(end_r_2992, pvrtmp_7605, pvrtmp_7608, pvrtmp_7606);
            CursorTy pvrtmp_7613 = tmp_struct_206.field0;
            CursorTy pvrtmp_7614 = tmp_struct_206.field1;
            CursorTy pvrtmp_7615 = tmp_struct_206.field2;
            CursorTy pvrtmp_7616 = tmp_struct_206.field3;
            CursorCursorCursorCursorProd tmp_struct_207 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, pvrtmp_7613, pvrtmp_7616, pvrtmp_7614);
            CursorTy pvrtmp_7621 = tmp_struct_207.field0;
            CursorTy pvrtmp_7622 = tmp_struct_207.field1;
            CursorTy pvrtmp_7623 = tmp_struct_207.field2;
            CursorTy pvrtmp_7624 = tmp_struct_207.field3;
            IntTy sizeof_y_2782__2785 = pvrtmp_7608 - pvrtmp_7607;
            IntTy sizeof_y_2783__2786 = pvrtmp_7616 - pvrtmp_7615;
            IntTy sizeof_y_2784__2787 = pvrtmp_7624 - pvrtmp_7623;
            IntTy fltPrm_2836 = sizeof_y_2782__2785 + 0;
            IntTy offset__2788 = 8 + fltPrm_2836;
            IntTy fltPrm_2837 = sizeof_y_2782__2785 + sizeof_y_2783__2786;
            IntTy offset__2789 = 0 + fltPrm_2837;
            IntTy fltPrm_2839 = sizeof_y_2783__2786 + sizeof_y_2784__2787;
            IntTy fltPrm_2838 = sizeof_y_2782__2785 + fltPrm_2839;
            IntTy size_dcon_2790 = 17 + fltPrm_2838;
            
            *(TagTyPacked *) loc_2991 = 170;
            
            CursorTy writetag_5133 = loc_2991 + 1;
            
            *(IntTy *) writetag_5133 = size_dcon_2790;
            
            CursorTy writecur_5134 = writetag_5133 + sizeof(IntTy);
            
            *(IntTy *) writecur_5134 = offset__2788;
            
            CursorTy writecur_5135 = writecur_5134 + sizeof(IntTy);
            
            *(IntTy *) writecur_5135 = offset__2789;
            
            CursorTy writecur_5136 = writecur_5135 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7621, pvrtmp_7622,
                                                   loc_2991, pvrtmp_7624};
            break;
        }
        
      case 7:
        {
            CursorCursorCursorCursorProd tmp_struct_208 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, end_r_2993, loc_3899, tmpcur_7476);
            CursorTy pvrtmp_7633 = tmp_struct_208.field0;
            CursorTy pvrtmp_7634 = tmp_struct_208.field1;
            CursorTy pvrtmp_7635 = tmp_struct_208.field2;
            CursorTy pvrtmp_7636 = tmp_struct_208.field3;
            CursorCursorCursorCursorProd tmp_struct_209 =
                                          _add_size_and_rel_offsets_Tags(end_r_2992, pvrtmp_7633, pvrtmp_7636, pvrtmp_7634);
            CursorTy pvrtmp_7641 = tmp_struct_209.field0;
            CursorTy pvrtmp_7642 = tmp_struct_209.field1;
            CursorTy pvrtmp_7643 = tmp_struct_209.field2;
            CursorTy pvrtmp_7644 = tmp_struct_209.field3;
            CursorCursorCursorCursorProd tmp_struct_210 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, pvrtmp_7641, pvrtmp_7644, pvrtmp_7642);
            CursorTy pvrtmp_7649 = tmp_struct_210.field0;
            CursorTy pvrtmp_7650 = tmp_struct_210.field1;
            CursorTy pvrtmp_7651 = tmp_struct_210.field2;
            CursorTy pvrtmp_7652 = tmp_struct_210.field3;
            IntTy sizeof_y_2794__2797 = pvrtmp_7636 - pvrtmp_7635;
            IntTy sizeof_y_2795__2798 = pvrtmp_7644 - pvrtmp_7643;
            IntTy sizeof_y_2796__2799 = pvrtmp_7652 - pvrtmp_7651;
            IntTy fltPrm_2840 = sizeof_y_2794__2797 + 0;
            IntTy offset__2800 = 8 + fltPrm_2840;
            IntTy fltPrm_2841 = sizeof_y_2794__2797 + sizeof_y_2795__2798;
            IntTy offset__2801 = 0 + fltPrm_2841;
            IntTy fltPrm_2843 = sizeof_y_2795__2798 + sizeof_y_2796__2799;
            IntTy fltPrm_2842 = sizeof_y_2794__2797 + fltPrm_2843;
            IntTy size_dcon_2802 = 17 + fltPrm_2842;
            
            *(TagTyPacked *) loc_2991 = 172;
            
            CursorTy writetag_5145 = loc_2991 + 1;
            
            *(IntTy *) writetag_5145 = size_dcon_2802;
            
            CursorTy writecur_5146 = writetag_5145 + sizeof(IntTy);
            
            *(IntTy *) writecur_5146 = offset__2800;
            
            CursorTy writecur_5147 = writecur_5146 + sizeof(IntTy);
            
            *(IntTy *) writecur_5147 = offset__2801;
            
            CursorTy writecur_5148 = writecur_5147 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7649, pvrtmp_7650,
                                                   loc_2991, pvrtmp_7652};
            break;
        }
        
      case 8:
        {
            CursorCursorCursorCursorProd tmp_struct_211 =
                                          _add_size_and_rel_offsets_Content(end_r_2992, end_r_2993, loc_3926, tmpcur_7476);
            CursorTy pvrtmp_7661 = tmp_struct_211.field0;
            CursorTy pvrtmp_7662 = tmp_struct_211.field1;
            CursorTy pvrtmp_7663 = tmp_struct_211.field2;
            CursorTy pvrtmp_7664 = tmp_struct_211.field3;
            CursorCursorCursorCursorProd tmp_struct_212 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, pvrtmp_7661, pvrtmp_7664, pvrtmp_7662);
            CursorTy pvrtmp_7669 = tmp_struct_212.field0;
            CursorTy pvrtmp_7670 = tmp_struct_212.field1;
            CursorTy pvrtmp_7671 = tmp_struct_212.field2;
            CursorTy pvrtmp_7672 = tmp_struct_212.field3;
            CursorCursorCursorCursorProd tmp_struct_213 =
                                          _add_size_and_rel_offsets_Tags(end_r_2992, pvrtmp_7669, pvrtmp_7672, pvrtmp_7670);
            CursorTy pvrtmp_7677 = tmp_struct_213.field0;
            CursorTy pvrtmp_7678 = tmp_struct_213.field1;
            CursorTy pvrtmp_7679 = tmp_struct_213.field2;
            CursorTy pvrtmp_7680 = tmp_struct_213.field3;
            IntTy sizeof_y_2806__2809 = pvrtmp_7664 - pvrtmp_7663;
            IntTy sizeof_y_2807__2810 = pvrtmp_7672 - pvrtmp_7671;
            IntTy sizeof_y_2808__2811 = pvrtmp_7680 - pvrtmp_7679;
            IntTy fltPrm_2844 = sizeof_y_2806__2809 + 0;
            IntTy offset__2812 = 8 + fltPrm_2844;
            IntTy fltPrm_2845 = sizeof_y_2806__2809 + sizeof_y_2807__2810;
            IntTy offset__2813 = 0 + fltPrm_2845;
            IntTy fltPrm_2847 = sizeof_y_2807__2810 + sizeof_y_2808__2811;
            IntTy fltPrm_2846 = sizeof_y_2806__2809 + fltPrm_2847;
            IntTy size_dcon_2814 = 17 + fltPrm_2846;
            
            *(TagTyPacked *) loc_2991 = 174;
            
            CursorTy writetag_5157 = loc_2991 + 1;
            
            *(IntTy *) writetag_5157 = size_dcon_2814;
            
            CursorTy writecur_5158 = writetag_5157 + sizeof(IntTy);
            
            *(IntTy *) writecur_5158 = offset__2812;
            
            CursorTy writecur_5159 = writecur_5158 + sizeof(IntTy);
            
            *(IntTy *) writecur_5159 = offset__2813;
            
            CursorTy writecur_5160 = writecur_5159 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7677, pvrtmp_7678,
                                                   loc_2991, pvrtmp_7680};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7689 = *(CursorTy *) tmpcur_7476;
            CursorTy tmpaftercur_7690 = tmpcur_7476 + 8;
            CursorTy jump_4386 = tmpcur_7476 + 8;
            CursorCursorCursorCursorProd tmp_struct_214 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, end_r_2993, loc_2991, tmpcur_7689);
            CursorTy pvrtmp_7691 = tmp_struct_214.field0;
            CursorTy pvrtmp_7692 = tmp_struct_214.field1;
            CursorTy pvrtmp_7693 = tmp_struct_214.field2;
            CursorTy pvrtmp_7694 = tmp_struct_214.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7691, jump_4386,
                                                   pvrtmp_7693, pvrtmp_7694};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7701 = *(CursorTy *) tmpcur_7476;
            CursorTy tmpaftercur_7702 = tmpcur_7476 + 8;
            CursorCursorCursorCursorProd tmp_struct_215 =
                                          _add_size_and_rel_offsets_Adt(end_r_2992, end_r_2993, loc_2991, tmpcur_7701);
            CursorTy pvrtmp_7703 = tmp_struct_215.field0;
            CursorTy pvrtmp_7704 = tmp_struct_215.field1;
            CursorTy pvrtmp_7705 = tmp_struct_215.field2;
            CursorTy pvrtmp_7706 = tmp_struct_215.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7703, pvrtmp_7704,
                                                   pvrtmp_7705, pvrtmp_7706};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7475");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2996,
                                                            CursorTy end_r_2997,
                                                            CursorTy loc_2995,
                                                            CursorTy arg_2815)
{
    if (loc_2995 + 32 > end_r_2997) {
        ChunkTy new_chunk_222 = alloc_chunk(end_r_2997);
        CursorTy chunk_start_223 = new_chunk_222.chunk_start;
        CursorTy chunk_end_224 = new_chunk_222.chunk_end;
        
        end_r_2997 = chunk_end_224;
        *(TagTyPacked *) loc_2995 = 255;
        
        CursorTy redir = loc_2995 + 1;
        
        *(CursorTy *) redir = chunk_start_223;
        loc_2995 = chunk_start_223;
    }
    
    CursorTy loc_3946 = loc_2995 + 1;
    CursorTy loc_3947 = loc_3946 + 8;
    TagTyPacked tmpval_7714 = *(TagTyPacked *) arg_2815;
    CursorTy tmpcur_7715 = arg_2815 + 1;
    
    
  switch_7758:
    ;
    switch (tmpval_7714) {
        
      case 0:
        {
            CursorTy jump_4254 = arg_2815 + 1;
            
            *(TagTyPacked *) loc_2995 = 0;
            
            CursorTy writetag_5172 = loc_2995 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2997, jump_4254,
                                                   loc_2995, writetag_5172};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7720 = *(IntTy *) tmpcur_7715;
            CursorTy tmpcur_7721 = tmpcur_7715 + sizeof(IntTy);
            CursorTy jump_4256 = tmpcur_7715 + 8;
            CursorCursorCursorCursorProd tmp_struct_219 =
                                          _add_size_and_rel_offsets_Tags(end_r_2996, end_r_2997, loc_3947, tmpcur_7721);
            CursorTy pvrtmp_7722 = tmp_struct_219.field0;
            CursorTy pvrtmp_7723 = tmp_struct_219.field1;
            CursorTy pvrtmp_7724 = tmp_struct_219.field2;
            CursorTy pvrtmp_7725 = tmp_struct_219.field3;
            
            *(TagTyPacked *) loc_2995 = 1;
            
            CursorTy writetag_5177 = loc_2995 + 1;
            
            *(IntTy *) writetag_5177 = tmpval_7720;
            
            CursorTy writecur_5178 = writetag_5177 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7722, pvrtmp_7723,
                                                   loc_2995, pvrtmp_7725};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7734 = *(CursorTy *) tmpcur_7715;
            CursorTy tmpaftercur_7735 = tmpcur_7715 + 8;
            CursorTy jump_4392 = tmpcur_7715 + 8;
            CursorCursorCursorCursorProd tmp_struct_220 =
                                          _add_size_and_rel_offsets_Tags(end_r_2996, end_r_2997, loc_2995, tmpcur_7734);
            CursorTy pvrtmp_7736 = tmp_struct_220.field0;
            CursorTy pvrtmp_7737 = tmp_struct_220.field1;
            CursorTy pvrtmp_7738 = tmp_struct_220.field2;
            CursorTy pvrtmp_7739 = tmp_struct_220.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7736, jump_4392,
                                                   pvrtmp_7738, pvrtmp_7739};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7746 = *(CursorTy *) tmpcur_7715;
            CursorTy tmpaftercur_7747 = tmpcur_7715 + 8;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          _add_size_and_rel_offsets_Tags(end_r_2996, end_r_2997, loc_2995, tmpcur_7746);
            CursorTy pvrtmp_7748 = tmp_struct_221.field0;
            CursorTy pvrtmp_7749 = tmp_struct_221.field1;
            CursorTy pvrtmp_7750 = tmp_struct_221.field2;
            CursorTy pvrtmp_7751 = tmp_struct_221.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7748, pvrtmp_7749,
                                                   pvrtmp_7750, pvrtmp_7751};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7714");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(6154, ")");
    add_symbol(6155, "(Text ");
    add_symbol(6156, "(Tag ");
    add_symbol(6157, "(TCA ");
    add_symbol(6158, "(TAC ");
    add_symbol(6159, "(Nul ");
    add_symbol(6160, "(Nil ");
    add_symbol(6161, "(Image ");
    add_symbol(6162, "(End ");
    add_symbol(6163, "(Char ");
    add_symbol(6164, "(CTA ");
    add_symbol(6165, "(CAT ");
    add_symbol(6166, "(CA ");
    add_symbol(6167, "(ATC ");
    add_symbol(6168, "(ACT ");
    add_symbol(6169, "(AC ");
    add_symbol(6170, " ->r ");
    add_symbol(6171, " ->i ");
    
    RegionTy *region_6172 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3007 = region_6172->reg_heap;
    IntTy sizeof_end_r_3007_6173 = global_init_inf_buf_size;
    CursorTy end_r_3007 = r_3007 + sizeof_end_r_3007_6173;
    RegionTy *region_6174 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3006 = region_6174->reg_heap;
    IntTy sizeof_end_r_3006_6175 = global_init_inf_buf_size;
    CursorTy end_r_3006 = r_3006 + sizeof_end_r_3006_6175;
    CursorCursorCursorProd tmp_struct_225 =
                            mkTCAList(end_r_3007, r_3007, 100000, 10, 2000);
    CursorTy pvrtmp_6176 = tmp_struct_225.field0;
    CursorTy pvrtmp_6177 = tmp_struct_225.field1;
    CursorTy pvrtmp_6178 = tmp_struct_225.field2;
    CursorTy pvrtmp_6192;
    CursorTy pvrtmp_6193;
    CursorTy pvrtmp_6194;
    VectorTy *times_230 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6192;
    struct timespec end_pvrtmp_6192;
    
    start_counters();
    for (long long iters_pvrtmp_6192 = 0; iters_pvrtmp_6192 <
         global_iters_param; iters_pvrtmp_6192++) {
        if (iters_pvrtmp_6192 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6192);
        
        CursorCursorCursorProd tmp_struct_226 =
                                addValTagsAdt(pvrtmp_6176, end_r_3006, r_3006, pvrtmp_6177);
        CursorTy pvrtmp_6183 = tmp_struct_226.field0;
        CursorTy pvrtmp_6184 = tmp_struct_226.field1;
        CursorTy pvrtmp_6185 = tmp_struct_226.field2;
        
        pvrtmp_6192 = pvrtmp_6183;
        pvrtmp_6193 = pvrtmp_6184;
        pvrtmp_6194 = pvrtmp_6185;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6192);
        if (iters_pvrtmp_6192 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_227 = difftimespecs(&begin_pvrtmp_6192,
                                            &end_pvrtmp_6192);
        
        vector_inplace_update(times_230, iters_pvrtmp_6192, &itertime_227);
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
