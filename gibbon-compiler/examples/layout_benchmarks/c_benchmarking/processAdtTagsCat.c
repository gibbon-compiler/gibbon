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

#include <papi.h>

#define KB 1024lu
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

#define REDIRECTION_TAG 255
#define INDIRECTION_TAG 254

#define SIZE 4

int ret;
int events[] = {PAPI_L2_TCM, PAPI_L3_TCM, PAPI_TOT_INS, PAPI_TOT_CYC};
char* defs[] = {"L2 Cache Misses", "L3 Cache Misses", "Instructions" ,"Total Cycles"};

unsigned long long values[SIZE];

void init_papi(){
  if (PAPI_library_init(PAPI_VER_CURRENT) != PAPI_VER_CURRENT){
    printf("PAPI Init Error\n");
    exit(1);
  }
  for(int i = 0; i < SIZE; i++){
    if (PAPI_query_event(events[i]) != PAPI_OK){
      printf("PAPI Event %d does not exist\n", i);
    }    
  }  
}

void start_counters() {
  if (PAPI_start_counters(events, SIZE) != PAPI_OK) {
    printf("PAPI Error starting counters\n");
  } 
}

void read_counters() {
  // Performance Counters Read
  ret = PAPI_stop_counters(values, SIZE);
  if (ret != PAPI_OK) {
    if (ret == PAPI_ESYS) {
      printf("error inside PAPI call\n");
    } else if (ret == PAPI_EINVAL) {
      printf("error with arguments\n");
    }

    printf("PAPI Error reading counters\n");
  }
}

void print_counters() {
  for (int i = 0; i < SIZE; ++i)
    printf("%s : %llu\n", defs[i], values[i]);
}

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
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2945, CursorTy end_r_2946,
                                     CursorTy loc_2944,
                                     CursorTy adt_31_932_1549);
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2949, CursorTy end_r_2950,
                                       CursorTy loc_2948,
                                       CursorTy tags_45_942_1556,
                                       IntTy inVal_46_943_1557);
CursorCursorCursorProd mkCATList(CursorTy end_r_2952, CursorTy loc_2951,
                                 IntTy len_49_946_1562,
                                 IntTy tagLen_50_947_1563,
                                 IntTy strLen_51_948_1564);
CursorCursorCursorProd mkString(CursorTy end_r_2954, CursorTy loc_2953,
                                IntTy len_204_1101_1570);
CursorCursorCursorProd mkContentText(CursorTy end_r_2956, CursorTy loc_2955,
                                     IntTy n_218_1115_1576);
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2958, CursorTy loc_2957,
                                    IntTy len_343_1240_1578);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2961,
                                          CursorTy end_r_2962,
                                          CursorTy loc_2960,
                                          CursorTy arg_647_1260_1583);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2965,
                                                       CursorTy end_r_2966,
                                                       CursorTy loc_2964,
                                                       CursorTy arg_652_1265_1588);
CursorProd _traverse_String(CursorTy end_r_2968, CursorTy arg_657_1270_1593);
CursorProd _print_String(CursorTy end_r_2970, CursorTy arg_662_1274_1597);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2973,
                                           CursorTy end_r_2974,
                                           CursorTy loc_2972,
                                           CursorTy arg_671_1283_1606);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2977,
                                                        CursorTy end_r_2978,
                                                        CursorTy loc_2976,
                                                        CursorTy arg_676_1288_1611);
CursorProd _traverse_Content(CursorTy end_r_2980, CursorTy arg_681_1293_1616);
CursorProd _print_Content(CursorTy end_r_2982, CursorTy arg_686_1298_1621);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2985, CursorTy end_r_2986,
                                       CursorTy loc_2984,
                                       CursorTy arg_695_1307_1630);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2989,
                                                    CursorTy end_r_2990,
                                                    CursorTy loc_2988,
                                                    CursorTy arg_740_1352_1675);
CursorProd _traverse_Adt(CursorTy end_r_2992, CursorTy arg_785_1397_1720);
CursorProd _print_Adt(CursorTy end_r_2994, CursorTy arg_830_1442_1765);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2997,
                                        CursorTy end_r_2998, CursorTy loc_2996,
                                        CursorTy arg_893_1505_1828);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_3001,
                                                     CursorTy end_r_3002,
                                                     CursorTy loc_3000,
                                                     CursorTy arg_898_1510_1833);
CursorProd _traverse_Tags(CursorTy end_r_3004, CursorTy arg_903_1515_1838);
CursorProd _print_Tags(CursorTy end_r_3006, CursorTy arg_908_1519_1842);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_3009, CursorTy end_r_3010,
                                 CursorTy loc_3008, CursorTy arg_2741);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_3013, CursorTy end_r_3014,
                                  CursorTy loc_3012, CursorTy arg_2746);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_3017,
                                                           CursorTy end_r_3018,
                                                           CursorTy loc_3016,
                                                           CursorTy arg_2751);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_3021,
                                                            CursorTy end_r_3022,
                                                            CursorTy loc_3020,
                                                            CursorTy arg_2840);
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2945, CursorTy end_r_2946,
                                     CursorTy loc_2944,
                                     CursorTy adt_31_932_1549)
{
    if (loc_2944 + 32 > end_r_2946) {
        ChunkTy new_chunk_4 = alloc_chunk(end_r_2946);
        CursorTy chunk_start_5 = new_chunk_4.chunk_start;
        CursorTy chunk_end_6 = new_chunk_4.chunk_end;
        
        end_r_2946 = chunk_end_6;
        *(TagTyPacked *) loc_2944 = 255;
        
        CursorTy redir = loc_2944 + 1;
        
        *(CursorTy *) redir = chunk_start_5;
        loc_2944 = chunk_start_5;
    }
    
    CursorTy loc_3051 = loc_2944 + 1;
    CursorTy loc_3052 = loc_3051 + 8;
    CursorTy loc_3053 = loc_3052 + 8;
    TagTyPacked tmpval_6224 = *(TagTyPacked *) adt_31_932_1549;
    CursorTy tmpcur_6225 = adt_31_932_1549 + 1;
    
    
  switch_6281:
    ;
    switch (tmpval_6224) {
        
      case 0:
        {
            CursorTy jump_3977 = adt_31_932_1549 + 1;
            
            *(TagTyPacked *) loc_2944 = 0;
            
            CursorTy writetag_4536 = loc_2944 + 1;
            
            return (CursorCursorCursorProd) {end_r_2946, loc_2944,
                                             writetag_4536};
            break;
        }
        
      case 23:
        {
            RegionTy *region_6230 = alloc_region(global_init_inf_buf_size);
            CursorTy r_3063 = region_6230->reg_heap;
            IntTy sizeof_end_r_3063_6231 = global_init_inf_buf_size;
            CursorTy end_r_3063 = r_3063 + sizeof_end_r_3063_6231;
            CursorTy tmpcur_6232 = *(CursorTy *) tmpcur_6225;
            CursorTy tmpaftercur_6233 = tmpcur_6225 + 8;
            CursorTy tmpcur_6234 = *(CursorTy *) tmpaftercur_6233;
            CursorTy tmpaftercur_6235 = tmpaftercur_6233 + 8;
            CursorTy jump_3980 = tmpaftercur_6233 + 8;
            CursorTy jump_3979 = tmpcur_6225 + 8;
            
            *(TagTyPacked *) loc_3053 = 254;
            
            CursorTy writetag_4541 = loc_3053 + 1;
            
            *(CursorTy *) writetag_4541 = tmpaftercur_6235;
            
            CursorTy writecur_4542 = writetag_4541 + 8;
            CursorCursorCursorCursorProd tmp_struct_0 =
                                          addValTag(end_r_2945, end_r_3063, r_3063, tmpcur_6234, 10);
            CursorTy pvrtmp_6238 = tmp_struct_0.field0;
            CursorTy pvrtmp_6239 = tmp_struct_0.field1;
            CursorTy pvrtmp_6240 = tmp_struct_0.field2;
            CursorTy pvrtmp_6241 = tmp_struct_0.field3;
            CursorCursorCursorProd tmp_struct_1 =
                                    addValTagsAdt(end_r_2945, end_r_2946, writecur_4542, tmpcur_6232);
            CursorTy pvrtmp_6246 = tmp_struct_1.field0;
            CursorTy pvrtmp_6247 = tmp_struct_1.field1;
            CursorTy pvrtmp_6248 = tmp_struct_1.field2;
            
            *(TagTyPacked *) pvrtmp_6248 = 254;
            
            CursorTy writetag_4546 = pvrtmp_6248 + 1;
            
            *(CursorTy *) writetag_4546 = r_3063;
            
            CursorTy writecur_4547 = writetag_4546 + 8;
            
            *(TagTyPacked *) loc_2944 = 23;
            
            CursorTy writetag_4549 = loc_2944 + 1;
            
            *(CursorTy *) writetag_4549 = tmpcur_6232;
            
            CursorTy writecur_4550 = writetag_4549 + 8;
            
            *(CursorTy *) writecur_4550 = pvrtmp_6248;
            
            CursorTy writecur_4551 = writecur_4550 + 8;
            
            return (CursorCursorCursorProd) {pvrtmp_6246, loc_2944,
                                             writecur_4547};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6259 = *(CursorTy *) tmpcur_6225;
            CursorTy tmpaftercur_6260 = tmpcur_6225 + 8;
            CursorTy jump_4289 = tmpcur_6225 + 8;
            CursorCursorCursorProd tmp_struct_2 =
                                    addValTagsAdt(end_r_2945, end_r_2946, loc_2944, tmpcur_6259);
            CursorTy pvrtmp_6261 = tmp_struct_2.field0;
            CursorTy pvrtmp_6262 = tmp_struct_2.field1;
            CursorTy pvrtmp_6263 = tmp_struct_2.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6261, pvrtmp_6262,
                                             pvrtmp_6263};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6270 = *(CursorTy *) tmpcur_6225;
            CursorTy tmpaftercur_6271 = tmpcur_6225 + 8;
            CursorCursorCursorProd tmp_struct_3 =
                                    addValTagsAdt(end_r_2945, end_r_2946, loc_2944, tmpcur_6270);
            CursorTy pvrtmp_6272 = tmp_struct_3.field0;
            CursorTy pvrtmp_6273 = tmp_struct_3.field1;
            CursorTy pvrtmp_6274 = tmp_struct_3.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6272, pvrtmp_6273,
                                             pvrtmp_6274};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6224");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2949, CursorTy end_r_2950,
                                       CursorTy loc_2948,
                                       CursorTy tags_45_942_1556,
                                       IntTy inVal_46_943_1557)
{
    if (loc_2948 + 32 > end_r_2950) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2950);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2950 = chunk_end_12;
        *(TagTyPacked *) loc_2948 = 255;
        
        CursorTy redir = loc_2948 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2948 = chunk_start_11;
    }
    
    CursorTy loc_3072 = loc_2948 + 1;
    CursorTy loc_3073 = loc_3072 + 8;
    TagTyPacked tmpval_6282 = *(TagTyPacked *) tags_45_942_1556;
    CursorTy tmpcur_6283 = tags_45_942_1556 + 1;
    
    
  switch_6326:
    ;
    switch (tmpval_6282) {
        
      case 0:
        {
            CursorTy jump_3983 = tags_45_942_1556 + 1;
            
            *(TagTyPacked *) loc_2948 = 0;
            
            CursorTy writetag_4563 = loc_2948 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2950, jump_3983,
                                                   loc_2948, writetag_4563};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6288 = *(IntTy *) tmpcur_6283;
            CursorTy tmpcur_6289 = tmpcur_6283 + sizeof(IntTy);
            CursorTy jump_3985 = tmpcur_6283 + 8;
            IntTy fltPkd_1537_1560 = tmpval_6288 + inVal_46_943_1557;
            CursorCursorCursorCursorProd tmp_struct_7 =
                                          addValTag(end_r_2949, end_r_2950, loc_3073, tmpcur_6289, inVal_46_943_1557);
            CursorTy pvrtmp_6290 = tmp_struct_7.field0;
            CursorTy pvrtmp_6291 = tmp_struct_7.field1;
            CursorTy pvrtmp_6292 = tmp_struct_7.field2;
            CursorTy pvrtmp_6293 = tmp_struct_7.field3;
            
            *(TagTyPacked *) loc_2948 = 1;
            
            CursorTy writetag_4568 = loc_2948 + 1;
            
            *(IntTy *) writetag_4568 = fltPkd_1537_1560;
            
            CursorTy writecur_4569 = writetag_4568 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6290, pvrtmp_6291,
                                                   loc_2948, pvrtmp_6293};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6302 = *(CursorTy *) tmpcur_6283;
            CursorTy tmpaftercur_6303 = tmpcur_6283 + 8;
            CursorTy jump_4294 = tmpcur_6283 + 8;
            CursorCursorCursorCursorProd tmp_struct_8 =
                                          addValTag(end_r_2949, end_r_2950, loc_2948, tmpcur_6302, inVal_46_943_1557);
            CursorTy pvrtmp_6304 = tmp_struct_8.field0;
            CursorTy pvrtmp_6305 = tmp_struct_8.field1;
            CursorTy pvrtmp_6306 = tmp_struct_8.field2;
            CursorTy pvrtmp_6307 = tmp_struct_8.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6304, jump_4294,
                                                   pvrtmp_6306, pvrtmp_6307};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6314 = *(CursorTy *) tmpcur_6283;
            CursorTy tmpaftercur_6315 = tmpcur_6283 + 8;
            CursorCursorCursorCursorProd tmp_struct_9 =
                                          addValTag(end_r_2949, end_r_2950, loc_2948, tmpcur_6314, inVal_46_943_1557);
            CursorTy pvrtmp_6316 = tmp_struct_9.field0;
            CursorTy pvrtmp_6317 = tmp_struct_9.field1;
            CursorTy pvrtmp_6318 = tmp_struct_9.field2;
            CursorTy pvrtmp_6319 = tmp_struct_9.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6316, pvrtmp_6317,
                                                   pvrtmp_6318, pvrtmp_6319};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6282");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkCATList(CursorTy end_r_2952, CursorTy loc_2951,
                                 IntTy len_49_946_1562,
                                 IntTy tagLen_50_947_1563,
                                 IntTy strLen_51_948_1564)
{
    if (loc_2951 + 32 > end_r_2952) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2952);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2952 = chunk_end_18;
        *(TagTyPacked *) loc_2951 = 255;
        
        CursorTy redir = loc_2951 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2951 = chunk_start_17;
    }
    
    CursorTy loc_3081 = loc_2951 + 1;
    CursorTy loc_3082 = loc_3081 + 8;
    CursorTy loc_3083 = loc_3082 + 8;
    BoolTy fltIf_1539_1565 = len_49_946_1562 <= 0;
    
    if (fltIf_1539_1565) {
        *(TagTyPacked *) loc_2951 = 0;
        
        CursorTy writetag_4578 = loc_2951 + 1;
        
        return (CursorCursorCursorProd) {end_r_2952, loc_2951, writetag_4578};
    } else {
        CursorCursorCursorProd tmp_struct_13 =
                                mkContentText(end_r_2952, loc_3083, strLen_51_948_1564);
        CursorTy pvrtmp_6331 = tmp_struct_13.field0;
        CursorTy pvrtmp_6332 = tmp_struct_13.field1;
        CursorTy pvrtmp_6333 = tmp_struct_13.field2;
        IntTy fltAppE_1540_1567 = len_49_946_1562 - 1;
        CursorCursorCursorProd tmp_struct_14 =
                                mkCATList(pvrtmp_6331, pvrtmp_6333, fltAppE_1540_1567, tagLen_50_947_1563, strLen_51_948_1564);
        CursorTy pvrtmp_6338 = tmp_struct_14.field0;
        CursorTy pvrtmp_6339 = tmp_struct_14.field1;
        CursorTy pvrtmp_6340 = tmp_struct_14.field2;
        CursorCursorCursorProd tmp_struct_15 =
                                mkRandomTags(pvrtmp_6338, pvrtmp_6340, tagLen_50_947_1563);
        CursorTy pvrtmp_6345 = tmp_struct_15.field0;
        CursorTy pvrtmp_6346 = tmp_struct_15.field1;
        CursorTy pvrtmp_6347 = tmp_struct_15.field2;
        
        *(TagTyPacked *) loc_2951 = 23;
        
        CursorTy writetag_4583 = loc_2951 + 1;
        
        *(CursorTy *) writetag_4583 = pvrtmp_6333;
        
        CursorTy writecur_4584 = writetag_4583 + 8;
        
        *(CursorTy *) writecur_4584 = pvrtmp_6340;
        
        CursorTy writecur_4585 = writecur_4584 + 8;
        
        return (CursorCursorCursorProd) {pvrtmp_6345, loc_2951, pvrtmp_6347};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2954, CursorTy loc_2953,
                                IntTy len_204_1101_1570)
{
    if (loc_2953 + 32 > end_r_2954) {
        ChunkTy new_chunk_20 = alloc_chunk(end_r_2954);
        CursorTy chunk_start_21 = new_chunk_20.chunk_start;
        CursorTy chunk_end_22 = new_chunk_20.chunk_end;
        
        end_r_2954 = chunk_end_22;
        *(TagTyPacked *) loc_2953 = 255;
        
        CursorTy redir = loc_2953 + 1;
        
        *(CursorTy *) redir = chunk_start_21;
        loc_2953 = chunk_start_21;
    }
    
    CursorTy loc_3095 = loc_2953 + 1;
    CursorTy loc_3096 = loc_3095 + 8;
    BoolTy fltIf_1541_1571 = len_204_1101_1570 <= 0;
    
    if (fltIf_1541_1571) {
        *(TagTyPacked *) loc_2953 = 0;
        
        CursorTy writetag_4590 = loc_2953 + 1;
        
        return (CursorCursorCursorProd) {end_r_2954, loc_2953, writetag_4590};
    } else {
        IntTy fltPrm_1542_1572 = rand();
        IntTy randomChar_205_1102_1573 = fltPrm_1542_1572 % 128;
        IntTy fltAppE_1543_1574 = len_204_1101_1570 - 1;
        CursorCursorCursorProd tmp_struct_19 =
                                mkString(end_r_2954, loc_3096, fltAppE_1543_1574);
        CursorTy pvrtmp_6360 = tmp_struct_19.field0;
        CursorTy pvrtmp_6361 = tmp_struct_19.field1;
        CursorTy pvrtmp_6362 = tmp_struct_19.field2;
        
        *(TagTyPacked *) loc_2953 = 1;
        
        CursorTy writetag_4593 = loc_2953 + 1;
        
        *(IntTy *) writetag_4593 = randomChar_205_1102_1573;
        
        CursorTy writecur_4594 = writetag_4593 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6360, loc_2953, pvrtmp_6362};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2956, CursorTy loc_2955,
                                     IntTy n_218_1115_1576)
{
    if (loc_2955 + 32 > end_r_2956) {
        ChunkTy new_chunk_24 = alloc_chunk(end_r_2956);
        CursorTy chunk_start_25 = new_chunk_24.chunk_start;
        CursorTy chunk_end_26 = new_chunk_24.chunk_end;
        
        end_r_2956 = chunk_end_26;
        *(TagTyPacked *) loc_2955 = 255;
        
        CursorTy redir = loc_2955 + 1;
        
        *(CursorTy *) redir = chunk_start_25;
        loc_2955 = chunk_start_25;
    }
    
    CursorTy loc_3101 = loc_2955 + 1;
    CursorCursorCursorProd tmp_struct_23 =
                            mkString(end_r_2956, loc_3101, n_218_1115_1576);
    CursorTy pvrtmp_6371 = tmp_struct_23.field0;
    CursorTy pvrtmp_6372 = tmp_struct_23.field1;
    CursorTy pvrtmp_6373 = tmp_struct_23.field2;
    
    *(TagTyPacked *) loc_2955 = 1;
    
    CursorTy writetag_4598 = loc_2955 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_6371, loc_2955, pvrtmp_6373};
}
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2958, CursorTy loc_2957,
                                    IntTy len_343_1240_1578)
{
    if (loc_2957 + 32 > end_r_2958) {
        ChunkTy new_chunk_28 = alloc_chunk(end_r_2958);
        CursorTy chunk_start_29 = new_chunk_28.chunk_start;
        CursorTy chunk_end_30 = new_chunk_28.chunk_end;
        
        end_r_2958 = chunk_end_30;
        *(TagTyPacked *) loc_2957 = 255;
        
        CursorTy redir = loc_2957 + 1;
        
        *(CursorTy *) redir = chunk_start_29;
        loc_2957 = chunk_start_29;
    }
    
    CursorTy loc_3105 = loc_2957 + 1;
    CursorTy loc_3106 = loc_3105 + 8;
    BoolTy fltIf_1545_1579 = len_343_1240_1578 <= 0;
    
    if (fltIf_1545_1579) {
        *(TagTyPacked *) loc_2957 = 0;
        
        CursorTy writetag_4601 = loc_2957 + 1;
        
        return (CursorCursorCursorProd) {end_r_2958, loc_2957, writetag_4601};
    } else {
        IntTy fltAppE_1546_1581 = len_343_1240_1578 - 1;
        CursorCursorCursorProd tmp_struct_27 =
                                mkRandomTags(end_r_2958, loc_3106, fltAppE_1546_1581);
        CursorTy pvrtmp_6386 = tmp_struct_27.field0;
        CursorTy pvrtmp_6387 = tmp_struct_27.field1;
        CursorTy pvrtmp_6388 = tmp_struct_27.field2;
        
        *(TagTyPacked *) loc_2957 = 1;
        
        CursorTy writetag_4604 = loc_2957 + 1;
        
        *(IntTy *) writetag_4604 = 100;
        
        CursorTy writecur_4605 = writetag_4604 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6386, loc_2957, pvrtmp_6388};
    }
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2961,
                                          CursorTy end_r_2962,
                                          CursorTy loc_2960,
                                          CursorTy arg_647_1260_1583)
{
    if (loc_2960 + 32 > end_r_2962) {
        ChunkTy new_chunk_34 = alloc_chunk(end_r_2962);
        CursorTy chunk_start_35 = new_chunk_34.chunk_start;
        CursorTy chunk_end_36 = new_chunk_34.chunk_end;
        
        end_r_2962 = chunk_end_36;
        *(TagTyPacked *) loc_2960 = 255;
        
        CursorTy redir = loc_2960 + 1;
        
        *(CursorTy *) redir = chunk_start_35;
        loc_2960 = chunk_start_35;
    }
    
    CursorTy loc_3116 = loc_2960 + 1;
    CursorTy loc_3117 = loc_3116 + 8;
    TagTyPacked tmpval_6397 = *(TagTyPacked *) arg_647_1260_1583;
    CursorTy tmpcur_6398 = arg_647_1260_1583 + 1;
    
    
  switch_6441:
    ;
    switch (tmpval_6397) {
        
      case 0:
        {
            CursorTy jump_3995 = arg_647_1260_1583 + 1;
            
            *(TagTyPacked *) loc_2960 = 0;
            
            CursorTy writetag_4609 = loc_2960 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2962, jump_3995,
                                                   loc_2960, writetag_4609};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6403 = *(IntTy *) tmpcur_6398;
            CursorTy tmpcur_6404 = tmpcur_6398 + sizeof(IntTy);
            CursorTy jump_3997 = tmpcur_6398 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_String(end_r_2961, end_r_2962, loc_3117, tmpcur_6404);
            CursorTy pvrtmp_6405 = tmp_struct_31.field0;
            CursorTy pvrtmp_6406 = tmp_struct_31.field1;
            CursorTy pvrtmp_6407 = tmp_struct_31.field2;
            CursorTy pvrtmp_6408 = tmp_struct_31.field3;
            
            *(TagTyPacked *) loc_2960 = 1;
            
            CursorTy writetag_4614 = loc_2960 + 1;
            
            *(IntTy *) writetag_4614 = tmpval_6403;
            
            CursorTy writecur_4615 = writetag_4614 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6405, pvrtmp_6406,
                                                   loc_2960, pvrtmp_6408};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6417 = *(CursorTy *) tmpcur_6398;
            CursorTy tmpaftercur_6418 = tmpcur_6398 + 8;
            CursorTy jump_4300 = tmpcur_6398 + 8;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_String(end_r_2961, end_r_2962, loc_2960, tmpcur_6417);
            CursorTy pvrtmp_6419 = tmp_struct_32.field0;
            CursorTy pvrtmp_6420 = tmp_struct_32.field1;
            CursorTy pvrtmp_6421 = tmp_struct_32.field2;
            CursorTy pvrtmp_6422 = tmp_struct_32.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6419, jump_4300,
                                                   pvrtmp_6421, pvrtmp_6422};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6429 = *(CursorTy *) tmpcur_6398;
            CursorTy tmpaftercur_6430 = tmpcur_6398 + 8;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_String(end_r_2961, end_r_2962, loc_2960, tmpcur_6429);
            CursorTy pvrtmp_6431 = tmp_struct_33.field0;
            CursorTy pvrtmp_6432 = tmp_struct_33.field1;
            CursorTy pvrtmp_6433 = tmp_struct_33.field2;
            CursorTy pvrtmp_6434 = tmp_struct_33.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6431, pvrtmp_6432,
                                                   pvrtmp_6433, pvrtmp_6434};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6397");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2965,
                                                       CursorTy end_r_2966,
                                                       CursorTy loc_2964,
                                                       CursorTy arg_652_1265_1588)
{
    CursorTy loc_3129 = loc_2964 + 1;
    CursorTy loc_3130 = loc_3129 + 8;
    TagTyPacked tmpval_6442 = *(TagTyPacked *) arg_652_1265_1588;
    CursorTy tmpcur_6443 = arg_652_1265_1588 + 1;
    
    
  switch_6486:
    ;
    switch (tmpval_6442) {
        
      case 0:
        {
            CursorTy jump_4000 = arg_652_1265_1588 + 1;
            
            *(TagTyPacked *) loc_2964 = 0;
            
            CursorTy writetag_4625 = loc_2964 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2966, jump_4000,
                                                   loc_2964, writetag_4625};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6448 = *(IntTy *) tmpcur_6443;
            CursorTy tmpcur_6449 = tmpcur_6443 + sizeof(IntTy);
            CursorTy jump_4002 = tmpcur_6443 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_String(end_r_2965, end_r_2966, loc_3130, tmpcur_6449);
            CursorTy pvrtmp_6450 = tmp_struct_37.field0;
            CursorTy pvrtmp_6451 = tmp_struct_37.field1;
            CursorTy pvrtmp_6452 = tmp_struct_37.field2;
            CursorTy pvrtmp_6453 = tmp_struct_37.field3;
            
            *(TagTyPacked *) loc_2964 = 1;
            
            CursorTy writetag_4630 = loc_2964 + 1;
            
            *(IntTy *) writetag_4630 = tmpval_6448;
            
            CursorTy writecur_4631 = writetag_4630 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6450, pvrtmp_6451,
                                                   loc_2964, pvrtmp_6453};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6462 = *(CursorTy *) tmpcur_6443;
            CursorTy tmpaftercur_6463 = tmpcur_6443 + 8;
            CursorTy jump_4306 = tmpcur_6443 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_String(end_r_2965, end_r_2966, loc_2964, tmpcur_6462);
            CursorTy pvrtmp_6464 = tmp_struct_38.field0;
            CursorTy pvrtmp_6465 = tmp_struct_38.field1;
            CursorTy pvrtmp_6466 = tmp_struct_38.field2;
            CursorTy pvrtmp_6467 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6464, jump_4306,
                                                   pvrtmp_6466, pvrtmp_6467};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6474 = *(CursorTy *) tmpcur_6443;
            CursorTy tmpaftercur_6475 = tmpcur_6443 + 8;
            CursorCursorCursorCursorProd tmp_struct_39 =
                                          _copy_without_ptrs_String(end_r_2965, end_r_2966, loc_2964, tmpcur_6474);
            CursorTy pvrtmp_6476 = tmp_struct_39.field0;
            CursorTy pvrtmp_6477 = tmp_struct_39.field1;
            CursorTy pvrtmp_6478 = tmp_struct_39.field2;
            CursorTy pvrtmp_6479 = tmp_struct_39.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6476, pvrtmp_6477,
                                                   pvrtmp_6478, pvrtmp_6479};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6442");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2968, CursorTy arg_657_1270_1593)
{
    TagTyPacked tmpval_6487 = *(TagTyPacked *) arg_657_1270_1593;
    CursorTy tmpcur_6488 = arg_657_1270_1593 + 1;
    
    
  switch_6498:
    ;
    switch (tmpval_6487) {
        
      case 0:
        {
            CursorTy jump_4005 = arg_657_1270_1593 + 1;
            
            return (CursorProd) {jump_4005};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6489 = *(IntTy *) tmpcur_6488;
            CursorTy tmpcur_6490 = tmpcur_6488 + sizeof(IntTy);
            CursorTy jump_4007 = tmpcur_6488 + 8;
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2968, tmpcur_6490);
            CursorTy pvrtmp_6491 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_6491};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6492 = *(CursorTy *) tmpcur_6488;
            CursorTy tmpaftercur_6493 = tmpcur_6488 + 8;
            CursorTy jump_4312 = tmpcur_6488 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_String(end_r_2968, tmpcur_6492);
            CursorTy pvrtmp_6494 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_4312};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6495 = *(CursorTy *) tmpcur_6488;
            CursorTy tmpaftercur_6496 = tmpcur_6488 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_String(end_r_2968, tmpcur_6495);
            CursorTy pvrtmp_6497 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_6497};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6487");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2970, CursorTy arg_662_1274_1597)
{
    TagTyPacked tmpval_6499 = *(TagTyPacked *) arg_662_1274_1597;
    CursorTy tmpcur_6500 = arg_662_1274_1597 + 1;
    
    
  switch_6510:
    ;
    switch (tmpval_6499) {
        
      case 0:
        {
            CursorTy jump_4010 = arg_662_1274_1597 + 1;
            unsigned char wildcard_663_1275_1598 = print_symbol(6184);
            unsigned char wildcard_664_1276_1599 = print_symbol(6176);
            
            return (CursorProd) {jump_4010};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6501 = *(IntTy *) tmpcur_6500;
            CursorTy tmpcur_6502 = tmpcur_6500 + sizeof(IntTy);
            CursorTy jump_4012 = tmpcur_6500 + 8;
            unsigned char wildcard_669_1279_1602 = print_symbol(6185);
            unsigned char y_667_1280_1603 = printf("%lld", tmpval_6501);
            CursorProd tmp_struct_43 =  _print_String(end_r_2970, tmpcur_6502);
            CursorTy pvrtmp_6503 = tmp_struct_43.field0;
            unsigned char wildcard_670_1282_1605 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_6503};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6504 = *(CursorTy *) tmpcur_6500;
            CursorTy tmpaftercur_6505 = tmpcur_6500 + 8;
            CursorTy jump_4318 = tmpcur_6500 + 8;
            unsigned char wildcard_4321 = print_symbol(6193);
            CursorProd tmp_struct_44 =  _print_String(end_r_2970, tmpcur_6504);
            CursorTy pvrtmp_6506 = tmp_struct_44.field0;
            
            return (CursorProd) {jump_4318};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6507 = *(CursorTy *) tmpcur_6500;
            CursorTy tmpaftercur_6508 = tmpcur_6500 + 8;
            unsigned char wildcard_4321 = print_symbol(6192);
            CursorProd tmp_struct_45 =  _print_String(end_r_2970, tmpcur_6507);
            CursorTy pvrtmp_6509 = tmp_struct_45.field0;
            
            return (CursorProd) {pvrtmp_6509};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6499");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2973,
                                           CursorTy end_r_2974,
                                           CursorTy loc_2972,
                                           CursorTy arg_671_1283_1606)
{
    if (loc_2972 + 32 > end_r_2974) {
        ChunkTy new_chunk_50 = alloc_chunk(end_r_2974);
        CursorTy chunk_start_51 = new_chunk_50.chunk_start;
        CursorTy chunk_end_52 = new_chunk_50.chunk_end;
        
        end_r_2974 = chunk_end_52;
        *(TagTyPacked *) loc_2972 = 255;
        
        CursorTy redir = loc_2972 + 1;
        
        *(CursorTy *) redir = chunk_start_51;
        loc_2972 = chunk_start_51;
    }
    
    TagTyPacked tmpval_6511 = *(TagTyPacked *) arg_671_1283_1606;
    CursorTy tmpcur_6512 = arg_671_1283_1606 + 1;
    
    
  switch_6561:
    ;
    switch (tmpval_6511) {
        
      case 0:
        {
            CursorTy loc_3152 = loc_2972 + 1;
            CursorCursorCursorCursorProd tmp_struct_46 =
                                          _copy_String(end_r_2973, end_r_2974, loc_3152, tmpcur_6512);
            CursorTy pvrtmp_6513 = tmp_struct_46.field0;
            CursorTy pvrtmp_6514 = tmp_struct_46.field1;
            CursorTy pvrtmp_6515 = tmp_struct_46.field2;
            CursorTy pvrtmp_6516 = tmp_struct_46.field3;
            
            *(TagTyPacked *) loc_2972 = 0;
            
            CursorTy writetag_4662 = loc_2972 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6513, pvrtmp_6514,
                                                   loc_2972, pvrtmp_6516};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3158 = loc_2972 + 1;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_String(end_r_2973, end_r_2974, loc_3158, tmpcur_6512);
            CursorTy pvrtmp_6525 = tmp_struct_47.field0;
            CursorTy pvrtmp_6526 = tmp_struct_47.field1;
            CursorTy pvrtmp_6527 = tmp_struct_47.field2;
            CursorTy pvrtmp_6528 = tmp_struct_47.field3;
            
            *(TagTyPacked *) loc_2972 = 1;
            
            CursorTy writetag_4667 = loc_2972 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6525, pvrtmp_6526,
                                                   loc_2972, pvrtmp_6528};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6537 = *(CursorTy *) tmpcur_6512;
            CursorTy tmpaftercur_6538 = tmpcur_6512 + 8;
            CursorTy jump_4324 = tmpcur_6512 + 8;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Content(end_r_2973, end_r_2974, loc_2972, tmpcur_6537);
            CursorTy pvrtmp_6539 = tmp_struct_48.field0;
            CursorTy pvrtmp_6540 = tmp_struct_48.field1;
            CursorTy pvrtmp_6541 = tmp_struct_48.field2;
            CursorTy pvrtmp_6542 = tmp_struct_48.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6539, jump_4324,
                                                   pvrtmp_6541, pvrtmp_6542};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6549 = *(CursorTy *) tmpcur_6512;
            CursorTy tmpaftercur_6550 = tmpcur_6512 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Content(end_r_2973, end_r_2974, loc_2972, tmpcur_6549);
            CursorTy pvrtmp_6551 = tmp_struct_49.field0;
            CursorTy pvrtmp_6552 = tmp_struct_49.field1;
            CursorTy pvrtmp_6553 = tmp_struct_49.field2;
            CursorTy pvrtmp_6554 = tmp_struct_49.field3;
            
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
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2977,
                                                        CursorTy end_r_2978,
                                                        CursorTy loc_2976,
                                                        CursorTy arg_676_1288_1611)
{
    TagTyPacked tmpval_6562 = *(TagTyPacked *) arg_676_1288_1611;
    CursorTy tmpcur_6563 = arg_676_1288_1611 + 1;
    
    
  switch_6612:
    ;
    switch (tmpval_6562) {
        
      case 0:
        {
            CursorTy loc_3166 = loc_2976 + 1;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_without_ptrs_String(end_r_2977, end_r_2978, loc_3166, tmpcur_6563);
            CursorTy pvrtmp_6564 = tmp_struct_53.field0;
            CursorTy pvrtmp_6565 = tmp_struct_53.field1;
            CursorTy pvrtmp_6566 = tmp_struct_53.field2;
            CursorTy pvrtmp_6567 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2976 = 0;
            
            CursorTy writetag_4678 = loc_2976 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6564, pvrtmp_6565,
                                                   loc_2976, pvrtmp_6567};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3172 = loc_2976 + 1;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_without_ptrs_String(end_r_2977, end_r_2978, loc_3172, tmpcur_6563);
            CursorTy pvrtmp_6576 = tmp_struct_54.field0;
            CursorTy pvrtmp_6577 = tmp_struct_54.field1;
            CursorTy pvrtmp_6578 = tmp_struct_54.field2;
            CursorTy pvrtmp_6579 = tmp_struct_54.field3;
            
            *(TagTyPacked *) loc_2976 = 1;
            
            CursorTy writetag_4683 = loc_2976 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6576, pvrtmp_6577,
                                                   loc_2976, pvrtmp_6579};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6588 = *(CursorTy *) tmpcur_6563;
            CursorTy tmpaftercur_6589 = tmpcur_6563 + 8;
            CursorTy jump_4330 = tmpcur_6563 + 8;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_without_ptrs_Content(end_r_2977, end_r_2978, loc_2976, tmpcur_6588);
            CursorTy pvrtmp_6590 = tmp_struct_55.field0;
            CursorTy pvrtmp_6591 = tmp_struct_55.field1;
            CursorTy pvrtmp_6592 = tmp_struct_55.field2;
            CursorTy pvrtmp_6593 = tmp_struct_55.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6590, jump_4330,
                                                   pvrtmp_6592, pvrtmp_6593};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6600 = *(CursorTy *) tmpcur_6563;
            CursorTy tmpaftercur_6601 = tmpcur_6563 + 8;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_without_ptrs_Content(end_r_2977, end_r_2978, loc_2976, tmpcur_6600);
            CursorTy pvrtmp_6602 = tmp_struct_56.field0;
            CursorTy pvrtmp_6603 = tmp_struct_56.field1;
            CursorTy pvrtmp_6604 = tmp_struct_56.field2;
            CursorTy pvrtmp_6605 = tmp_struct_56.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6602, pvrtmp_6603,
                                                   pvrtmp_6604, pvrtmp_6605};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6562");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2980, CursorTy arg_681_1293_1616)
{
    TagTyPacked tmpval_6613 = *(TagTyPacked *) arg_681_1293_1616;
    CursorTy tmpcur_6614 = arg_681_1293_1616 + 1;
    
    
  switch_6623:
    ;
    switch (tmpval_6613) {
        
      case 0:
        {
            CursorProd tmp_struct_57 =
                        _traverse_String(end_r_2980, tmpcur_6614);
            CursorTy pvrtmp_6615 = tmp_struct_57.field0;
            
            return (CursorProd) {pvrtmp_6615};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_58 =
                        _traverse_String(end_r_2980, tmpcur_6614);
            CursorTy pvrtmp_6616 = tmp_struct_58.field0;
            
            return (CursorProd) {pvrtmp_6616};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6617 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6618 = tmpcur_6614 + 8;
            CursorTy jump_4336 = tmpcur_6614 + 8;
            CursorProd tmp_struct_59 =
                        _traverse_Content(end_r_2980, tmpcur_6617);
            CursorTy pvrtmp_6619 = tmp_struct_59.field0;
            
            return (CursorProd) {jump_4336};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6620 = *(CursorTy *) tmpcur_6614;
            CursorTy tmpaftercur_6621 = tmpcur_6614 + 8;
            CursorProd tmp_struct_60 =
                        _traverse_Content(end_r_2980, tmpcur_6620);
            CursorTy pvrtmp_6622 = tmp_struct_60.field0;
            
            return (CursorProd) {pvrtmp_6622};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6613");
            exit(1);
        }
    }
}
CursorProd _print_Content(CursorTy end_r_2982, CursorTy arg_686_1298_1621)
{
    TagTyPacked tmpval_6624 = *(TagTyPacked *) arg_686_1298_1621;
    CursorTy tmpcur_6625 = arg_686_1298_1621 + 1;
    
    
  switch_6634:
    ;
    switch (tmpval_6624) {
        
      case 0:
        {
            unsigned char wildcard_689_1300_1623 = print_symbol(6183);
            CursorProd tmp_struct_61 =  _print_String(end_r_2982, tmpcur_6625);
            CursorTy pvrtmp_6626 = tmp_struct_61.field0;
            unsigned char wildcard_690_1302_1625 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_6626};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_693_1304_1627 = print_symbol(6177);
            CursorProd tmp_struct_62 =  _print_String(end_r_2982, tmpcur_6625);
            CursorTy pvrtmp_6627 = tmp_struct_62.field0;
            unsigned char wildcard_694_1306_1629 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_6627};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6628 = *(CursorTy *) tmpcur_6625;
            CursorTy tmpaftercur_6629 = tmpcur_6625 + 8;
            CursorTy jump_4342 = tmpcur_6625 + 8;
            unsigned char wildcard_4345 = print_symbol(6193);
            CursorProd tmp_struct_63 =  _print_Content(end_r_2982, tmpcur_6628);
            CursorTy pvrtmp_6630 = tmp_struct_63.field0;
            
            return (CursorProd) {jump_4342};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6631 = *(CursorTy *) tmpcur_6625;
            CursorTy tmpaftercur_6632 = tmpcur_6625 + 8;
            unsigned char wildcard_4345 = print_symbol(6192);
            CursorProd tmp_struct_64 =  _print_Content(end_r_2982, tmpcur_6631);
            CursorTy pvrtmp_6633 = tmp_struct_64.field0;
            
            return (CursorProd) {pvrtmp_6633};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6624");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2985, CursorTy end_r_2986,
                                       CursorTy loc_2984,
                                       CursorTy arg_695_1307_1630)
{
    if (loc_2984 + 32 > end_r_2986) {
        ChunkTy new_chunk_89 = alloc_chunk(end_r_2986);
        CursorTy chunk_start_90 = new_chunk_89.chunk_start;
        CursorTy chunk_end_91 = new_chunk_89.chunk_end;
        
        end_r_2986 = chunk_end_91;
        *(TagTyPacked *) loc_2984 = 255;
        
        CursorTy redir = loc_2984 + 1;
        
        *(CursorTy *) redir = chunk_start_90;
        loc_2984 = chunk_start_90;
    }
    
    CursorTy loc_3202 = loc_2984 + 1;
    CursorTy loc_3203 = loc_3202 + 8;
    CursorTy loc_3218 = loc_2984 + 1;
    CursorTy loc_3219 = loc_3218 + 8;
    CursorTy loc_3239 = loc_2984 + 1;
    CursorTy loc_3240 = loc_3239 + 8;
    CursorTy loc_3241 = loc_3240 + 8;
    CursorTy loc_3265 = loc_2984 + 1;
    CursorTy loc_3266 = loc_3265 + 8;
    CursorTy loc_3267 = loc_3266 + 8;
    CursorTy loc_3291 = loc_2984 + 1;
    CursorTy loc_3292 = loc_3291 + 8;
    CursorTy loc_3293 = loc_3292 + 8;
    CursorTy loc_3317 = loc_2984 + 1;
    CursorTy loc_3318 = loc_3317 + 8;
    CursorTy loc_3319 = loc_3318 + 8;
    CursorTy loc_3343 = loc_2984 + 1;
    CursorTy loc_3344 = loc_3343 + 8;
    CursorTy loc_3345 = loc_3344 + 8;
    CursorTy loc_3369 = loc_2984 + 1;
    CursorTy loc_3370 = loc_3369 + 8;
    CursorTy loc_3371 = loc_3370 + 8;
    TagTyPacked tmpval_6635 = *(TagTyPacked *) arg_695_1307_1630;
    CursorTy tmpcur_6636 = arg_695_1307_1630 + 1;
    
    
  switch_6901:
    ;
    switch (tmpval_6635) {
        
      case 0:
        {
            CursorTy jump_4031 = arg_695_1307_1630 + 1;
            
            *(TagTyPacked *) loc_2984 = 0;
            
            CursorTy writetag_4713 = loc_2984 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2986, jump_4031,
                                                   loc_2984, writetag_4713};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6641 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6642 = tmpcur_6636 + 8;
            CursorTy jump_4033 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Content(end_r_2985, end_r_2986, loc_3203, tmpaftercur_6642);
            CursorTy pvrtmp_6643 = tmp_struct_65.field0;
            CursorTy pvrtmp_6644 = tmp_struct_65.field1;
            CursorTy pvrtmp_6645 = tmp_struct_65.field2;
            CursorTy pvrtmp_6646 = tmp_struct_65.field3;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Adt(end_r_2985, pvrtmp_6643, pvrtmp_6646, tmpcur_6641);
            CursorTy pvrtmp_6651 = tmp_struct_66.field0;
            CursorTy pvrtmp_6652 = tmp_struct_66.field1;
            CursorTy pvrtmp_6653 = tmp_struct_66.field2;
            CursorTy pvrtmp_6654 = tmp_struct_66.field3;
            
            *(TagTyPacked *) loc_2984 = 9;
            
            CursorTy writetag_4719 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4719 = pvrtmp_6646;
            
            CursorTy writecur_4720 = writetag_4719 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6651, pvrtmp_6652,
                                                   loc_2984, pvrtmp_6654};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6663 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6664 = tmpcur_6636 + 8;
            CursorTy jump_4037 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2985, end_r_2986, loc_3219, tmpaftercur_6664);
            CursorTy pvrtmp_6665 = tmp_struct_67.field0;
            CursorTy pvrtmp_6666 = tmp_struct_67.field1;
            CursorTy pvrtmp_6667 = tmp_struct_67.field2;
            CursorTy pvrtmp_6668 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Content(end_r_2985, pvrtmp_6665, pvrtmp_6668, tmpcur_6663);
            CursorTy pvrtmp_6673 = tmp_struct_68.field0;
            CursorTy pvrtmp_6674 = tmp_struct_68.field1;
            CursorTy pvrtmp_6675 = tmp_struct_68.field2;
            CursorTy pvrtmp_6676 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2984 = 11;
            
            CursorTy writetag_4728 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4728 = pvrtmp_6668;
            
            CursorTy writecur_4729 = writetag_4728 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6673, pvrtmp_6674,
                                                   loc_2984, pvrtmp_6676};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6685 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6686 = tmpcur_6636 + 8;
            CursorTy tmpcur_6687 = *(CursorTy *) tmpaftercur_6686;
            CursorTy tmpaftercur_6688 = tmpaftercur_6686 + 8;
            CursorTy jump_4042 = tmpaftercur_6686 + 8;
            CursorTy jump_4041 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Tags(end_r_2985, end_r_2986, loc_3241, tmpaftercur_6688);
            CursorTy pvrtmp_6689 = tmp_struct_69.field0;
            CursorTy pvrtmp_6690 = tmp_struct_69.field1;
            CursorTy pvrtmp_6691 = tmp_struct_69.field2;
            CursorTy pvrtmp_6692 = tmp_struct_69.field3;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Content(end_r_2985, pvrtmp_6689, pvrtmp_6692, tmpcur_6685);
            CursorTy pvrtmp_6697 = tmp_struct_70.field0;
            CursorTy pvrtmp_6698 = tmp_struct_70.field1;
            CursorTy pvrtmp_6699 = tmp_struct_70.field2;
            CursorTy pvrtmp_6700 = tmp_struct_70.field3;
            CursorCursorCursorCursorProd tmp_struct_71 =
                                          _copy_Adt(end_r_2985, pvrtmp_6697, pvrtmp_6700, tmpcur_6687);
            CursorTy pvrtmp_6705 = tmp_struct_71.field0;
            CursorTy pvrtmp_6706 = tmp_struct_71.field1;
            CursorTy pvrtmp_6707 = tmp_struct_71.field2;
            CursorTy pvrtmp_6708 = tmp_struct_71.field3;
            
            *(TagTyPacked *) loc_2984 = 13;
            
            CursorTy writetag_4739 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4739 = pvrtmp_6692;
            
            CursorTy writecur_4740 = writetag_4739 + 8;
            
            *(CursorTy *) writecur_4740 = pvrtmp_6700;
            
            CursorTy writecur_4741 = writecur_4740 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6705, pvrtmp_6706,
                                                   loc_2984, pvrtmp_6708};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6717 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6718 = tmpcur_6636 + 8;
            CursorTy tmpcur_6719 = *(CursorTy *) tmpaftercur_6718;
            CursorTy tmpaftercur_6720 = tmpaftercur_6718 + 8;
            CursorTy jump_4048 = tmpaftercur_6718 + 8;
            CursorTy jump_4047 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_72 =
                                          _copy_Adt(end_r_2985, end_r_2986, loc_3267, tmpaftercur_6720);
            CursorTy pvrtmp_6721 = tmp_struct_72.field0;
            CursorTy pvrtmp_6722 = tmp_struct_72.field1;
            CursorTy pvrtmp_6723 = tmp_struct_72.field2;
            CursorTy pvrtmp_6724 = tmp_struct_72.field3;
            CursorCursorCursorCursorProd tmp_struct_73 =
                                          _copy_Content(end_r_2985, pvrtmp_6721, pvrtmp_6724, tmpcur_6717);
            CursorTy pvrtmp_6729 = tmp_struct_73.field0;
            CursorTy pvrtmp_6730 = tmp_struct_73.field1;
            CursorTy pvrtmp_6731 = tmp_struct_73.field2;
            CursorTy pvrtmp_6732 = tmp_struct_73.field3;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_Tags(end_r_2985, pvrtmp_6729, pvrtmp_6732, tmpcur_6719);
            CursorTy pvrtmp_6737 = tmp_struct_74.field0;
            CursorTy pvrtmp_6738 = tmp_struct_74.field1;
            CursorTy pvrtmp_6739 = tmp_struct_74.field2;
            CursorTy pvrtmp_6740 = tmp_struct_74.field3;
            
            *(TagTyPacked *) loc_2984 = 15;
            
            CursorTy writetag_4752 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4752 = pvrtmp_6724;
            
            CursorTy writecur_4753 = writetag_4752 + 8;
            
            *(CursorTy *) writecur_4753 = pvrtmp_6732;
            
            CursorTy writecur_4754 = writecur_4753 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6737, pvrtmp_6738,
                                                   loc_2984, pvrtmp_6740};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6749 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6750 = tmpcur_6636 + 8;
            CursorTy tmpcur_6751 = *(CursorTy *) tmpaftercur_6750;
            CursorTy tmpaftercur_6752 = tmpaftercur_6750 + 8;
            CursorTy jump_4054 = tmpaftercur_6750 + 8;
            CursorTy jump_4053 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_Tags(end_r_2985, end_r_2986, loc_3293, tmpaftercur_6752);
            CursorTy pvrtmp_6753 = tmp_struct_75.field0;
            CursorTy pvrtmp_6754 = tmp_struct_75.field1;
            CursorTy pvrtmp_6755 = tmp_struct_75.field2;
            CursorTy pvrtmp_6756 = tmp_struct_75.field3;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_Adt(end_r_2985, pvrtmp_6753, pvrtmp_6756, tmpcur_6749);
            CursorTy pvrtmp_6761 = tmp_struct_76.field0;
            CursorTy pvrtmp_6762 = tmp_struct_76.field1;
            CursorTy pvrtmp_6763 = tmp_struct_76.field2;
            CursorTy pvrtmp_6764 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_Content(end_r_2985, pvrtmp_6761, pvrtmp_6764, tmpcur_6751);
            CursorTy pvrtmp_6769 = tmp_struct_77.field0;
            CursorTy pvrtmp_6770 = tmp_struct_77.field1;
            CursorTy pvrtmp_6771 = tmp_struct_77.field2;
            CursorTy pvrtmp_6772 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2984 = 17;
            
            CursorTy writetag_4765 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4765 = pvrtmp_6756;
            
            CursorTy writecur_4766 = writetag_4765 + 8;
            
            *(CursorTy *) writecur_4766 = pvrtmp_6764;
            
            CursorTy writecur_4767 = writecur_4766 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6769, pvrtmp_6770,
                                                   loc_2984, pvrtmp_6772};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6781 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6782 = tmpcur_6636 + 8;
            CursorTy tmpcur_6783 = *(CursorTy *) tmpaftercur_6782;
            CursorTy tmpaftercur_6784 = tmpaftercur_6782 + 8;
            CursorTy jump_4060 = tmpaftercur_6782 + 8;
            CursorTy jump_4059 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_Adt(end_r_2985, end_r_2986, loc_3319, tmpaftercur_6784);
            CursorTy pvrtmp_6785 = tmp_struct_78.field0;
            CursorTy pvrtmp_6786 = tmp_struct_78.field1;
            CursorTy pvrtmp_6787 = tmp_struct_78.field2;
            CursorTy pvrtmp_6788 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_Tags(end_r_2985, pvrtmp_6785, pvrtmp_6788, tmpcur_6781);
            CursorTy pvrtmp_6793 = tmp_struct_79.field0;
            CursorTy pvrtmp_6794 = tmp_struct_79.field1;
            CursorTy pvrtmp_6795 = tmp_struct_79.field2;
            CursorTy pvrtmp_6796 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_Content(end_r_2985, pvrtmp_6793, pvrtmp_6796, tmpcur_6783);
            CursorTy pvrtmp_6801 = tmp_struct_80.field0;
            CursorTy pvrtmp_6802 = tmp_struct_80.field1;
            CursorTy pvrtmp_6803 = tmp_struct_80.field2;
            CursorTy pvrtmp_6804 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2984 = 19;
            
            CursorTy writetag_4778 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4778 = pvrtmp_6788;
            
            CursorTy writecur_4779 = writetag_4778 + 8;
            
            *(CursorTy *) writecur_4779 = pvrtmp_6796;
            
            CursorTy writecur_4780 = writecur_4779 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6801, pvrtmp_6802,
                                                   loc_2984, pvrtmp_6804};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6813 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6814 = tmpcur_6636 + 8;
            CursorTy tmpcur_6815 = *(CursorTy *) tmpaftercur_6814;
            CursorTy tmpaftercur_6816 = tmpaftercur_6814 + 8;
            CursorTy jump_4066 = tmpaftercur_6814 + 8;
            CursorTy jump_4065 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_Content(end_r_2985, end_r_2986, loc_3345, tmpaftercur_6816);
            CursorTy pvrtmp_6817 = tmp_struct_81.field0;
            CursorTy pvrtmp_6818 = tmp_struct_81.field1;
            CursorTy pvrtmp_6819 = tmp_struct_81.field2;
            CursorTy pvrtmp_6820 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_Tags(end_r_2985, pvrtmp_6817, pvrtmp_6820, tmpcur_6813);
            CursorTy pvrtmp_6825 = tmp_struct_82.field0;
            CursorTy pvrtmp_6826 = tmp_struct_82.field1;
            CursorTy pvrtmp_6827 = tmp_struct_82.field2;
            CursorTy pvrtmp_6828 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_Adt(end_r_2985, pvrtmp_6825, pvrtmp_6828, tmpcur_6815);
            CursorTy pvrtmp_6833 = tmp_struct_83.field0;
            CursorTy pvrtmp_6834 = tmp_struct_83.field1;
            CursorTy pvrtmp_6835 = tmp_struct_83.field2;
            CursorTy pvrtmp_6836 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2984 = 21;
            
            CursorTy writetag_4791 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4791 = pvrtmp_6820;
            
            CursorTy writecur_4792 = writetag_4791 + 8;
            
            *(CursorTy *) writecur_4792 = pvrtmp_6828;
            
            CursorTy writecur_4793 = writecur_4792 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6833, pvrtmp_6834,
                                                   loc_2984, pvrtmp_6836};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6845 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6846 = tmpcur_6636 + 8;
            CursorTy tmpcur_6847 = *(CursorTy *) tmpaftercur_6846;
            CursorTy tmpaftercur_6848 = tmpaftercur_6846 + 8;
            CursorTy jump_4072 = tmpaftercur_6846 + 8;
            CursorTy jump_4071 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_Content(end_r_2985, end_r_2986, loc_3371, tmpaftercur_6848);
            CursorTy pvrtmp_6849 = tmp_struct_84.field0;
            CursorTy pvrtmp_6850 = tmp_struct_84.field1;
            CursorTy pvrtmp_6851 = tmp_struct_84.field2;
            CursorTy pvrtmp_6852 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_Adt(end_r_2985, pvrtmp_6849, pvrtmp_6852, tmpcur_6845);
            CursorTy pvrtmp_6857 = tmp_struct_85.field0;
            CursorTy pvrtmp_6858 = tmp_struct_85.field1;
            CursorTy pvrtmp_6859 = tmp_struct_85.field2;
            CursorTy pvrtmp_6860 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_Tags(end_r_2985, pvrtmp_6857, pvrtmp_6860, tmpcur_6847);
            CursorTy pvrtmp_6865 = tmp_struct_86.field0;
            CursorTy pvrtmp_6866 = tmp_struct_86.field1;
            CursorTy pvrtmp_6867 = tmp_struct_86.field2;
            CursorTy pvrtmp_6868 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2984 = 23;
            
            CursorTy writetag_4804 = loc_2984 + 1;
            
            *(CursorTy *) writetag_4804 = pvrtmp_6852;
            
            CursorTy writecur_4805 = writetag_4804 + 8;
            
            *(CursorTy *) writecur_4805 = pvrtmp_6860;
            
            CursorTy writecur_4806 = writecur_4805 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6865, pvrtmp_6866,
                                                   loc_2984, pvrtmp_6868};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6877 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6878 = tmpcur_6636 + 8;
            CursorTy jump_4348 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_Adt(end_r_2985, end_r_2986, loc_2984, tmpcur_6877);
            CursorTy pvrtmp_6879 = tmp_struct_87.field0;
            CursorTy pvrtmp_6880 = tmp_struct_87.field1;
            CursorTy pvrtmp_6881 = tmp_struct_87.field2;
            CursorTy pvrtmp_6882 = tmp_struct_87.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6879, jump_4348,
                                                   pvrtmp_6881, pvrtmp_6882};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6889 = *(CursorTy *) tmpcur_6636;
            CursorTy tmpaftercur_6890 = tmpcur_6636 + 8;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_Adt(end_r_2985, end_r_2986, loc_2984, tmpcur_6889);
            CursorTy pvrtmp_6891 = tmp_struct_88.field0;
            CursorTy pvrtmp_6892 = tmp_struct_88.field1;
            CursorTy pvrtmp_6893 = tmp_struct_88.field2;
            CursorTy pvrtmp_6894 = tmp_struct_88.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6891, pvrtmp_6892,
                                                   pvrtmp_6893, pvrtmp_6894};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6635");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2989,
                                                    CursorTy end_r_2990,
                                                    CursorTy loc_2988,
                                                    CursorTy arg_740_1352_1675)
{
    TagTyPacked tmpval_6902 = *(TagTyPacked *) arg_740_1352_1675;
    CursorTy tmpcur_6903 = arg_740_1352_1675 + 1;
    
    
  switch_7168:
    ;
    switch (tmpval_6902) {
        
      case 0:
        {
            CursorTy jump_4077 = arg_740_1352_1675 + 1;
            
            *(TagTyPacked *) loc_2988 = 0;
            
            CursorTy writetag_4818 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2990, jump_4077,
                                                   loc_2988, writetag_4818};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6908 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_6909 = tmpcur_6903 + 8;
            CursorTy jump_4079 = tmpcur_6903 + 8;
            CursorTy loc_3393 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Content(end_r_2989, end_r_2990, loc_3393, tmpaftercur_6909);
            CursorTy pvrtmp_6910 = tmp_struct_92.field0;
            CursorTy pvrtmp_6911 = tmp_struct_92.field1;
            CursorTy pvrtmp_6912 = tmp_struct_92.field2;
            CursorTy pvrtmp_6913 = tmp_struct_92.field3;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Adt(end_r_2989, pvrtmp_6910, pvrtmp_6913, tmpcur_6908);
            CursorTy pvrtmp_6918 = tmp_struct_93.field0;
            CursorTy pvrtmp_6919 = tmp_struct_93.field1;
            CursorTy pvrtmp_6920 = tmp_struct_93.field2;
            CursorTy pvrtmp_6921 = tmp_struct_93.field3;
            
            *(TagTyPacked *) loc_2988 = 1;
            
            CursorTy writetag_4824 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6918, pvrtmp_6919,
                                                   loc_2988, pvrtmp_6921};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6930 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_6931 = tmpcur_6903 + 8;
            CursorTy jump_4083 = tmpcur_6903 + 8;
            CursorTy loc_3406 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2989, end_r_2990, loc_3406, tmpaftercur_6931);
            CursorTy pvrtmp_6932 = tmp_struct_94.field0;
            CursorTy pvrtmp_6933 = tmp_struct_94.field1;
            CursorTy pvrtmp_6934 = tmp_struct_94.field2;
            CursorTy pvrtmp_6935 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Content(end_r_2989, pvrtmp_6932, pvrtmp_6935, tmpcur_6930);
            CursorTy pvrtmp_6940 = tmp_struct_95.field0;
            CursorTy pvrtmp_6941 = tmp_struct_95.field1;
            CursorTy pvrtmp_6942 = tmp_struct_95.field2;
            CursorTy pvrtmp_6943 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2988 = 2;
            
            CursorTy writetag_4832 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6940, pvrtmp_6941,
                                                   loc_2988, pvrtmp_6943};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6952 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_6953 = tmpcur_6903 + 8;
            CursorTy tmpcur_6954 = *(CursorTy *) tmpaftercur_6953;
            CursorTy tmpaftercur_6955 = tmpaftercur_6953 + 8;
            CursorTy jump_4088 = tmpaftercur_6953 + 8;
            CursorTy jump_4087 = tmpcur_6903 + 8;
            CursorTy loc_3424 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Tags(end_r_2989, end_r_2990, loc_3424, tmpaftercur_6955);
            CursorTy pvrtmp_6956 = tmp_struct_96.field0;
            CursorTy pvrtmp_6957 = tmp_struct_96.field1;
            CursorTy pvrtmp_6958 = tmp_struct_96.field2;
            CursorTy pvrtmp_6959 = tmp_struct_96.field3;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Content(end_r_2989, pvrtmp_6956, pvrtmp_6959, tmpcur_6952);
            CursorTy pvrtmp_6964 = tmp_struct_97.field0;
            CursorTy pvrtmp_6965 = tmp_struct_97.field1;
            CursorTy pvrtmp_6966 = tmp_struct_97.field2;
            CursorTy pvrtmp_6967 = tmp_struct_97.field3;
            CursorCursorCursorCursorProd tmp_struct_98 =
                                          _copy_without_ptrs_Adt(end_r_2989, pvrtmp_6964, pvrtmp_6967, tmpcur_6954);
            CursorTy pvrtmp_6972 = tmp_struct_98.field0;
            CursorTy pvrtmp_6973 = tmp_struct_98.field1;
            CursorTy pvrtmp_6974 = tmp_struct_98.field2;
            CursorTy pvrtmp_6975 = tmp_struct_98.field3;
            
            *(TagTyPacked *) loc_2988 = 3;
            
            CursorTy writetag_4842 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6972, pvrtmp_6973,
                                                   loc_2988, pvrtmp_6975};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6984 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_6985 = tmpcur_6903 + 8;
            CursorTy tmpcur_6986 = *(CursorTy *) tmpaftercur_6985;
            CursorTy tmpaftercur_6987 = tmpaftercur_6985 + 8;
            CursorTy jump_4094 = tmpaftercur_6985 + 8;
            CursorTy jump_4093 = tmpcur_6903 + 8;
            CursorTy loc_3444 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_99 =
                                          _copy_without_ptrs_Adt(end_r_2989, end_r_2990, loc_3444, tmpaftercur_6987);
            CursorTy pvrtmp_6988 = tmp_struct_99.field0;
            CursorTy pvrtmp_6989 = tmp_struct_99.field1;
            CursorTy pvrtmp_6990 = tmp_struct_99.field2;
            CursorTy pvrtmp_6991 = tmp_struct_99.field3;
            CursorCursorCursorCursorProd tmp_struct_100 =
                                          _copy_without_ptrs_Content(end_r_2989, pvrtmp_6988, pvrtmp_6991, tmpcur_6984);
            CursorTy pvrtmp_6996 = tmp_struct_100.field0;
            CursorTy pvrtmp_6997 = tmp_struct_100.field1;
            CursorTy pvrtmp_6998 = tmp_struct_100.field2;
            CursorTy pvrtmp_6999 = tmp_struct_100.field3;
            CursorCursorCursorCursorProd tmp_struct_101 =
                                          _copy_without_ptrs_Tags(end_r_2989, pvrtmp_6996, pvrtmp_6999, tmpcur_6986);
            CursorTy pvrtmp_7004 = tmp_struct_101.field0;
            CursorTy pvrtmp_7005 = tmp_struct_101.field1;
            CursorTy pvrtmp_7006 = tmp_struct_101.field2;
            CursorTy pvrtmp_7007 = tmp_struct_101.field3;
            
            *(TagTyPacked *) loc_2988 = 4;
            
            CursorTy writetag_4853 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7004, pvrtmp_7005,
                                                   loc_2988, pvrtmp_7007};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7016 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_7017 = tmpcur_6903 + 8;
            CursorTy tmpcur_7018 = *(CursorTy *) tmpaftercur_7017;
            CursorTy tmpaftercur_7019 = tmpaftercur_7017 + 8;
            CursorTy jump_4100 = tmpaftercur_7017 + 8;
            CursorTy jump_4099 = tmpcur_6903 + 8;
            CursorTy loc_3464 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_102 =
                                          _copy_without_ptrs_Tags(end_r_2989, end_r_2990, loc_3464, tmpaftercur_7019);
            CursorTy pvrtmp_7020 = tmp_struct_102.field0;
            CursorTy pvrtmp_7021 = tmp_struct_102.field1;
            CursorTy pvrtmp_7022 = tmp_struct_102.field2;
            CursorTy pvrtmp_7023 = tmp_struct_102.field3;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          _copy_without_ptrs_Adt(end_r_2989, pvrtmp_7020, pvrtmp_7023, tmpcur_7016);
            CursorTy pvrtmp_7028 = tmp_struct_103.field0;
            CursorTy pvrtmp_7029 = tmp_struct_103.field1;
            CursorTy pvrtmp_7030 = tmp_struct_103.field2;
            CursorTy pvrtmp_7031 = tmp_struct_103.field3;
            CursorCursorCursorCursorProd tmp_struct_104 =
                                          _copy_without_ptrs_Content(end_r_2989, pvrtmp_7028, pvrtmp_7031, tmpcur_7018);
            CursorTy pvrtmp_7036 = tmp_struct_104.field0;
            CursorTy pvrtmp_7037 = tmp_struct_104.field1;
            CursorTy pvrtmp_7038 = tmp_struct_104.field2;
            CursorTy pvrtmp_7039 = tmp_struct_104.field3;
            
            *(TagTyPacked *) loc_2988 = 5;
            
            CursorTy writetag_4864 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7036, pvrtmp_7037,
                                                   loc_2988, pvrtmp_7039};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7048 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_7049 = tmpcur_6903 + 8;
            CursorTy tmpcur_7050 = *(CursorTy *) tmpaftercur_7049;
            CursorTy tmpaftercur_7051 = tmpaftercur_7049 + 8;
            CursorTy jump_4106 = tmpaftercur_7049 + 8;
            CursorTy jump_4105 = tmpcur_6903 + 8;
            CursorTy loc_3484 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_105 =
                                          _copy_without_ptrs_Adt(end_r_2989, end_r_2990, loc_3484, tmpaftercur_7051);
            CursorTy pvrtmp_7052 = tmp_struct_105.field0;
            CursorTy pvrtmp_7053 = tmp_struct_105.field1;
            CursorTy pvrtmp_7054 = tmp_struct_105.field2;
            CursorTy pvrtmp_7055 = tmp_struct_105.field3;
            CursorCursorCursorCursorProd tmp_struct_106 =
                                          _copy_without_ptrs_Tags(end_r_2989, pvrtmp_7052, pvrtmp_7055, tmpcur_7048);
            CursorTy pvrtmp_7060 = tmp_struct_106.field0;
            CursorTy pvrtmp_7061 = tmp_struct_106.field1;
            CursorTy pvrtmp_7062 = tmp_struct_106.field2;
            CursorTy pvrtmp_7063 = tmp_struct_106.field3;
            CursorCursorCursorCursorProd tmp_struct_107 =
                                          _copy_without_ptrs_Content(end_r_2989, pvrtmp_7060, pvrtmp_7063, tmpcur_7050);
            CursorTy pvrtmp_7068 = tmp_struct_107.field0;
            CursorTy pvrtmp_7069 = tmp_struct_107.field1;
            CursorTy pvrtmp_7070 = tmp_struct_107.field2;
            CursorTy pvrtmp_7071 = tmp_struct_107.field3;
            
            *(TagTyPacked *) loc_2988 = 6;
            
            CursorTy writetag_4875 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7068, pvrtmp_7069,
                                                   loc_2988, pvrtmp_7071};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7080 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_7081 = tmpcur_6903 + 8;
            CursorTy tmpcur_7082 = *(CursorTy *) tmpaftercur_7081;
            CursorTy tmpaftercur_7083 = tmpaftercur_7081 + 8;
            CursorTy jump_4112 = tmpaftercur_7081 + 8;
            CursorTy jump_4111 = tmpcur_6903 + 8;
            CursorTy loc_3504 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_108 =
                                          _copy_without_ptrs_Content(end_r_2989, end_r_2990, loc_3504, tmpaftercur_7083);
            CursorTy pvrtmp_7084 = tmp_struct_108.field0;
            CursorTy pvrtmp_7085 = tmp_struct_108.field1;
            CursorTy pvrtmp_7086 = tmp_struct_108.field2;
            CursorTy pvrtmp_7087 = tmp_struct_108.field3;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          _copy_without_ptrs_Tags(end_r_2989, pvrtmp_7084, pvrtmp_7087, tmpcur_7080);
            CursorTy pvrtmp_7092 = tmp_struct_109.field0;
            CursorTy pvrtmp_7093 = tmp_struct_109.field1;
            CursorTy pvrtmp_7094 = tmp_struct_109.field2;
            CursorTy pvrtmp_7095 = tmp_struct_109.field3;
            CursorCursorCursorCursorProd tmp_struct_110 =
                                          _copy_without_ptrs_Adt(end_r_2989, pvrtmp_7092, pvrtmp_7095, tmpcur_7082);
            CursorTy pvrtmp_7100 = tmp_struct_110.field0;
            CursorTy pvrtmp_7101 = tmp_struct_110.field1;
            CursorTy pvrtmp_7102 = tmp_struct_110.field2;
            CursorTy pvrtmp_7103 = tmp_struct_110.field3;
            
            *(TagTyPacked *) loc_2988 = 7;
            
            CursorTy writetag_4886 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7100, pvrtmp_7101,
                                                   loc_2988, pvrtmp_7103};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7112 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_7113 = tmpcur_6903 + 8;
            CursorTy tmpcur_7114 = *(CursorTy *) tmpaftercur_7113;
            CursorTy tmpaftercur_7115 = tmpaftercur_7113 + 8;
            CursorTy jump_4118 = tmpaftercur_7113 + 8;
            CursorTy jump_4117 = tmpcur_6903 + 8;
            CursorTy loc_3524 = loc_2988 + 1;
            CursorCursorCursorCursorProd tmp_struct_111 =
                                          _copy_without_ptrs_Content(end_r_2989, end_r_2990, loc_3524, tmpaftercur_7115);
            CursorTy pvrtmp_7116 = tmp_struct_111.field0;
            CursorTy pvrtmp_7117 = tmp_struct_111.field1;
            CursorTy pvrtmp_7118 = tmp_struct_111.field2;
            CursorTy pvrtmp_7119 = tmp_struct_111.field3;
            CursorCursorCursorCursorProd tmp_struct_112 =
                                          _copy_without_ptrs_Adt(end_r_2989, pvrtmp_7116, pvrtmp_7119, tmpcur_7112);
            CursorTy pvrtmp_7124 = tmp_struct_112.field0;
            CursorTy pvrtmp_7125 = tmp_struct_112.field1;
            CursorTy pvrtmp_7126 = tmp_struct_112.field2;
            CursorTy pvrtmp_7127 = tmp_struct_112.field3;
            CursorCursorCursorCursorProd tmp_struct_113 =
                                          _copy_without_ptrs_Tags(end_r_2989, pvrtmp_7124, pvrtmp_7127, tmpcur_7114);
            CursorTy pvrtmp_7132 = tmp_struct_113.field0;
            CursorTy pvrtmp_7133 = tmp_struct_113.field1;
            CursorTy pvrtmp_7134 = tmp_struct_113.field2;
            CursorTy pvrtmp_7135 = tmp_struct_113.field3;
            
            *(TagTyPacked *) loc_2988 = 8;
            
            CursorTy writetag_4897 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7132, pvrtmp_7133,
                                                   loc_2988, pvrtmp_7135};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7144 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_7145 = tmpcur_6903 + 8;
            CursorTy jump_4354 = tmpcur_6903 + 8;
            CursorCursorCursorCursorProd tmp_struct_114 =
                                          _copy_without_ptrs_Adt(end_r_2989, end_r_2990, loc_2988, tmpcur_7144);
            CursorTy pvrtmp_7146 = tmp_struct_114.field0;
            CursorTy pvrtmp_7147 = tmp_struct_114.field1;
            CursorTy pvrtmp_7148 = tmp_struct_114.field2;
            CursorTy pvrtmp_7149 = tmp_struct_114.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7146, jump_4354,
                                                   pvrtmp_7148, pvrtmp_7149};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7156 = *(CursorTy *) tmpcur_6903;
            CursorTy tmpaftercur_7157 = tmpcur_6903 + 8;
            CursorCursorCursorCursorProd tmp_struct_115 =
                                          _copy_without_ptrs_Adt(end_r_2989, end_r_2990, loc_2988, tmpcur_7156);
            CursorTy pvrtmp_7158 = tmp_struct_115.field0;
            CursorTy pvrtmp_7159 = tmp_struct_115.field1;
            CursorTy pvrtmp_7160 = tmp_struct_115.field2;
            CursorTy pvrtmp_7161 = tmp_struct_115.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7158, pvrtmp_7159,
                                                   pvrtmp_7160, pvrtmp_7161};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6902");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2992, CursorTy arg_785_1397_1720)
{
    TagTyPacked tmpval_7169 = *(TagTyPacked *) arg_785_1397_1720;
    CursorTy tmpcur_7170 = arg_785_1397_1720 + 1;
    
    
  switch_7227:
    ;
    switch (tmpval_7169) {
        
      case 0:
        {
            CursorTy jump_4123 = arg_785_1397_1720 + 1;
            
            return (CursorProd) {jump_4123};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7171 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7172 = tmpcur_7170 + 8;
            CursorTy jump_4125 = tmpcur_7170 + 8;
            CursorProd tmp_struct_116 =
                        _traverse_Content(end_r_2992, tmpaftercur_7172);
            CursorTy pvrtmp_7173 = tmp_struct_116.field0;
            CursorProd tmp_struct_117 =  _traverse_Adt(end_r_2992, tmpcur_7171);
            CursorTy pvrtmp_7174 = tmp_struct_117.field0;
            
            return (CursorProd) {pvrtmp_7174};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7175 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7176 = tmpcur_7170 + 8;
            CursorTy jump_4129 = tmpcur_7170 + 8;
            CursorProd tmp_struct_118 =
                        _traverse_Adt(end_r_2992, tmpaftercur_7176);
            CursorTy pvrtmp_7177 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Content(end_r_2992, tmpcur_7175);
            CursorTy pvrtmp_7178 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_7178};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7179 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7180 = tmpcur_7170 + 8;
            CursorTy tmpcur_7181 = *(CursorTy *) tmpaftercur_7180;
            CursorTy tmpaftercur_7182 = tmpaftercur_7180 + 8;
            CursorTy jump_4134 = tmpaftercur_7180 + 8;
            CursorTy jump_4133 = tmpcur_7170 + 8;
            CursorProd tmp_struct_120 =
                        _traverse_Tags(end_r_2992, tmpaftercur_7182);
            CursorTy pvrtmp_7183 = tmp_struct_120.field0;
            CursorProd tmp_struct_121 =
                        _traverse_Content(end_r_2992, tmpcur_7179);
            CursorTy pvrtmp_7184 = tmp_struct_121.field0;
            CursorProd tmp_struct_122 =  _traverse_Adt(end_r_2992, tmpcur_7181);
            CursorTy pvrtmp_7185 = tmp_struct_122.field0;
            
            return (CursorProd) {pvrtmp_7185};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7186 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7187 = tmpcur_7170 + 8;
            CursorTy tmpcur_7188 = *(CursorTy *) tmpaftercur_7187;
            CursorTy tmpaftercur_7189 = tmpaftercur_7187 + 8;
            CursorTy jump_4140 = tmpaftercur_7187 + 8;
            CursorTy jump_4139 = tmpcur_7170 + 8;
            CursorProd tmp_struct_123 =
                        _traverse_Adt(end_r_2992, tmpaftercur_7189);
            CursorTy pvrtmp_7190 = tmp_struct_123.field0;
            CursorProd tmp_struct_124 =
                        _traverse_Content(end_r_2992, tmpcur_7186);
            CursorTy pvrtmp_7191 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _traverse_Tags(end_r_2992, tmpcur_7188);
            CursorTy pvrtmp_7192 = tmp_struct_125.field0;
            
            return (CursorProd) {pvrtmp_7192};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7193 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7194 = tmpcur_7170 + 8;
            CursorTy tmpcur_7195 = *(CursorTy *) tmpaftercur_7194;
            CursorTy tmpaftercur_7196 = tmpaftercur_7194 + 8;
            CursorTy jump_4146 = tmpaftercur_7194 + 8;
            CursorTy jump_4145 = tmpcur_7170 + 8;
            CursorProd tmp_struct_126 =
                        _traverse_Tags(end_r_2992, tmpaftercur_7196);
            CursorTy pvrtmp_7197 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =  _traverse_Adt(end_r_2992, tmpcur_7193);
            CursorTy pvrtmp_7198 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =
                        _traverse_Content(end_r_2992, tmpcur_7195);
            CursorTy pvrtmp_7199 = tmp_struct_128.field0;
            
            return (CursorProd) {pvrtmp_7199};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7200 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7201 = tmpcur_7170 + 8;
            CursorTy tmpcur_7202 = *(CursorTy *) tmpaftercur_7201;
            CursorTy tmpaftercur_7203 = tmpaftercur_7201 + 8;
            CursorTy jump_4152 = tmpaftercur_7201 + 8;
            CursorTy jump_4151 = tmpcur_7170 + 8;
            CursorProd tmp_struct_129 =
                        _traverse_Adt(end_r_2992, tmpaftercur_7203);
            CursorTy pvrtmp_7204 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _traverse_Tags(end_r_2992, tmpcur_7200);
            CursorTy pvrtmp_7205 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =
                        _traverse_Content(end_r_2992, tmpcur_7202);
            CursorTy pvrtmp_7206 = tmp_struct_131.field0;
            
            return (CursorProd) {pvrtmp_7206};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7207 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7208 = tmpcur_7170 + 8;
            CursorTy tmpcur_7209 = *(CursorTy *) tmpaftercur_7208;
            CursorTy tmpaftercur_7210 = tmpaftercur_7208 + 8;
            CursorTy jump_4158 = tmpaftercur_7208 + 8;
            CursorTy jump_4157 = tmpcur_7170 + 8;
            CursorProd tmp_struct_132 =
                        _traverse_Content(end_r_2992, tmpaftercur_7210);
            CursorTy pvrtmp_7211 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =
                        _traverse_Tags(end_r_2992, tmpcur_7207);
            CursorTy pvrtmp_7212 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =  _traverse_Adt(end_r_2992, tmpcur_7209);
            CursorTy pvrtmp_7213 = tmp_struct_134.field0;
            
            return (CursorProd) {pvrtmp_7213};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7214 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7215 = tmpcur_7170 + 8;
            CursorTy tmpcur_7216 = *(CursorTy *) tmpaftercur_7215;
            CursorTy tmpaftercur_7217 = tmpaftercur_7215 + 8;
            CursorTy jump_4164 = tmpaftercur_7215 + 8;
            CursorTy jump_4163 = tmpcur_7170 + 8;
            CursorProd tmp_struct_135 =
                        _traverse_Content(end_r_2992, tmpaftercur_7217);
            CursorTy pvrtmp_7218 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _traverse_Adt(end_r_2992, tmpcur_7214);
            CursorTy pvrtmp_7219 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _traverse_Tags(end_r_2992, tmpcur_7216);
            CursorTy pvrtmp_7220 = tmp_struct_137.field0;
            
            return (CursorProd) {pvrtmp_7220};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7221 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7222 = tmpcur_7170 + 8;
            CursorTy jump_4360 = tmpcur_7170 + 8;
            CursorProd tmp_struct_138 =  _traverse_Adt(end_r_2992, tmpcur_7221);
            CursorTy pvrtmp_7223 = tmp_struct_138.field0;
            
            return (CursorProd) {jump_4360};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7224 = *(CursorTy *) tmpcur_7170;
            CursorTy tmpaftercur_7225 = tmpcur_7170 + 8;
            CursorProd tmp_struct_139 =  _traverse_Adt(end_r_2992, tmpcur_7224);
            CursorTy pvrtmp_7226 = tmp_struct_139.field0;
            
            return (CursorProd) {pvrtmp_7226};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7169");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2994, CursorTy arg_830_1442_1765)
{
    TagTyPacked tmpval_7228 = *(TagTyPacked *) arg_830_1442_1765;
    CursorTy tmpcur_7229 = arg_830_1442_1765 + 1;
    
    
  switch_7286:
    ;
    switch (tmpval_7228) {
        
      case 0:
        {
            CursorTy jump_4169 = arg_830_1442_1765 + 1;
            unsigned char wildcard_831_1443_1766 = print_symbol(6182);
            unsigned char wildcard_832_1444_1767 = print_symbol(6176);
            
            return (CursorProd) {jump_4169};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7230 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7231 = tmpcur_7229 + 8;
            CursorTy jump_4171 = tmpcur_7229 + 8;
            unsigned char wildcard_837_1447_1770 = print_symbol(6188);
            CursorProd tmp_struct_140 =
                        _print_Content(end_r_2994, tmpaftercur_7231);
            CursorTy pvrtmp_7232 = tmp_struct_140.field0;
            CursorProd tmp_struct_141 =  _print_Adt(end_r_2994, tmpcur_7230);
            CursorTy pvrtmp_7233 = tmp_struct_141.field0;
            unsigned char wildcard_838_1450_1773 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7233};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7234 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7235 = tmpcur_7229 + 8;
            CursorTy jump_4175 = tmpcur_7229 + 8;
            unsigned char wildcard_843_1453_1776 = print_symbol(6191);
            CursorProd tmp_struct_142 =
                        _print_Adt(end_r_2994, tmpaftercur_7235);
            CursorTy pvrtmp_7236 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =
                        _print_Content(end_r_2994, tmpcur_7234);
            CursorTy pvrtmp_7237 = tmp_struct_143.field0;
            unsigned char wildcard_844_1456_1779 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7237};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7238 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7239 = tmpcur_7229 + 8;
            CursorTy tmpcur_7240 = *(CursorTy *) tmpaftercur_7239;
            CursorTy tmpaftercur_7241 = tmpaftercur_7239 + 8;
            CursorTy jump_4180 = tmpaftercur_7239 + 8;
            CursorTy jump_4179 = tmpcur_7229 + 8;
            unsigned char wildcard_851_1460_1783 = print_symbol(6179);
            CursorProd tmp_struct_144 =
                        _print_Tags(end_r_2994, tmpaftercur_7241);
            CursorTy pvrtmp_7242 = tmp_struct_144.field0;
            CursorProd tmp_struct_145 =
                        _print_Content(end_r_2994, tmpcur_7238);
            CursorTy pvrtmp_7243 = tmp_struct_145.field0;
            CursorProd tmp_struct_146 =  _print_Adt(end_r_2994, tmpcur_7240);
            CursorTy pvrtmp_7244 = tmp_struct_146.field0;
            unsigned char wildcard_852_1464_1787 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7244};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7245 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7246 = tmpcur_7229 + 8;
            CursorTy tmpcur_7247 = *(CursorTy *) tmpaftercur_7246;
            CursorTy tmpaftercur_7248 = tmpaftercur_7246 + 8;
            CursorTy jump_4186 = tmpaftercur_7246 + 8;
            CursorTy jump_4185 = tmpcur_7229 + 8;
            unsigned char wildcard_859_1468_1791 = print_symbol(6190);
            CursorProd tmp_struct_147 =
                        _print_Adt(end_r_2994, tmpaftercur_7248);
            CursorTy pvrtmp_7249 = tmp_struct_147.field0;
            CursorProd tmp_struct_148 =
                        _print_Content(end_r_2994, tmpcur_7245);
            CursorTy pvrtmp_7250 = tmp_struct_148.field0;
            CursorProd tmp_struct_149 =  _print_Tags(end_r_2994, tmpcur_7247);
            CursorTy pvrtmp_7251 = tmp_struct_149.field0;
            unsigned char wildcard_860_1472_1795 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7251};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7252 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7253 = tmpcur_7229 + 8;
            CursorTy tmpcur_7254 = *(CursorTy *) tmpaftercur_7253;
            CursorTy tmpaftercur_7255 = tmpaftercur_7253 + 8;
            CursorTy jump_4192 = tmpaftercur_7253 + 8;
            CursorTy jump_4191 = tmpcur_7229 + 8;
            unsigned char wildcard_867_1476_1799 = print_symbol(6180);
            CursorProd tmp_struct_150 =
                        _print_Tags(end_r_2994, tmpaftercur_7255);
            CursorTy pvrtmp_7256 = tmp_struct_150.field0;
            CursorProd tmp_struct_151 =  _print_Adt(end_r_2994, tmpcur_7252);
            CursorTy pvrtmp_7257 = tmp_struct_151.field0;
            CursorProd tmp_struct_152 =
                        _print_Content(end_r_2994, tmpcur_7254);
            CursorTy pvrtmp_7258 = tmp_struct_152.field0;
            unsigned char wildcard_868_1480_1803 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7258};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7259 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7260 = tmpcur_7229 + 8;
            CursorTy tmpcur_7261 = *(CursorTy *) tmpaftercur_7260;
            CursorTy tmpaftercur_7262 = tmpaftercur_7260 + 8;
            CursorTy jump_4198 = tmpaftercur_7260 + 8;
            CursorTy jump_4197 = tmpcur_7229 + 8;
            unsigned char wildcard_875_1484_1807 = print_symbol(6189);
            CursorProd tmp_struct_153 =
                        _print_Adt(end_r_2994, tmpaftercur_7262);
            CursorTy pvrtmp_7263 = tmp_struct_153.field0;
            CursorProd tmp_struct_154 =  _print_Tags(end_r_2994, tmpcur_7259);
            CursorTy pvrtmp_7264 = tmp_struct_154.field0;
            CursorProd tmp_struct_155 =
                        _print_Content(end_r_2994, tmpcur_7261);
            CursorTy pvrtmp_7265 = tmp_struct_155.field0;
            unsigned char wildcard_876_1488_1811 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7265};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7266 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7267 = tmpcur_7229 + 8;
            CursorTy tmpcur_7268 = *(CursorTy *) tmpaftercur_7267;
            CursorTy tmpaftercur_7269 = tmpaftercur_7267 + 8;
            CursorTy jump_4204 = tmpaftercur_7267 + 8;
            CursorTy jump_4203 = tmpcur_7229 + 8;
            unsigned char wildcard_883_1492_1815 = print_symbol(6186);
            CursorProd tmp_struct_156 =
                        _print_Content(end_r_2994, tmpaftercur_7269);
            CursorTy pvrtmp_7270 = tmp_struct_156.field0;
            CursorProd tmp_struct_157 =  _print_Tags(end_r_2994, tmpcur_7266);
            CursorTy pvrtmp_7271 = tmp_struct_157.field0;
            CursorProd tmp_struct_158 =  _print_Adt(end_r_2994, tmpcur_7268);
            CursorTy pvrtmp_7272 = tmp_struct_158.field0;
            unsigned char wildcard_884_1496_1819 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7272};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7273 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7274 = tmpcur_7229 + 8;
            CursorTy tmpcur_7275 = *(CursorTy *) tmpaftercur_7274;
            CursorTy tmpaftercur_7276 = tmpaftercur_7274 + 8;
            CursorTy jump_4210 = tmpaftercur_7274 + 8;
            CursorTy jump_4209 = tmpcur_7229 + 8;
            unsigned char wildcard_891_1500_1823 = print_symbol(6187);
            CursorProd tmp_struct_159 =
                        _print_Content(end_r_2994, tmpaftercur_7276);
            CursorTy pvrtmp_7277 = tmp_struct_159.field0;
            CursorProd tmp_struct_160 =  _print_Adt(end_r_2994, tmpcur_7273);
            CursorTy pvrtmp_7278 = tmp_struct_160.field0;
            CursorProd tmp_struct_161 =  _print_Tags(end_r_2994, tmpcur_7275);
            CursorTy pvrtmp_7279 = tmp_struct_161.field0;
            unsigned char wildcard_892_1504_1827 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7279};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7280 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7281 = tmpcur_7229 + 8;
            CursorTy jump_4366 = tmpcur_7229 + 8;
            unsigned char wildcard_4369 = print_symbol(6193);
            CursorProd tmp_struct_162 =  _print_Adt(end_r_2994, tmpcur_7280);
            CursorTy pvrtmp_7282 = tmp_struct_162.field0;
            
            return (CursorProd) {jump_4366};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7283 = *(CursorTy *) tmpcur_7229;
            CursorTy tmpaftercur_7284 = tmpcur_7229 + 8;
            unsigned char wildcard_4369 = print_symbol(6192);
            CursorProd tmp_struct_163 =  _print_Adt(end_r_2994, tmpcur_7283);
            CursorTy pvrtmp_7285 = tmp_struct_163.field0;
            
            return (CursorProd) {pvrtmp_7285};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7228");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2997,
                                        CursorTy end_r_2998, CursorTy loc_2996,
                                        CursorTy arg_893_1505_1828)
{
    if (loc_2996 + 32 > end_r_2998) {
        ChunkTy new_chunk_167 = alloc_chunk(end_r_2998);
        CursorTy chunk_start_168 = new_chunk_167.chunk_start;
        CursorTy chunk_end_169 = new_chunk_167.chunk_end;
        
        end_r_2998 = chunk_end_169;
        *(TagTyPacked *) loc_2996 = 255;
        
        CursorTy redir = loc_2996 + 1;
        
        *(CursorTy *) redir = chunk_start_168;
        loc_2996 = chunk_start_168;
    }
    
    CursorTy loc_3702 = loc_2996 + 1;
    CursorTy loc_3703 = loc_3702 + 8;
    TagTyPacked tmpval_7287 = *(TagTyPacked *) arg_893_1505_1828;
    CursorTy tmpcur_7288 = arg_893_1505_1828 + 1;
    
    
  switch_7331:
    ;
    switch (tmpval_7287) {
        
      case 0:
        {
            CursorTy jump_4215 = arg_893_1505_1828 + 1;
            
            *(TagTyPacked *) loc_2996 = 0;
            
            CursorTy writetag_5011 = loc_2996 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2998, jump_4215,
                                                   loc_2996, writetag_5011};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7293 = *(IntTy *) tmpcur_7288;
            CursorTy tmpcur_7294 = tmpcur_7288 + sizeof(IntTy);
            CursorTy jump_4217 = tmpcur_7288 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          _copy_Tags(end_r_2997, end_r_2998, loc_3703, tmpcur_7294);
            CursorTy pvrtmp_7295 = tmp_struct_164.field0;
            CursorTy pvrtmp_7296 = tmp_struct_164.field1;
            CursorTy pvrtmp_7297 = tmp_struct_164.field2;
            CursorTy pvrtmp_7298 = tmp_struct_164.field3;
            
            *(TagTyPacked *) loc_2996 = 1;
            
            CursorTy writetag_5016 = loc_2996 + 1;
            
            *(IntTy *) writetag_5016 = tmpval_7293;
            
            CursorTy writecur_5017 = writetag_5016 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7295, pvrtmp_7296,
                                                   loc_2996, pvrtmp_7298};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7307 = *(CursorTy *) tmpcur_7288;
            CursorTy tmpaftercur_7308 = tmpcur_7288 + 8;
            CursorTy jump_4372 = tmpcur_7288 + 8;
            CursorCursorCursorCursorProd tmp_struct_165 =
                                          _copy_Tags(end_r_2997, end_r_2998, loc_2996, tmpcur_7307);
            CursorTy pvrtmp_7309 = tmp_struct_165.field0;
            CursorTy pvrtmp_7310 = tmp_struct_165.field1;
            CursorTy pvrtmp_7311 = tmp_struct_165.field2;
            CursorTy pvrtmp_7312 = tmp_struct_165.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7309, jump_4372,
                                                   pvrtmp_7311, pvrtmp_7312};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7319 = *(CursorTy *) tmpcur_7288;
            CursorTy tmpaftercur_7320 = tmpcur_7288 + 8;
            CursorCursorCursorCursorProd tmp_struct_166 =
                                          _copy_Tags(end_r_2997, end_r_2998, loc_2996, tmpcur_7319);
            CursorTy pvrtmp_7321 = tmp_struct_166.field0;
            CursorTy pvrtmp_7322 = tmp_struct_166.field1;
            CursorTy pvrtmp_7323 = tmp_struct_166.field2;
            CursorTy pvrtmp_7324 = tmp_struct_166.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7321, pvrtmp_7322,
                                                   pvrtmp_7323, pvrtmp_7324};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7287");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_3001,
                                                     CursorTy end_r_3002,
                                                     CursorTy loc_3000,
                                                     CursorTy arg_898_1510_1833)
{
    CursorTy loc_3715 = loc_3000 + 1;
    CursorTy loc_3716 = loc_3715 + 8;
    TagTyPacked tmpval_7332 = *(TagTyPacked *) arg_898_1510_1833;
    CursorTy tmpcur_7333 = arg_898_1510_1833 + 1;
    
    
  switch_7376:
    ;
    switch (tmpval_7332) {
        
      case 0:
        {
            CursorTy jump_4220 = arg_898_1510_1833 + 1;
            
            *(TagTyPacked *) loc_3000 = 0;
            
            CursorTy writetag_5027 = loc_3000 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3002, jump_4220,
                                                   loc_3000, writetag_5027};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7338 = *(IntTy *) tmpcur_7333;
            CursorTy tmpcur_7339 = tmpcur_7333 + sizeof(IntTy);
            CursorTy jump_4222 = tmpcur_7333 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _copy_without_ptrs_Tags(end_r_3001, end_r_3002, loc_3716, tmpcur_7339);
            CursorTy pvrtmp_7340 = tmp_struct_170.field0;
            CursorTy pvrtmp_7341 = tmp_struct_170.field1;
            CursorTy pvrtmp_7342 = tmp_struct_170.field2;
            CursorTy pvrtmp_7343 = tmp_struct_170.field3;
            
            *(TagTyPacked *) loc_3000 = 1;
            
            CursorTy writetag_5032 = loc_3000 + 1;
            
            *(IntTy *) writetag_5032 = tmpval_7338;
            
            CursorTy writecur_5033 = writetag_5032 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7340, pvrtmp_7341,
                                                   loc_3000, pvrtmp_7343};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7352 = *(CursorTy *) tmpcur_7333;
            CursorTy tmpaftercur_7353 = tmpcur_7333 + 8;
            CursorTy jump_4378 = tmpcur_7333 + 8;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          _copy_without_ptrs_Tags(end_r_3001, end_r_3002, loc_3000, tmpcur_7352);
            CursorTy pvrtmp_7354 = tmp_struct_171.field0;
            CursorTy pvrtmp_7355 = tmp_struct_171.field1;
            CursorTy pvrtmp_7356 = tmp_struct_171.field2;
            CursorTy pvrtmp_7357 = tmp_struct_171.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7354, jump_4378,
                                                   pvrtmp_7356, pvrtmp_7357};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7364 = *(CursorTy *) tmpcur_7333;
            CursorTy tmpaftercur_7365 = tmpcur_7333 + 8;
            CursorCursorCursorCursorProd tmp_struct_172 =
                                          _copy_without_ptrs_Tags(end_r_3001, end_r_3002, loc_3000, tmpcur_7364);
            CursorTy pvrtmp_7366 = tmp_struct_172.field0;
            CursorTy pvrtmp_7367 = tmp_struct_172.field1;
            CursorTy pvrtmp_7368 = tmp_struct_172.field2;
            CursorTy pvrtmp_7369 = tmp_struct_172.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7366, pvrtmp_7367,
                                                   pvrtmp_7368, pvrtmp_7369};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7332");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_3004, CursorTy arg_903_1515_1838)
{
    TagTyPacked tmpval_7377 = *(TagTyPacked *) arg_903_1515_1838;
    CursorTy tmpcur_7378 = arg_903_1515_1838 + 1;
    
    
  switch_7388:
    ;
    switch (tmpval_7377) {
        
      case 0:
        {
            CursorTy jump_4225 = arg_903_1515_1838 + 1;
            
            return (CursorProd) {jump_4225};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7379 = *(IntTy *) tmpcur_7378;
            CursorTy tmpcur_7380 = tmpcur_7378 + sizeof(IntTy);
            CursorTy jump_4227 = tmpcur_7378 + 8;
            CursorProd tmp_struct_173 =
                        _traverse_Tags(end_r_3004, tmpcur_7380);
            CursorTy pvrtmp_7381 = tmp_struct_173.field0;
            
            return (CursorProd) {pvrtmp_7381};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7382 = *(CursorTy *) tmpcur_7378;
            CursorTy tmpaftercur_7383 = tmpcur_7378 + 8;
            CursorTy jump_4384 = tmpcur_7378 + 8;
            CursorProd tmp_struct_174 =
                        _traverse_Tags(end_r_3004, tmpcur_7382);
            CursorTy pvrtmp_7384 = tmp_struct_174.field0;
            
            return (CursorProd) {jump_4384};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7385 = *(CursorTy *) tmpcur_7378;
            CursorTy tmpaftercur_7386 = tmpcur_7378 + 8;
            CursorProd tmp_struct_175 =
                        _traverse_Tags(end_r_3004, tmpcur_7385);
            CursorTy pvrtmp_7387 = tmp_struct_175.field0;
            
            return (CursorProd) {pvrtmp_7387};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7377");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_3006, CursorTy arg_908_1519_1842)
{
    TagTyPacked tmpval_7389 = *(TagTyPacked *) arg_908_1519_1842;
    CursorTy tmpcur_7390 = arg_908_1519_1842 + 1;
    
    
  switch_7400:
    ;
    switch (tmpval_7389) {
        
      case 0:
        {
            CursorTy jump_4230 = arg_908_1519_1842 + 1;
            unsigned char wildcard_909_1520_1843 = print_symbol(6181);
            unsigned char wildcard_910_1521_1844 = print_symbol(6176);
            
            return (CursorProd) {jump_4230};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7391 = *(IntTy *) tmpcur_7390;
            CursorTy tmpcur_7392 = tmpcur_7390 + sizeof(IntTy);
            CursorTy jump_4232 = tmpcur_7390 + 8;
            unsigned char wildcard_915_1524_1847 = print_symbol(6178);
            unsigned char y_913_1525_1848 = printf("%lld", tmpval_7391);
            CursorProd tmp_struct_176 =  _print_Tags(end_r_3006, tmpcur_7392);
            CursorTy pvrtmp_7393 = tmp_struct_176.field0;
            unsigned char wildcard_916_1527_1850 = print_symbol(6176);
            
            return (CursorProd) {pvrtmp_7393};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7394 = *(CursorTy *) tmpcur_7390;
            CursorTy tmpaftercur_7395 = tmpcur_7390 + 8;
            CursorTy jump_4390 = tmpcur_7390 + 8;
            unsigned char wildcard_4393 = print_symbol(6193);
            CursorProd tmp_struct_177 =  _print_Tags(end_r_3006, tmpcur_7394);
            CursorTy pvrtmp_7396 = tmp_struct_177.field0;
            
            return (CursorProd) {jump_4390};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7397 = *(CursorTy *) tmpcur_7390;
            CursorTy tmpaftercur_7398 = tmpcur_7390 + 8;
            unsigned char wildcard_4393 = print_symbol(6192);
            CursorProd tmp_struct_178 =  _print_Tags(end_r_3006, tmpcur_7397);
            CursorTy pvrtmp_7399 = tmp_struct_178.field0;
            
            return (CursorProd) {pvrtmp_7399};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7389");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_3009,
                                                              CursorTy end_r_3010,
                                                              CursorTy loc_3008,
                                                              CursorTy arg_2741)
{
    if (loc_3008 + 32 > end_r_3010) {
        ChunkTy new_chunk_182 = alloc_chunk(end_r_3010);
        CursorTy chunk_start_183 = new_chunk_182.chunk_start;
        CursorTy chunk_end_184 = new_chunk_182.chunk_end;
        
        end_r_3010 = chunk_end_184;
        *(TagTyPacked *) loc_3008 = 255;
        
        CursorTy redir = loc_3008 + 1;
        
        *(CursorTy *) redir = chunk_start_183;
        loc_3008 = chunk_start_183;
    }
    
    CursorTy loc_3740 = loc_3008 + 1;
    CursorTy loc_3741 = loc_3740 + 8;
    TagTyPacked tmpval_7401 = *(TagTyPacked *) arg_2741;
    CursorTy tmpcur_7402 = arg_2741 + 1;
    
    
  switch_7445:
    ;
    switch (tmpval_7401) {
        
      case 0:
        {
            CursorTy jump_4235 = arg_2741 + 1;
            
            *(TagTyPacked *) loc_3008 = 0;
            
            CursorTy writetag_5063 = loc_3008 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3010, jump_4235,
                                                   loc_3008, writetag_5063};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7407 = *(IntTy *) tmpcur_7402;
            CursorTy tmpcur_7408 = tmpcur_7402 + sizeof(IntTy);
            CursorTy jump_4237 = tmpcur_7402 + 8;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_String(end_r_3009, end_r_3010, loc_3741, tmpcur_7408);
            CursorTy pvrtmp_7409 = tmp_struct_179.field0;
            CursorTy pvrtmp_7410 = tmp_struct_179.field1;
            CursorTy pvrtmp_7411 = tmp_struct_179.field2;
            CursorTy pvrtmp_7412 = tmp_struct_179.field3;
            
            *(TagTyPacked *) loc_3008 = 1;
            
            CursorTy writetag_5068 = loc_3008 + 1;
            
            *(IntTy *) writetag_5068 = tmpval_7407;
            
            CursorTy writecur_5069 = writetag_5068 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7409, pvrtmp_7410,
                                                   loc_3008, pvrtmp_7412};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7421 = *(CursorTy *) tmpcur_7402;
            CursorTy tmpaftercur_7422 = tmpcur_7402 + 8;
            CursorTy jump_4396 = tmpcur_7402 + 8;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_String(end_r_3009, end_r_3010, loc_3008, tmpcur_7421);
            CursorTy pvrtmp_7423 = tmp_struct_180.field0;
            CursorTy pvrtmp_7424 = tmp_struct_180.field1;
            CursorTy pvrtmp_7425 = tmp_struct_180.field2;
            CursorTy pvrtmp_7426 = tmp_struct_180.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7423, jump_4396,
                                                   pvrtmp_7425, pvrtmp_7426};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7433 = *(CursorTy *) tmpcur_7402;
            CursorTy tmpaftercur_7434 = tmpcur_7402 + 8;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_String(end_r_3009, end_r_3010, loc_3008, tmpcur_7433);
            CursorTy pvrtmp_7435 = tmp_struct_181.field0;
            CursorTy pvrtmp_7436 = tmp_struct_181.field1;
            CursorTy pvrtmp_7437 = tmp_struct_181.field2;
            CursorTy pvrtmp_7438 = tmp_struct_181.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7435, pvrtmp_7436,
                                                   pvrtmp_7437, pvrtmp_7438};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7401");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_3013,
                                                               CursorTy end_r_3014,
                                                               CursorTy loc_3012,
                                                               CursorTy arg_2746)
{
    if (loc_3012 + 32 > end_r_3014) {
        ChunkTy new_chunk_189 = alloc_chunk(end_r_3014);
        CursorTy chunk_start_190 = new_chunk_189.chunk_start;
        CursorTy chunk_end_191 = new_chunk_189.chunk_end;
        
        end_r_3014 = chunk_end_191;
        *(TagTyPacked *) loc_3012 = 255;
        
        CursorTy redir = loc_3012 + 1;
        
        *(CursorTy *) redir = chunk_start_190;
        loc_3012 = chunk_start_190;
    }
    
    TagTyPacked tmpval_7446 = *(TagTyPacked *) arg_2746;
    CursorTy tmpcur_7447 = arg_2746 + 1;
    
    
  switch_7496:
    ;
    switch (tmpval_7446) {
        
      case 0:
        {
            CursorTy loc_3751 = loc_3012 + 1;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_String(end_r_3013, end_r_3014, loc_3751, tmpcur_7447);
            CursorTy pvrtmp_7448 = tmp_struct_185.field0;
            CursorTy pvrtmp_7449 = tmp_struct_185.field1;
            CursorTy pvrtmp_7450 = tmp_struct_185.field2;
            CursorTy pvrtmp_7451 = tmp_struct_185.field3;
            
            *(TagTyPacked *) loc_3012 = 0;
            
            CursorTy writetag_5080 = loc_3012 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7448, pvrtmp_7449,
                                                   loc_3012, pvrtmp_7451};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3757 = loc_3012 + 1;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_String(end_r_3013, end_r_3014, loc_3757, tmpcur_7447);
            CursorTy pvrtmp_7460 = tmp_struct_186.field0;
            CursorTy pvrtmp_7461 = tmp_struct_186.field1;
            CursorTy pvrtmp_7462 = tmp_struct_186.field2;
            CursorTy pvrtmp_7463 = tmp_struct_186.field3;
            
            *(TagTyPacked *) loc_3012 = 1;
            
            CursorTy writetag_5085 = loc_3012 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7460, pvrtmp_7461,
                                                   loc_3012, pvrtmp_7463};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7472 = *(CursorTy *) tmpcur_7447;
            CursorTy tmpaftercur_7473 = tmpcur_7447 + 8;
            CursorTy jump_4402 = tmpcur_7447 + 8;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Content(end_r_3013, end_r_3014, loc_3012, tmpcur_7472);
            CursorTy pvrtmp_7474 = tmp_struct_187.field0;
            CursorTy pvrtmp_7475 = tmp_struct_187.field1;
            CursorTy pvrtmp_7476 = tmp_struct_187.field2;
            CursorTy pvrtmp_7477 = tmp_struct_187.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7474, jump_4402,
                                                   pvrtmp_7476, pvrtmp_7477};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7484 = *(CursorTy *) tmpcur_7447;
            CursorTy tmpaftercur_7485 = tmpcur_7447 + 8;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Content(end_r_3013, end_r_3014, loc_3012, tmpcur_7484);
            CursorTy pvrtmp_7486 = tmp_struct_188.field0;
            CursorTy pvrtmp_7487 = tmp_struct_188.field1;
            CursorTy pvrtmp_7488 = tmp_struct_188.field2;
            CursorTy pvrtmp_7489 = tmp_struct_188.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7486, pvrtmp_7487,
                                                   pvrtmp_7488, pvrtmp_7489};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7446");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_3017,
                                                           CursorTy end_r_3018,
                                                           CursorTy loc_3016,
                                                           CursorTy arg_2751)
{
    if (loc_3016 + 32 > end_r_3018) {
        ChunkTy new_chunk_216 = alloc_chunk(end_r_3018);
        CursorTy chunk_start_217 = new_chunk_216.chunk_start;
        CursorTy chunk_end_218 = new_chunk_216.chunk_end;
        
        end_r_3018 = chunk_end_218;
        *(TagTyPacked *) loc_3016 = 255;
        
        CursorTy redir = loc_3016 + 1;
        
        *(CursorTy *) redir = chunk_start_217;
        loc_3016 = chunk_start_217;
    }
    
    CursorTy loc_3770 = loc_3016 + 1;
    CursorTy loc_3771 = loc_3770 + 8;
    CursorTy loc_3772 = loc_3771 + 8;
    CursorTy loc_3788 = loc_3016 + 1;
    CursorTy loc_3789 = loc_3788 + 8;
    CursorTy loc_3790 = loc_3789 + 8;
    CursorTy loc_3810 = loc_3016 + 1;
    CursorTy loc_3811 = loc_3810 + 8;
    CursorTy loc_3812 = loc_3811 + 8;
    CursorTy loc_3813 = loc_3812 + 8;
    CursorTy loc_3837 = loc_3016 + 1;
    CursorTy loc_3838 = loc_3837 + 8;
    CursorTy loc_3839 = loc_3838 + 8;
    CursorTy loc_3840 = loc_3839 + 8;
    CursorTy loc_3864 = loc_3016 + 1;
    CursorTy loc_3865 = loc_3864 + 8;
    CursorTy loc_3866 = loc_3865 + 8;
    CursorTy loc_3867 = loc_3866 + 8;
    CursorTy loc_3891 = loc_3016 + 1;
    CursorTy loc_3892 = loc_3891 + 8;
    CursorTy loc_3893 = loc_3892 + 8;
    CursorTy loc_3894 = loc_3893 + 8;
    CursorTy loc_3918 = loc_3016 + 1;
    CursorTy loc_3919 = loc_3918 + 8;
    CursorTy loc_3920 = loc_3919 + 8;
    CursorTy loc_3921 = loc_3920 + 8;
    CursorTy loc_3945 = loc_3016 + 1;
    CursorTy loc_3946 = loc_3945 + 8;
    CursorTy loc_3947 = loc_3946 + 8;
    CursorTy loc_3948 = loc_3947 + 8;
    TagTyPacked tmpval_7497 = *(TagTyPacked *) arg_2751;
    CursorTy tmpcur_7498 = arg_2751 + 1;
    
    
  switch_7735:
    ;
    switch (tmpval_7497) {
        
      case 0:
        {
            CursorTy jump_4244 = arg_2751 + 1;
            
            *(TagTyPacked *) loc_3016 = 0;
            
            CursorTy writetag_5095 = loc_3016 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3018, jump_4244,
                                                   loc_3016, writetag_5095};
            break;
        }
        
      case 1:
        {
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, end_r_3018, loc_3772, tmpcur_7498);
            CursorTy pvrtmp_7503 = tmp_struct_192.field0;
            CursorTy pvrtmp_7504 = tmp_struct_192.field1;
            CursorTy pvrtmp_7505 = tmp_struct_192.field2;
            CursorTy pvrtmp_7506 = tmp_struct_192.field3;
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, pvrtmp_7503, pvrtmp_7506, pvrtmp_7504);
            CursorTy pvrtmp_7511 = tmp_struct_193.field0;
            CursorTy pvrtmp_7512 = tmp_struct_193.field1;
            CursorTy pvrtmp_7513 = tmp_struct_193.field2;
            CursorTy pvrtmp_7514 = tmp_struct_193.field3;
            IntTy sizeof_y_2754__2756 = pvrtmp_7506 - pvrtmp_7505;
            IntTy sizeof_y_2755__2757 = pvrtmp_7514 - pvrtmp_7513;
            IntTy fltPrm_2845 = sizeof_y_2754__2756 + 0;
            IntTy offset__2758 = 0 + fltPrm_2845;
            IntTy fltPrm_2846 = sizeof_y_2754__2756 + sizeof_y_2755__2757;
            IntTy size_dcon_2759 = 9 + fltPrm_2846;
            
            *(TagTyPacked *) loc_3016 = 160;
            
            CursorTy writetag_5100 = loc_3016 + 1;
            
            *(IntTy *) writetag_5100 = size_dcon_2759;
            
            CursorTy writecur_5101 = writetag_5100 + sizeof(IntTy);
            
            *(IntTy *) writecur_5101 = offset__2758;
            
            CursorTy writecur_5102 = writecur_5101 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7511, pvrtmp_7512,
                                                   loc_3016, pvrtmp_7514};
            break;
        }
        
      case 2:
        {
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, end_r_3018, loc_3790, tmpcur_7498);
            CursorTy pvrtmp_7523 = tmp_struct_194.field0;
            CursorTy pvrtmp_7524 = tmp_struct_194.field1;
            CursorTy pvrtmp_7525 = tmp_struct_194.field2;
            CursorTy pvrtmp_7526 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, pvrtmp_7523, pvrtmp_7526, pvrtmp_7524);
            CursorTy pvrtmp_7531 = tmp_struct_195.field0;
            CursorTy pvrtmp_7532 = tmp_struct_195.field1;
            CursorTy pvrtmp_7533 = tmp_struct_195.field2;
            CursorTy pvrtmp_7534 = tmp_struct_195.field3;
            IntTy sizeof_y_2762__2764 = pvrtmp_7526 - pvrtmp_7525;
            IntTy sizeof_y_2763__2765 = pvrtmp_7534 - pvrtmp_7533;
            IntTy fltPrm_2847 = sizeof_y_2762__2764 + 0;
            IntTy offset__2766 = 0 + fltPrm_2847;
            IntTy fltPrm_2848 = sizeof_y_2762__2764 + sizeof_y_2763__2765;
            IntTy size_dcon_2767 = 9 + fltPrm_2848;
            
            *(TagTyPacked *) loc_3016 = 162;
            
            CursorTy writetag_5109 = loc_3016 + 1;
            
            *(IntTy *) writetag_5109 = size_dcon_2767;
            
            CursorTy writecur_5110 = writetag_5109 + sizeof(IntTy);
            
            *(IntTy *) writecur_5110 = offset__2766;
            
            CursorTy writecur_5111 = writecur_5110 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7531, pvrtmp_7532,
                                                   loc_3016, pvrtmp_7534};
            break;
        }
        
      case 3:
        {
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Tags(end_r_3017, end_r_3018, loc_3813, tmpcur_7498);
            CursorTy pvrtmp_7543 = tmp_struct_196.field0;
            CursorTy pvrtmp_7544 = tmp_struct_196.field1;
            CursorTy pvrtmp_7545 = tmp_struct_196.field2;
            CursorTy pvrtmp_7546 = tmp_struct_196.field3;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, pvrtmp_7543, pvrtmp_7546, pvrtmp_7544);
            CursorTy pvrtmp_7551 = tmp_struct_197.field0;
            CursorTy pvrtmp_7552 = tmp_struct_197.field1;
            CursorTy pvrtmp_7553 = tmp_struct_197.field2;
            CursorTy pvrtmp_7554 = tmp_struct_197.field3;
            CursorCursorCursorCursorProd tmp_struct_198 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, pvrtmp_7551, pvrtmp_7554, pvrtmp_7552);
            CursorTy pvrtmp_7559 = tmp_struct_198.field0;
            CursorTy pvrtmp_7560 = tmp_struct_198.field1;
            CursorTy pvrtmp_7561 = tmp_struct_198.field2;
            CursorTy pvrtmp_7562 = tmp_struct_198.field3;
            IntTy sizeof_y_2771__2774 = pvrtmp_7546 - pvrtmp_7545;
            IntTy sizeof_y_2772__2775 = pvrtmp_7554 - pvrtmp_7553;
            IntTy sizeof_y_2773__2776 = pvrtmp_7562 - pvrtmp_7561;
            IntTy fltPrm_2849 = sizeof_y_2771__2774 + 0;
            IntTy offset__2777 = 8 + fltPrm_2849;
            IntTy fltPrm_2850 = sizeof_y_2771__2774 + sizeof_y_2772__2775;
            IntTy offset__2778 = 0 + fltPrm_2850;
            IntTy fltPrm_2852 = sizeof_y_2772__2775 + sizeof_y_2773__2776;
            IntTy fltPrm_2851 = sizeof_y_2771__2774 + fltPrm_2852;
            IntTy size_dcon_2779 = 17 + fltPrm_2851;
            
            *(TagTyPacked *) loc_3016 = 164;
            
            CursorTy writetag_5119 = loc_3016 + 1;
            
            *(IntTy *) writetag_5119 = size_dcon_2779;
            
            CursorTy writecur_5120 = writetag_5119 + sizeof(IntTy);
            
            *(IntTy *) writecur_5120 = offset__2777;
            
            CursorTy writecur_5121 = writecur_5120 + sizeof(IntTy);
            
            *(IntTy *) writecur_5121 = offset__2778;
            
            CursorTy writecur_5122 = writecur_5121 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7559, pvrtmp_7560,
                                                   loc_3016, pvrtmp_7562};
            break;
        }
        
      case 4:
        {
            CursorCursorCursorCursorProd tmp_struct_199 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, end_r_3018, loc_3840, tmpcur_7498);
            CursorTy pvrtmp_7571 = tmp_struct_199.field0;
            CursorTy pvrtmp_7572 = tmp_struct_199.field1;
            CursorTy pvrtmp_7573 = tmp_struct_199.field2;
            CursorTy pvrtmp_7574 = tmp_struct_199.field3;
            CursorCursorCursorCursorProd tmp_struct_200 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, pvrtmp_7571, pvrtmp_7574, pvrtmp_7572);
            CursorTy pvrtmp_7579 = tmp_struct_200.field0;
            CursorTy pvrtmp_7580 = tmp_struct_200.field1;
            CursorTy pvrtmp_7581 = tmp_struct_200.field2;
            CursorTy pvrtmp_7582 = tmp_struct_200.field3;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_3017, pvrtmp_7579, pvrtmp_7582, pvrtmp_7580);
            CursorTy pvrtmp_7587 = tmp_struct_201.field0;
            CursorTy pvrtmp_7588 = tmp_struct_201.field1;
            CursorTy pvrtmp_7589 = tmp_struct_201.field2;
            CursorTy pvrtmp_7590 = tmp_struct_201.field3;
            IntTy sizeof_y_2783__2786 = pvrtmp_7574 - pvrtmp_7573;
            IntTy sizeof_y_2784__2787 = pvrtmp_7582 - pvrtmp_7581;
            IntTy sizeof_y_2785__2788 = pvrtmp_7590 - pvrtmp_7589;
            IntTy fltPrm_2853 = sizeof_y_2783__2786 + 0;
            IntTy offset__2789 = 8 + fltPrm_2853;
            IntTy fltPrm_2854 = sizeof_y_2783__2786 + sizeof_y_2784__2787;
            IntTy offset__2790 = 0 + fltPrm_2854;
            IntTy fltPrm_2856 = sizeof_y_2784__2787 + sizeof_y_2785__2788;
            IntTy fltPrm_2855 = sizeof_y_2783__2786 + fltPrm_2856;
            IntTy size_dcon_2791 = 17 + fltPrm_2855;
            
            *(TagTyPacked *) loc_3016 = 166;
            
            CursorTy writetag_5131 = loc_3016 + 1;
            
            *(IntTy *) writetag_5131 = size_dcon_2791;
            
            CursorTy writecur_5132 = writetag_5131 + sizeof(IntTy);
            
            *(IntTy *) writecur_5132 = offset__2789;
            
            CursorTy writecur_5133 = writecur_5132 + sizeof(IntTy);
            
            *(IntTy *) writecur_5133 = offset__2790;
            
            CursorTy writecur_5134 = writecur_5133 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7587, pvrtmp_7588,
                                                   loc_3016, pvrtmp_7590};
            break;
        }
        
      case 5:
        {
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_3017, end_r_3018, loc_3867, tmpcur_7498);
            CursorTy pvrtmp_7599 = tmp_struct_202.field0;
            CursorTy pvrtmp_7600 = tmp_struct_202.field1;
            CursorTy pvrtmp_7601 = tmp_struct_202.field2;
            CursorTy pvrtmp_7602 = tmp_struct_202.field3;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, pvrtmp_7599, pvrtmp_7602, pvrtmp_7600);
            CursorTy pvrtmp_7607 = tmp_struct_203.field0;
            CursorTy pvrtmp_7608 = tmp_struct_203.field1;
            CursorTy pvrtmp_7609 = tmp_struct_203.field2;
            CursorTy pvrtmp_7610 = tmp_struct_203.field3;
            CursorCursorCursorCursorProd tmp_struct_204 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, pvrtmp_7607, pvrtmp_7610, pvrtmp_7608);
            CursorTy pvrtmp_7615 = tmp_struct_204.field0;
            CursorTy pvrtmp_7616 = tmp_struct_204.field1;
            CursorTy pvrtmp_7617 = tmp_struct_204.field2;
            CursorTy pvrtmp_7618 = tmp_struct_204.field3;
            IntTy sizeof_y_2795__2798 = pvrtmp_7602 - pvrtmp_7601;
            IntTy sizeof_y_2796__2799 = pvrtmp_7610 - pvrtmp_7609;
            IntTy sizeof_y_2797__2800 = pvrtmp_7618 - pvrtmp_7617;
            IntTy fltPrm_2857 = sizeof_y_2795__2798 + 0;
            IntTy offset__2801 = 8 + fltPrm_2857;
            IntTy fltPrm_2858 = sizeof_y_2795__2798 + sizeof_y_2796__2799;
            IntTy offset__2802 = 0 + fltPrm_2858;
            IntTy fltPrm_2860 = sizeof_y_2796__2799 + sizeof_y_2797__2800;
            IntTy fltPrm_2859 = sizeof_y_2795__2798 + fltPrm_2860;
            IntTy size_dcon_2803 = 17 + fltPrm_2859;
            
            *(TagTyPacked *) loc_3016 = 168;
            
            CursorTy writetag_5143 = loc_3016 + 1;
            
            *(IntTy *) writetag_5143 = size_dcon_2803;
            
            CursorTy writecur_5144 = writetag_5143 + sizeof(IntTy);
            
            *(IntTy *) writecur_5144 = offset__2801;
            
            CursorTy writecur_5145 = writecur_5144 + sizeof(IntTy);
            
            *(IntTy *) writecur_5145 = offset__2802;
            
            CursorTy writecur_5146 = writecur_5145 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7615, pvrtmp_7616,
                                                   loc_3016, pvrtmp_7618};
            break;
        }
        
      case 6:
        {
            CursorCursorCursorCursorProd tmp_struct_205 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, end_r_3018, loc_3894, tmpcur_7498);
            CursorTy pvrtmp_7627 = tmp_struct_205.field0;
            CursorTy pvrtmp_7628 = tmp_struct_205.field1;
            CursorTy pvrtmp_7629 = tmp_struct_205.field2;
            CursorTy pvrtmp_7630 = tmp_struct_205.field3;
            CursorCursorCursorCursorProd tmp_struct_206 =
                                          _add_size_and_rel_offsets_Tags(end_r_3017, pvrtmp_7627, pvrtmp_7630, pvrtmp_7628);
            CursorTy pvrtmp_7635 = tmp_struct_206.field0;
            CursorTy pvrtmp_7636 = tmp_struct_206.field1;
            CursorTy pvrtmp_7637 = tmp_struct_206.field2;
            CursorTy pvrtmp_7638 = tmp_struct_206.field3;
            CursorCursorCursorCursorProd tmp_struct_207 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, pvrtmp_7635, pvrtmp_7638, pvrtmp_7636);
            CursorTy pvrtmp_7643 = tmp_struct_207.field0;
            CursorTy pvrtmp_7644 = tmp_struct_207.field1;
            CursorTy pvrtmp_7645 = tmp_struct_207.field2;
            CursorTy pvrtmp_7646 = tmp_struct_207.field3;
            IntTy sizeof_y_2807__2810 = pvrtmp_7630 - pvrtmp_7629;
            IntTy sizeof_y_2808__2811 = pvrtmp_7638 - pvrtmp_7637;
            IntTy sizeof_y_2809__2812 = pvrtmp_7646 - pvrtmp_7645;
            IntTy fltPrm_2861 = sizeof_y_2807__2810 + 0;
            IntTy offset__2813 = 8 + fltPrm_2861;
            IntTy fltPrm_2862 = sizeof_y_2807__2810 + sizeof_y_2808__2811;
            IntTy offset__2814 = 0 + fltPrm_2862;
            IntTy fltPrm_2864 = sizeof_y_2808__2811 + sizeof_y_2809__2812;
            IntTy fltPrm_2863 = sizeof_y_2807__2810 + fltPrm_2864;
            IntTy size_dcon_2815 = 17 + fltPrm_2863;
            
            *(TagTyPacked *) loc_3016 = 170;
            
            CursorTy writetag_5155 = loc_3016 + 1;
            
            *(IntTy *) writetag_5155 = size_dcon_2815;
            
            CursorTy writecur_5156 = writetag_5155 + sizeof(IntTy);
            
            *(IntTy *) writecur_5156 = offset__2813;
            
            CursorTy writecur_5157 = writecur_5156 + sizeof(IntTy);
            
            *(IntTy *) writecur_5157 = offset__2814;
            
            CursorTy writecur_5158 = writecur_5157 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7643, pvrtmp_7644,
                                                   loc_3016, pvrtmp_7646};
            break;
        }
        
      case 7:
        {
            CursorCursorCursorCursorProd tmp_struct_208 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, end_r_3018, loc_3921, tmpcur_7498);
            CursorTy pvrtmp_7655 = tmp_struct_208.field0;
            CursorTy pvrtmp_7656 = tmp_struct_208.field1;
            CursorTy pvrtmp_7657 = tmp_struct_208.field2;
            CursorTy pvrtmp_7658 = tmp_struct_208.field3;
            CursorCursorCursorCursorProd tmp_struct_209 =
                                          _add_size_and_rel_offsets_Tags(end_r_3017, pvrtmp_7655, pvrtmp_7658, pvrtmp_7656);
            CursorTy pvrtmp_7663 = tmp_struct_209.field0;
            CursorTy pvrtmp_7664 = tmp_struct_209.field1;
            CursorTy pvrtmp_7665 = tmp_struct_209.field2;
            CursorTy pvrtmp_7666 = tmp_struct_209.field3;
            CursorCursorCursorCursorProd tmp_struct_210 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, pvrtmp_7663, pvrtmp_7666, pvrtmp_7664);
            CursorTy pvrtmp_7671 = tmp_struct_210.field0;
            CursorTy pvrtmp_7672 = tmp_struct_210.field1;
            CursorTy pvrtmp_7673 = tmp_struct_210.field2;
            CursorTy pvrtmp_7674 = tmp_struct_210.field3;
            IntTy sizeof_y_2819__2822 = pvrtmp_7658 - pvrtmp_7657;
            IntTy sizeof_y_2820__2823 = pvrtmp_7666 - pvrtmp_7665;
            IntTy sizeof_y_2821__2824 = pvrtmp_7674 - pvrtmp_7673;
            IntTy fltPrm_2865 = sizeof_y_2819__2822 + 0;
            IntTy offset__2825 = 8 + fltPrm_2865;
            IntTy fltPrm_2866 = sizeof_y_2819__2822 + sizeof_y_2820__2823;
            IntTy offset__2826 = 0 + fltPrm_2866;
            IntTy fltPrm_2868 = sizeof_y_2820__2823 + sizeof_y_2821__2824;
            IntTy fltPrm_2867 = sizeof_y_2819__2822 + fltPrm_2868;
            IntTy size_dcon_2827 = 17 + fltPrm_2867;
            
            *(TagTyPacked *) loc_3016 = 172;
            
            CursorTy writetag_5167 = loc_3016 + 1;
            
            *(IntTy *) writetag_5167 = size_dcon_2827;
            
            CursorTy writecur_5168 = writetag_5167 + sizeof(IntTy);
            
            *(IntTy *) writecur_5168 = offset__2825;
            
            CursorTy writecur_5169 = writecur_5168 + sizeof(IntTy);
            
            *(IntTy *) writecur_5169 = offset__2826;
            
            CursorTy writecur_5170 = writecur_5169 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7671, pvrtmp_7672,
                                                   loc_3016, pvrtmp_7674};
            break;
        }
        
      case 8:
        {
            CursorCursorCursorCursorProd tmp_struct_211 =
                                          _add_size_and_rel_offsets_Content(end_r_3017, end_r_3018, loc_3948, tmpcur_7498);
            CursorTy pvrtmp_7683 = tmp_struct_211.field0;
            CursorTy pvrtmp_7684 = tmp_struct_211.field1;
            CursorTy pvrtmp_7685 = tmp_struct_211.field2;
            CursorTy pvrtmp_7686 = tmp_struct_211.field3;
            CursorCursorCursorCursorProd tmp_struct_212 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, pvrtmp_7683, pvrtmp_7686, pvrtmp_7684);
            CursorTy pvrtmp_7691 = tmp_struct_212.field0;
            CursorTy pvrtmp_7692 = tmp_struct_212.field1;
            CursorTy pvrtmp_7693 = tmp_struct_212.field2;
            CursorTy pvrtmp_7694 = tmp_struct_212.field3;
            CursorCursorCursorCursorProd tmp_struct_213 =
                                          _add_size_and_rel_offsets_Tags(end_r_3017, pvrtmp_7691, pvrtmp_7694, pvrtmp_7692);
            CursorTy pvrtmp_7699 = tmp_struct_213.field0;
            CursorTy pvrtmp_7700 = tmp_struct_213.field1;
            CursorTy pvrtmp_7701 = tmp_struct_213.field2;
            CursorTy pvrtmp_7702 = tmp_struct_213.field3;
            IntTy sizeof_y_2831__2834 = pvrtmp_7686 - pvrtmp_7685;
            IntTy sizeof_y_2832__2835 = pvrtmp_7694 - pvrtmp_7693;
            IntTy sizeof_y_2833__2836 = pvrtmp_7702 - pvrtmp_7701;
            IntTy fltPrm_2869 = sizeof_y_2831__2834 + 0;
            IntTy offset__2837 = 8 + fltPrm_2869;
            IntTy fltPrm_2870 = sizeof_y_2831__2834 + sizeof_y_2832__2835;
            IntTy offset__2838 = 0 + fltPrm_2870;
            IntTy fltPrm_2872 = sizeof_y_2832__2835 + sizeof_y_2833__2836;
            IntTy fltPrm_2871 = sizeof_y_2831__2834 + fltPrm_2872;
            IntTy size_dcon_2839 = 17 + fltPrm_2871;
            
            *(TagTyPacked *) loc_3016 = 174;
            
            CursorTy writetag_5179 = loc_3016 + 1;
            
            *(IntTy *) writetag_5179 = size_dcon_2839;
            
            CursorTy writecur_5180 = writetag_5179 + sizeof(IntTy);
            
            *(IntTy *) writecur_5180 = offset__2837;
            
            CursorTy writecur_5181 = writecur_5180 + sizeof(IntTy);
            
            *(IntTy *) writecur_5181 = offset__2838;
            
            CursorTy writecur_5182 = writecur_5181 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7699, pvrtmp_7700,
                                                   loc_3016, pvrtmp_7702};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7711 = *(CursorTy *) tmpcur_7498;
            CursorTy tmpaftercur_7712 = tmpcur_7498 + 8;
            CursorTy jump_4408 = tmpcur_7498 + 8;
            CursorCursorCursorCursorProd tmp_struct_214 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, end_r_3018, loc_3016, tmpcur_7711);
            CursorTy pvrtmp_7713 = tmp_struct_214.field0;
            CursorTy pvrtmp_7714 = tmp_struct_214.field1;
            CursorTy pvrtmp_7715 = tmp_struct_214.field2;
            CursorTy pvrtmp_7716 = tmp_struct_214.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7713, jump_4408,
                                                   pvrtmp_7715, pvrtmp_7716};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7723 = *(CursorTy *) tmpcur_7498;
            CursorTy tmpaftercur_7724 = tmpcur_7498 + 8;
            CursorCursorCursorCursorProd tmp_struct_215 =
                                          _add_size_and_rel_offsets_Adt(end_r_3017, end_r_3018, loc_3016, tmpcur_7723);
            CursorTy pvrtmp_7725 = tmp_struct_215.field0;
            CursorTy pvrtmp_7726 = tmp_struct_215.field1;
            CursorTy pvrtmp_7727 = tmp_struct_215.field2;
            CursorTy pvrtmp_7728 = tmp_struct_215.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7725, pvrtmp_7726,
                                                   pvrtmp_7727, pvrtmp_7728};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7497");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_3021,
                                                            CursorTy end_r_3022,
                                                            CursorTy loc_3020,
                                                            CursorTy arg_2840)
{
    if (loc_3020 + 32 > end_r_3022) {
        ChunkTy new_chunk_222 = alloc_chunk(end_r_3022);
        CursorTy chunk_start_223 = new_chunk_222.chunk_start;
        CursorTy chunk_end_224 = new_chunk_222.chunk_end;
        
        end_r_3022 = chunk_end_224;
        *(TagTyPacked *) loc_3020 = 255;
        
        CursorTy redir = loc_3020 + 1;
        
        *(CursorTy *) redir = chunk_start_223;
        loc_3020 = chunk_start_223;
    }
    
    CursorTy loc_3968 = loc_3020 + 1;
    CursorTy loc_3969 = loc_3968 + 8;
    TagTyPacked tmpval_7736 = *(TagTyPacked *) arg_2840;
    CursorTy tmpcur_7737 = arg_2840 + 1;
    
    
  switch_7780:
    ;
    switch (tmpval_7736) {
        
      case 0:
        {
            CursorTy jump_4276 = arg_2840 + 1;
            
            *(TagTyPacked *) loc_3020 = 0;
            
            CursorTy writetag_5194 = loc_3020 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3022, jump_4276,
                                                   loc_3020, writetag_5194};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7742 = *(IntTy *) tmpcur_7737;
            CursorTy tmpcur_7743 = tmpcur_7737 + sizeof(IntTy);
            CursorTy jump_4278 = tmpcur_7737 + 8;
            CursorCursorCursorCursorProd tmp_struct_219 =
                                          _add_size_and_rel_offsets_Tags(end_r_3021, end_r_3022, loc_3969, tmpcur_7743);
            CursorTy pvrtmp_7744 = tmp_struct_219.field0;
            CursorTy pvrtmp_7745 = tmp_struct_219.field1;
            CursorTy pvrtmp_7746 = tmp_struct_219.field2;
            CursorTy pvrtmp_7747 = tmp_struct_219.field3;
            
            *(TagTyPacked *) loc_3020 = 1;
            
            CursorTy writetag_5199 = loc_3020 + 1;
            
            *(IntTy *) writetag_5199 = tmpval_7742;
            
            CursorTy writecur_5200 = writetag_5199 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7744, pvrtmp_7745,
                                                   loc_3020, pvrtmp_7747};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7756 = *(CursorTy *) tmpcur_7737;
            CursorTy tmpaftercur_7757 = tmpcur_7737 + 8;
            CursorTy jump_4414 = tmpcur_7737 + 8;
            CursorCursorCursorCursorProd tmp_struct_220 =
                                          _add_size_and_rel_offsets_Tags(end_r_3021, end_r_3022, loc_3020, tmpcur_7756);
            CursorTy pvrtmp_7758 = tmp_struct_220.field0;
            CursorTy pvrtmp_7759 = tmp_struct_220.field1;
            CursorTy pvrtmp_7760 = tmp_struct_220.field2;
            CursorTy pvrtmp_7761 = tmp_struct_220.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7758, jump_4414,
                                                   pvrtmp_7760, pvrtmp_7761};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7768 = *(CursorTy *) tmpcur_7737;
            CursorTy tmpaftercur_7769 = tmpcur_7737 + 8;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          _add_size_and_rel_offsets_Tags(end_r_3021, end_r_3022, loc_3020, tmpcur_7768);
            CursorTy pvrtmp_7770 = tmp_struct_221.field0;
            CursorTy pvrtmp_7771 = tmp_struct_221.field1;
            CursorTy pvrtmp_7772 = tmp_struct_221.field2;
            CursorTy pvrtmp_7773 = tmp_struct_221.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7770, pvrtmp_7771,
                                                   pvrtmp_7772, pvrtmp_7773};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7736");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(6176, ")");
    add_symbol(6177, "(Text ");
    add_symbol(6178, "(Tag ");
    add_symbol(6179, "(TCA ");
    add_symbol(6180, "(TAC ");
    add_symbol(6181, "(Nul ");
    add_symbol(6182, "(Nil ");
    add_symbol(6183, "(Image ");
    add_symbol(6184, "(End ");
    add_symbol(6185, "(Char ");
    add_symbol(6186, "(CTA ");
    add_symbol(6187, "(CAT ");
    add_symbol(6188, "(CA ");
    add_symbol(6189, "(ATC ");
    add_symbol(6190, "(ACT ");
    add_symbol(6191, "(AC ");
    add_symbol(6192, " ->r ");
    add_symbol(6193, " ->i ");
    
    RegionTy *region_6194 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3032 = region_6194->reg_heap;
    IntTy sizeof_end_r_3032_6195 = global_init_inf_buf_size;
    CursorTy end_r_3032 = r_3032 + sizeof_end_r_3032_6195;
    RegionTy *region_6196 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3031 = region_6196->reg_heap;
    IntTy sizeof_end_r_3031_6197 = global_init_inf_buf_size;
    CursorTy end_r_3031 = r_3031 + sizeof_end_r_3031_6197;
    CursorCursorCursorProd tmp_struct_225 =
                            mkCATList(end_r_3032, r_3032, 100000, 10, 2000);
    CursorTy pvrtmp_6198 = tmp_struct_225.field0;
    CursorTy pvrtmp_6199 = tmp_struct_225.field1;
    CursorTy pvrtmp_6200 = tmp_struct_225.field2;
    CursorTy pvrtmp_6214;
    CursorTy pvrtmp_6215;
    CursorTy pvrtmp_6216;
    VectorTy *times_230 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6214;
    struct timespec end_pvrtmp_6214;
    
    start_counters();
    for (long long iters_pvrtmp_6214 = 0; iters_pvrtmp_6214 <
         global_iters_param; iters_pvrtmp_6214++) {
        if (iters_pvrtmp_6214 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6214);
        
        CursorCursorCursorProd tmp_struct_226 =
                                addValTagsAdt(pvrtmp_6198, end_r_3031, r_3031, pvrtmp_6199);
        CursorTy pvrtmp_6205 = tmp_struct_226.field0;
        CursorTy pvrtmp_6206 = tmp_struct_226.field1;
        CursorTy pvrtmp_6207 = tmp_struct_226.field2;
        
        pvrtmp_6214 = pvrtmp_6205;
        pvrtmp_6215 = pvrtmp_6206;
        pvrtmp_6216 = pvrtmp_6207;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6214);
        if (iters_pvrtmp_6214 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_227 = difftimespecs(&begin_pvrtmp_6214,
                                            &end_pvrtmp_6214);
        
        vector_inplace_update(times_230, iters_pvrtmp_6214, &itertime_227);
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
