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

#define SIZE 4

#include <papi.h>

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
  for (int i = 0; i < SIZE; ++i){
    printf("%s : %llu\n", defs[i], values[i]);
  }
  
  printf("CPI: %f\n", ((double)values[3]/(double)values[2]));   
    
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
IntTy getLengthTR(CursorTy end_r_2554, CursorTy adt_31_923_1539,
                  IntTy accumulator_32_924_1540);
CursorCursorCursorProd mkACList(CursorTy end_r_2556, CursorTy loc_2555,
                                IntTy len_35_927_1544,
                                IntTy strLen_36_928_1545);
CursorCursorCursorProd mkString(CursorTy end_r_2558, CursorTy loc_2557,
                                IntTy len_188_1080_1550);
CursorCursorCursorProd mkContentText(CursorTy end_r_2560, CursorTy loc_2559,
                                     IntTy n_202_1094_1556);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2563,
                                          CursorTy end_r_2564,
                                          CursorTy loc_2562,
                                          CursorTy arg_637_1249_1558);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2567,
                                                       CursorTy end_r_2568,
                                                       CursorTy loc_2566,
                                                       CursorTy arg_642_1254_1563);
CursorProd _traverse_String(CursorTy end_r_2570, CursorTy arg_647_1259_1568);
CursorProd _print_String(CursorTy end_r_2572, CursorTy arg_652_1263_1572);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2575,
                                           CursorTy end_r_2576,
                                           CursorTy loc_2574,
                                           CursorTy arg_661_1272_1581);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2579,
                                                        CursorTy end_r_2580,
                                                        CursorTy loc_2578,
                                                        CursorTy arg_666_1277_1586);
CursorProd _traverse_Content(CursorTy end_r_2582, CursorTy arg_671_1282_1591);
CursorProd _print_Content(CursorTy end_r_2584, CursorTy arg_676_1287_1596);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2587, CursorTy end_r_2588,
                                       CursorTy loc_2586,
                                       CursorTy arg_685_1296_1605);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2591,
                                                    CursorTy end_r_2592,
                                                    CursorTy loc_2590,
                                                    CursorTy arg_730_1341_1650);
CursorProd _traverse_Adt(CursorTy end_r_2594, CursorTy arg_775_1386_1695);
CursorProd _print_Adt(CursorTy end_r_2596, CursorTy arg_820_1431_1740);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2599,
                                        CursorTy end_r_2600, CursorTy loc_2598,
                                        CursorTy arg_883_1494_1803);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2603,
                                                     CursorTy end_r_2604,
                                                     CursorTy loc_2602,
                                                     CursorTy arg_888_1499_1808);
CursorProd _traverse_Tags(CursorTy end_r_2606, CursorTy arg_893_1504_1813);
CursorProd _print_Tags(CursorTy end_r_2608, CursorTy arg_898_1508_1817);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_2611, CursorTy end_r_2612,
                                 CursorTy loc_2610, CursorTy arg_2467);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_2615, CursorTy end_r_2616,
                                  CursorTy loc_2614, CursorTy arg_2472);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2619,
                                                           CursorTy end_r_2620,
                                                           CursorTy loc_2618,
                                                           CursorTy arg_2477);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2623,
                                                            CursorTy end_r_2624,
                                                            CursorTy loc_2622,
                                                            CursorTy arg_2522);
IntTy getLengthTR(CursorTy end_r_2554, CursorTy adt_31_923_1539,
                  IntTy accumulator_32_924_1540)
{
    TagTyPacked tmpval_5264 = *(TagTyPacked *) adt_31_923_1539;
    CursorTy tmpcur_5265 = adt_31_923_1539 + 1;
    
    
  switch_5270:
    ;
    switch (tmpval_5264) {
        
      case 0:
        {
            CursorTy jump_3359 = adt_31_923_1539 + 1;
            
            return accumulator_32_924_1540;
            break;
        }
        
      case 2:
        {
            IntTy fltAppE_1525_1543 = 1 + accumulator_32_924_1540;
            IntTy tailapp_3360 =
                   getLengthTR(end_r_2554, tmpcur_5265, fltAppE_1525_1543);
            
            return tailapp_3360;
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5266 = *(CursorTy *) tmpcur_5265;
            CursorTy tmpaftercur_5267 = tmpcur_5265 + 8;
            CursorTy jump_3604 = tmpcur_5265 + 8;
            IntTy call_3605 =
                   getLengthTR(end_r_2554, tmpcur_5266, accumulator_32_924_1540);
            
            return call_3605;
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5268 = *(CursorTy *) tmpcur_5265;
            CursorTy tmpaftercur_5269 = tmpcur_5265 + 8;
            IntTy call_3605 =
                   getLengthTR(end_r_2554, tmpcur_5268, accumulator_32_924_1540);
            
            return call_3605;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5264");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkACList(CursorTy end_r_2556, CursorTy loc_2555,
                                IntTy len_35_927_1544, IntTy strLen_36_928_1545)
{
    if (loc_2555 + 32 > end_r_2556) {
        ChunkTy new_chunk_2 = alloc_chunk(end_r_2556);
        CursorTy chunk_start_3 = new_chunk_2.chunk_start;
        CursorTy chunk_end_4 = new_chunk_2.chunk_end;
        
        end_r_2556 = chunk_end_4;
        *(TagTyPacked *) loc_2555 = 255;
        
        CursorTy redir = loc_2555 + 1;
        
        *(CursorTy *) redir = chunk_start_3;
        loc_2555 = chunk_start_3;
    }
    
    BoolTy fltIf_1526_1546 = len_35_927_1544 <= 0;
    
    if (fltIf_1526_1546) {
        *(TagTyPacked *) loc_2555 = 0;
        
        CursorTy writetag_3840 = loc_2555 + 1;
        
        return (CursorCursorCursorProd) {end_r_2556, loc_2555, writetag_3840};
    } else {
        IntTy fltAppE_1527_1547 = len_35_927_1544 - 1;
        CursorTy loc_2640 = loc_2555 + 1;
        CursorCursorCursorProd tmp_struct_0 =
                                mkACList(end_r_2556, loc_2640, fltAppE_1527_1547, strLen_36_928_1545);
        CursorTy pvrtmp_5275 = tmp_struct_0.field0;
        CursorTy pvrtmp_5276 = tmp_struct_0.field1;
        CursorTy pvrtmp_5277 = tmp_struct_0.field2;
        CursorCursorCursorProd tmp_struct_1 =
                                mkContentText(pvrtmp_5275, pvrtmp_5277, strLen_36_928_1545);
        CursorTy pvrtmp_5282 = tmp_struct_1.field0;
        CursorTy pvrtmp_5283 = tmp_struct_1.field1;
        CursorTy pvrtmp_5284 = tmp_struct_1.field2;
        
        *(TagTyPacked *) loc_2555 = 2;
        
        CursorTy writetag_3844 = loc_2555 + 1;
        
        return (CursorCursorCursorProd) {pvrtmp_5282, loc_2555, pvrtmp_5284};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2558, CursorTy loc_2557,
                                IntTy len_188_1080_1550)
{
    if (loc_2557 + 32 > end_r_2558) {
        ChunkTy new_chunk_6 = alloc_chunk(end_r_2558);
        CursorTy chunk_start_7 = new_chunk_6.chunk_start;
        CursorTy chunk_end_8 = new_chunk_6.chunk_end;
        
        end_r_2558 = chunk_end_8;
        *(TagTyPacked *) loc_2557 = 255;
        
        CursorTy redir = loc_2557 + 1;
        
        *(CursorTy *) redir = chunk_start_7;
        loc_2557 = chunk_start_7;
    }
    
    CursorTy loc_2646 = loc_2557 + 1;
    CursorTy loc_2647 = loc_2646 + 8;
    BoolTy fltIf_1528_1551 = len_188_1080_1550 <= 0;
    
    if (fltIf_1528_1551) {
        *(TagTyPacked *) loc_2557 = 0;
        
        CursorTy writetag_3848 = loc_2557 + 1;
        
        return (CursorCursorCursorProd) {end_r_2558, loc_2557, writetag_3848};
    } else {
        IntTy fltPrm_1529_1552 = rand();
        IntTy randomChar_189_1081_1553 = fltPrm_1529_1552 % 128;
        IntTy fltAppE_1530_1554 = len_188_1080_1550 - 1;
        CursorCursorCursorProd tmp_struct_5 =
                                mkString(end_r_2558, loc_2647, fltAppE_1530_1554);
        CursorTy pvrtmp_5297 = tmp_struct_5.field0;
        CursorTy pvrtmp_5298 = tmp_struct_5.field1;
        CursorTy pvrtmp_5299 = tmp_struct_5.field2;
        
        *(TagTyPacked *) loc_2557 = 1;
        
        CursorTy writetag_3851 = loc_2557 + 1;
        
        *(IntTy *) writetag_3851 = randomChar_189_1081_1553;
        
        CursorTy writecur_3852 = writetag_3851 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_5297, loc_2557, pvrtmp_5299};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2560, CursorTy loc_2559,
                                     IntTy n_202_1094_1556)
{
    if (loc_2559 + 32 > end_r_2560) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2560);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2560 = chunk_end_12;
        *(TagTyPacked *) loc_2559 = 255;
        
        CursorTy redir = loc_2559 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2559 = chunk_start_11;
    }
    
    CursorTy loc_2652 = loc_2559 + 1;
    CursorCursorCursorProd tmp_struct_9 =
                            mkString(end_r_2560, loc_2652, n_202_1094_1556);
    CursorTy pvrtmp_5308 = tmp_struct_9.field0;
    CursorTy pvrtmp_5309 = tmp_struct_9.field1;
    CursorTy pvrtmp_5310 = tmp_struct_9.field2;
    
    *(TagTyPacked *) loc_2559 = 1;
    
    CursorTy writetag_3856 = loc_2559 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_5308, loc_2559, pvrtmp_5310};
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2563,
                                          CursorTy end_r_2564,
                                          CursorTy loc_2562,
                                          CursorTy arg_637_1249_1558)
{
    if (loc_2562 + 32 > end_r_2564) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2564);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2564 = chunk_end_18;
        *(TagTyPacked *) loc_2562 = 255;
        
        CursorTy redir = loc_2562 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2562 = chunk_start_17;
    }
    
    CursorTy loc_2662 = loc_2562 + 1;
    CursorTy loc_2663 = loc_2662 + 8;
    TagTyPacked tmpval_5319 = *(TagTyPacked *) arg_637_1249_1558;
    CursorTy tmpcur_5320 = arg_637_1249_1558 + 1;
    
    
  switch_5363:
    ;
    switch (tmpval_5319) {
        
      case 0:
        {
            CursorTy jump_3366 = arg_637_1249_1558 + 1;
            
            *(TagTyPacked *) loc_2562 = 0;
            
            CursorTy writetag_3860 = loc_2562 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2564, jump_3366,
                                                   loc_2562, writetag_3860};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_5325 = *(IntTy *) tmpcur_5320;
            CursorTy tmpcur_5326 = tmpcur_5320 + sizeof(IntTy);
            CursorTy jump_3368 = tmpcur_5320 + 8;
            CursorCursorCursorCursorProd tmp_struct_13 =
                                          _copy_String(end_r_2563, end_r_2564, loc_2663, tmpcur_5326);
            CursorTy pvrtmp_5327 = tmp_struct_13.field0;
            CursorTy pvrtmp_5328 = tmp_struct_13.field1;
            CursorTy pvrtmp_5329 = tmp_struct_13.field2;
            CursorTy pvrtmp_5330 = tmp_struct_13.field3;
            
            *(TagTyPacked *) loc_2562 = 1;
            
            CursorTy writetag_3865 = loc_2562 + 1;
            
            *(IntTy *) writetag_3865 = tmpval_5325;
            
            CursorTy writecur_3866 = writetag_3865 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5327, pvrtmp_5328,
                                                   loc_2562, pvrtmp_5330};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5339 = *(CursorTy *) tmpcur_5320;
            CursorTy tmpaftercur_5340 = tmpcur_5320 + 8;
            CursorTy jump_3609 = tmpcur_5320 + 8;
            CursorCursorCursorCursorProd tmp_struct_14 =
                                          _copy_String(end_r_2563, end_r_2564, loc_2562, tmpcur_5339);
            CursorTy pvrtmp_5341 = tmp_struct_14.field0;
            CursorTy pvrtmp_5342 = tmp_struct_14.field1;
            CursorTy pvrtmp_5343 = tmp_struct_14.field2;
            CursorTy pvrtmp_5344 = tmp_struct_14.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5341, jump_3609,
                                                   pvrtmp_5343, pvrtmp_5344};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5351 = *(CursorTy *) tmpcur_5320;
            CursorTy tmpaftercur_5352 = tmpcur_5320 + 8;
            CursorCursorCursorCursorProd tmp_struct_15 =
                                          _copy_String(end_r_2563, end_r_2564, loc_2562, tmpcur_5351);
            CursorTy pvrtmp_5353 = tmp_struct_15.field0;
            CursorTy pvrtmp_5354 = tmp_struct_15.field1;
            CursorTy pvrtmp_5355 = tmp_struct_15.field2;
            CursorTy pvrtmp_5356 = tmp_struct_15.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5353, pvrtmp_5354,
                                                   pvrtmp_5355, pvrtmp_5356};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5319");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2567,
                                                       CursorTy end_r_2568,
                                                       CursorTy loc_2566,
                                                       CursorTy arg_642_1254_1563)
{
    CursorTy loc_2675 = loc_2566 + 1;
    CursorTy loc_2676 = loc_2675 + 8;
    TagTyPacked tmpval_5364 = *(TagTyPacked *) arg_642_1254_1563;
    CursorTy tmpcur_5365 = arg_642_1254_1563 + 1;
    
    
  switch_5408:
    ;
    switch (tmpval_5364) {
        
      case 0:
        {
            CursorTy jump_3371 = arg_642_1254_1563 + 1;
            
            *(TagTyPacked *) loc_2566 = 0;
            
            CursorTy writetag_3876 = loc_2566 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2568, jump_3371,
                                                   loc_2566, writetag_3876};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_5370 = *(IntTy *) tmpcur_5365;
            CursorTy tmpcur_5371 = tmpcur_5365 + sizeof(IntTy);
            CursorTy jump_3373 = tmpcur_5365 + 8;
            CursorCursorCursorCursorProd tmp_struct_19 =
                                          _copy_without_ptrs_String(end_r_2567, end_r_2568, loc_2676, tmpcur_5371);
            CursorTy pvrtmp_5372 = tmp_struct_19.field0;
            CursorTy pvrtmp_5373 = tmp_struct_19.field1;
            CursorTy pvrtmp_5374 = tmp_struct_19.field2;
            CursorTy pvrtmp_5375 = tmp_struct_19.field3;
            
            *(TagTyPacked *) loc_2566 = 1;
            
            CursorTy writetag_3881 = loc_2566 + 1;
            
            *(IntTy *) writetag_3881 = tmpval_5370;
            
            CursorTy writecur_3882 = writetag_3881 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5372, pvrtmp_5373,
                                                   loc_2566, pvrtmp_5375};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5384 = *(CursorTy *) tmpcur_5365;
            CursorTy tmpaftercur_5385 = tmpcur_5365 + 8;
            CursorTy jump_3615 = tmpcur_5365 + 8;
            CursorCursorCursorCursorProd tmp_struct_20 =
                                          _copy_without_ptrs_String(end_r_2567, end_r_2568, loc_2566, tmpcur_5384);
            CursorTy pvrtmp_5386 = tmp_struct_20.field0;
            CursorTy pvrtmp_5387 = tmp_struct_20.field1;
            CursorTy pvrtmp_5388 = tmp_struct_20.field2;
            CursorTy pvrtmp_5389 = tmp_struct_20.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5386, jump_3615,
                                                   pvrtmp_5388, pvrtmp_5389};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5396 = *(CursorTy *) tmpcur_5365;
            CursorTy tmpaftercur_5397 = tmpcur_5365 + 8;
            CursorCursorCursorCursorProd tmp_struct_21 =
                                          _copy_without_ptrs_String(end_r_2567, end_r_2568, loc_2566, tmpcur_5396);
            CursorTy pvrtmp_5398 = tmp_struct_21.field0;
            CursorTy pvrtmp_5399 = tmp_struct_21.field1;
            CursorTy pvrtmp_5400 = tmp_struct_21.field2;
            CursorTy pvrtmp_5401 = tmp_struct_21.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5398, pvrtmp_5399,
                                                   pvrtmp_5400, pvrtmp_5401};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5364");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2570, CursorTy arg_647_1259_1568)
{
    TagTyPacked tmpval_5409 = *(TagTyPacked *) arg_647_1259_1568;
    CursorTy tmpcur_5410 = arg_647_1259_1568 + 1;
    
    
  switch_5420:
    ;
    switch (tmpval_5409) {
        
      case 0:
        {
            CursorTy jump_3376 = arg_647_1259_1568 + 1;
            
            return (CursorProd) {jump_3376};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_5411 = *(IntTy *) tmpcur_5410;
            CursorTy tmpcur_5412 = tmpcur_5410 + sizeof(IntTy);
            CursorTy jump_3378 = tmpcur_5410 + 8;
            CursorProd tmp_struct_22 =
                        _traverse_String(end_r_2570, tmpcur_5412);
            CursorTy pvrtmp_5413 = tmp_struct_22.field0;
            
            return (CursorProd) {pvrtmp_5413};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5414 = *(CursorTy *) tmpcur_5410;
            CursorTy tmpaftercur_5415 = tmpcur_5410 + 8;
            CursorTy jump_3621 = tmpcur_5410 + 8;
            CursorProd tmp_struct_23 =
                        _traverse_String(end_r_2570, tmpcur_5414);
            CursorTy pvrtmp_5416 = tmp_struct_23.field0;
            
            return (CursorProd) {jump_3621};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5417 = *(CursorTy *) tmpcur_5410;
            CursorTy tmpaftercur_5418 = tmpcur_5410 + 8;
            CursorProd tmp_struct_24 =
                        _traverse_String(end_r_2570, tmpcur_5417);
            CursorTy pvrtmp_5419 = tmp_struct_24.field0;
            
            return (CursorProd) {pvrtmp_5419};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5409");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2572, CursorTy arg_652_1263_1572)
{
    TagTyPacked tmpval_5421 = *(TagTyPacked *) arg_652_1263_1572;
    CursorTy tmpcur_5422 = arg_652_1263_1572 + 1;
    
    
  switch_5432:
    ;
    switch (tmpval_5421) {
        
      case 0:
        {
            CursorTy jump_3381 = arg_652_1263_1572 + 1;
            unsigned char wildcard_653_1264_1573 = print_symbol(5245);
            unsigned char wildcard_654_1265_1574 = print_symbol(5237);
            
            return (CursorProd) {jump_3381};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_5423 = *(IntTy *) tmpcur_5422;
            CursorTy tmpcur_5424 = tmpcur_5422 + sizeof(IntTy);
            CursorTy jump_3383 = tmpcur_5422 + 8;
            unsigned char wildcard_659_1268_1577 = print_symbol(5246);
            unsigned char y_657_1269_1578 = printf("%lld", tmpval_5423);
            CursorProd tmp_struct_25 =  _print_String(end_r_2572, tmpcur_5424);
            CursorTy pvrtmp_5425 = tmp_struct_25.field0;
            unsigned char wildcard_660_1271_1580 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_5425};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5426 = *(CursorTy *) tmpcur_5422;
            CursorTy tmpaftercur_5427 = tmpcur_5422 + 8;
            CursorTy jump_3627 = tmpcur_5422 + 8;
            unsigned char wildcard_3630 = print_symbol(5254);
            CursorProd tmp_struct_26 =  _print_String(end_r_2572, tmpcur_5426);
            CursorTy pvrtmp_5428 = tmp_struct_26.field0;
            
            return (CursorProd) {jump_3627};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5429 = *(CursorTy *) tmpcur_5422;
            CursorTy tmpaftercur_5430 = tmpcur_5422 + 8;
            unsigned char wildcard_3630 = print_symbol(5253);
            CursorProd tmp_struct_27 =  _print_String(end_r_2572, tmpcur_5429);
            CursorTy pvrtmp_5431 = tmp_struct_27.field0;
            
            return (CursorProd) {pvrtmp_5431};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5421");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2575,
                                           CursorTy end_r_2576,
                                           CursorTy loc_2574,
                                           CursorTy arg_661_1272_1581)
{
    if (loc_2574 + 32 > end_r_2576) {
        ChunkTy new_chunk_32 = alloc_chunk(end_r_2576);
        CursorTy chunk_start_33 = new_chunk_32.chunk_start;
        CursorTy chunk_end_34 = new_chunk_32.chunk_end;
        
        end_r_2576 = chunk_end_34;
        *(TagTyPacked *) loc_2574 = 255;
        
        CursorTy redir = loc_2574 + 1;
        
        *(CursorTy *) redir = chunk_start_33;
        loc_2574 = chunk_start_33;
    }
    
    TagTyPacked tmpval_5433 = *(TagTyPacked *) arg_661_1272_1581;
    CursorTy tmpcur_5434 = arg_661_1272_1581 + 1;
    
    
  switch_5483:
    ;
    switch (tmpval_5433) {
        
      case 0:
        {
            CursorTy loc_2698 = loc_2574 + 1;
            CursorCursorCursorCursorProd tmp_struct_28 =
                                          _copy_String(end_r_2575, end_r_2576, loc_2698, tmpcur_5434);
            CursorTy pvrtmp_5435 = tmp_struct_28.field0;
            CursorTy pvrtmp_5436 = tmp_struct_28.field1;
            CursorTy pvrtmp_5437 = tmp_struct_28.field2;
            CursorTy pvrtmp_5438 = tmp_struct_28.field3;
            
            *(TagTyPacked *) loc_2574 = 0;
            
            CursorTy writetag_3913 = loc_2574 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5435, pvrtmp_5436,
                                                   loc_2574, pvrtmp_5438};
            break;
        }
        
      case 1:
        {
            CursorTy loc_2704 = loc_2574 + 1;
            CursorCursorCursorCursorProd tmp_struct_29 =
                                          _copy_String(end_r_2575, end_r_2576, loc_2704, tmpcur_5434);
            CursorTy pvrtmp_5447 = tmp_struct_29.field0;
            CursorTy pvrtmp_5448 = tmp_struct_29.field1;
            CursorTy pvrtmp_5449 = tmp_struct_29.field2;
            CursorTy pvrtmp_5450 = tmp_struct_29.field3;
            
            *(TagTyPacked *) loc_2574 = 1;
            
            CursorTy writetag_3918 = loc_2574 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5447, pvrtmp_5448,
                                                   loc_2574, pvrtmp_5450};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5459 = *(CursorTy *) tmpcur_5434;
            CursorTy tmpaftercur_5460 = tmpcur_5434 + 8;
            CursorTy jump_3633 = tmpcur_5434 + 8;
            CursorCursorCursorCursorProd tmp_struct_30 =
                                          _copy_Content(end_r_2575, end_r_2576, loc_2574, tmpcur_5459);
            CursorTy pvrtmp_5461 = tmp_struct_30.field0;
            CursorTy pvrtmp_5462 = tmp_struct_30.field1;
            CursorTy pvrtmp_5463 = tmp_struct_30.field2;
            CursorTy pvrtmp_5464 = tmp_struct_30.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5461, jump_3633,
                                                   pvrtmp_5463, pvrtmp_5464};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5471 = *(CursorTy *) tmpcur_5434;
            CursorTy tmpaftercur_5472 = tmpcur_5434 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_Content(end_r_2575, end_r_2576, loc_2574, tmpcur_5471);
            CursorTy pvrtmp_5473 = tmp_struct_31.field0;
            CursorTy pvrtmp_5474 = tmp_struct_31.field1;
            CursorTy pvrtmp_5475 = tmp_struct_31.field2;
            CursorTy pvrtmp_5476 = tmp_struct_31.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5473, pvrtmp_5474,
                                                   pvrtmp_5475, pvrtmp_5476};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5433");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2579,
                                                        CursorTy end_r_2580,
                                                        CursorTy loc_2578,
                                                        CursorTy arg_666_1277_1586)
{
    TagTyPacked tmpval_5484 = *(TagTyPacked *) arg_666_1277_1586;
    CursorTy tmpcur_5485 = arg_666_1277_1586 + 1;
    
    
  switch_5534:
    ;
    switch (tmpval_5484) {
        
      case 0:
        {
            CursorTy loc_2712 = loc_2578 + 1;
            CursorCursorCursorCursorProd tmp_struct_35 =
                                          _copy_without_ptrs_String(end_r_2579, end_r_2580, loc_2712, tmpcur_5485);
            CursorTy pvrtmp_5486 = tmp_struct_35.field0;
            CursorTy pvrtmp_5487 = tmp_struct_35.field1;
            CursorTy pvrtmp_5488 = tmp_struct_35.field2;
            CursorTy pvrtmp_5489 = tmp_struct_35.field3;
            
            *(TagTyPacked *) loc_2578 = 0;
            
            CursorTy writetag_3929 = loc_2578 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5486, pvrtmp_5487,
                                                   loc_2578, pvrtmp_5489};
            break;
        }
        
      case 1:
        {
            CursorTy loc_2718 = loc_2578 + 1;
            CursorCursorCursorCursorProd tmp_struct_36 =
                                          _copy_without_ptrs_String(end_r_2579, end_r_2580, loc_2718, tmpcur_5485);
            CursorTy pvrtmp_5498 = tmp_struct_36.field0;
            CursorTy pvrtmp_5499 = tmp_struct_36.field1;
            CursorTy pvrtmp_5500 = tmp_struct_36.field2;
            CursorTy pvrtmp_5501 = tmp_struct_36.field3;
            
            *(TagTyPacked *) loc_2578 = 1;
            
            CursorTy writetag_3934 = loc_2578 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5498, pvrtmp_5499,
                                                   loc_2578, pvrtmp_5501};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5510 = *(CursorTy *) tmpcur_5485;
            CursorTy tmpaftercur_5511 = tmpcur_5485 + 8;
            CursorTy jump_3639 = tmpcur_5485 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_Content(end_r_2579, end_r_2580, loc_2578, tmpcur_5510);
            CursorTy pvrtmp_5512 = tmp_struct_37.field0;
            CursorTy pvrtmp_5513 = tmp_struct_37.field1;
            CursorTy pvrtmp_5514 = tmp_struct_37.field2;
            CursorTy pvrtmp_5515 = tmp_struct_37.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5512, jump_3639,
                                                   pvrtmp_5514, pvrtmp_5515};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5522 = *(CursorTy *) tmpcur_5485;
            CursorTy tmpaftercur_5523 = tmpcur_5485 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_Content(end_r_2579, end_r_2580, loc_2578, tmpcur_5522);
            CursorTy pvrtmp_5524 = tmp_struct_38.field0;
            CursorTy pvrtmp_5525 = tmp_struct_38.field1;
            CursorTy pvrtmp_5526 = tmp_struct_38.field2;
            CursorTy pvrtmp_5527 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5524, pvrtmp_5525,
                                                   pvrtmp_5526, pvrtmp_5527};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5484");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2582, CursorTy arg_671_1282_1591)
{
    TagTyPacked tmpval_5535 = *(TagTyPacked *) arg_671_1282_1591;
    CursorTy tmpcur_5536 = arg_671_1282_1591 + 1;
    
    
  switch_5545:
    ;
    switch (tmpval_5535) {
        
      case 0:
        {
            CursorProd tmp_struct_39 =
                        _traverse_String(end_r_2582, tmpcur_5536);
            CursorTy pvrtmp_5537 = tmp_struct_39.field0;
            
            return (CursorProd) {pvrtmp_5537};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2582, tmpcur_5536);
            CursorTy pvrtmp_5538 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_5538};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5539 = *(CursorTy *) tmpcur_5536;
            CursorTy tmpaftercur_5540 = tmpcur_5536 + 8;
            CursorTy jump_3645 = tmpcur_5536 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_Content(end_r_2582, tmpcur_5539);
            CursorTy pvrtmp_5541 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_3645};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5542 = *(CursorTy *) tmpcur_5536;
            CursorTy tmpaftercur_5543 = tmpcur_5536 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_Content(end_r_2582, tmpcur_5542);
            CursorTy pvrtmp_5544 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_5544};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5535");
            exit(1);
        }
    }
}
CursorProd _print_Content(CursorTy end_r_2584, CursorTy arg_676_1287_1596)
{
    TagTyPacked tmpval_5546 = *(TagTyPacked *) arg_676_1287_1596;
    CursorTy tmpcur_5547 = arg_676_1287_1596 + 1;
    
    
  switch_5556:
    ;
    switch (tmpval_5546) {
        
      case 0:
        {
            unsigned char wildcard_679_1289_1598 = print_symbol(5244);
            CursorProd tmp_struct_43 =  _print_String(end_r_2584, tmpcur_5547);
            CursorTy pvrtmp_5548 = tmp_struct_43.field0;
            unsigned char wildcard_680_1291_1600 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_5548};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_683_1293_1602 = print_symbol(5238);
            CursorProd tmp_struct_44 =  _print_String(end_r_2584, tmpcur_5547);
            CursorTy pvrtmp_5549 = tmp_struct_44.field0;
            unsigned char wildcard_684_1295_1604 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_5549};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5550 = *(CursorTy *) tmpcur_5547;
            CursorTy tmpaftercur_5551 = tmpcur_5547 + 8;
            CursorTy jump_3651 = tmpcur_5547 + 8;
            unsigned char wildcard_3654 = print_symbol(5254);
            CursorProd tmp_struct_45 =  _print_Content(end_r_2584, tmpcur_5550);
            CursorTy pvrtmp_5552 = tmp_struct_45.field0;
            
            return (CursorProd) {jump_3651};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5553 = *(CursorTy *) tmpcur_5547;
            CursorTy tmpaftercur_5554 = tmpcur_5547 + 8;
            unsigned char wildcard_3654 = print_symbol(5253);
            CursorProd tmp_struct_46 =  _print_Content(end_r_2584, tmpcur_5553);
            CursorTy pvrtmp_5555 = tmp_struct_46.field0;
            
            return (CursorProd) {pvrtmp_5555};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5546");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2587, CursorTy end_r_2588,
                                       CursorTy loc_2586,
                                       CursorTy arg_685_1296_1605)
{
    if (loc_2586 + 32 > end_r_2588) {
        ChunkTy new_chunk_71 = alloc_chunk(end_r_2588);
        CursorTy chunk_start_72 = new_chunk_71.chunk_start;
        CursorTy chunk_end_73 = new_chunk_71.chunk_end;
        
        end_r_2588 = chunk_end_73;
        *(TagTyPacked *) loc_2586 = 255;
        
        CursorTy redir = loc_2586 + 1;
        
        *(CursorTy *) redir = chunk_start_72;
        loc_2586 = chunk_start_72;
    }
    
    TagTyPacked tmpval_5557 = *(TagTyPacked *) arg_685_1296_1605;
    CursorTy tmpcur_5558 = arg_685_1296_1605 + 1;
    
    
  switch_5795:
    ;
    switch (tmpval_5557) {
        
      case 0:
        {
            CursorTy jump_3402 = arg_685_1296_1605 + 1;
            
            *(TagTyPacked *) loc_2586 = 0;
            
            CursorTy writetag_3964 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2588, jump_3402,
                                                   loc_2586, writetag_3964};
            break;
        }
        
      case 1:
        {
            CursorTy loc_2747 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_Content(end_r_2587, end_r_2588, loc_2747, tmpcur_5558);
            CursorTy pvrtmp_5563 = tmp_struct_47.field0;
            CursorTy pvrtmp_5564 = tmp_struct_47.field1;
            CursorTy pvrtmp_5565 = tmp_struct_47.field2;
            CursorTy pvrtmp_5566 = tmp_struct_47.field3;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Adt(end_r_2587, pvrtmp_5563, pvrtmp_5566, pvrtmp_5564);
            CursorTy pvrtmp_5571 = tmp_struct_48.field0;
            CursorTy pvrtmp_5572 = tmp_struct_48.field1;
            CursorTy pvrtmp_5573 = tmp_struct_48.field2;
            CursorTy pvrtmp_5574 = tmp_struct_48.field3;
            
            *(TagTyPacked *) loc_2586 = 1;
            
            CursorTy writetag_3969 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5571, pvrtmp_5572,
                                                   loc_2586, pvrtmp_5574};
            break;
        }
        
      case 2:
        {
            CursorTy loc_2759 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Adt(end_r_2587, end_r_2588, loc_2759, tmpcur_5558);
            CursorTy pvrtmp_5583 = tmp_struct_49.field0;
            CursorTy pvrtmp_5584 = tmp_struct_49.field1;
            CursorTy pvrtmp_5585 = tmp_struct_49.field2;
            CursorTy pvrtmp_5586 = tmp_struct_49.field3;
            CursorCursorCursorCursorProd tmp_struct_50 =
                                          _copy_Content(end_r_2587, pvrtmp_5583, pvrtmp_5586, pvrtmp_5584);
            CursorTy pvrtmp_5591 = tmp_struct_50.field0;
            CursorTy pvrtmp_5592 = tmp_struct_50.field1;
            CursorTy pvrtmp_5593 = tmp_struct_50.field2;
            CursorTy pvrtmp_5594 = tmp_struct_50.field3;
            
            *(TagTyPacked *) loc_2586 = 2;
            
            CursorTy writetag_3976 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5591, pvrtmp_5592,
                                                   loc_2586, pvrtmp_5594};
            break;
        }
        
      case 3:
        {
            CursorTy loc_2775 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_51 =
                                          _copy_Tags(end_r_2587, end_r_2588, loc_2775, tmpcur_5558);
            CursorTy pvrtmp_5603 = tmp_struct_51.field0;
            CursorTy pvrtmp_5604 = tmp_struct_51.field1;
            CursorTy pvrtmp_5605 = tmp_struct_51.field2;
            CursorTy pvrtmp_5606 = tmp_struct_51.field3;
            CursorCursorCursorCursorProd tmp_struct_52 =
                                          _copy_Content(end_r_2587, pvrtmp_5603, pvrtmp_5606, pvrtmp_5604);
            CursorTy pvrtmp_5611 = tmp_struct_52.field0;
            CursorTy pvrtmp_5612 = tmp_struct_52.field1;
            CursorTy pvrtmp_5613 = tmp_struct_52.field2;
            CursorTy pvrtmp_5614 = tmp_struct_52.field3;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_Adt(end_r_2587, pvrtmp_5611, pvrtmp_5614, pvrtmp_5612);
            CursorTy pvrtmp_5619 = tmp_struct_53.field0;
            CursorTy pvrtmp_5620 = tmp_struct_53.field1;
            CursorTy pvrtmp_5621 = tmp_struct_53.field2;
            CursorTy pvrtmp_5622 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2586 = 3;
            
            CursorTy writetag_3984 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5619, pvrtmp_5620,
                                                   loc_2586, pvrtmp_5622};
            break;
        }
        
      case 4:
        {
            CursorTy loc_2793 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_Adt(end_r_2587, end_r_2588, loc_2793, tmpcur_5558);
            CursorTy pvrtmp_5631 = tmp_struct_54.field0;
            CursorTy pvrtmp_5632 = tmp_struct_54.field1;
            CursorTy pvrtmp_5633 = tmp_struct_54.field2;
            CursorTy pvrtmp_5634 = tmp_struct_54.field3;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_Content(end_r_2587, pvrtmp_5631, pvrtmp_5634, pvrtmp_5632);
            CursorTy pvrtmp_5639 = tmp_struct_55.field0;
            CursorTy pvrtmp_5640 = tmp_struct_55.field1;
            CursorTy pvrtmp_5641 = tmp_struct_55.field2;
            CursorTy pvrtmp_5642 = tmp_struct_55.field3;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_Tags(end_r_2587, pvrtmp_5639, pvrtmp_5642, pvrtmp_5640);
            CursorTy pvrtmp_5647 = tmp_struct_56.field0;
            CursorTy pvrtmp_5648 = tmp_struct_56.field1;
            CursorTy pvrtmp_5649 = tmp_struct_56.field2;
            CursorTy pvrtmp_5650 = tmp_struct_56.field3;
            
            *(TagTyPacked *) loc_2586 = 4;
            
            CursorTy writetag_3993 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5647, pvrtmp_5648,
                                                   loc_2586, pvrtmp_5650};
            break;
        }
        
      case 5:
        {
            CursorTy loc_2811 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_57 =
                                          _copy_Tags(end_r_2587, end_r_2588, loc_2811, tmpcur_5558);
            CursorTy pvrtmp_5659 = tmp_struct_57.field0;
            CursorTy pvrtmp_5660 = tmp_struct_57.field1;
            CursorTy pvrtmp_5661 = tmp_struct_57.field2;
            CursorTy pvrtmp_5662 = tmp_struct_57.field3;
            CursorCursorCursorCursorProd tmp_struct_58 =
                                          _copy_Adt(end_r_2587, pvrtmp_5659, pvrtmp_5662, pvrtmp_5660);
            CursorTy pvrtmp_5667 = tmp_struct_58.field0;
            CursorTy pvrtmp_5668 = tmp_struct_58.field1;
            CursorTy pvrtmp_5669 = tmp_struct_58.field2;
            CursorTy pvrtmp_5670 = tmp_struct_58.field3;
            CursorCursorCursorCursorProd tmp_struct_59 =
                                          _copy_Content(end_r_2587, pvrtmp_5667, pvrtmp_5670, pvrtmp_5668);
            CursorTy pvrtmp_5675 = tmp_struct_59.field0;
            CursorTy pvrtmp_5676 = tmp_struct_59.field1;
            CursorTy pvrtmp_5677 = tmp_struct_59.field2;
            CursorTy pvrtmp_5678 = tmp_struct_59.field3;
            
            *(TagTyPacked *) loc_2586 = 5;
            
            CursorTy writetag_4002 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5675, pvrtmp_5676,
                                                   loc_2586, pvrtmp_5678};
            break;
        }
        
      case 6:
        {
            CursorTy loc_2829 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_60 =
                                          _copy_Adt(end_r_2587, end_r_2588, loc_2829, tmpcur_5558);
            CursorTy pvrtmp_5687 = tmp_struct_60.field0;
            CursorTy pvrtmp_5688 = tmp_struct_60.field1;
            CursorTy pvrtmp_5689 = tmp_struct_60.field2;
            CursorTy pvrtmp_5690 = tmp_struct_60.field3;
            CursorCursorCursorCursorProd tmp_struct_61 =
                                          _copy_Tags(end_r_2587, pvrtmp_5687, pvrtmp_5690, pvrtmp_5688);
            CursorTy pvrtmp_5695 = tmp_struct_61.field0;
            CursorTy pvrtmp_5696 = tmp_struct_61.field1;
            CursorTy pvrtmp_5697 = tmp_struct_61.field2;
            CursorTy pvrtmp_5698 = tmp_struct_61.field3;
            CursorCursorCursorCursorProd tmp_struct_62 =
                                          _copy_Content(end_r_2587, pvrtmp_5695, pvrtmp_5698, pvrtmp_5696);
            CursorTy pvrtmp_5703 = tmp_struct_62.field0;
            CursorTy pvrtmp_5704 = tmp_struct_62.field1;
            CursorTy pvrtmp_5705 = tmp_struct_62.field2;
            CursorTy pvrtmp_5706 = tmp_struct_62.field3;
            
            *(TagTyPacked *) loc_2586 = 6;
            
            CursorTy writetag_4011 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5703, pvrtmp_5704,
                                                   loc_2586, pvrtmp_5706};
            break;
        }
        
      case 7:
        {
            CursorTy loc_2847 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_63 =
                                          _copy_Content(end_r_2587, end_r_2588, loc_2847, tmpcur_5558);
            CursorTy pvrtmp_5715 = tmp_struct_63.field0;
            CursorTy pvrtmp_5716 = tmp_struct_63.field1;
            CursorTy pvrtmp_5717 = tmp_struct_63.field2;
            CursorTy pvrtmp_5718 = tmp_struct_63.field3;
            CursorCursorCursorCursorProd tmp_struct_64 =
                                          _copy_Tags(end_r_2587, pvrtmp_5715, pvrtmp_5718, pvrtmp_5716);
            CursorTy pvrtmp_5723 = tmp_struct_64.field0;
            CursorTy pvrtmp_5724 = tmp_struct_64.field1;
            CursorTy pvrtmp_5725 = tmp_struct_64.field2;
            CursorTy pvrtmp_5726 = tmp_struct_64.field3;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Adt(end_r_2587, pvrtmp_5723, pvrtmp_5726, pvrtmp_5724);
            CursorTy pvrtmp_5731 = tmp_struct_65.field0;
            CursorTy pvrtmp_5732 = tmp_struct_65.field1;
            CursorTy pvrtmp_5733 = tmp_struct_65.field2;
            CursorTy pvrtmp_5734 = tmp_struct_65.field3;
            
            *(TagTyPacked *) loc_2586 = 7;
            
            CursorTy writetag_4020 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5731, pvrtmp_5732,
                                                   loc_2586, pvrtmp_5734};
            break;
        }
        
      case 8:
        {
            CursorTy loc_2865 = loc_2586 + 1;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Content(end_r_2587, end_r_2588, loc_2865, tmpcur_5558);
            CursorTy pvrtmp_5743 = tmp_struct_66.field0;
            CursorTy pvrtmp_5744 = tmp_struct_66.field1;
            CursorTy pvrtmp_5745 = tmp_struct_66.field2;
            CursorTy pvrtmp_5746 = tmp_struct_66.field3;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2587, pvrtmp_5743, pvrtmp_5746, pvrtmp_5744);
            CursorTy pvrtmp_5751 = tmp_struct_67.field0;
            CursorTy pvrtmp_5752 = tmp_struct_67.field1;
            CursorTy pvrtmp_5753 = tmp_struct_67.field2;
            CursorTy pvrtmp_5754 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Tags(end_r_2587, pvrtmp_5751, pvrtmp_5754, pvrtmp_5752);
            CursorTy pvrtmp_5759 = tmp_struct_68.field0;
            CursorTy pvrtmp_5760 = tmp_struct_68.field1;
            CursorTy pvrtmp_5761 = tmp_struct_68.field2;
            CursorTy pvrtmp_5762 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2586 = 8;
            
            CursorTy writetag_4029 = loc_2586 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5759, pvrtmp_5760,
                                                   loc_2586, pvrtmp_5762};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5771 = *(CursorTy *) tmpcur_5558;
            CursorTy tmpaftercur_5772 = tmpcur_5558 + 8;
            CursorTy jump_3657 = tmpcur_5558 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Adt(end_r_2587, end_r_2588, loc_2586, tmpcur_5771);
            CursorTy pvrtmp_5773 = tmp_struct_69.field0;
            CursorTy pvrtmp_5774 = tmp_struct_69.field1;
            CursorTy pvrtmp_5775 = tmp_struct_69.field2;
            CursorTy pvrtmp_5776 = tmp_struct_69.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5773, jump_3657,
                                                   pvrtmp_5775, pvrtmp_5776};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5783 = *(CursorTy *) tmpcur_5558;
            CursorTy tmpaftercur_5784 = tmpcur_5558 + 8;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Adt(end_r_2587, end_r_2588, loc_2586, tmpcur_5783);
            CursorTy pvrtmp_5785 = tmp_struct_70.field0;
            CursorTy pvrtmp_5786 = tmp_struct_70.field1;
            CursorTy pvrtmp_5787 = tmp_struct_70.field2;
            CursorTy pvrtmp_5788 = tmp_struct_70.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5785, pvrtmp_5786,
                                                   pvrtmp_5787, pvrtmp_5788};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5557");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2591,
                                                    CursorTy end_r_2592,
                                                    CursorTy loc_2590,
                                                    CursorTy arg_730_1341_1650)
{
    TagTyPacked tmpval_5796 = *(TagTyPacked *) arg_730_1341_1650;
    CursorTy tmpcur_5797 = arg_730_1341_1650 + 1;
    
    
  switch_6034:
    ;
    switch (tmpval_5796) {
        
      case 0:
        {
            CursorTy jump_3434 = arg_730_1341_1650 + 1;
            
            *(TagTyPacked *) loc_2590 = 0;
            
            CursorTy writetag_4041 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2592, jump_3434,
                                                   loc_2590, writetag_4041};
            break;
        }
        
      case 1:
        {
            CursorTy loc_2882 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_without_ptrs_Content(end_r_2591, end_r_2592, loc_2882, tmpcur_5797);
            CursorTy pvrtmp_5802 = tmp_struct_74.field0;
            CursorTy pvrtmp_5803 = tmp_struct_74.field1;
            CursorTy pvrtmp_5804 = tmp_struct_74.field2;
            CursorTy pvrtmp_5805 = tmp_struct_74.field3;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_without_ptrs_Adt(end_r_2591, pvrtmp_5802, pvrtmp_5805, pvrtmp_5803);
            CursorTy pvrtmp_5810 = tmp_struct_75.field0;
            CursorTy pvrtmp_5811 = tmp_struct_75.field1;
            CursorTy pvrtmp_5812 = tmp_struct_75.field2;
            CursorTy pvrtmp_5813 = tmp_struct_75.field3;
            
            *(TagTyPacked *) loc_2590 = 1;
            
            CursorTy writetag_4046 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5810, pvrtmp_5811,
                                                   loc_2590, pvrtmp_5813};
            break;
        }
        
      case 2:
        {
            CursorTy loc_2894 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_without_ptrs_Adt(end_r_2591, end_r_2592, loc_2894, tmpcur_5797);
            CursorTy pvrtmp_5822 = tmp_struct_76.field0;
            CursorTy pvrtmp_5823 = tmp_struct_76.field1;
            CursorTy pvrtmp_5824 = tmp_struct_76.field2;
            CursorTy pvrtmp_5825 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_without_ptrs_Content(end_r_2591, pvrtmp_5822, pvrtmp_5825, pvrtmp_5823);
            CursorTy pvrtmp_5830 = tmp_struct_77.field0;
            CursorTy pvrtmp_5831 = tmp_struct_77.field1;
            CursorTy pvrtmp_5832 = tmp_struct_77.field2;
            CursorTy pvrtmp_5833 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2590 = 2;
            
            CursorTy writetag_4053 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5830, pvrtmp_5831,
                                                   loc_2590, pvrtmp_5833};
            break;
        }
        
      case 3:
        {
            CursorTy loc_2910 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_without_ptrs_Tags(end_r_2591, end_r_2592, loc_2910, tmpcur_5797);
            CursorTy pvrtmp_5842 = tmp_struct_78.field0;
            CursorTy pvrtmp_5843 = tmp_struct_78.field1;
            CursorTy pvrtmp_5844 = tmp_struct_78.field2;
            CursorTy pvrtmp_5845 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_without_ptrs_Content(end_r_2591, pvrtmp_5842, pvrtmp_5845, pvrtmp_5843);
            CursorTy pvrtmp_5850 = tmp_struct_79.field0;
            CursorTy pvrtmp_5851 = tmp_struct_79.field1;
            CursorTy pvrtmp_5852 = tmp_struct_79.field2;
            CursorTy pvrtmp_5853 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_without_ptrs_Adt(end_r_2591, pvrtmp_5850, pvrtmp_5853, pvrtmp_5851);
            CursorTy pvrtmp_5858 = tmp_struct_80.field0;
            CursorTy pvrtmp_5859 = tmp_struct_80.field1;
            CursorTy pvrtmp_5860 = tmp_struct_80.field2;
            CursorTy pvrtmp_5861 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2590 = 3;
            
            CursorTy writetag_4061 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5858, pvrtmp_5859,
                                                   loc_2590, pvrtmp_5861};
            break;
        }
        
      case 4:
        {
            CursorTy loc_2928 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_without_ptrs_Adt(end_r_2591, end_r_2592, loc_2928, tmpcur_5797);
            CursorTy pvrtmp_5870 = tmp_struct_81.field0;
            CursorTy pvrtmp_5871 = tmp_struct_81.field1;
            CursorTy pvrtmp_5872 = tmp_struct_81.field2;
            CursorTy pvrtmp_5873 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_without_ptrs_Content(end_r_2591, pvrtmp_5870, pvrtmp_5873, pvrtmp_5871);
            CursorTy pvrtmp_5878 = tmp_struct_82.field0;
            CursorTy pvrtmp_5879 = tmp_struct_82.field1;
            CursorTy pvrtmp_5880 = tmp_struct_82.field2;
            CursorTy pvrtmp_5881 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_without_ptrs_Tags(end_r_2591, pvrtmp_5878, pvrtmp_5881, pvrtmp_5879);
            CursorTy pvrtmp_5886 = tmp_struct_83.field0;
            CursorTy pvrtmp_5887 = tmp_struct_83.field1;
            CursorTy pvrtmp_5888 = tmp_struct_83.field2;
            CursorTy pvrtmp_5889 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2590 = 4;
            
            CursorTy writetag_4070 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5886, pvrtmp_5887,
                                                   loc_2590, pvrtmp_5889};
            break;
        }
        
      case 5:
        {
            CursorTy loc_2946 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_without_ptrs_Tags(end_r_2591, end_r_2592, loc_2946, tmpcur_5797);
            CursorTy pvrtmp_5898 = tmp_struct_84.field0;
            CursorTy pvrtmp_5899 = tmp_struct_84.field1;
            CursorTy pvrtmp_5900 = tmp_struct_84.field2;
            CursorTy pvrtmp_5901 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_without_ptrs_Adt(end_r_2591, pvrtmp_5898, pvrtmp_5901, pvrtmp_5899);
            CursorTy pvrtmp_5906 = tmp_struct_85.field0;
            CursorTy pvrtmp_5907 = tmp_struct_85.field1;
            CursorTy pvrtmp_5908 = tmp_struct_85.field2;
            CursorTy pvrtmp_5909 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_without_ptrs_Content(end_r_2591, pvrtmp_5906, pvrtmp_5909, pvrtmp_5907);
            CursorTy pvrtmp_5914 = tmp_struct_86.field0;
            CursorTy pvrtmp_5915 = tmp_struct_86.field1;
            CursorTy pvrtmp_5916 = tmp_struct_86.field2;
            CursorTy pvrtmp_5917 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2590 = 5;
            
            CursorTy writetag_4079 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5914, pvrtmp_5915,
                                                   loc_2590, pvrtmp_5917};
            break;
        }
        
      case 6:
        {
            CursorTy loc_2964 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_without_ptrs_Adt(end_r_2591, end_r_2592, loc_2964, tmpcur_5797);
            CursorTy pvrtmp_5926 = tmp_struct_87.field0;
            CursorTy pvrtmp_5927 = tmp_struct_87.field1;
            CursorTy pvrtmp_5928 = tmp_struct_87.field2;
            CursorTy pvrtmp_5929 = tmp_struct_87.field3;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_without_ptrs_Tags(end_r_2591, pvrtmp_5926, pvrtmp_5929, pvrtmp_5927);
            CursorTy pvrtmp_5934 = tmp_struct_88.field0;
            CursorTy pvrtmp_5935 = tmp_struct_88.field1;
            CursorTy pvrtmp_5936 = tmp_struct_88.field2;
            CursorTy pvrtmp_5937 = tmp_struct_88.field3;
            CursorCursorCursorCursorProd tmp_struct_89 =
                                          _copy_without_ptrs_Content(end_r_2591, pvrtmp_5934, pvrtmp_5937, pvrtmp_5935);
            CursorTy pvrtmp_5942 = tmp_struct_89.field0;
            CursorTy pvrtmp_5943 = tmp_struct_89.field1;
            CursorTy pvrtmp_5944 = tmp_struct_89.field2;
            CursorTy pvrtmp_5945 = tmp_struct_89.field3;
            
            *(TagTyPacked *) loc_2590 = 6;
            
            CursorTy writetag_4088 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5942, pvrtmp_5943,
                                                   loc_2590, pvrtmp_5945};
            break;
        }
        
      case 7:
        {
            CursorTy loc_2982 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_90 =
                                          _copy_without_ptrs_Content(end_r_2591, end_r_2592, loc_2982, tmpcur_5797);
            CursorTy pvrtmp_5954 = tmp_struct_90.field0;
            CursorTy pvrtmp_5955 = tmp_struct_90.field1;
            CursorTy pvrtmp_5956 = tmp_struct_90.field2;
            CursorTy pvrtmp_5957 = tmp_struct_90.field3;
            CursorCursorCursorCursorProd tmp_struct_91 =
                                          _copy_without_ptrs_Tags(end_r_2591, pvrtmp_5954, pvrtmp_5957, pvrtmp_5955);
            CursorTy pvrtmp_5962 = tmp_struct_91.field0;
            CursorTy pvrtmp_5963 = tmp_struct_91.field1;
            CursorTy pvrtmp_5964 = tmp_struct_91.field2;
            CursorTy pvrtmp_5965 = tmp_struct_91.field3;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Adt(end_r_2591, pvrtmp_5962, pvrtmp_5965, pvrtmp_5963);
            CursorTy pvrtmp_5970 = tmp_struct_92.field0;
            CursorTy pvrtmp_5971 = tmp_struct_92.field1;
            CursorTy pvrtmp_5972 = tmp_struct_92.field2;
            CursorTy pvrtmp_5973 = tmp_struct_92.field3;
            
            *(TagTyPacked *) loc_2590 = 7;
            
            CursorTy writetag_4097 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5970, pvrtmp_5971,
                                                   loc_2590, pvrtmp_5973};
            break;
        }
        
      case 8:
        {
            CursorTy loc_3000 = loc_2590 + 1;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Content(end_r_2591, end_r_2592, loc_3000, tmpcur_5797);
            CursorTy pvrtmp_5982 = tmp_struct_93.field0;
            CursorTy pvrtmp_5983 = tmp_struct_93.field1;
            CursorTy pvrtmp_5984 = tmp_struct_93.field2;
            CursorTy pvrtmp_5985 = tmp_struct_93.field3;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2591, pvrtmp_5982, pvrtmp_5985, pvrtmp_5983);
            CursorTy pvrtmp_5990 = tmp_struct_94.field0;
            CursorTy pvrtmp_5991 = tmp_struct_94.field1;
            CursorTy pvrtmp_5992 = tmp_struct_94.field2;
            CursorTy pvrtmp_5993 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Tags(end_r_2591, pvrtmp_5990, pvrtmp_5993, pvrtmp_5991);
            CursorTy pvrtmp_5998 = tmp_struct_95.field0;
            CursorTy pvrtmp_5999 = tmp_struct_95.field1;
            CursorTy pvrtmp_6000 = tmp_struct_95.field2;
            CursorTy pvrtmp_6001 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2590 = 8;
            
            CursorTy writetag_4106 = loc_2590 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5998, pvrtmp_5999,
                                                   loc_2590, pvrtmp_6001};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6010 = *(CursorTy *) tmpcur_5797;
            CursorTy tmpaftercur_6011 = tmpcur_5797 + 8;
            CursorTy jump_3663 = tmpcur_5797 + 8;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Adt(end_r_2591, end_r_2592, loc_2590, tmpcur_6010);
            CursorTy pvrtmp_6012 = tmp_struct_96.field0;
            CursorTy pvrtmp_6013 = tmp_struct_96.field1;
            CursorTy pvrtmp_6014 = tmp_struct_96.field2;
            CursorTy pvrtmp_6015 = tmp_struct_96.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6012, jump_3663,
                                                   pvrtmp_6014, pvrtmp_6015};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6022 = *(CursorTy *) tmpcur_5797;
            CursorTy tmpaftercur_6023 = tmpcur_5797 + 8;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Adt(end_r_2591, end_r_2592, loc_2590, tmpcur_6022);
            CursorTy pvrtmp_6024 = tmp_struct_97.field0;
            CursorTy pvrtmp_6025 = tmp_struct_97.field1;
            CursorTy pvrtmp_6026 = tmp_struct_97.field2;
            CursorTy pvrtmp_6027 = tmp_struct_97.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6024, pvrtmp_6025,
                                                   pvrtmp_6026, pvrtmp_6027};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5796");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2594, CursorTy arg_775_1386_1695)
{
    TagTyPacked tmpval_6035 = *(TagTyPacked *) arg_775_1386_1695;
    CursorTy tmpcur_6036 = arg_775_1386_1695 + 1;
    
    
  switch_6065:
    ;
    switch (tmpval_6035) {
        
      case 0:
        {
            CursorTy jump_3466 = arg_775_1386_1695 + 1;
            
            return (CursorProd) {jump_3466};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_98 =
                        _traverse_Content(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6037 = tmp_struct_98.field0;
            CursorProd tmp_struct_99 =  _traverse_Adt(end_r_2594, pvrtmp_6037);
            CursorTy pvrtmp_6038 = tmp_struct_99.field0;
            
            return (CursorProd) {pvrtmp_6038};
            break;
        }
        
      case 2:
        {
            CursorProd tmp_struct_100 =  _traverse_Adt(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6039 = tmp_struct_100.field0;
            CursorProd tmp_struct_101 =
                        _traverse_Content(end_r_2594, pvrtmp_6039);
            CursorTy pvrtmp_6040 = tmp_struct_101.field0;
            
            return (CursorProd) {pvrtmp_6040};
            break;
        }
        
      case 3:
        {
            CursorProd tmp_struct_102 =
                        _traverse_Tags(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6041 = tmp_struct_102.field0;
            CursorProd tmp_struct_103 =
                        _traverse_Content(end_r_2594, pvrtmp_6041);
            CursorTy pvrtmp_6042 = tmp_struct_103.field0;
            CursorProd tmp_struct_104 =  _traverse_Adt(end_r_2594, pvrtmp_6042);
            CursorTy pvrtmp_6043 = tmp_struct_104.field0;
            
            return (CursorProd) {pvrtmp_6043};
            break;
        }
        
      case 4:
        {
            CursorProd tmp_struct_105 =  _traverse_Adt(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6044 = tmp_struct_105.field0;
            CursorProd tmp_struct_106 =
                        _traverse_Content(end_r_2594, pvrtmp_6044);
            CursorTy pvrtmp_6045 = tmp_struct_106.field0;
            CursorProd tmp_struct_107 =
                        _traverse_Tags(end_r_2594, pvrtmp_6045);
            CursorTy pvrtmp_6046 = tmp_struct_107.field0;
            
            return (CursorProd) {pvrtmp_6046};
            break;
        }
        
      case 5:
        {
            CursorProd tmp_struct_108 =
                        _traverse_Tags(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6047 = tmp_struct_108.field0;
            CursorProd tmp_struct_109 =  _traverse_Adt(end_r_2594, pvrtmp_6047);
            CursorTy pvrtmp_6048 = tmp_struct_109.field0;
            CursorProd tmp_struct_110 =
                        _traverse_Content(end_r_2594, pvrtmp_6048);
            CursorTy pvrtmp_6049 = tmp_struct_110.field0;
            
            return (CursorProd) {pvrtmp_6049};
            break;
        }
        
      case 6:
        {
            CursorProd tmp_struct_111 =  _traverse_Adt(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6050 = tmp_struct_111.field0;
            CursorProd tmp_struct_112 =
                        _traverse_Tags(end_r_2594, pvrtmp_6050);
            CursorTy pvrtmp_6051 = tmp_struct_112.field0;
            CursorProd tmp_struct_113 =
                        _traverse_Content(end_r_2594, pvrtmp_6051);
            CursorTy pvrtmp_6052 = tmp_struct_113.field0;
            
            return (CursorProd) {pvrtmp_6052};
            break;
        }
        
      case 7:
        {
            CursorProd tmp_struct_114 =
                        _traverse_Content(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6053 = tmp_struct_114.field0;
            CursorProd tmp_struct_115 =
                        _traverse_Tags(end_r_2594, pvrtmp_6053);
            CursorTy pvrtmp_6054 = tmp_struct_115.field0;
            CursorProd tmp_struct_116 =  _traverse_Adt(end_r_2594, pvrtmp_6054);
            CursorTy pvrtmp_6055 = tmp_struct_116.field0;
            
            return (CursorProd) {pvrtmp_6055};
            break;
        }
        
      case 8:
        {
            CursorProd tmp_struct_117 =
                        _traverse_Content(end_r_2594, tmpcur_6036);
            CursorTy pvrtmp_6056 = tmp_struct_117.field0;
            CursorProd tmp_struct_118 =  _traverse_Adt(end_r_2594, pvrtmp_6056);
            CursorTy pvrtmp_6057 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Tags(end_r_2594, pvrtmp_6057);
            CursorTy pvrtmp_6058 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_6058};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6059 = *(CursorTy *) tmpcur_6036;
            CursorTy tmpaftercur_6060 = tmpcur_6036 + 8;
            CursorTy jump_3669 = tmpcur_6036 + 8;
            CursorProd tmp_struct_120 =  _traverse_Adt(end_r_2594, tmpcur_6059);
            CursorTy pvrtmp_6061 = tmp_struct_120.field0;
            
            return (CursorProd) {jump_3669};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6062 = *(CursorTy *) tmpcur_6036;
            CursorTy tmpaftercur_6063 = tmpcur_6036 + 8;
            CursorProd tmp_struct_121 =  _traverse_Adt(end_r_2594, tmpcur_6062);
            CursorTy pvrtmp_6064 = tmp_struct_121.field0;
            
            return (CursorProd) {pvrtmp_6064};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6035");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2596, CursorTy arg_820_1431_1740)
{
    TagTyPacked tmpval_6066 = *(TagTyPacked *) arg_820_1431_1740;
    CursorTy tmpcur_6067 = arg_820_1431_1740 + 1;
    
    
  switch_6096:
    ;
    switch (tmpval_6066) {
        
      case 0:
        {
            CursorTy jump_3498 = arg_820_1431_1740 + 1;
            unsigned char wildcard_821_1432_1741 = print_symbol(5243);
            unsigned char wildcard_822_1433_1742 = print_symbol(5237);
            
            return (CursorProd) {jump_3498};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_827_1436_1745 = print_symbol(5249);
            CursorProd tmp_struct_122 =
                        _print_Content(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6068 = tmp_struct_122.field0;
            CursorProd tmp_struct_123 =  _print_Adt(end_r_2596, pvrtmp_6068);
            CursorTy pvrtmp_6069 = tmp_struct_123.field0;
            unsigned char wildcard_828_1439_1748 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6069};
            break;
        }
        
      case 2:
        {
            unsigned char wildcard_833_1442_1751 = print_symbol(5252);
            CursorProd tmp_struct_124 =  _print_Adt(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6070 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _print_Content(end_r_2596, pvrtmp_6070);
            CursorTy pvrtmp_6071 = tmp_struct_125.field0;
            unsigned char wildcard_834_1445_1754 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6071};
            break;
        }
        
      case 3:
        {
            unsigned char wildcard_841_1449_1758 = print_symbol(5240);
            CursorProd tmp_struct_126 =  _print_Tags(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6072 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =
                        _print_Content(end_r_2596, pvrtmp_6072);
            CursorTy pvrtmp_6073 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =  _print_Adt(end_r_2596, pvrtmp_6073);
            CursorTy pvrtmp_6074 = tmp_struct_128.field0;
            unsigned char wildcard_842_1453_1762 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6074};
            break;
        }
        
      case 4:
        {
            unsigned char wildcard_849_1457_1766 = print_symbol(5251);
            CursorProd tmp_struct_129 =  _print_Adt(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6075 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _print_Content(end_r_2596, pvrtmp_6075);
            CursorTy pvrtmp_6076 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =  _print_Tags(end_r_2596, pvrtmp_6076);
            CursorTy pvrtmp_6077 = tmp_struct_131.field0;
            unsigned char wildcard_850_1461_1770 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6077};
            break;
        }
        
      case 5:
        {
            unsigned char wildcard_857_1465_1774 = print_symbol(5241);
            CursorProd tmp_struct_132 =  _print_Tags(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6078 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =  _print_Adt(end_r_2596, pvrtmp_6078);
            CursorTy pvrtmp_6079 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =
                        _print_Content(end_r_2596, pvrtmp_6079);
            CursorTy pvrtmp_6080 = tmp_struct_134.field0;
            unsigned char wildcard_858_1469_1778 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6080};
            break;
        }
        
      case 6:
        {
            unsigned char wildcard_865_1473_1782 = print_symbol(5250);
            CursorProd tmp_struct_135 =  _print_Adt(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6081 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _print_Tags(end_r_2596, pvrtmp_6081);
            CursorTy pvrtmp_6082 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _print_Content(end_r_2596, pvrtmp_6082);
            CursorTy pvrtmp_6083 = tmp_struct_137.field0;
            unsigned char wildcard_866_1477_1786 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6083};
            break;
        }
        
      case 7:
        {
            unsigned char wildcard_873_1481_1790 = print_symbol(5247);
            CursorProd tmp_struct_138 =
                        _print_Content(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6084 = tmp_struct_138.field0;
            CursorProd tmp_struct_139 =  _print_Tags(end_r_2596, pvrtmp_6084);
            CursorTy pvrtmp_6085 = tmp_struct_139.field0;
            CursorProd tmp_struct_140 =  _print_Adt(end_r_2596, pvrtmp_6085);
            CursorTy pvrtmp_6086 = tmp_struct_140.field0;
            unsigned char wildcard_874_1485_1794 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6086};
            break;
        }
        
      case 8:
        {
            unsigned char wildcard_881_1489_1798 = print_symbol(5248);
            CursorProd tmp_struct_141 =
                        _print_Content(end_r_2596, tmpcur_6067);
            CursorTy pvrtmp_6087 = tmp_struct_141.field0;
            CursorProd tmp_struct_142 =  _print_Adt(end_r_2596, pvrtmp_6087);
            CursorTy pvrtmp_6088 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =  _print_Tags(end_r_2596, pvrtmp_6088);
            CursorTy pvrtmp_6089 = tmp_struct_143.field0;
            unsigned char wildcard_882_1493_1802 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6089};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6090 = *(CursorTy *) tmpcur_6067;
            CursorTy tmpaftercur_6091 = tmpcur_6067 + 8;
            CursorTy jump_3675 = tmpcur_6067 + 8;
            unsigned char wildcard_3678 = print_symbol(5254);
            CursorProd tmp_struct_144 =  _print_Adt(end_r_2596, tmpcur_6090);
            CursorTy pvrtmp_6092 = tmp_struct_144.field0;
            
            return (CursorProd) {jump_3675};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6093 = *(CursorTy *) tmpcur_6067;
            CursorTy tmpaftercur_6094 = tmpcur_6067 + 8;
            unsigned char wildcard_3678 = print_symbol(5253);
            CursorProd tmp_struct_145 =  _print_Adt(end_r_2596, tmpcur_6093);
            CursorTy pvrtmp_6095 = tmp_struct_145.field0;
            
            return (CursorProd) {pvrtmp_6095};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6066");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2599,
                                        CursorTy end_r_2600, CursorTy loc_2598,
                                        CursorTy arg_883_1494_1803)
{
    if (loc_2598 + 32 > end_r_2600) {
        ChunkTy new_chunk_149 = alloc_chunk(end_r_2600);
        CursorTy chunk_start_150 = new_chunk_149.chunk_start;
        CursorTy chunk_end_151 = new_chunk_149.chunk_end;
        
        end_r_2600 = chunk_end_151;
        *(TagTyPacked *) loc_2598 = 255;
        
        CursorTy redir = loc_2598 + 1;
        
        *(CursorTy *) redir = chunk_start_150;
        loc_2598 = chunk_start_150;
    }
    
    CursorTy loc_3150 = loc_2598 + 1;
    CursorTy loc_3151 = loc_3150 + 8;
    TagTyPacked tmpval_6097 = *(TagTyPacked *) arg_883_1494_1803;
    CursorTy tmpcur_6098 = arg_883_1494_1803 + 1;
    
    
  switch_6141:
    ;
    switch (tmpval_6097) {
        
      case 0:
        {
            CursorTy jump_3530 = arg_883_1494_1803 + 1;
            
            *(TagTyPacked *) loc_2598 = 0;
            
            CursorTy writetag_4192 = loc_2598 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2600, jump_3530,
                                                   loc_2598, writetag_4192};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6103 = *(IntTy *) tmpcur_6098;
            CursorTy tmpcur_6104 = tmpcur_6098 + sizeof(IntTy);
            CursorTy jump_3532 = tmpcur_6098 + 8;
            CursorCursorCursorCursorProd tmp_struct_146 =
                                          _copy_Tags(end_r_2599, end_r_2600, loc_3151, tmpcur_6104);
            CursorTy pvrtmp_6105 = tmp_struct_146.field0;
            CursorTy pvrtmp_6106 = tmp_struct_146.field1;
            CursorTy pvrtmp_6107 = tmp_struct_146.field2;
            CursorTy pvrtmp_6108 = tmp_struct_146.field3;
            
            *(TagTyPacked *) loc_2598 = 1;
            
            CursorTy writetag_4197 = loc_2598 + 1;
            
            *(IntTy *) writetag_4197 = tmpval_6103;
            
            CursorTy writecur_4198 = writetag_4197 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6105, pvrtmp_6106,
                                                   loc_2598, pvrtmp_6108};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6117 = *(CursorTy *) tmpcur_6098;
            CursorTy tmpaftercur_6118 = tmpcur_6098 + 8;
            CursorTy jump_3681 = tmpcur_6098 + 8;
            CursorCursorCursorCursorProd tmp_struct_147 =
                                          _copy_Tags(end_r_2599, end_r_2600, loc_2598, tmpcur_6117);
            CursorTy pvrtmp_6119 = tmp_struct_147.field0;
            CursorTy pvrtmp_6120 = tmp_struct_147.field1;
            CursorTy pvrtmp_6121 = tmp_struct_147.field2;
            CursorTy pvrtmp_6122 = tmp_struct_147.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6119, jump_3681,
                                                   pvrtmp_6121, pvrtmp_6122};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6129 = *(CursorTy *) tmpcur_6098;
            CursorTy tmpaftercur_6130 = tmpcur_6098 + 8;
            CursorCursorCursorCursorProd tmp_struct_148 =
                                          _copy_Tags(end_r_2599, end_r_2600, loc_2598, tmpcur_6129);
            CursorTy pvrtmp_6131 = tmp_struct_148.field0;
            CursorTy pvrtmp_6132 = tmp_struct_148.field1;
            CursorTy pvrtmp_6133 = tmp_struct_148.field2;
            CursorTy pvrtmp_6134 = tmp_struct_148.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6131, pvrtmp_6132,
                                                   pvrtmp_6133, pvrtmp_6134};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6097");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2603,
                                                     CursorTy end_r_2604,
                                                     CursorTy loc_2602,
                                                     CursorTy arg_888_1499_1808)
{
    CursorTy loc_3163 = loc_2602 + 1;
    CursorTy loc_3164 = loc_3163 + 8;
    TagTyPacked tmpval_6142 = *(TagTyPacked *) arg_888_1499_1808;
    CursorTy tmpcur_6143 = arg_888_1499_1808 + 1;
    
    
  switch_6186:
    ;
    switch (tmpval_6142) {
        
      case 0:
        {
            CursorTy jump_3535 = arg_888_1499_1808 + 1;
            
            *(TagTyPacked *) loc_2602 = 0;
            
            CursorTy writetag_4208 = loc_2602 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2604, jump_3535,
                                                   loc_2602, writetag_4208};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6148 = *(IntTy *) tmpcur_6143;
            CursorTy tmpcur_6149 = tmpcur_6143 + sizeof(IntTy);
            CursorTy jump_3537 = tmpcur_6143 + 8;
            CursorCursorCursorCursorProd tmp_struct_152 =
                                          _copy_without_ptrs_Tags(end_r_2603, end_r_2604, loc_3164, tmpcur_6149);
            CursorTy pvrtmp_6150 = tmp_struct_152.field0;
            CursorTy pvrtmp_6151 = tmp_struct_152.field1;
            CursorTy pvrtmp_6152 = tmp_struct_152.field2;
            CursorTy pvrtmp_6153 = tmp_struct_152.field3;
            
            *(TagTyPacked *) loc_2602 = 1;
            
            CursorTy writetag_4213 = loc_2602 + 1;
            
            *(IntTy *) writetag_4213 = tmpval_6148;
            
            CursorTy writecur_4214 = writetag_4213 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6150, pvrtmp_6151,
                                                   loc_2602, pvrtmp_6153};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6162 = *(CursorTy *) tmpcur_6143;
            CursorTy tmpaftercur_6163 = tmpcur_6143 + 8;
            CursorTy jump_3687 = tmpcur_6143 + 8;
            CursorCursorCursorCursorProd tmp_struct_153 =
                                          _copy_without_ptrs_Tags(end_r_2603, end_r_2604, loc_2602, tmpcur_6162);
            CursorTy pvrtmp_6164 = tmp_struct_153.field0;
            CursorTy pvrtmp_6165 = tmp_struct_153.field1;
            CursorTy pvrtmp_6166 = tmp_struct_153.field2;
            CursorTy pvrtmp_6167 = tmp_struct_153.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6164, jump_3687,
                                                   pvrtmp_6166, pvrtmp_6167};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6174 = *(CursorTy *) tmpcur_6143;
            CursorTy tmpaftercur_6175 = tmpcur_6143 + 8;
            CursorCursorCursorCursorProd tmp_struct_154 =
                                          _copy_without_ptrs_Tags(end_r_2603, end_r_2604, loc_2602, tmpcur_6174);
            CursorTy pvrtmp_6176 = tmp_struct_154.field0;
            CursorTy pvrtmp_6177 = tmp_struct_154.field1;
            CursorTy pvrtmp_6178 = tmp_struct_154.field2;
            CursorTy pvrtmp_6179 = tmp_struct_154.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6176, pvrtmp_6177,
                                                   pvrtmp_6178, pvrtmp_6179};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6142");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_2606, CursorTy arg_893_1504_1813)
{
    TagTyPacked tmpval_6187 = *(TagTyPacked *) arg_893_1504_1813;
    CursorTy tmpcur_6188 = arg_893_1504_1813 + 1;
    
    
  switch_6198:
    ;
    switch (tmpval_6187) {
        
      case 0:
        {
            CursorTy jump_3540 = arg_893_1504_1813 + 1;
            
            return (CursorProd) {jump_3540};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6189 = *(IntTy *) tmpcur_6188;
            CursorTy tmpcur_6190 = tmpcur_6188 + sizeof(IntTy);
            CursorTy jump_3542 = tmpcur_6188 + 8;
            CursorProd tmp_struct_155 =
                        _traverse_Tags(end_r_2606, tmpcur_6190);
            CursorTy pvrtmp_6191 = tmp_struct_155.field0;
            
            return (CursorProd) {pvrtmp_6191};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6192 = *(CursorTy *) tmpcur_6188;
            CursorTy tmpaftercur_6193 = tmpcur_6188 + 8;
            CursorTy jump_3693 = tmpcur_6188 + 8;
            CursorProd tmp_struct_156 =
                        _traverse_Tags(end_r_2606, tmpcur_6192);
            CursorTy pvrtmp_6194 = tmp_struct_156.field0;
            
            return (CursorProd) {jump_3693};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6195 = *(CursorTy *) tmpcur_6188;
            CursorTy tmpaftercur_6196 = tmpcur_6188 + 8;
            CursorProd tmp_struct_157 =
                        _traverse_Tags(end_r_2606, tmpcur_6195);
            CursorTy pvrtmp_6197 = tmp_struct_157.field0;
            
            return (CursorProd) {pvrtmp_6197};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6187");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_2608, CursorTy arg_898_1508_1817)
{
    TagTyPacked tmpval_6199 = *(TagTyPacked *) arg_898_1508_1817;
    CursorTy tmpcur_6200 = arg_898_1508_1817 + 1;
    
    
  switch_6210:
    ;
    switch (tmpval_6199) {
        
      case 0:
        {
            CursorTy jump_3545 = arg_898_1508_1817 + 1;
            unsigned char wildcard_899_1509_1818 = print_symbol(5242);
            unsigned char wildcard_900_1510_1819 = print_symbol(5237);
            
            return (CursorProd) {jump_3545};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6201 = *(IntTy *) tmpcur_6200;
            CursorTy tmpcur_6202 = tmpcur_6200 + sizeof(IntTy);
            CursorTy jump_3547 = tmpcur_6200 + 8;
            unsigned char wildcard_905_1513_1822 = print_symbol(5239);
            unsigned char y_903_1514_1823 = printf("%lld", tmpval_6201);
            CursorProd tmp_struct_158 =  _print_Tags(end_r_2608, tmpcur_6202);
            CursorTy pvrtmp_6203 = tmp_struct_158.field0;
            unsigned char wildcard_906_1516_1825 = print_symbol(5237);
            
            return (CursorProd) {pvrtmp_6203};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6204 = *(CursorTy *) tmpcur_6200;
            CursorTy tmpaftercur_6205 = tmpcur_6200 + 8;
            CursorTy jump_3699 = tmpcur_6200 + 8;
            unsigned char wildcard_3702 = print_symbol(5254);
            CursorProd tmp_struct_159 =  _print_Tags(end_r_2608, tmpcur_6204);
            CursorTy pvrtmp_6206 = tmp_struct_159.field0;
            
            return (CursorProd) {jump_3699};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6207 = *(CursorTy *) tmpcur_6200;
            CursorTy tmpaftercur_6208 = tmpcur_6200 + 8;
            unsigned char wildcard_3702 = print_symbol(5253);
            CursorProd tmp_struct_160 =  _print_Tags(end_r_2608, tmpcur_6207);
            CursorTy pvrtmp_6209 = tmp_struct_160.field0;
            
            return (CursorProd) {pvrtmp_6209};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6199");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_2611,
                                                              CursorTy end_r_2612,
                                                              CursorTy loc_2610,
                                                              CursorTy arg_2467)
{
    if (loc_2610 + 32 > end_r_2612) {
        ChunkTy new_chunk_164 = alloc_chunk(end_r_2612);
        CursorTy chunk_start_165 = new_chunk_164.chunk_start;
        CursorTy chunk_end_166 = new_chunk_164.chunk_end;
        
        end_r_2612 = chunk_end_166;
        *(TagTyPacked *) loc_2610 = 255;
        
        CursorTy redir = loc_2610 + 1;
        
        *(CursorTy *) redir = chunk_start_165;
        loc_2610 = chunk_start_165;
    }
    
    CursorTy loc_3188 = loc_2610 + 1;
    CursorTy loc_3189 = loc_3188 + 8;
    TagTyPacked tmpval_6211 = *(TagTyPacked *) arg_2467;
    CursorTy tmpcur_6212 = arg_2467 + 1;
    
    
  switch_6255:
    ;
    switch (tmpval_6211) {
        
      case 0:
        {
            CursorTy jump_3550 = arg_2467 + 1;
            
            *(TagTyPacked *) loc_2610 = 0;
            
            CursorTy writetag_4244 = loc_2610 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2612, jump_3550,
                                                   loc_2610, writetag_4244};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6217 = *(IntTy *) tmpcur_6212;
            CursorTy tmpcur_6218 = tmpcur_6212 + sizeof(IntTy);
            CursorTy jump_3552 = tmpcur_6212 + 8;
            CursorCursorCursorCursorProd tmp_struct_161 =
                                          _add_size_and_rel_offsets_String(end_r_2611, end_r_2612, loc_3189, tmpcur_6218);
            CursorTy pvrtmp_6219 = tmp_struct_161.field0;
            CursorTy pvrtmp_6220 = tmp_struct_161.field1;
            CursorTy pvrtmp_6221 = tmp_struct_161.field2;
            CursorTy pvrtmp_6222 = tmp_struct_161.field3;
            
            *(TagTyPacked *) loc_2610 = 1;
            
            CursorTy writetag_4249 = loc_2610 + 1;
            
            *(IntTy *) writetag_4249 = tmpval_6217;
            
            CursorTy writecur_4250 = writetag_4249 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6219, pvrtmp_6220,
                                                   loc_2610, pvrtmp_6222};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6231 = *(CursorTy *) tmpcur_6212;
            CursorTy tmpaftercur_6232 = tmpcur_6212 + 8;
            CursorTy jump_3705 = tmpcur_6212 + 8;
            CursorCursorCursorCursorProd tmp_struct_162 =
                                          _add_size_and_rel_offsets_String(end_r_2611, end_r_2612, loc_2610, tmpcur_6231);
            CursorTy pvrtmp_6233 = tmp_struct_162.field0;
            CursorTy pvrtmp_6234 = tmp_struct_162.field1;
            CursorTy pvrtmp_6235 = tmp_struct_162.field2;
            CursorTy pvrtmp_6236 = tmp_struct_162.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6233, jump_3705,
                                                   pvrtmp_6235, pvrtmp_6236};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6243 = *(CursorTy *) tmpcur_6212;
            CursorTy tmpaftercur_6244 = tmpcur_6212 + 8;
            CursorCursorCursorCursorProd tmp_struct_163 =
                                          _add_size_and_rel_offsets_String(end_r_2611, end_r_2612, loc_2610, tmpcur_6243);
            CursorTy pvrtmp_6245 = tmp_struct_163.field0;
            CursorTy pvrtmp_6246 = tmp_struct_163.field1;
            CursorTy pvrtmp_6247 = tmp_struct_163.field2;
            CursorTy pvrtmp_6248 = tmp_struct_163.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6245, pvrtmp_6246,
                                                   pvrtmp_6247, pvrtmp_6248};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6211");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_2615,
                                                               CursorTy end_r_2616,
                                                               CursorTy loc_2614,
                                                               CursorTy arg_2472)
{
    if (loc_2614 + 32 > end_r_2616) {
        ChunkTy new_chunk_171 = alloc_chunk(end_r_2616);
        CursorTy chunk_start_172 = new_chunk_171.chunk_start;
        CursorTy chunk_end_173 = new_chunk_171.chunk_end;
        
        end_r_2616 = chunk_end_173;
        *(TagTyPacked *) loc_2614 = 255;
        
        CursorTy redir = loc_2614 + 1;
        
        *(CursorTy *) redir = chunk_start_172;
        loc_2614 = chunk_start_172;
    }
    
    TagTyPacked tmpval_6256 = *(TagTyPacked *) arg_2472;
    CursorTy tmpcur_6257 = arg_2472 + 1;
    
    
  switch_6306:
    ;
    switch (tmpval_6256) {
        
      case 0:
        {
            CursorTy loc_3199 = loc_2614 + 1;
            CursorCursorCursorCursorProd tmp_struct_167 =
                                          _add_size_and_rel_offsets_String(end_r_2615, end_r_2616, loc_3199, tmpcur_6257);
            CursorTy pvrtmp_6258 = tmp_struct_167.field0;
            CursorTy pvrtmp_6259 = tmp_struct_167.field1;
            CursorTy pvrtmp_6260 = tmp_struct_167.field2;
            CursorTy pvrtmp_6261 = tmp_struct_167.field3;
            
            *(TagTyPacked *) loc_2614 = 0;
            
            CursorTy writetag_4261 = loc_2614 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6258, pvrtmp_6259,
                                                   loc_2614, pvrtmp_6261};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3205 = loc_2614 + 1;
            CursorCursorCursorCursorProd tmp_struct_168 =
                                          _add_size_and_rel_offsets_String(end_r_2615, end_r_2616, loc_3205, tmpcur_6257);
            CursorTy pvrtmp_6270 = tmp_struct_168.field0;
            CursorTy pvrtmp_6271 = tmp_struct_168.field1;
            CursorTy pvrtmp_6272 = tmp_struct_168.field2;
            CursorTy pvrtmp_6273 = tmp_struct_168.field3;
            
            *(TagTyPacked *) loc_2614 = 1;
            
            CursorTy writetag_4266 = loc_2614 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6270, pvrtmp_6271,
                                                   loc_2614, pvrtmp_6273};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6282 = *(CursorTy *) tmpcur_6257;
            CursorTy tmpaftercur_6283 = tmpcur_6257 + 8;
            CursorTy jump_3711 = tmpcur_6257 + 8;
            CursorCursorCursorCursorProd tmp_struct_169 =
                                          _add_size_and_rel_offsets_Content(end_r_2615, end_r_2616, loc_2614, tmpcur_6282);
            CursorTy pvrtmp_6284 = tmp_struct_169.field0;
            CursorTy pvrtmp_6285 = tmp_struct_169.field1;
            CursorTy pvrtmp_6286 = tmp_struct_169.field2;
            CursorTy pvrtmp_6287 = tmp_struct_169.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6284, jump_3711,
                                                   pvrtmp_6286, pvrtmp_6287};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6294 = *(CursorTy *) tmpcur_6257;
            CursorTy tmpaftercur_6295 = tmpcur_6257 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _add_size_and_rel_offsets_Content(end_r_2615, end_r_2616, loc_2614, tmpcur_6294);
            CursorTy pvrtmp_6296 = tmp_struct_170.field0;
            CursorTy pvrtmp_6297 = tmp_struct_170.field1;
            CursorTy pvrtmp_6298 = tmp_struct_170.field2;
            CursorTy pvrtmp_6299 = tmp_struct_170.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6296, pvrtmp_6297,
                                                   pvrtmp_6298, pvrtmp_6299};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6256");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2619,
                                                           CursorTy end_r_2620,
                                                           CursorTy loc_2618,
                                                           CursorTy arg_2477)
{
    if (loc_2618 + 32 > end_r_2620) {
        ChunkTy new_chunk_198 = alloc_chunk(end_r_2620);
        CursorTy chunk_start_199 = new_chunk_198.chunk_start;
        CursorTy chunk_end_200 = new_chunk_198.chunk_end;
        
        end_r_2620 = chunk_end_200;
        *(TagTyPacked *) loc_2618 = 255;
        
        CursorTy redir = loc_2618 + 1;
        
        *(CursorTy *) redir = chunk_start_199;
        loc_2618 = chunk_start_199;
    }
    
    TagTyPacked tmpval_6307 = *(TagTyPacked *) arg_2477;
    CursorTy tmpcur_6308 = arg_2477 + 1;
    
    
  switch_6545:
    ;
    switch (tmpval_6307) {
        
      case 0:
        {
            CursorTy jump_3559 = arg_2477 + 1;
            
            *(TagTyPacked *) loc_2618 = 0;
            
            CursorTy writetag_4276 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2620, jump_3559,
                                                   loc_2618, writetag_4276};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3218 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_174 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, end_r_2620, loc_3218, tmpcur_6308);
            CursorTy pvrtmp_6313 = tmp_struct_174.field0;
            CursorTy pvrtmp_6314 = tmp_struct_174.field1;
            CursorTy pvrtmp_6315 = tmp_struct_174.field2;
            CursorTy pvrtmp_6316 = tmp_struct_174.field3;
            CursorCursorCursorCursorProd tmp_struct_175 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, pvrtmp_6313, pvrtmp_6316, pvrtmp_6314);
            CursorTy pvrtmp_6321 = tmp_struct_175.field0;
            CursorTy pvrtmp_6322 = tmp_struct_175.field1;
            CursorTy pvrtmp_6323 = tmp_struct_175.field2;
            CursorTy pvrtmp_6324 = tmp_struct_175.field3;
            
            *(TagTyPacked *) loc_2618 = 1;
            
            CursorTy writetag_4281 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6321, pvrtmp_6322,
                                                   loc_2618, pvrtmp_6324};
            break;
        }
        
      case 2:
        {
            CursorTy loc_3230 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_176 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, end_r_2620, loc_3230, tmpcur_6308);
            CursorTy pvrtmp_6333 = tmp_struct_176.field0;
            CursorTy pvrtmp_6334 = tmp_struct_176.field1;
            CursorTy pvrtmp_6335 = tmp_struct_176.field2;
            CursorTy pvrtmp_6336 = tmp_struct_176.field3;
            CursorCursorCursorCursorProd tmp_struct_177 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, pvrtmp_6333, pvrtmp_6336, pvrtmp_6334);
            CursorTy pvrtmp_6341 = tmp_struct_177.field0;
            CursorTy pvrtmp_6342 = tmp_struct_177.field1;
            CursorTy pvrtmp_6343 = tmp_struct_177.field2;
            CursorTy pvrtmp_6344 = tmp_struct_177.field3;
            
            *(TagTyPacked *) loc_2618 = 2;
            
            CursorTy writetag_4288 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6341, pvrtmp_6342,
                                                   loc_2618, pvrtmp_6344};
            break;
        }
        
      case 3:
        {
            CursorTy loc_3246 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_178 =
                                          _add_size_and_rel_offsets_Tags(end_r_2619, end_r_2620, loc_3246, tmpcur_6308);
            CursorTy pvrtmp_6353 = tmp_struct_178.field0;
            CursorTy pvrtmp_6354 = tmp_struct_178.field1;
            CursorTy pvrtmp_6355 = tmp_struct_178.field2;
            CursorTy pvrtmp_6356 = tmp_struct_178.field3;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, pvrtmp_6353, pvrtmp_6356, pvrtmp_6354);
            CursorTy pvrtmp_6361 = tmp_struct_179.field0;
            CursorTy pvrtmp_6362 = tmp_struct_179.field1;
            CursorTy pvrtmp_6363 = tmp_struct_179.field2;
            CursorTy pvrtmp_6364 = tmp_struct_179.field3;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, pvrtmp_6361, pvrtmp_6364, pvrtmp_6362);
            CursorTy pvrtmp_6369 = tmp_struct_180.field0;
            CursorTy pvrtmp_6370 = tmp_struct_180.field1;
            CursorTy pvrtmp_6371 = tmp_struct_180.field2;
            CursorTy pvrtmp_6372 = tmp_struct_180.field3;
            
            *(TagTyPacked *) loc_2618 = 3;
            
            CursorTy writetag_4296 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6369, pvrtmp_6370,
                                                   loc_2618, pvrtmp_6372};
            break;
        }
        
      case 4:
        {
            CursorTy loc_3264 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, end_r_2620, loc_3264, tmpcur_6308);
            CursorTy pvrtmp_6381 = tmp_struct_181.field0;
            CursorTy pvrtmp_6382 = tmp_struct_181.field1;
            CursorTy pvrtmp_6383 = tmp_struct_181.field2;
            CursorTy pvrtmp_6384 = tmp_struct_181.field3;
            CursorCursorCursorCursorProd tmp_struct_182 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, pvrtmp_6381, pvrtmp_6384, pvrtmp_6382);
            CursorTy pvrtmp_6389 = tmp_struct_182.field0;
            CursorTy pvrtmp_6390 = tmp_struct_182.field1;
            CursorTy pvrtmp_6391 = tmp_struct_182.field2;
            CursorTy pvrtmp_6392 = tmp_struct_182.field3;
            CursorCursorCursorCursorProd tmp_struct_183 =
                                          _add_size_and_rel_offsets_Tags(end_r_2619, pvrtmp_6389, pvrtmp_6392, pvrtmp_6390);
            CursorTy pvrtmp_6397 = tmp_struct_183.field0;
            CursorTy pvrtmp_6398 = tmp_struct_183.field1;
            CursorTy pvrtmp_6399 = tmp_struct_183.field2;
            CursorTy pvrtmp_6400 = tmp_struct_183.field3;
            
            *(TagTyPacked *) loc_2618 = 4;
            
            CursorTy writetag_4305 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6397, pvrtmp_6398,
                                                   loc_2618, pvrtmp_6400};
            break;
        }
        
      case 5:
        {
            CursorTy loc_3282 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_184 =
                                          _add_size_and_rel_offsets_Tags(end_r_2619, end_r_2620, loc_3282, tmpcur_6308);
            CursorTy pvrtmp_6409 = tmp_struct_184.field0;
            CursorTy pvrtmp_6410 = tmp_struct_184.field1;
            CursorTy pvrtmp_6411 = tmp_struct_184.field2;
            CursorTy pvrtmp_6412 = tmp_struct_184.field3;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, pvrtmp_6409, pvrtmp_6412, pvrtmp_6410);
            CursorTy pvrtmp_6417 = tmp_struct_185.field0;
            CursorTy pvrtmp_6418 = tmp_struct_185.field1;
            CursorTy pvrtmp_6419 = tmp_struct_185.field2;
            CursorTy pvrtmp_6420 = tmp_struct_185.field3;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, pvrtmp_6417, pvrtmp_6420, pvrtmp_6418);
            CursorTy pvrtmp_6425 = tmp_struct_186.field0;
            CursorTy pvrtmp_6426 = tmp_struct_186.field1;
            CursorTy pvrtmp_6427 = tmp_struct_186.field2;
            CursorTy pvrtmp_6428 = tmp_struct_186.field3;
            
            *(TagTyPacked *) loc_2618 = 5;
            
            CursorTy writetag_4314 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6425, pvrtmp_6426,
                                                   loc_2618, pvrtmp_6428};
            break;
        }
        
      case 6:
        {
            CursorTy loc_3300 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, end_r_2620, loc_3300, tmpcur_6308);
            CursorTy pvrtmp_6437 = tmp_struct_187.field0;
            CursorTy pvrtmp_6438 = tmp_struct_187.field1;
            CursorTy pvrtmp_6439 = tmp_struct_187.field2;
            CursorTy pvrtmp_6440 = tmp_struct_187.field3;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Tags(end_r_2619, pvrtmp_6437, pvrtmp_6440, pvrtmp_6438);
            CursorTy pvrtmp_6445 = tmp_struct_188.field0;
            CursorTy pvrtmp_6446 = tmp_struct_188.field1;
            CursorTy pvrtmp_6447 = tmp_struct_188.field2;
            CursorTy pvrtmp_6448 = tmp_struct_188.field3;
            CursorCursorCursorCursorProd tmp_struct_189 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, pvrtmp_6445, pvrtmp_6448, pvrtmp_6446);
            CursorTy pvrtmp_6453 = tmp_struct_189.field0;
            CursorTy pvrtmp_6454 = tmp_struct_189.field1;
            CursorTy pvrtmp_6455 = tmp_struct_189.field2;
            CursorTy pvrtmp_6456 = tmp_struct_189.field3;
            
            *(TagTyPacked *) loc_2618 = 6;
            
            CursorTy writetag_4323 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6453, pvrtmp_6454,
                                                   loc_2618, pvrtmp_6456};
            break;
        }
        
      case 7:
        {
            CursorTy loc_3318 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_190 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, end_r_2620, loc_3318, tmpcur_6308);
            CursorTy pvrtmp_6465 = tmp_struct_190.field0;
            CursorTy pvrtmp_6466 = tmp_struct_190.field1;
            CursorTy pvrtmp_6467 = tmp_struct_190.field2;
            CursorTy pvrtmp_6468 = tmp_struct_190.field3;
            CursorCursorCursorCursorProd tmp_struct_191 =
                                          _add_size_and_rel_offsets_Tags(end_r_2619, pvrtmp_6465, pvrtmp_6468, pvrtmp_6466);
            CursorTy pvrtmp_6473 = tmp_struct_191.field0;
            CursorTy pvrtmp_6474 = tmp_struct_191.field1;
            CursorTy pvrtmp_6475 = tmp_struct_191.field2;
            CursorTy pvrtmp_6476 = tmp_struct_191.field3;
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, pvrtmp_6473, pvrtmp_6476, pvrtmp_6474);
            CursorTy pvrtmp_6481 = tmp_struct_192.field0;
            CursorTy pvrtmp_6482 = tmp_struct_192.field1;
            CursorTy pvrtmp_6483 = tmp_struct_192.field2;
            CursorTy pvrtmp_6484 = tmp_struct_192.field3;
            
            *(TagTyPacked *) loc_2618 = 7;
            
            CursorTy writetag_4332 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6481, pvrtmp_6482,
                                                   loc_2618, pvrtmp_6484};
            break;
        }
        
      case 8:
        {
            CursorTy loc_3336 = loc_2618 + 1;
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Content(end_r_2619, end_r_2620, loc_3336, tmpcur_6308);
            CursorTy pvrtmp_6493 = tmp_struct_193.field0;
            CursorTy pvrtmp_6494 = tmp_struct_193.field1;
            CursorTy pvrtmp_6495 = tmp_struct_193.field2;
            CursorTy pvrtmp_6496 = tmp_struct_193.field3;
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, pvrtmp_6493, pvrtmp_6496, pvrtmp_6494);
            CursorTy pvrtmp_6501 = tmp_struct_194.field0;
            CursorTy pvrtmp_6502 = tmp_struct_194.field1;
            CursorTy pvrtmp_6503 = tmp_struct_194.field2;
            CursorTy pvrtmp_6504 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Tags(end_r_2619, pvrtmp_6501, pvrtmp_6504, pvrtmp_6502);
            CursorTy pvrtmp_6509 = tmp_struct_195.field0;
            CursorTy pvrtmp_6510 = tmp_struct_195.field1;
            CursorTy pvrtmp_6511 = tmp_struct_195.field2;
            CursorTy pvrtmp_6512 = tmp_struct_195.field3;
            
            *(TagTyPacked *) loc_2618 = 8;
            
            CursorTy writetag_4341 = loc_2618 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6509, pvrtmp_6510,
                                                   loc_2618, pvrtmp_6512};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6521 = *(CursorTy *) tmpcur_6308;
            CursorTy tmpaftercur_6522 = tmpcur_6308 + 8;
            CursorTy jump_3717 = tmpcur_6308 + 8;
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, end_r_2620, loc_2618, tmpcur_6521);
            CursorTy pvrtmp_6523 = tmp_struct_196.field0;
            CursorTy pvrtmp_6524 = tmp_struct_196.field1;
            CursorTy pvrtmp_6525 = tmp_struct_196.field2;
            CursorTy pvrtmp_6526 = tmp_struct_196.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6523, jump_3717,
                                                   pvrtmp_6525, pvrtmp_6526};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6533 = *(CursorTy *) tmpcur_6308;
            CursorTy tmpaftercur_6534 = tmpcur_6308 + 8;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Adt(end_r_2619, end_r_2620, loc_2618, tmpcur_6533);
            CursorTy pvrtmp_6535 = tmp_struct_197.field0;
            CursorTy pvrtmp_6536 = tmp_struct_197.field1;
            CursorTy pvrtmp_6537 = tmp_struct_197.field2;
            CursorTy pvrtmp_6538 = tmp_struct_197.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6535, pvrtmp_6536,
                                                   pvrtmp_6537, pvrtmp_6538};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6307");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2623,
                                                            CursorTy end_r_2624,
                                                            CursorTy loc_2622,
                                                            CursorTy arg_2522)
{
    if (loc_2622 + 32 > end_r_2624) {
        ChunkTy new_chunk_204 = alloc_chunk(end_r_2624);
        CursorTy chunk_start_205 = new_chunk_204.chunk_start;
        CursorTy chunk_end_206 = new_chunk_204.chunk_end;
        
        end_r_2624 = chunk_end_206;
        *(TagTyPacked *) loc_2622 = 255;
        
        CursorTy redir = loc_2622 + 1;
        
        *(CursorTy *) redir = chunk_start_205;
        loc_2622 = chunk_start_205;
    }
    
    CursorTy loc_3350 = loc_2622 + 1;
    CursorTy loc_3351 = loc_3350 + 8;
    TagTyPacked tmpval_6546 = *(TagTyPacked *) arg_2522;
    CursorTy tmpcur_6547 = arg_2522 + 1;
    
    
  switch_6590:
    ;
    switch (tmpval_6546) {
        
      case 0:
        {
            CursorTy jump_3591 = arg_2522 + 1;
            
            *(TagTyPacked *) loc_2622 = 0;
            
            CursorTy writetag_4353 = loc_2622 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2624, jump_3591,
                                                   loc_2622, writetag_4353};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6552 = *(IntTy *) tmpcur_6547;
            CursorTy tmpcur_6553 = tmpcur_6547 + sizeof(IntTy);
            CursorTy jump_3593 = tmpcur_6547 + 8;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_2623, end_r_2624, loc_3351, tmpcur_6553);
            CursorTy pvrtmp_6554 = tmp_struct_201.field0;
            CursorTy pvrtmp_6555 = tmp_struct_201.field1;
            CursorTy pvrtmp_6556 = tmp_struct_201.field2;
            CursorTy pvrtmp_6557 = tmp_struct_201.field3;
            
            *(TagTyPacked *) loc_2622 = 1;
            
            CursorTy writetag_4358 = loc_2622 + 1;
            
            *(IntTy *) writetag_4358 = tmpval_6552;
            
            CursorTy writecur_4359 = writetag_4358 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6554, pvrtmp_6555,
                                                   loc_2622, pvrtmp_6557};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6566 = *(CursorTy *) tmpcur_6547;
            CursorTy tmpaftercur_6567 = tmpcur_6547 + 8;
            CursorTy jump_3723 = tmpcur_6547 + 8;
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_2623, end_r_2624, loc_2622, tmpcur_6566);
            CursorTy pvrtmp_6568 = tmp_struct_202.field0;
            CursorTy pvrtmp_6569 = tmp_struct_202.field1;
            CursorTy pvrtmp_6570 = tmp_struct_202.field2;
            CursorTy pvrtmp_6571 = tmp_struct_202.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6568, jump_3723,
                                                   pvrtmp_6570, pvrtmp_6571};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6578 = *(CursorTy *) tmpcur_6547;
            CursorTy tmpaftercur_6579 = tmpcur_6547 + 8;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Tags(end_r_2623, end_r_2624, loc_2622, tmpcur_6578);
            CursorTy pvrtmp_6580 = tmp_struct_203.field0;
            CursorTy pvrtmp_6581 = tmp_struct_203.field1;
            CursorTy pvrtmp_6582 = tmp_struct_203.field2;
            CursorTy pvrtmp_6583 = tmp_struct_203.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6580, pvrtmp_6581,
                                                   pvrtmp_6582, pvrtmp_6583};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6546");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(5234, "Time for Adt: AC");
    set_newline(5235);
    add_symbol(5236, "Count of Adt AC is: ");
    add_symbol(5237, ")");
    add_symbol(5238, "(Text ");
    add_symbol(5239, "(Tag ");
    add_symbol(5240, "(TCA ");
    add_symbol(5241, "(TAC ");
    add_symbol(5242, "(Nul ");
    add_symbol(5243, "(Nil ");
    add_symbol(5244, "(Image ");
    add_symbol(5245, "(End ");
    add_symbol(5246, "(Char ");
    add_symbol(5247, "(CTA ");
    add_symbol(5248, "(CAT ");
    add_symbol(5249, "(CA ");
    add_symbol(5250, "(ATC ");
    add_symbol(5251, "(ACT ");
    add_symbol(5252, "(AC ");
    add_symbol(5253, " ->r ");
    add_symbol(5254, " ->i ");
    
    RegionTy *region_5255 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2630 = region_5255->reg_heap;
    IntTy sizeof_end_r_2630_5256 = global_init_inf_buf_size;
    CursorTy end_r_2630 = r_2630 + sizeof_end_r_2630_5256;
    CursorCursorCursorProd tmp_struct_207 =
                            mkACList(end_r_2630, r_2630, 1000000, 100);
    CursorTy pvrtmp_5257 = tmp_struct_207.field0;
    CursorTy pvrtmp_5258 = tmp_struct_207.field1;
    CursorTy pvrtmp_5259 = tmp_struct_207.field2;
    unsigned char wildcard__17_22_914_1533 = print_symbol(5234);
    unsigned char wildcard__15_23_915_1534 = print_symbol(5235);
    IntTy timed_4657;
    VectorTy *times_211 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_timed_4657;
    struct timespec end_timed_4657;
    
    start_counters();
    for (long long iters_timed_4657 = 0; iters_timed_4657 < global_iters_param;
         iters_timed_4657++) {
        if (iters_timed_4657 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_4657);
        
        IntTy tailapp_3596 =  getLengthTR(pvrtmp_5257, pvrtmp_5258, 0);
        
        timed_4657 = tailapp_3596;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_4657);
        if (iters_timed_4657 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_208 = difftimespecs(&begin_timed_4657, &end_timed_4657);
        
        vector_inplace_update(times_211, iters_timed_4657, &itertime_208);
    }
    read_counters();
    print_counters();
    vector_inplace_sort(times_211, compare_doubles);
    
    double *tmp_212 = (double *) vector_nth(times_211, global_iters_param / 2);
    double selftimed_210 = *tmp_212;
    double batchtime_209 = sum_timing_array(times_211);
    
    print_timing_array(times_211);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_209);
    printf("SELFTIMED: %e\n", selftimed_210);
    
    unsigned char wildcard__11_25_917_1536 = print_symbol(5236);
    unsigned char wildcard__9_26_918_1537 = printf("%lld", timed_4657);
    unsigned char wildcard__7_27_919_1538 = print_symbol(5235);
    
    printf("'#()");
    printf("\n");
    free_symtable();
    return 0;
}
