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
  
  printf("CPI: %lld\n", values[3]/values[2]);   
    
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
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2937, CursorTy end_r_2938,
                                     CursorTy loc_2936,
                                     CursorTy adt_30_931_1547);
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2941, CursorTy end_r_2942,
                                       CursorTy loc_2940,
                                       CursorTy tags_44_941_1553,
                                       IntTy inVal_45_942_1554);
CursorCursorCursorProd mkTACList(CursorTy end_r_2944, CursorTy loc_2943,
                                 IntTy len_48_945_1559,
                                 IntTy tagLen_49_946_1560,
                                 IntTy strLen_50_947_1561);
CursorCursorCursorProd mkString(CursorTy end_r_2946, CursorTy loc_2945,
                                IntTy len_203_1100_1567);
CursorCursorCursorProd mkContentText(CursorTy end_r_2948, CursorTy loc_2947,
                                     IntTy n_217_1114_1573);
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2950, CursorTy loc_2949,
                                    IntTy len_342_1239_1575);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2953,
                                          CursorTy end_r_2954,
                                          CursorTy loc_2952,
                                          CursorTy arg_646_1259_1580);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2957,
                                                       CursorTy end_r_2958,
                                                       CursorTy loc_2956,
                                                       CursorTy arg_651_1264_1585);
CursorProd _traverse_String(CursorTy end_r_2960, CursorTy arg_656_1269_1590);
CursorProd _print_String(CursorTy end_r_2962, CursorTy arg_661_1273_1594);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2965,
                                           CursorTy end_r_2966,
                                           CursorTy loc_2964,
                                           CursorTy arg_670_1282_1603);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2969,
                                                        CursorTy end_r_2970,
                                                        CursorTy loc_2968,
                                                        CursorTy arg_675_1287_1608);
CursorProd _traverse_Content(CursorTy end_r_2972, CursorTy arg_680_1292_1613);
CursorProd _print_Content(CursorTy end_r_2974, CursorTy arg_685_1297_1618);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2977, CursorTy end_r_2978,
                                       CursorTy loc_2976,
                                       CursorTy arg_694_1306_1627);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2981,
                                                    CursorTy end_r_2982,
                                                    CursorTy loc_2980,
                                                    CursorTy arg_739_1351_1672);
CursorProd _traverse_Adt(CursorTy end_r_2984, CursorTy arg_784_1396_1717);
CursorProd _print_Adt(CursorTy end_r_2986, CursorTy arg_829_1441_1762);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2989,
                                        CursorTy end_r_2990, CursorTy loc_2988,
                                        CursorTy arg_892_1504_1825);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2993,
                                                     CursorTy end_r_2994,
                                                     CursorTy loc_2992,
                                                     CursorTy arg_897_1509_1830);
CursorProd _traverse_Tags(CursorTy end_r_2996, CursorTy arg_902_1514_1835);
CursorProd _print_Tags(CursorTy end_r_2998, CursorTy arg_907_1518_1839);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_3001, CursorTy end_r_3002,
                                 CursorTy loc_3000, CursorTy arg_2733);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_3005, CursorTy end_r_3006,
                                  CursorTy loc_3004, CursorTy arg_2738);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_3009,
                                                           CursorTy end_r_3010,
                                                           CursorTy loc_3008,
                                                           CursorTy arg_2743);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_3013,
                                                            CursorTy end_r_3014,
                                                            CursorTy loc_3012,
                                                            CursorTy arg_2832);
CursorCursorCursorProd addValTagsAdt(CursorTy end_r_2937, CursorTy end_r_2938,
                                     CursorTy loc_2936,
                                     CursorTy adt_30_931_1547)
{
    if (loc_2936 + 32 > end_r_2938) {
        ChunkTy new_chunk_4 = alloc_chunk(end_r_2938);
        CursorTy chunk_start_5 = new_chunk_4.chunk_start;
        CursorTy chunk_end_6 = new_chunk_4.chunk_end;
        
        end_r_2938 = chunk_end_6;
        *(TagTyPacked *) loc_2936 = 255;
        
        CursorTy redir = loc_2936 + 1;
        
        *(CursorTy *) redir = chunk_start_5;
        loc_2936 = chunk_start_5;
    }
    
    CursorTy loc_3039 = loc_2936 + 1;
    CursorTy loc_3040 = loc_3039 + 8;
    CursorTy loc_3041 = loc_3040 + 8;
    TagTyPacked tmpval_6208 = *(TagTyPacked *) adt_30_931_1547;
    CursorTy tmpcur_6209 = adt_30_931_1547 + 1;
    
    
  switch_6261:
    ;
    switch (tmpval_6208) {
        
      case 0:
        {
            CursorTy jump_3964 = adt_30_931_1547 + 1;
            
            *(TagTyPacked *) loc_2936 = 0;
            
            CursorTy writetag_4523 = loc_2936 + 1;
            
            return (CursorCursorCursorProd) {end_r_2938, loc_2936,
                                             writetag_4523};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6214 = *(CursorTy *) tmpcur_6209;
            CursorTy tmpaftercur_6215 = tmpcur_6209 + 8;
            CursorTy tmpcur_6216 = *(CursorTy *) tmpaftercur_6215;
            CursorTy tmpaftercur_6217 = tmpaftercur_6215 + 8;
            CursorTy jump_3967 = tmpaftercur_6215 + 8;
            CursorTy jump_3966 = tmpcur_6209 + 8;
            CursorCursorCursorCursorProd tmp_struct_0 =
                                          addValTag(end_r_2937, end_r_2938, loc_3041, tmpaftercur_6217, 10);
            CursorTy pvrtmp_6218 = tmp_struct_0.field0;
            CursorTy pvrtmp_6219 = tmp_struct_0.field1;
            CursorTy pvrtmp_6220 = tmp_struct_0.field2;
            CursorTy pvrtmp_6221 = tmp_struct_0.field3;
            CursorCursorCursorProd tmp_struct_1 =
                                    addValTagsAdt(end_r_2937, pvrtmp_6218, pvrtmp_6221, tmpcur_6214);
            CursorTy pvrtmp_6226 = tmp_struct_1.field0;
            CursorTy pvrtmp_6227 = tmp_struct_1.field1;
            CursorTy pvrtmp_6228 = tmp_struct_1.field2;
            
            *(TagTyPacked *) pvrtmp_6228 = 254;
            
            CursorTy writetag_4530 = pvrtmp_6228 + 1;
            
            *(CursorTy *) writetag_4530 = tmpcur_6216;
            
            CursorTy writecur_4531 = writetag_4530 + 8;
            
            *(TagTyPacked *) loc_2936 = 17;
            
            CursorTy writetag_4533 = loc_2936 + 1;
            
            *(CursorTy *) writetag_4533 = pvrtmp_6221;
            
            CursorTy writecur_4534 = writetag_4533 + 8;
            
            *(CursorTy *) writecur_4534 = pvrtmp_6228;
            
            CursorTy writecur_4535 = writecur_4534 + 8;
            
            return (CursorCursorCursorProd) {pvrtmp_6226, loc_2936,
                                             writecur_4531};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6239 = *(CursorTy *) tmpcur_6209;
            CursorTy tmpaftercur_6240 = tmpcur_6209 + 8;
            CursorTy jump_4276 = tmpcur_6209 + 8;
            CursorCursorCursorProd tmp_struct_2 =
                                    addValTagsAdt(end_r_2937, end_r_2938, loc_2936, tmpcur_6239);
            CursorTy pvrtmp_6241 = tmp_struct_2.field0;
            CursorTy pvrtmp_6242 = tmp_struct_2.field1;
            CursorTy pvrtmp_6243 = tmp_struct_2.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6241, pvrtmp_6242,
                                             pvrtmp_6243};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6250 = *(CursorTy *) tmpcur_6209;
            CursorTy tmpaftercur_6251 = tmpcur_6209 + 8;
            CursorCursorCursorProd tmp_struct_3 =
                                    addValTagsAdt(end_r_2937, end_r_2938, loc_2936, tmpcur_6250);
            CursorTy pvrtmp_6252 = tmp_struct_3.field0;
            CursorTy pvrtmp_6253 = tmp_struct_3.field1;
            CursorTy pvrtmp_6254 = tmp_struct_3.field2;
            
            return (CursorCursorCursorProd) {pvrtmp_6252, pvrtmp_6253,
                                             pvrtmp_6254};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6208");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd addValTag(CursorTy end_r_2941, CursorTy end_r_2942,
                                       CursorTy loc_2940,
                                       CursorTy tags_44_941_1553,
                                       IntTy inVal_45_942_1554)
{
    if (loc_2940 + 32 > end_r_2942) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2942);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2942 = chunk_end_12;
        *(TagTyPacked *) loc_2940 = 255;
        
        CursorTy redir = loc_2940 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2940 = chunk_start_11;
    }
    
    CursorTy loc_3059 = loc_2940 + 1;
    CursorTy loc_3060 = loc_3059 + 8;
    TagTyPacked tmpval_6262 = *(TagTyPacked *) tags_44_941_1553;
    CursorTy tmpcur_6263 = tags_44_941_1553 + 1;
    
    
  switch_6306:
    ;
    switch (tmpval_6262) {
        
      case 0:
        {
            CursorTy jump_3970 = tags_44_941_1553 + 1;
            
            *(TagTyPacked *) loc_2940 = 0;
            
            CursorTy writetag_4547 = loc_2940 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2942, jump_3970,
                                                   loc_2940, writetag_4547};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6268 = *(IntTy *) tmpcur_6263;
            CursorTy tmpcur_6269 = tmpcur_6263 + sizeof(IntTy);
            CursorTy jump_3972 = tmpcur_6263 + 8;
            IntTy fltPkd_1535_1557 = tmpval_6268 + inVal_45_942_1554;
            CursorCursorCursorCursorProd tmp_struct_7 =
                                          addValTag(end_r_2941, end_r_2942, loc_3060, tmpcur_6269, inVal_45_942_1554);
            CursorTy pvrtmp_6270 = tmp_struct_7.field0;
            CursorTy pvrtmp_6271 = tmp_struct_7.field1;
            CursorTy pvrtmp_6272 = tmp_struct_7.field2;
            CursorTy pvrtmp_6273 = tmp_struct_7.field3;
            
            *(TagTyPacked *) loc_2940 = 1;
            
            CursorTy writetag_4552 = loc_2940 + 1;
            
            *(IntTy *) writetag_4552 = fltPkd_1535_1557;
            
            CursorTy writecur_4553 = writetag_4552 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6270, pvrtmp_6271,
                                                   loc_2940, pvrtmp_6273};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6282 = *(CursorTy *) tmpcur_6263;
            CursorTy tmpaftercur_6283 = tmpcur_6263 + 8;
            CursorTy jump_4281 = tmpcur_6263 + 8;
            CursorCursorCursorCursorProd tmp_struct_8 =
                                          addValTag(end_r_2941, end_r_2942, loc_2940, tmpcur_6282, inVal_45_942_1554);
            CursorTy pvrtmp_6284 = tmp_struct_8.field0;
            CursorTy pvrtmp_6285 = tmp_struct_8.field1;
            CursorTy pvrtmp_6286 = tmp_struct_8.field2;
            CursorTy pvrtmp_6287 = tmp_struct_8.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6284, jump_4281,
                                                   pvrtmp_6286, pvrtmp_6287};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6294 = *(CursorTy *) tmpcur_6263;
            CursorTy tmpaftercur_6295 = tmpcur_6263 + 8;
            CursorCursorCursorCursorProd tmp_struct_9 =
                                          addValTag(end_r_2941, end_r_2942, loc_2940, tmpcur_6294, inVal_45_942_1554);
            CursorTy pvrtmp_6296 = tmp_struct_9.field0;
            CursorTy pvrtmp_6297 = tmp_struct_9.field1;
            CursorTy pvrtmp_6298 = tmp_struct_9.field2;
            CursorTy pvrtmp_6299 = tmp_struct_9.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6296, pvrtmp_6297,
                                                   pvrtmp_6298, pvrtmp_6299};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6262");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkTACList(CursorTy end_r_2944, CursorTy loc_2943,
                                 IntTy len_48_945_1559,
                                 IntTy tagLen_49_946_1560,
                                 IntTy strLen_50_947_1561)
{
    if (loc_2943 + 32 > end_r_2944) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2944);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2944 = chunk_end_18;
        *(TagTyPacked *) loc_2943 = 255;
        
        CursorTy redir = loc_2943 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2943 = chunk_start_17;
    }
    
    CursorTy loc_3068 = loc_2943 + 1;
    CursorTy loc_3069 = loc_3068 + 8;
    CursorTy loc_3070 = loc_3069 + 8;
    BoolTy fltIf_1537_1562 = len_48_945_1559 <= 0;
    
    if (fltIf_1537_1562) {
        *(TagTyPacked *) loc_2943 = 0;
        
        CursorTy writetag_4562 = loc_2943 + 1;
        
        return (CursorCursorCursorProd) {end_r_2944, loc_2943, writetag_4562};
    } else {
        CursorCursorCursorProd tmp_struct_13 =
                                mkRandomTags(end_r_2944, loc_3070, tagLen_49_946_1560);
        CursorTy pvrtmp_6311 = tmp_struct_13.field0;
        CursorTy pvrtmp_6312 = tmp_struct_13.field1;
        CursorTy pvrtmp_6313 = tmp_struct_13.field2;
        IntTy fltAppE_1538_1564 = len_48_945_1559 - 1;
        CursorCursorCursorProd tmp_struct_14 =
                                mkTACList(pvrtmp_6311, pvrtmp_6313, fltAppE_1538_1564, tagLen_49_946_1560, strLen_50_947_1561);
        CursorTy pvrtmp_6318 = tmp_struct_14.field0;
        CursorTy pvrtmp_6319 = tmp_struct_14.field1;
        CursorTy pvrtmp_6320 = tmp_struct_14.field2;
        CursorCursorCursorProd tmp_struct_15 =
                                mkContentText(pvrtmp_6318, pvrtmp_6320, strLen_50_947_1561);
        CursorTy pvrtmp_6325 = tmp_struct_15.field0;
        CursorTy pvrtmp_6326 = tmp_struct_15.field1;
        CursorTy pvrtmp_6327 = tmp_struct_15.field2;
        
        *(TagTyPacked *) loc_2943 = 17;
        
        CursorTy writetag_4567 = loc_2943 + 1;
        
        *(CursorTy *) writetag_4567 = pvrtmp_6313;
        
        CursorTy writecur_4568 = writetag_4567 + 8;
        
        *(CursorTy *) writecur_4568 = pvrtmp_6320;
        
        CursorTy writecur_4569 = writecur_4568 + 8;
        
        return (CursorCursorCursorProd) {pvrtmp_6325, loc_2943, pvrtmp_6327};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2946, CursorTy loc_2945,
                                IntTy len_203_1100_1567)
{
    if (loc_2945 + 32 > end_r_2946) {
        ChunkTy new_chunk_20 = alloc_chunk(end_r_2946);
        CursorTy chunk_start_21 = new_chunk_20.chunk_start;
        CursorTy chunk_end_22 = new_chunk_20.chunk_end;
        
        end_r_2946 = chunk_end_22;
        *(TagTyPacked *) loc_2945 = 255;
        
        CursorTy redir = loc_2945 + 1;
        
        *(CursorTy *) redir = chunk_start_21;
        loc_2945 = chunk_start_21;
    }
    
    CursorTy loc_3082 = loc_2945 + 1;
    CursorTy loc_3083 = loc_3082 + 8;
    BoolTy fltIf_1539_1568 = len_203_1100_1567 <= 0;
    
    if (fltIf_1539_1568) {
        *(TagTyPacked *) loc_2945 = 0;
        
        CursorTy writetag_4574 = loc_2945 + 1;
        
        return (CursorCursorCursorProd) {end_r_2946, loc_2945, writetag_4574};
    } else {
        IntTy fltPrm_1540_1569 = rand();
        IntTy randomChar_204_1101_1570 = fltPrm_1540_1569 % 128;
        IntTy fltAppE_1541_1571 = len_203_1100_1567 - 1;
        CursorCursorCursorProd tmp_struct_19 =
                                mkString(end_r_2946, loc_3083, fltAppE_1541_1571);
        CursorTy pvrtmp_6340 = tmp_struct_19.field0;
        CursorTy pvrtmp_6341 = tmp_struct_19.field1;
        CursorTy pvrtmp_6342 = tmp_struct_19.field2;
        
        *(TagTyPacked *) loc_2945 = 1;
        
        CursorTy writetag_4577 = loc_2945 + 1;
        
        *(IntTy *) writetag_4577 = randomChar_204_1101_1570;
        
        CursorTy writecur_4578 = writetag_4577 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6340, loc_2945, pvrtmp_6342};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2948, CursorTy loc_2947,
                                     IntTy n_217_1114_1573)
{
    if (loc_2947 + 32 > end_r_2948) {
        ChunkTy new_chunk_24 = alloc_chunk(end_r_2948);
        CursorTy chunk_start_25 = new_chunk_24.chunk_start;
        CursorTy chunk_end_26 = new_chunk_24.chunk_end;
        
        end_r_2948 = chunk_end_26;
        *(TagTyPacked *) loc_2947 = 255;
        
        CursorTy redir = loc_2947 + 1;
        
        *(CursorTy *) redir = chunk_start_25;
        loc_2947 = chunk_start_25;
    }
    
    CursorTy loc_3088 = loc_2947 + 1;
    CursorCursorCursorProd tmp_struct_23 =
                            mkString(end_r_2948, loc_3088, n_217_1114_1573);
    CursorTy pvrtmp_6351 = tmp_struct_23.field0;
    CursorTy pvrtmp_6352 = tmp_struct_23.field1;
    CursorTy pvrtmp_6353 = tmp_struct_23.field2;
    
    *(TagTyPacked *) loc_2947 = 1;
    
    CursorTy writetag_4582 = loc_2947 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_6351, loc_2947, pvrtmp_6353};
}
CursorCursorCursorProd mkRandomTags(CursorTy end_r_2950, CursorTy loc_2949,
                                    IntTy len_342_1239_1575)
{
    if (loc_2949 + 32 > end_r_2950) {
        ChunkTy new_chunk_28 = alloc_chunk(end_r_2950);
        CursorTy chunk_start_29 = new_chunk_28.chunk_start;
        CursorTy chunk_end_30 = new_chunk_28.chunk_end;
        
        end_r_2950 = chunk_end_30;
        *(TagTyPacked *) loc_2949 = 255;
        
        CursorTy redir = loc_2949 + 1;
        
        *(CursorTy *) redir = chunk_start_29;
        loc_2949 = chunk_start_29;
    }
    
    CursorTy loc_3092 = loc_2949 + 1;
    CursorTy loc_3093 = loc_3092 + 8;
    BoolTy fltIf_1543_1576 = len_342_1239_1575 <= 0;
    
    if (fltIf_1543_1576) {
        *(TagTyPacked *) loc_2949 = 0;
        
        CursorTy writetag_4585 = loc_2949 + 1;
        
        return (CursorCursorCursorProd) {end_r_2950, loc_2949, writetag_4585};
    } else {
        IntTy fltAppE_1544_1578 = len_342_1239_1575 - 1;
        CursorCursorCursorProd tmp_struct_27 =
                                mkRandomTags(end_r_2950, loc_3093, fltAppE_1544_1578);
        CursorTy pvrtmp_6366 = tmp_struct_27.field0;
        CursorTy pvrtmp_6367 = tmp_struct_27.field1;
        CursorTy pvrtmp_6368 = tmp_struct_27.field2;
        
        *(TagTyPacked *) loc_2949 = 1;
        
        CursorTy writetag_4588 = loc_2949 + 1;
        
        *(IntTy *) writetag_4588 = 100;
        
        CursorTy writecur_4589 = writetag_4588 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_6366, loc_2949, pvrtmp_6368};
    }
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2953,
                                          CursorTy end_r_2954,
                                          CursorTy loc_2952,
                                          CursorTy arg_646_1259_1580)
{
    if (loc_2952 + 32 > end_r_2954) {
        ChunkTy new_chunk_34 = alloc_chunk(end_r_2954);
        CursorTy chunk_start_35 = new_chunk_34.chunk_start;
        CursorTy chunk_end_36 = new_chunk_34.chunk_end;
        
        end_r_2954 = chunk_end_36;
        *(TagTyPacked *) loc_2952 = 255;
        
        CursorTy redir = loc_2952 + 1;
        
        *(CursorTy *) redir = chunk_start_35;
        loc_2952 = chunk_start_35;
    }
    
    CursorTy loc_3103 = loc_2952 + 1;
    CursorTy loc_3104 = loc_3103 + 8;
    TagTyPacked tmpval_6377 = *(TagTyPacked *) arg_646_1259_1580;
    CursorTy tmpcur_6378 = arg_646_1259_1580 + 1;
    
    
  switch_6421:
    ;
    switch (tmpval_6377) {
        
      case 0:
        {
            CursorTy jump_3982 = arg_646_1259_1580 + 1;
            
            *(TagTyPacked *) loc_2952 = 0;
            
            CursorTy writetag_4593 = loc_2952 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2954, jump_3982,
                                                   loc_2952, writetag_4593};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6383 = *(IntTy *) tmpcur_6378;
            CursorTy tmpcur_6384 = tmpcur_6378 + sizeof(IntTy);
            CursorTy jump_3984 = tmpcur_6378 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_String(end_r_2953, end_r_2954, loc_3104, tmpcur_6384);
            CursorTy pvrtmp_6385 = tmp_struct_31.field0;
            CursorTy pvrtmp_6386 = tmp_struct_31.field1;
            CursorTy pvrtmp_6387 = tmp_struct_31.field2;
            CursorTy pvrtmp_6388 = tmp_struct_31.field3;
            
            *(TagTyPacked *) loc_2952 = 1;
            
            CursorTy writetag_4598 = loc_2952 + 1;
            
            *(IntTy *) writetag_4598 = tmpval_6383;
            
            CursorTy writecur_4599 = writetag_4598 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6385, pvrtmp_6386,
                                                   loc_2952, pvrtmp_6388};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6397 = *(CursorTy *) tmpcur_6378;
            CursorTy tmpaftercur_6398 = tmpcur_6378 + 8;
            CursorTy jump_4287 = tmpcur_6378 + 8;
            CursorCursorCursorCursorProd tmp_struct_32 =
                                          _copy_String(end_r_2953, end_r_2954, loc_2952, tmpcur_6397);
            CursorTy pvrtmp_6399 = tmp_struct_32.field0;
            CursorTy pvrtmp_6400 = tmp_struct_32.field1;
            CursorTy pvrtmp_6401 = tmp_struct_32.field2;
            CursorTy pvrtmp_6402 = tmp_struct_32.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6399, jump_4287,
                                                   pvrtmp_6401, pvrtmp_6402};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6409 = *(CursorTy *) tmpcur_6378;
            CursorTy tmpaftercur_6410 = tmpcur_6378 + 8;
            CursorCursorCursorCursorProd tmp_struct_33 =
                                          _copy_String(end_r_2953, end_r_2954, loc_2952, tmpcur_6409);
            CursorTy pvrtmp_6411 = tmp_struct_33.field0;
            CursorTy pvrtmp_6412 = tmp_struct_33.field1;
            CursorTy pvrtmp_6413 = tmp_struct_33.field2;
            CursorTy pvrtmp_6414 = tmp_struct_33.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6411, pvrtmp_6412,
                                                   pvrtmp_6413, pvrtmp_6414};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6377");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2957,
                                                       CursorTy end_r_2958,
                                                       CursorTy loc_2956,
                                                       CursorTy arg_651_1264_1585)
{
    CursorTy loc_3116 = loc_2956 + 1;
    CursorTy loc_3117 = loc_3116 + 8;
    TagTyPacked tmpval_6422 = *(TagTyPacked *) arg_651_1264_1585;
    CursorTy tmpcur_6423 = arg_651_1264_1585 + 1;
    
    
  switch_6466:
    ;
    switch (tmpval_6422) {
        
      case 0:
        {
            CursorTy jump_3987 = arg_651_1264_1585 + 1;
            
            *(TagTyPacked *) loc_2956 = 0;
            
            CursorTy writetag_4609 = loc_2956 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2958, jump_3987,
                                                   loc_2956, writetag_4609};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6428 = *(IntTy *) tmpcur_6423;
            CursorTy tmpcur_6429 = tmpcur_6423 + sizeof(IntTy);
            CursorTy jump_3989 = tmpcur_6423 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_String(end_r_2957, end_r_2958, loc_3117, tmpcur_6429);
            CursorTy pvrtmp_6430 = tmp_struct_37.field0;
            CursorTy pvrtmp_6431 = tmp_struct_37.field1;
            CursorTy pvrtmp_6432 = tmp_struct_37.field2;
            CursorTy pvrtmp_6433 = tmp_struct_37.field3;
            
            *(TagTyPacked *) loc_2956 = 1;
            
            CursorTy writetag_4614 = loc_2956 + 1;
            
            *(IntTy *) writetag_4614 = tmpval_6428;
            
            CursorTy writecur_4615 = writetag_4614 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6430, pvrtmp_6431,
                                                   loc_2956, pvrtmp_6433};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6442 = *(CursorTy *) tmpcur_6423;
            CursorTy tmpaftercur_6443 = tmpcur_6423 + 8;
            CursorTy jump_4293 = tmpcur_6423 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_String(end_r_2957, end_r_2958, loc_2956, tmpcur_6442);
            CursorTy pvrtmp_6444 = tmp_struct_38.field0;
            CursorTy pvrtmp_6445 = tmp_struct_38.field1;
            CursorTy pvrtmp_6446 = tmp_struct_38.field2;
            CursorTy pvrtmp_6447 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6444, jump_4293,
                                                   pvrtmp_6446, pvrtmp_6447};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6454 = *(CursorTy *) tmpcur_6423;
            CursorTy tmpaftercur_6455 = tmpcur_6423 + 8;
            CursorCursorCursorCursorProd tmp_struct_39 =
                                          _copy_without_ptrs_String(end_r_2957, end_r_2958, loc_2956, tmpcur_6454);
            CursorTy pvrtmp_6456 = tmp_struct_39.field0;
            CursorTy pvrtmp_6457 = tmp_struct_39.field1;
            CursorTy pvrtmp_6458 = tmp_struct_39.field2;
            CursorTy pvrtmp_6459 = tmp_struct_39.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6456, pvrtmp_6457,
                                                   pvrtmp_6458, pvrtmp_6459};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6422");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2960, CursorTy arg_656_1269_1590)
{
    TagTyPacked tmpval_6467 = *(TagTyPacked *) arg_656_1269_1590;
    CursorTy tmpcur_6468 = arg_656_1269_1590 + 1;
    
    
  switch_6478:
    ;
    switch (tmpval_6467) {
        
      case 0:
        {
            CursorTy jump_3992 = arg_656_1269_1590 + 1;
            
            return (CursorProd) {jump_3992};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6469 = *(IntTy *) tmpcur_6468;
            CursorTy tmpcur_6470 = tmpcur_6468 + sizeof(IntTy);
            CursorTy jump_3994 = tmpcur_6468 + 8;
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2960, tmpcur_6470);
            CursorTy pvrtmp_6471 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_6471};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6472 = *(CursorTy *) tmpcur_6468;
            CursorTy tmpaftercur_6473 = tmpcur_6468 + 8;
            CursorTy jump_4299 = tmpcur_6468 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_String(end_r_2960, tmpcur_6472);
            CursorTy pvrtmp_6474 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_4299};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6475 = *(CursorTy *) tmpcur_6468;
            CursorTy tmpaftercur_6476 = tmpcur_6468 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_String(end_r_2960, tmpcur_6475);
            CursorTy pvrtmp_6477 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_6477};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6467");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2962, CursorTy arg_661_1273_1594)
{
    TagTyPacked tmpval_6479 = *(TagTyPacked *) arg_661_1273_1594;
    CursorTy tmpcur_6480 = arg_661_1273_1594 + 1;
    
    
  switch_6490:
    ;
    switch (tmpval_6479) {
        
      case 0:
        {
            CursorTy jump_3997 = arg_661_1273_1594 + 1;
            unsigned char wildcard_662_1274_1595 = print_symbol(6168);
            unsigned char wildcard_663_1275_1596 = print_symbol(6160);
            
            return (CursorProd) {jump_3997};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6481 = *(IntTy *) tmpcur_6480;
            CursorTy tmpcur_6482 = tmpcur_6480 + sizeof(IntTy);
            CursorTy jump_3999 = tmpcur_6480 + 8;
            unsigned char wildcard_668_1278_1599 = print_symbol(6169);
            unsigned char y_666_1279_1600 = printf("%lld", tmpval_6481);
            CursorProd tmp_struct_43 =  _print_String(end_r_2962, tmpcur_6482);
            CursorTy pvrtmp_6483 = tmp_struct_43.field0;
            unsigned char wildcard_669_1281_1602 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_6483};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6484 = *(CursorTy *) tmpcur_6480;
            CursorTy tmpaftercur_6485 = tmpcur_6480 + 8;
            CursorTy jump_4305 = tmpcur_6480 + 8;
            unsigned char wildcard_4308 = print_symbol(6177);
            CursorProd tmp_struct_44 =  _print_String(end_r_2962, tmpcur_6484);
            CursorTy pvrtmp_6486 = tmp_struct_44.field0;
            
            return (CursorProd) {jump_4305};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6487 = *(CursorTy *) tmpcur_6480;
            CursorTy tmpaftercur_6488 = tmpcur_6480 + 8;
            unsigned char wildcard_4308 = print_symbol(6176);
            CursorProd tmp_struct_45 =  _print_String(end_r_2962, tmpcur_6487);
            CursorTy pvrtmp_6489 = tmp_struct_45.field0;
            
            return (CursorProd) {pvrtmp_6489};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6479");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2965,
                                           CursorTy end_r_2966,
                                           CursorTy loc_2964,
                                           CursorTy arg_670_1282_1603)
{
    if (loc_2964 + 32 > end_r_2966) {
        ChunkTy new_chunk_50 = alloc_chunk(end_r_2966);
        CursorTy chunk_start_51 = new_chunk_50.chunk_start;
        CursorTy chunk_end_52 = new_chunk_50.chunk_end;
        
        end_r_2966 = chunk_end_52;
        *(TagTyPacked *) loc_2964 = 255;
        
        CursorTy redir = loc_2964 + 1;
        
        *(CursorTy *) redir = chunk_start_51;
        loc_2964 = chunk_start_51;
    }
    
    TagTyPacked tmpval_6491 = *(TagTyPacked *) arg_670_1282_1603;
    CursorTy tmpcur_6492 = arg_670_1282_1603 + 1;
    
    
  switch_6541:
    ;
    switch (tmpval_6491) {
        
      case 0:
        {
            CursorTy loc_3139 = loc_2964 + 1;
            CursorCursorCursorCursorProd tmp_struct_46 =
                                          _copy_String(end_r_2965, end_r_2966, loc_3139, tmpcur_6492);
            CursorTy pvrtmp_6493 = tmp_struct_46.field0;
            CursorTy pvrtmp_6494 = tmp_struct_46.field1;
            CursorTy pvrtmp_6495 = tmp_struct_46.field2;
            CursorTy pvrtmp_6496 = tmp_struct_46.field3;
            
            *(TagTyPacked *) loc_2964 = 0;
            
            CursorTy writetag_4646 = loc_2964 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6493, pvrtmp_6494,
                                                   loc_2964, pvrtmp_6496};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3145 = loc_2964 + 1;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_String(end_r_2965, end_r_2966, loc_3145, tmpcur_6492);
            CursorTy pvrtmp_6505 = tmp_struct_47.field0;
            CursorTy pvrtmp_6506 = tmp_struct_47.field1;
            CursorTy pvrtmp_6507 = tmp_struct_47.field2;
            CursorTy pvrtmp_6508 = tmp_struct_47.field3;
            
            *(TagTyPacked *) loc_2964 = 1;
            
            CursorTy writetag_4651 = loc_2964 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6505, pvrtmp_6506,
                                                   loc_2964, pvrtmp_6508};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6517 = *(CursorTy *) tmpcur_6492;
            CursorTy tmpaftercur_6518 = tmpcur_6492 + 8;
            CursorTy jump_4311 = tmpcur_6492 + 8;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Content(end_r_2965, end_r_2966, loc_2964, tmpcur_6517);
            CursorTy pvrtmp_6519 = tmp_struct_48.field0;
            CursorTy pvrtmp_6520 = tmp_struct_48.field1;
            CursorTy pvrtmp_6521 = tmp_struct_48.field2;
            CursorTy pvrtmp_6522 = tmp_struct_48.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6519, jump_4311,
                                                   pvrtmp_6521, pvrtmp_6522};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6529 = *(CursorTy *) tmpcur_6492;
            CursorTy tmpaftercur_6530 = tmpcur_6492 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Content(end_r_2965, end_r_2966, loc_2964, tmpcur_6529);
            CursorTy pvrtmp_6531 = tmp_struct_49.field0;
            CursorTy pvrtmp_6532 = tmp_struct_49.field1;
            CursorTy pvrtmp_6533 = tmp_struct_49.field2;
            CursorTy pvrtmp_6534 = tmp_struct_49.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6531, pvrtmp_6532,
                                                   pvrtmp_6533, pvrtmp_6534};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6491");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2969,
                                                        CursorTy end_r_2970,
                                                        CursorTy loc_2968,
                                                        CursorTy arg_675_1287_1608)
{
    TagTyPacked tmpval_6542 = *(TagTyPacked *) arg_675_1287_1608;
    CursorTy tmpcur_6543 = arg_675_1287_1608 + 1;
    
    
  switch_6592:
    ;
    switch (tmpval_6542) {
        
      case 0:
        {
            CursorTy loc_3153 = loc_2968 + 1;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_without_ptrs_String(end_r_2969, end_r_2970, loc_3153, tmpcur_6543);
            CursorTy pvrtmp_6544 = tmp_struct_53.field0;
            CursorTy pvrtmp_6545 = tmp_struct_53.field1;
            CursorTy pvrtmp_6546 = tmp_struct_53.field2;
            CursorTy pvrtmp_6547 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2968 = 0;
            
            CursorTy writetag_4662 = loc_2968 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6544, pvrtmp_6545,
                                                   loc_2968, pvrtmp_6547};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3159 = loc_2968 + 1;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_without_ptrs_String(end_r_2969, end_r_2970, loc_3159, tmpcur_6543);
            CursorTy pvrtmp_6556 = tmp_struct_54.field0;
            CursorTy pvrtmp_6557 = tmp_struct_54.field1;
            CursorTy pvrtmp_6558 = tmp_struct_54.field2;
            CursorTy pvrtmp_6559 = tmp_struct_54.field3;
            
            *(TagTyPacked *) loc_2968 = 1;
            
            CursorTy writetag_4667 = loc_2968 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6556, pvrtmp_6557,
                                                   loc_2968, pvrtmp_6559};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6568 = *(CursorTy *) tmpcur_6543;
            CursorTy tmpaftercur_6569 = tmpcur_6543 + 8;
            CursorTy jump_4317 = tmpcur_6543 + 8;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_without_ptrs_Content(end_r_2969, end_r_2970, loc_2968, tmpcur_6568);
            CursorTy pvrtmp_6570 = tmp_struct_55.field0;
            CursorTy pvrtmp_6571 = tmp_struct_55.field1;
            CursorTy pvrtmp_6572 = tmp_struct_55.field2;
            CursorTy pvrtmp_6573 = tmp_struct_55.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6570, jump_4317,
                                                   pvrtmp_6572, pvrtmp_6573};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6580 = *(CursorTy *) tmpcur_6543;
            CursorTy tmpaftercur_6581 = tmpcur_6543 + 8;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_without_ptrs_Content(end_r_2969, end_r_2970, loc_2968, tmpcur_6580);
            CursorTy pvrtmp_6582 = tmp_struct_56.field0;
            CursorTy pvrtmp_6583 = tmp_struct_56.field1;
            CursorTy pvrtmp_6584 = tmp_struct_56.field2;
            CursorTy pvrtmp_6585 = tmp_struct_56.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6582, pvrtmp_6583,
                                                   pvrtmp_6584, pvrtmp_6585};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6542");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2972, CursorTy arg_680_1292_1613)
{
    TagTyPacked tmpval_6593 = *(TagTyPacked *) arg_680_1292_1613;
    CursorTy tmpcur_6594 = arg_680_1292_1613 + 1;
    
    
  switch_6603:
    ;
    switch (tmpval_6593) {
        
      case 0:
        {
            CursorProd tmp_struct_57 =
                        _traverse_String(end_r_2972, tmpcur_6594);
            CursorTy pvrtmp_6595 = tmp_struct_57.field0;
            
            return (CursorProd) {pvrtmp_6595};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_58 =
                        _traverse_String(end_r_2972, tmpcur_6594);
            CursorTy pvrtmp_6596 = tmp_struct_58.field0;
            
            return (CursorProd) {pvrtmp_6596};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6597 = *(CursorTy *) tmpcur_6594;
            CursorTy tmpaftercur_6598 = tmpcur_6594 + 8;
            CursorTy jump_4323 = tmpcur_6594 + 8;
            CursorProd tmp_struct_59 =
                        _traverse_Content(end_r_2972, tmpcur_6597);
            CursorTy pvrtmp_6599 = tmp_struct_59.field0;
            
            return (CursorProd) {jump_4323};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6600 = *(CursorTy *) tmpcur_6594;
            CursorTy tmpaftercur_6601 = tmpcur_6594 + 8;
            CursorProd tmp_struct_60 =
                        _traverse_Content(end_r_2972, tmpcur_6600);
            CursorTy pvrtmp_6602 = tmp_struct_60.field0;
            
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
CursorProd _print_Content(CursorTy end_r_2974, CursorTy arg_685_1297_1618)
{
    TagTyPacked tmpval_6604 = *(TagTyPacked *) arg_685_1297_1618;
    CursorTy tmpcur_6605 = arg_685_1297_1618 + 1;
    
    
  switch_6614:
    ;
    switch (tmpval_6604) {
        
      case 0:
        {
            unsigned char wildcard_688_1299_1620 = print_symbol(6167);
            CursorProd tmp_struct_61 =  _print_String(end_r_2974, tmpcur_6605);
            CursorTy pvrtmp_6606 = tmp_struct_61.field0;
            unsigned char wildcard_689_1301_1622 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_6606};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_692_1303_1624 = print_symbol(6161);
            CursorProd tmp_struct_62 =  _print_String(end_r_2974, tmpcur_6605);
            CursorTy pvrtmp_6607 = tmp_struct_62.field0;
            unsigned char wildcard_693_1305_1626 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_6607};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6608 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6609 = tmpcur_6605 + 8;
            CursorTy jump_4329 = tmpcur_6605 + 8;
            unsigned char wildcard_4332 = print_symbol(6177);
            CursorProd tmp_struct_63 =  _print_Content(end_r_2974, tmpcur_6608);
            CursorTy pvrtmp_6610 = tmp_struct_63.field0;
            
            return (CursorProd) {jump_4329};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6611 = *(CursorTy *) tmpcur_6605;
            CursorTy tmpaftercur_6612 = tmpcur_6605 + 8;
            unsigned char wildcard_4332 = print_symbol(6176);
            CursorProd tmp_struct_64 =  _print_Content(end_r_2974, tmpcur_6611);
            CursorTy pvrtmp_6613 = tmp_struct_64.field0;
            
            return (CursorProd) {pvrtmp_6613};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6604");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2977, CursorTy end_r_2978,
                                       CursorTy loc_2976,
                                       CursorTy arg_694_1306_1627)
{
    if (loc_2976 + 32 > end_r_2978) {
        ChunkTy new_chunk_89 = alloc_chunk(end_r_2978);
        CursorTy chunk_start_90 = new_chunk_89.chunk_start;
        CursorTy chunk_end_91 = new_chunk_89.chunk_end;
        
        end_r_2978 = chunk_end_91;
        *(TagTyPacked *) loc_2976 = 255;
        
        CursorTy redir = loc_2976 + 1;
        
        *(CursorTy *) redir = chunk_start_90;
        loc_2976 = chunk_start_90;
    }
    
    CursorTy loc_3189 = loc_2976 + 1;
    CursorTy loc_3190 = loc_3189 + 8;
    CursorTy loc_3205 = loc_2976 + 1;
    CursorTy loc_3206 = loc_3205 + 8;
    CursorTy loc_3226 = loc_2976 + 1;
    CursorTy loc_3227 = loc_3226 + 8;
    CursorTy loc_3228 = loc_3227 + 8;
    CursorTy loc_3252 = loc_2976 + 1;
    CursorTy loc_3253 = loc_3252 + 8;
    CursorTy loc_3254 = loc_3253 + 8;
    CursorTy loc_3278 = loc_2976 + 1;
    CursorTy loc_3279 = loc_3278 + 8;
    CursorTy loc_3280 = loc_3279 + 8;
    CursorTy loc_3304 = loc_2976 + 1;
    CursorTy loc_3305 = loc_3304 + 8;
    CursorTy loc_3306 = loc_3305 + 8;
    CursorTy loc_3330 = loc_2976 + 1;
    CursorTy loc_3331 = loc_3330 + 8;
    CursorTy loc_3332 = loc_3331 + 8;
    CursorTy loc_3356 = loc_2976 + 1;
    CursorTy loc_3357 = loc_3356 + 8;
    CursorTy loc_3358 = loc_3357 + 8;
    TagTyPacked tmpval_6615 = *(TagTyPacked *) arg_694_1306_1627;
    CursorTy tmpcur_6616 = arg_694_1306_1627 + 1;
    
    
  switch_6881:
    ;
    switch (tmpval_6615) {
        
      case 0:
        {
            CursorTy jump_4018 = arg_694_1306_1627 + 1;
            
            *(TagTyPacked *) loc_2976 = 0;
            
            CursorTy writetag_4697 = loc_2976 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2978, jump_4018,
                                                   loc_2976, writetag_4697};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6621 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6622 = tmpcur_6616 + 8;
            CursorTy jump_4020 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Content(end_r_2977, end_r_2978, loc_3190, tmpaftercur_6622);
            CursorTy pvrtmp_6623 = tmp_struct_65.field0;
            CursorTy pvrtmp_6624 = tmp_struct_65.field1;
            CursorTy pvrtmp_6625 = tmp_struct_65.field2;
            CursorTy pvrtmp_6626 = tmp_struct_65.field3;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Adt(end_r_2977, pvrtmp_6623, pvrtmp_6626, tmpcur_6621);
            CursorTy pvrtmp_6631 = tmp_struct_66.field0;
            CursorTy pvrtmp_6632 = tmp_struct_66.field1;
            CursorTy pvrtmp_6633 = tmp_struct_66.field2;
            CursorTy pvrtmp_6634 = tmp_struct_66.field3;
            
            *(TagTyPacked *) loc_2976 = 9;
            
            CursorTy writetag_4703 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4703 = pvrtmp_6626;
            
            CursorTy writecur_4704 = writetag_4703 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6631, pvrtmp_6632,
                                                   loc_2976, pvrtmp_6634};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6643 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6644 = tmpcur_6616 + 8;
            CursorTy jump_4024 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2977, end_r_2978, loc_3206, tmpaftercur_6644);
            CursorTy pvrtmp_6645 = tmp_struct_67.field0;
            CursorTy pvrtmp_6646 = tmp_struct_67.field1;
            CursorTy pvrtmp_6647 = tmp_struct_67.field2;
            CursorTy pvrtmp_6648 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Content(end_r_2977, pvrtmp_6645, pvrtmp_6648, tmpcur_6643);
            CursorTy pvrtmp_6653 = tmp_struct_68.field0;
            CursorTy pvrtmp_6654 = tmp_struct_68.field1;
            CursorTy pvrtmp_6655 = tmp_struct_68.field2;
            CursorTy pvrtmp_6656 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2976 = 11;
            
            CursorTy writetag_4712 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4712 = pvrtmp_6648;
            
            CursorTy writecur_4713 = writetag_4712 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6653, pvrtmp_6654,
                                                   loc_2976, pvrtmp_6656};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6665 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6666 = tmpcur_6616 + 8;
            CursorTy tmpcur_6667 = *(CursorTy *) tmpaftercur_6666;
            CursorTy tmpaftercur_6668 = tmpaftercur_6666 + 8;
            CursorTy jump_4029 = tmpaftercur_6666 + 8;
            CursorTy jump_4028 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Tags(end_r_2977, end_r_2978, loc_3228, tmpaftercur_6668);
            CursorTy pvrtmp_6669 = tmp_struct_69.field0;
            CursorTy pvrtmp_6670 = tmp_struct_69.field1;
            CursorTy pvrtmp_6671 = tmp_struct_69.field2;
            CursorTy pvrtmp_6672 = tmp_struct_69.field3;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Content(end_r_2977, pvrtmp_6669, pvrtmp_6672, tmpcur_6665);
            CursorTy pvrtmp_6677 = tmp_struct_70.field0;
            CursorTy pvrtmp_6678 = tmp_struct_70.field1;
            CursorTy pvrtmp_6679 = tmp_struct_70.field2;
            CursorTy pvrtmp_6680 = tmp_struct_70.field3;
            CursorCursorCursorCursorProd tmp_struct_71 =
                                          _copy_Adt(end_r_2977, pvrtmp_6677, pvrtmp_6680, tmpcur_6667);
            CursorTy pvrtmp_6685 = tmp_struct_71.field0;
            CursorTy pvrtmp_6686 = tmp_struct_71.field1;
            CursorTy pvrtmp_6687 = tmp_struct_71.field2;
            CursorTy pvrtmp_6688 = tmp_struct_71.field3;
            
            *(TagTyPacked *) loc_2976 = 13;
            
            CursorTy writetag_4723 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4723 = pvrtmp_6672;
            
            CursorTy writecur_4724 = writetag_4723 + 8;
            
            *(CursorTy *) writecur_4724 = pvrtmp_6680;
            
            CursorTy writecur_4725 = writecur_4724 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6685, pvrtmp_6686,
                                                   loc_2976, pvrtmp_6688};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6697 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6698 = tmpcur_6616 + 8;
            CursorTy tmpcur_6699 = *(CursorTy *) tmpaftercur_6698;
            CursorTy tmpaftercur_6700 = tmpaftercur_6698 + 8;
            CursorTy jump_4035 = tmpaftercur_6698 + 8;
            CursorTy jump_4034 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_72 =
                                          _copy_Adt(end_r_2977, end_r_2978, loc_3254, tmpaftercur_6700);
            CursorTy pvrtmp_6701 = tmp_struct_72.field0;
            CursorTy pvrtmp_6702 = tmp_struct_72.field1;
            CursorTy pvrtmp_6703 = tmp_struct_72.field2;
            CursorTy pvrtmp_6704 = tmp_struct_72.field3;
            CursorCursorCursorCursorProd tmp_struct_73 =
                                          _copy_Content(end_r_2977, pvrtmp_6701, pvrtmp_6704, tmpcur_6697);
            CursorTy pvrtmp_6709 = tmp_struct_73.field0;
            CursorTy pvrtmp_6710 = tmp_struct_73.field1;
            CursorTy pvrtmp_6711 = tmp_struct_73.field2;
            CursorTy pvrtmp_6712 = tmp_struct_73.field3;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_Tags(end_r_2977, pvrtmp_6709, pvrtmp_6712, tmpcur_6699);
            CursorTy pvrtmp_6717 = tmp_struct_74.field0;
            CursorTy pvrtmp_6718 = tmp_struct_74.field1;
            CursorTy pvrtmp_6719 = tmp_struct_74.field2;
            CursorTy pvrtmp_6720 = tmp_struct_74.field3;
            
            *(TagTyPacked *) loc_2976 = 15;
            
            CursorTy writetag_4736 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4736 = pvrtmp_6704;
            
            CursorTy writecur_4737 = writetag_4736 + 8;
            
            *(CursorTy *) writecur_4737 = pvrtmp_6712;
            
            CursorTy writecur_4738 = writecur_4737 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6717, pvrtmp_6718,
                                                   loc_2976, pvrtmp_6720};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6729 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6730 = tmpcur_6616 + 8;
            CursorTy tmpcur_6731 = *(CursorTy *) tmpaftercur_6730;
            CursorTy tmpaftercur_6732 = tmpaftercur_6730 + 8;
            CursorTy jump_4041 = tmpaftercur_6730 + 8;
            CursorTy jump_4040 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_Tags(end_r_2977, end_r_2978, loc_3280, tmpaftercur_6732);
            CursorTy pvrtmp_6733 = tmp_struct_75.field0;
            CursorTy pvrtmp_6734 = tmp_struct_75.field1;
            CursorTy pvrtmp_6735 = tmp_struct_75.field2;
            CursorTy pvrtmp_6736 = tmp_struct_75.field3;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_Adt(end_r_2977, pvrtmp_6733, pvrtmp_6736, tmpcur_6729);
            CursorTy pvrtmp_6741 = tmp_struct_76.field0;
            CursorTy pvrtmp_6742 = tmp_struct_76.field1;
            CursorTy pvrtmp_6743 = tmp_struct_76.field2;
            CursorTy pvrtmp_6744 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_Content(end_r_2977, pvrtmp_6741, pvrtmp_6744, tmpcur_6731);
            CursorTy pvrtmp_6749 = tmp_struct_77.field0;
            CursorTy pvrtmp_6750 = tmp_struct_77.field1;
            CursorTy pvrtmp_6751 = tmp_struct_77.field2;
            CursorTy pvrtmp_6752 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2976 = 17;
            
            CursorTy writetag_4749 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4749 = pvrtmp_6736;
            
            CursorTy writecur_4750 = writetag_4749 + 8;
            
            *(CursorTy *) writecur_4750 = pvrtmp_6744;
            
            CursorTy writecur_4751 = writecur_4750 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6749, pvrtmp_6750,
                                                   loc_2976, pvrtmp_6752};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6761 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6762 = tmpcur_6616 + 8;
            CursorTy tmpcur_6763 = *(CursorTy *) tmpaftercur_6762;
            CursorTy tmpaftercur_6764 = tmpaftercur_6762 + 8;
            CursorTy jump_4047 = tmpaftercur_6762 + 8;
            CursorTy jump_4046 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_Adt(end_r_2977, end_r_2978, loc_3306, tmpaftercur_6764);
            CursorTy pvrtmp_6765 = tmp_struct_78.field0;
            CursorTy pvrtmp_6766 = tmp_struct_78.field1;
            CursorTy pvrtmp_6767 = tmp_struct_78.field2;
            CursorTy pvrtmp_6768 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_Tags(end_r_2977, pvrtmp_6765, pvrtmp_6768, tmpcur_6761);
            CursorTy pvrtmp_6773 = tmp_struct_79.field0;
            CursorTy pvrtmp_6774 = tmp_struct_79.field1;
            CursorTy pvrtmp_6775 = tmp_struct_79.field2;
            CursorTy pvrtmp_6776 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_Content(end_r_2977, pvrtmp_6773, pvrtmp_6776, tmpcur_6763);
            CursorTy pvrtmp_6781 = tmp_struct_80.field0;
            CursorTy pvrtmp_6782 = tmp_struct_80.field1;
            CursorTy pvrtmp_6783 = tmp_struct_80.field2;
            CursorTy pvrtmp_6784 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2976 = 19;
            
            CursorTy writetag_4762 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4762 = pvrtmp_6768;
            
            CursorTy writecur_4763 = writetag_4762 + 8;
            
            *(CursorTy *) writecur_4763 = pvrtmp_6776;
            
            CursorTy writecur_4764 = writecur_4763 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6781, pvrtmp_6782,
                                                   loc_2976, pvrtmp_6784};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6793 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6794 = tmpcur_6616 + 8;
            CursorTy tmpcur_6795 = *(CursorTy *) tmpaftercur_6794;
            CursorTy tmpaftercur_6796 = tmpaftercur_6794 + 8;
            CursorTy jump_4053 = tmpaftercur_6794 + 8;
            CursorTy jump_4052 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_Content(end_r_2977, end_r_2978, loc_3332, tmpaftercur_6796);
            CursorTy pvrtmp_6797 = tmp_struct_81.field0;
            CursorTy pvrtmp_6798 = tmp_struct_81.field1;
            CursorTy pvrtmp_6799 = tmp_struct_81.field2;
            CursorTy pvrtmp_6800 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_Tags(end_r_2977, pvrtmp_6797, pvrtmp_6800, tmpcur_6793);
            CursorTy pvrtmp_6805 = tmp_struct_82.field0;
            CursorTy pvrtmp_6806 = tmp_struct_82.field1;
            CursorTy pvrtmp_6807 = tmp_struct_82.field2;
            CursorTy pvrtmp_6808 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_Adt(end_r_2977, pvrtmp_6805, pvrtmp_6808, tmpcur_6795);
            CursorTy pvrtmp_6813 = tmp_struct_83.field0;
            CursorTy pvrtmp_6814 = tmp_struct_83.field1;
            CursorTy pvrtmp_6815 = tmp_struct_83.field2;
            CursorTy pvrtmp_6816 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2976 = 21;
            
            CursorTy writetag_4775 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4775 = pvrtmp_6800;
            
            CursorTy writecur_4776 = writetag_4775 + 8;
            
            *(CursorTy *) writecur_4776 = pvrtmp_6808;
            
            CursorTy writecur_4777 = writecur_4776 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6813, pvrtmp_6814,
                                                   loc_2976, pvrtmp_6816};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6825 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6826 = tmpcur_6616 + 8;
            CursorTy tmpcur_6827 = *(CursorTy *) tmpaftercur_6826;
            CursorTy tmpaftercur_6828 = tmpaftercur_6826 + 8;
            CursorTy jump_4059 = tmpaftercur_6826 + 8;
            CursorTy jump_4058 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_Content(end_r_2977, end_r_2978, loc_3358, tmpaftercur_6828);
            CursorTy pvrtmp_6829 = tmp_struct_84.field0;
            CursorTy pvrtmp_6830 = tmp_struct_84.field1;
            CursorTy pvrtmp_6831 = tmp_struct_84.field2;
            CursorTy pvrtmp_6832 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_Adt(end_r_2977, pvrtmp_6829, pvrtmp_6832, tmpcur_6825);
            CursorTy pvrtmp_6837 = tmp_struct_85.field0;
            CursorTy pvrtmp_6838 = tmp_struct_85.field1;
            CursorTy pvrtmp_6839 = tmp_struct_85.field2;
            CursorTy pvrtmp_6840 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_Tags(end_r_2977, pvrtmp_6837, pvrtmp_6840, tmpcur_6827);
            CursorTy pvrtmp_6845 = tmp_struct_86.field0;
            CursorTy pvrtmp_6846 = tmp_struct_86.field1;
            CursorTy pvrtmp_6847 = tmp_struct_86.field2;
            CursorTy pvrtmp_6848 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2976 = 23;
            
            CursorTy writetag_4788 = loc_2976 + 1;
            
            *(CursorTy *) writetag_4788 = pvrtmp_6832;
            
            CursorTy writecur_4789 = writetag_4788 + 8;
            
            *(CursorTy *) writecur_4789 = pvrtmp_6840;
            
            CursorTy writecur_4790 = writecur_4789 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6845, pvrtmp_6846,
                                                   loc_2976, pvrtmp_6848};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6857 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6858 = tmpcur_6616 + 8;
            CursorTy jump_4335 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_Adt(end_r_2977, end_r_2978, loc_2976, tmpcur_6857);
            CursorTy pvrtmp_6859 = tmp_struct_87.field0;
            CursorTy pvrtmp_6860 = tmp_struct_87.field1;
            CursorTy pvrtmp_6861 = tmp_struct_87.field2;
            CursorTy pvrtmp_6862 = tmp_struct_87.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6859, jump_4335,
                                                   pvrtmp_6861, pvrtmp_6862};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6869 = *(CursorTy *) tmpcur_6616;
            CursorTy tmpaftercur_6870 = tmpcur_6616 + 8;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_Adt(end_r_2977, end_r_2978, loc_2976, tmpcur_6869);
            CursorTy pvrtmp_6871 = tmp_struct_88.field0;
            CursorTy pvrtmp_6872 = tmp_struct_88.field1;
            CursorTy pvrtmp_6873 = tmp_struct_88.field2;
            CursorTy pvrtmp_6874 = tmp_struct_88.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6871, pvrtmp_6872,
                                                   pvrtmp_6873, pvrtmp_6874};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6615");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2981,
                                                    CursorTy end_r_2982,
                                                    CursorTy loc_2980,
                                                    CursorTy arg_739_1351_1672)
{
    TagTyPacked tmpval_6882 = *(TagTyPacked *) arg_739_1351_1672;
    CursorTy tmpcur_6883 = arg_739_1351_1672 + 1;
    
    
  switch_7148:
    ;
    switch (tmpval_6882) {
        
      case 0:
        {
            CursorTy jump_4064 = arg_739_1351_1672 + 1;
            
            *(TagTyPacked *) loc_2980 = 0;
            
            CursorTy writetag_4802 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2982, jump_4064,
                                                   loc_2980, writetag_4802};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6888 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_6889 = tmpcur_6883 + 8;
            CursorTy jump_4066 = tmpcur_6883 + 8;
            CursorTy loc_3380 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Content(end_r_2981, end_r_2982, loc_3380, tmpaftercur_6889);
            CursorTy pvrtmp_6890 = tmp_struct_92.field0;
            CursorTy pvrtmp_6891 = tmp_struct_92.field1;
            CursorTy pvrtmp_6892 = tmp_struct_92.field2;
            CursorTy pvrtmp_6893 = tmp_struct_92.field3;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Adt(end_r_2981, pvrtmp_6890, pvrtmp_6893, tmpcur_6888);
            CursorTy pvrtmp_6898 = tmp_struct_93.field0;
            CursorTy pvrtmp_6899 = tmp_struct_93.field1;
            CursorTy pvrtmp_6900 = tmp_struct_93.field2;
            CursorTy pvrtmp_6901 = tmp_struct_93.field3;
            
            *(TagTyPacked *) loc_2980 = 1;
            
            CursorTy writetag_4808 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6898, pvrtmp_6899,
                                                   loc_2980, pvrtmp_6901};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6910 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_6911 = tmpcur_6883 + 8;
            CursorTy jump_4070 = tmpcur_6883 + 8;
            CursorTy loc_3393 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2981, end_r_2982, loc_3393, tmpaftercur_6911);
            CursorTy pvrtmp_6912 = tmp_struct_94.field0;
            CursorTy pvrtmp_6913 = tmp_struct_94.field1;
            CursorTy pvrtmp_6914 = tmp_struct_94.field2;
            CursorTy pvrtmp_6915 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Content(end_r_2981, pvrtmp_6912, pvrtmp_6915, tmpcur_6910);
            CursorTy pvrtmp_6920 = tmp_struct_95.field0;
            CursorTy pvrtmp_6921 = tmp_struct_95.field1;
            CursorTy pvrtmp_6922 = tmp_struct_95.field2;
            CursorTy pvrtmp_6923 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2980 = 2;
            
            CursorTy writetag_4816 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6920, pvrtmp_6921,
                                                   loc_2980, pvrtmp_6923};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6932 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_6933 = tmpcur_6883 + 8;
            CursorTy tmpcur_6934 = *(CursorTy *) tmpaftercur_6933;
            CursorTy tmpaftercur_6935 = tmpaftercur_6933 + 8;
            CursorTy jump_4075 = tmpaftercur_6933 + 8;
            CursorTy jump_4074 = tmpcur_6883 + 8;
            CursorTy loc_3411 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Tags(end_r_2981, end_r_2982, loc_3411, tmpaftercur_6935);
            CursorTy pvrtmp_6936 = tmp_struct_96.field0;
            CursorTy pvrtmp_6937 = tmp_struct_96.field1;
            CursorTy pvrtmp_6938 = tmp_struct_96.field2;
            CursorTy pvrtmp_6939 = tmp_struct_96.field3;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Content(end_r_2981, pvrtmp_6936, pvrtmp_6939, tmpcur_6932);
            CursorTy pvrtmp_6944 = tmp_struct_97.field0;
            CursorTy pvrtmp_6945 = tmp_struct_97.field1;
            CursorTy pvrtmp_6946 = tmp_struct_97.field2;
            CursorTy pvrtmp_6947 = tmp_struct_97.field3;
            CursorCursorCursorCursorProd tmp_struct_98 =
                                          _copy_without_ptrs_Adt(end_r_2981, pvrtmp_6944, pvrtmp_6947, tmpcur_6934);
            CursorTy pvrtmp_6952 = tmp_struct_98.field0;
            CursorTy pvrtmp_6953 = tmp_struct_98.field1;
            CursorTy pvrtmp_6954 = tmp_struct_98.field2;
            CursorTy pvrtmp_6955 = tmp_struct_98.field3;
            
            *(TagTyPacked *) loc_2980 = 3;
            
            CursorTy writetag_4826 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6952, pvrtmp_6953,
                                                   loc_2980, pvrtmp_6955};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6964 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_6965 = tmpcur_6883 + 8;
            CursorTy tmpcur_6966 = *(CursorTy *) tmpaftercur_6965;
            CursorTy tmpaftercur_6967 = tmpaftercur_6965 + 8;
            CursorTy jump_4081 = tmpaftercur_6965 + 8;
            CursorTy jump_4080 = tmpcur_6883 + 8;
            CursorTy loc_3431 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_99 =
                                          _copy_without_ptrs_Adt(end_r_2981, end_r_2982, loc_3431, tmpaftercur_6967);
            CursorTy pvrtmp_6968 = tmp_struct_99.field0;
            CursorTy pvrtmp_6969 = tmp_struct_99.field1;
            CursorTy pvrtmp_6970 = tmp_struct_99.field2;
            CursorTy pvrtmp_6971 = tmp_struct_99.field3;
            CursorCursorCursorCursorProd tmp_struct_100 =
                                          _copy_without_ptrs_Content(end_r_2981, pvrtmp_6968, pvrtmp_6971, tmpcur_6964);
            CursorTy pvrtmp_6976 = tmp_struct_100.field0;
            CursorTy pvrtmp_6977 = tmp_struct_100.field1;
            CursorTy pvrtmp_6978 = tmp_struct_100.field2;
            CursorTy pvrtmp_6979 = tmp_struct_100.field3;
            CursorCursorCursorCursorProd tmp_struct_101 =
                                          _copy_without_ptrs_Tags(end_r_2981, pvrtmp_6976, pvrtmp_6979, tmpcur_6966);
            CursorTy pvrtmp_6984 = tmp_struct_101.field0;
            CursorTy pvrtmp_6985 = tmp_struct_101.field1;
            CursorTy pvrtmp_6986 = tmp_struct_101.field2;
            CursorTy pvrtmp_6987 = tmp_struct_101.field3;
            
            *(TagTyPacked *) loc_2980 = 4;
            
            CursorTy writetag_4837 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6984, pvrtmp_6985,
                                                   loc_2980, pvrtmp_6987};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6996 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_6997 = tmpcur_6883 + 8;
            CursorTy tmpcur_6998 = *(CursorTy *) tmpaftercur_6997;
            CursorTy tmpaftercur_6999 = tmpaftercur_6997 + 8;
            CursorTy jump_4087 = tmpaftercur_6997 + 8;
            CursorTy jump_4086 = tmpcur_6883 + 8;
            CursorTy loc_3451 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_102 =
                                          _copy_without_ptrs_Tags(end_r_2981, end_r_2982, loc_3451, tmpaftercur_6999);
            CursorTy pvrtmp_7000 = tmp_struct_102.field0;
            CursorTy pvrtmp_7001 = tmp_struct_102.field1;
            CursorTy pvrtmp_7002 = tmp_struct_102.field2;
            CursorTy pvrtmp_7003 = tmp_struct_102.field3;
            CursorCursorCursorCursorProd tmp_struct_103 =
                                          _copy_without_ptrs_Adt(end_r_2981, pvrtmp_7000, pvrtmp_7003, tmpcur_6996);
            CursorTy pvrtmp_7008 = tmp_struct_103.field0;
            CursorTy pvrtmp_7009 = tmp_struct_103.field1;
            CursorTy pvrtmp_7010 = tmp_struct_103.field2;
            CursorTy pvrtmp_7011 = tmp_struct_103.field3;
            CursorCursorCursorCursorProd tmp_struct_104 =
                                          _copy_without_ptrs_Content(end_r_2981, pvrtmp_7008, pvrtmp_7011, tmpcur_6998);
            CursorTy pvrtmp_7016 = tmp_struct_104.field0;
            CursorTy pvrtmp_7017 = tmp_struct_104.field1;
            CursorTy pvrtmp_7018 = tmp_struct_104.field2;
            CursorTy pvrtmp_7019 = tmp_struct_104.field3;
            
            *(TagTyPacked *) loc_2980 = 5;
            
            CursorTy writetag_4848 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7016, pvrtmp_7017,
                                                   loc_2980, pvrtmp_7019};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7028 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_7029 = tmpcur_6883 + 8;
            CursorTy tmpcur_7030 = *(CursorTy *) tmpaftercur_7029;
            CursorTy tmpaftercur_7031 = tmpaftercur_7029 + 8;
            CursorTy jump_4093 = tmpaftercur_7029 + 8;
            CursorTy jump_4092 = tmpcur_6883 + 8;
            CursorTy loc_3471 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_105 =
                                          _copy_without_ptrs_Adt(end_r_2981, end_r_2982, loc_3471, tmpaftercur_7031);
            CursorTy pvrtmp_7032 = tmp_struct_105.field0;
            CursorTy pvrtmp_7033 = tmp_struct_105.field1;
            CursorTy pvrtmp_7034 = tmp_struct_105.field2;
            CursorTy pvrtmp_7035 = tmp_struct_105.field3;
            CursorCursorCursorCursorProd tmp_struct_106 =
                                          _copy_without_ptrs_Tags(end_r_2981, pvrtmp_7032, pvrtmp_7035, tmpcur_7028);
            CursorTy pvrtmp_7040 = tmp_struct_106.field0;
            CursorTy pvrtmp_7041 = tmp_struct_106.field1;
            CursorTy pvrtmp_7042 = tmp_struct_106.field2;
            CursorTy pvrtmp_7043 = tmp_struct_106.field3;
            CursorCursorCursorCursorProd tmp_struct_107 =
                                          _copy_without_ptrs_Content(end_r_2981, pvrtmp_7040, pvrtmp_7043, tmpcur_7030);
            CursorTy pvrtmp_7048 = tmp_struct_107.field0;
            CursorTy pvrtmp_7049 = tmp_struct_107.field1;
            CursorTy pvrtmp_7050 = tmp_struct_107.field2;
            CursorTy pvrtmp_7051 = tmp_struct_107.field3;
            
            *(TagTyPacked *) loc_2980 = 6;
            
            CursorTy writetag_4859 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7048, pvrtmp_7049,
                                                   loc_2980, pvrtmp_7051};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7060 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_7061 = tmpcur_6883 + 8;
            CursorTy tmpcur_7062 = *(CursorTy *) tmpaftercur_7061;
            CursorTy tmpaftercur_7063 = tmpaftercur_7061 + 8;
            CursorTy jump_4099 = tmpaftercur_7061 + 8;
            CursorTy jump_4098 = tmpcur_6883 + 8;
            CursorTy loc_3491 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_108 =
                                          _copy_without_ptrs_Content(end_r_2981, end_r_2982, loc_3491, tmpaftercur_7063);
            CursorTy pvrtmp_7064 = tmp_struct_108.field0;
            CursorTy pvrtmp_7065 = tmp_struct_108.field1;
            CursorTy pvrtmp_7066 = tmp_struct_108.field2;
            CursorTy pvrtmp_7067 = tmp_struct_108.field3;
            CursorCursorCursorCursorProd tmp_struct_109 =
                                          _copy_without_ptrs_Tags(end_r_2981, pvrtmp_7064, pvrtmp_7067, tmpcur_7060);
            CursorTy pvrtmp_7072 = tmp_struct_109.field0;
            CursorTy pvrtmp_7073 = tmp_struct_109.field1;
            CursorTy pvrtmp_7074 = tmp_struct_109.field2;
            CursorTy pvrtmp_7075 = tmp_struct_109.field3;
            CursorCursorCursorCursorProd tmp_struct_110 =
                                          _copy_without_ptrs_Adt(end_r_2981, pvrtmp_7072, pvrtmp_7075, tmpcur_7062);
            CursorTy pvrtmp_7080 = tmp_struct_110.field0;
            CursorTy pvrtmp_7081 = tmp_struct_110.field1;
            CursorTy pvrtmp_7082 = tmp_struct_110.field2;
            CursorTy pvrtmp_7083 = tmp_struct_110.field3;
            
            *(TagTyPacked *) loc_2980 = 7;
            
            CursorTy writetag_4870 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7080, pvrtmp_7081,
                                                   loc_2980, pvrtmp_7083};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7092 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_7093 = tmpcur_6883 + 8;
            CursorTy tmpcur_7094 = *(CursorTy *) tmpaftercur_7093;
            CursorTy tmpaftercur_7095 = tmpaftercur_7093 + 8;
            CursorTy jump_4105 = tmpaftercur_7093 + 8;
            CursorTy jump_4104 = tmpcur_6883 + 8;
            CursorTy loc_3511 = loc_2980 + 1;
            CursorCursorCursorCursorProd tmp_struct_111 =
                                          _copy_without_ptrs_Content(end_r_2981, end_r_2982, loc_3511, tmpaftercur_7095);
            CursorTy pvrtmp_7096 = tmp_struct_111.field0;
            CursorTy pvrtmp_7097 = tmp_struct_111.field1;
            CursorTy pvrtmp_7098 = tmp_struct_111.field2;
            CursorTy pvrtmp_7099 = tmp_struct_111.field3;
            CursorCursorCursorCursorProd tmp_struct_112 =
                                          _copy_without_ptrs_Adt(end_r_2981, pvrtmp_7096, pvrtmp_7099, tmpcur_7092);
            CursorTy pvrtmp_7104 = tmp_struct_112.field0;
            CursorTy pvrtmp_7105 = tmp_struct_112.field1;
            CursorTy pvrtmp_7106 = tmp_struct_112.field2;
            CursorTy pvrtmp_7107 = tmp_struct_112.field3;
            CursorCursorCursorCursorProd tmp_struct_113 =
                                          _copy_without_ptrs_Tags(end_r_2981, pvrtmp_7104, pvrtmp_7107, tmpcur_7094);
            CursorTy pvrtmp_7112 = tmp_struct_113.field0;
            CursorTy pvrtmp_7113 = tmp_struct_113.field1;
            CursorTy pvrtmp_7114 = tmp_struct_113.field2;
            CursorTy pvrtmp_7115 = tmp_struct_113.field3;
            
            *(TagTyPacked *) loc_2980 = 8;
            
            CursorTy writetag_4881 = loc_2980 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7112, pvrtmp_7113,
                                                   loc_2980, pvrtmp_7115};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7124 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_7125 = tmpcur_6883 + 8;
            CursorTy jump_4341 = tmpcur_6883 + 8;
            CursorCursorCursorCursorProd tmp_struct_114 =
                                          _copy_without_ptrs_Adt(end_r_2981, end_r_2982, loc_2980, tmpcur_7124);
            CursorTy pvrtmp_7126 = tmp_struct_114.field0;
            CursorTy pvrtmp_7127 = tmp_struct_114.field1;
            CursorTy pvrtmp_7128 = tmp_struct_114.field2;
            CursorTy pvrtmp_7129 = tmp_struct_114.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7126, jump_4341,
                                                   pvrtmp_7128, pvrtmp_7129};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7136 = *(CursorTy *) tmpcur_6883;
            CursorTy tmpaftercur_7137 = tmpcur_6883 + 8;
            CursorCursorCursorCursorProd tmp_struct_115 =
                                          _copy_without_ptrs_Adt(end_r_2981, end_r_2982, loc_2980, tmpcur_7136);
            CursorTy pvrtmp_7138 = tmp_struct_115.field0;
            CursorTy pvrtmp_7139 = tmp_struct_115.field1;
            CursorTy pvrtmp_7140 = tmp_struct_115.field2;
            CursorTy pvrtmp_7141 = tmp_struct_115.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7138, pvrtmp_7139,
                                                   pvrtmp_7140, pvrtmp_7141};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6882");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2984, CursorTy arg_784_1396_1717)
{
    TagTyPacked tmpval_7149 = *(TagTyPacked *) arg_784_1396_1717;
    CursorTy tmpcur_7150 = arg_784_1396_1717 + 1;
    
    
  switch_7207:
    ;
    switch (tmpval_7149) {
        
      case 0:
        {
            CursorTy jump_4110 = arg_784_1396_1717 + 1;
            
            return (CursorProd) {jump_4110};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7151 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7152 = tmpcur_7150 + 8;
            CursorTy jump_4112 = tmpcur_7150 + 8;
            CursorProd tmp_struct_116 =
                        _traverse_Content(end_r_2984, tmpaftercur_7152);
            CursorTy pvrtmp_7153 = tmp_struct_116.field0;
            CursorProd tmp_struct_117 =  _traverse_Adt(end_r_2984, tmpcur_7151);
            CursorTy pvrtmp_7154 = tmp_struct_117.field0;
            
            return (CursorProd) {pvrtmp_7154};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7155 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7156 = tmpcur_7150 + 8;
            CursorTy jump_4116 = tmpcur_7150 + 8;
            CursorProd tmp_struct_118 =
                        _traverse_Adt(end_r_2984, tmpaftercur_7156);
            CursorTy pvrtmp_7157 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Content(end_r_2984, tmpcur_7155);
            CursorTy pvrtmp_7158 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_7158};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7159 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7160 = tmpcur_7150 + 8;
            CursorTy tmpcur_7161 = *(CursorTy *) tmpaftercur_7160;
            CursorTy tmpaftercur_7162 = tmpaftercur_7160 + 8;
            CursorTy jump_4121 = tmpaftercur_7160 + 8;
            CursorTy jump_4120 = tmpcur_7150 + 8;
            CursorProd tmp_struct_120 =
                        _traverse_Tags(end_r_2984, tmpaftercur_7162);
            CursorTy pvrtmp_7163 = tmp_struct_120.field0;
            CursorProd tmp_struct_121 =
                        _traverse_Content(end_r_2984, tmpcur_7159);
            CursorTy pvrtmp_7164 = tmp_struct_121.field0;
            CursorProd tmp_struct_122 =  _traverse_Adt(end_r_2984, tmpcur_7161);
            CursorTy pvrtmp_7165 = tmp_struct_122.field0;
            
            return (CursorProd) {pvrtmp_7165};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7166 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7167 = tmpcur_7150 + 8;
            CursorTy tmpcur_7168 = *(CursorTy *) tmpaftercur_7167;
            CursorTy tmpaftercur_7169 = tmpaftercur_7167 + 8;
            CursorTy jump_4127 = tmpaftercur_7167 + 8;
            CursorTy jump_4126 = tmpcur_7150 + 8;
            CursorProd tmp_struct_123 =
                        _traverse_Adt(end_r_2984, tmpaftercur_7169);
            CursorTy pvrtmp_7170 = tmp_struct_123.field0;
            CursorProd tmp_struct_124 =
                        _traverse_Content(end_r_2984, tmpcur_7166);
            CursorTy pvrtmp_7171 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _traverse_Tags(end_r_2984, tmpcur_7168);
            CursorTy pvrtmp_7172 = tmp_struct_125.field0;
            
            return (CursorProd) {pvrtmp_7172};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7173 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7174 = tmpcur_7150 + 8;
            CursorTy tmpcur_7175 = *(CursorTy *) tmpaftercur_7174;
            CursorTy tmpaftercur_7176 = tmpaftercur_7174 + 8;
            CursorTy jump_4133 = tmpaftercur_7174 + 8;
            CursorTy jump_4132 = tmpcur_7150 + 8;
            CursorProd tmp_struct_126 =
                        _traverse_Tags(end_r_2984, tmpaftercur_7176);
            CursorTy pvrtmp_7177 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =  _traverse_Adt(end_r_2984, tmpcur_7173);
            CursorTy pvrtmp_7178 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =
                        _traverse_Content(end_r_2984, tmpcur_7175);
            CursorTy pvrtmp_7179 = tmp_struct_128.field0;
            
            return (CursorProd) {pvrtmp_7179};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7180 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7181 = tmpcur_7150 + 8;
            CursorTy tmpcur_7182 = *(CursorTy *) tmpaftercur_7181;
            CursorTy tmpaftercur_7183 = tmpaftercur_7181 + 8;
            CursorTy jump_4139 = tmpaftercur_7181 + 8;
            CursorTy jump_4138 = tmpcur_7150 + 8;
            CursorProd tmp_struct_129 =
                        _traverse_Adt(end_r_2984, tmpaftercur_7183);
            CursorTy pvrtmp_7184 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _traverse_Tags(end_r_2984, tmpcur_7180);
            CursorTy pvrtmp_7185 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =
                        _traverse_Content(end_r_2984, tmpcur_7182);
            CursorTy pvrtmp_7186 = tmp_struct_131.field0;
            
            return (CursorProd) {pvrtmp_7186};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7187 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7188 = tmpcur_7150 + 8;
            CursorTy tmpcur_7189 = *(CursorTy *) tmpaftercur_7188;
            CursorTy tmpaftercur_7190 = tmpaftercur_7188 + 8;
            CursorTy jump_4145 = tmpaftercur_7188 + 8;
            CursorTy jump_4144 = tmpcur_7150 + 8;
            CursorProd tmp_struct_132 =
                        _traverse_Content(end_r_2984, tmpaftercur_7190);
            CursorTy pvrtmp_7191 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =
                        _traverse_Tags(end_r_2984, tmpcur_7187);
            CursorTy pvrtmp_7192 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =  _traverse_Adt(end_r_2984, tmpcur_7189);
            CursorTy pvrtmp_7193 = tmp_struct_134.field0;
            
            return (CursorProd) {pvrtmp_7193};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7194 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7195 = tmpcur_7150 + 8;
            CursorTy tmpcur_7196 = *(CursorTy *) tmpaftercur_7195;
            CursorTy tmpaftercur_7197 = tmpaftercur_7195 + 8;
            CursorTy jump_4151 = tmpaftercur_7195 + 8;
            CursorTy jump_4150 = tmpcur_7150 + 8;
            CursorProd tmp_struct_135 =
                        _traverse_Content(end_r_2984, tmpaftercur_7197);
            CursorTy pvrtmp_7198 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _traverse_Adt(end_r_2984, tmpcur_7194);
            CursorTy pvrtmp_7199 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _traverse_Tags(end_r_2984, tmpcur_7196);
            CursorTy pvrtmp_7200 = tmp_struct_137.field0;
            
            return (CursorProd) {pvrtmp_7200};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7201 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7202 = tmpcur_7150 + 8;
            CursorTy jump_4347 = tmpcur_7150 + 8;
            CursorProd tmp_struct_138 =  _traverse_Adt(end_r_2984, tmpcur_7201);
            CursorTy pvrtmp_7203 = tmp_struct_138.field0;
            
            return (CursorProd) {jump_4347};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7204 = *(CursorTy *) tmpcur_7150;
            CursorTy tmpaftercur_7205 = tmpcur_7150 + 8;
            CursorProd tmp_struct_139 =  _traverse_Adt(end_r_2984, tmpcur_7204);
            CursorTy pvrtmp_7206 = tmp_struct_139.field0;
            
            return (CursorProd) {pvrtmp_7206};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7149");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2986, CursorTy arg_829_1441_1762)
{
    TagTyPacked tmpval_7208 = *(TagTyPacked *) arg_829_1441_1762;
    CursorTy tmpcur_7209 = arg_829_1441_1762 + 1;
    
    
  switch_7266:
    ;
    switch (tmpval_7208) {
        
      case 0:
        {
            CursorTy jump_4156 = arg_829_1441_1762 + 1;
            unsigned char wildcard_830_1442_1763 = print_symbol(6166);
            unsigned char wildcard_831_1443_1764 = print_symbol(6160);
            
            return (CursorProd) {jump_4156};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_7210 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7211 = tmpcur_7209 + 8;
            CursorTy jump_4158 = tmpcur_7209 + 8;
            unsigned char wildcard_836_1446_1767 = print_symbol(6172);
            CursorProd tmp_struct_140 =
                        _print_Content(end_r_2986, tmpaftercur_7211);
            CursorTy pvrtmp_7212 = tmp_struct_140.field0;
            CursorProd tmp_struct_141 =  _print_Adt(end_r_2986, tmpcur_7210);
            CursorTy pvrtmp_7213 = tmp_struct_141.field0;
            unsigned char wildcard_837_1449_1770 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7213};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_7214 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7215 = tmpcur_7209 + 8;
            CursorTy jump_4162 = tmpcur_7209 + 8;
            unsigned char wildcard_842_1452_1773 = print_symbol(6175);
            CursorProd tmp_struct_142 =
                        _print_Adt(end_r_2986, tmpaftercur_7215);
            CursorTy pvrtmp_7216 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =
                        _print_Content(end_r_2986, tmpcur_7214);
            CursorTy pvrtmp_7217 = tmp_struct_143.field0;
            unsigned char wildcard_843_1455_1776 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7217};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_7218 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7219 = tmpcur_7209 + 8;
            CursorTy tmpcur_7220 = *(CursorTy *) tmpaftercur_7219;
            CursorTy tmpaftercur_7221 = tmpaftercur_7219 + 8;
            CursorTy jump_4167 = tmpaftercur_7219 + 8;
            CursorTy jump_4166 = tmpcur_7209 + 8;
            unsigned char wildcard_850_1459_1780 = print_symbol(6163);
            CursorProd tmp_struct_144 =
                        _print_Tags(end_r_2986, tmpaftercur_7221);
            CursorTy pvrtmp_7222 = tmp_struct_144.field0;
            CursorProd tmp_struct_145 =
                        _print_Content(end_r_2986, tmpcur_7218);
            CursorTy pvrtmp_7223 = tmp_struct_145.field0;
            CursorProd tmp_struct_146 =  _print_Adt(end_r_2986, tmpcur_7220);
            CursorTy pvrtmp_7224 = tmp_struct_146.field0;
            unsigned char wildcard_851_1463_1784 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7224};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_7225 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7226 = tmpcur_7209 + 8;
            CursorTy tmpcur_7227 = *(CursorTy *) tmpaftercur_7226;
            CursorTy tmpaftercur_7228 = tmpaftercur_7226 + 8;
            CursorTy jump_4173 = tmpaftercur_7226 + 8;
            CursorTy jump_4172 = tmpcur_7209 + 8;
            unsigned char wildcard_858_1467_1788 = print_symbol(6174);
            CursorProd tmp_struct_147 =
                        _print_Adt(end_r_2986, tmpaftercur_7228);
            CursorTy pvrtmp_7229 = tmp_struct_147.field0;
            CursorProd tmp_struct_148 =
                        _print_Content(end_r_2986, tmpcur_7225);
            CursorTy pvrtmp_7230 = tmp_struct_148.field0;
            CursorProd tmp_struct_149 =  _print_Tags(end_r_2986, tmpcur_7227);
            CursorTy pvrtmp_7231 = tmp_struct_149.field0;
            unsigned char wildcard_859_1471_1792 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7231};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_7232 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7233 = tmpcur_7209 + 8;
            CursorTy tmpcur_7234 = *(CursorTy *) tmpaftercur_7233;
            CursorTy tmpaftercur_7235 = tmpaftercur_7233 + 8;
            CursorTy jump_4179 = tmpaftercur_7233 + 8;
            CursorTy jump_4178 = tmpcur_7209 + 8;
            unsigned char wildcard_866_1475_1796 = print_symbol(6164);
            CursorProd tmp_struct_150 =
                        _print_Tags(end_r_2986, tmpaftercur_7235);
            CursorTy pvrtmp_7236 = tmp_struct_150.field0;
            CursorProd tmp_struct_151 =  _print_Adt(end_r_2986, tmpcur_7232);
            CursorTy pvrtmp_7237 = tmp_struct_151.field0;
            CursorProd tmp_struct_152 =
                        _print_Content(end_r_2986, tmpcur_7234);
            CursorTy pvrtmp_7238 = tmp_struct_152.field0;
            unsigned char wildcard_867_1479_1800 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7238};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_7239 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7240 = tmpcur_7209 + 8;
            CursorTy tmpcur_7241 = *(CursorTy *) tmpaftercur_7240;
            CursorTy tmpaftercur_7242 = tmpaftercur_7240 + 8;
            CursorTy jump_4185 = tmpaftercur_7240 + 8;
            CursorTy jump_4184 = tmpcur_7209 + 8;
            unsigned char wildcard_874_1483_1804 = print_symbol(6173);
            CursorProd tmp_struct_153 =
                        _print_Adt(end_r_2986, tmpaftercur_7242);
            CursorTy pvrtmp_7243 = tmp_struct_153.field0;
            CursorProd tmp_struct_154 =  _print_Tags(end_r_2986, tmpcur_7239);
            CursorTy pvrtmp_7244 = tmp_struct_154.field0;
            CursorProd tmp_struct_155 =
                        _print_Content(end_r_2986, tmpcur_7241);
            CursorTy pvrtmp_7245 = tmp_struct_155.field0;
            unsigned char wildcard_875_1487_1808 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7245};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_7246 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7247 = tmpcur_7209 + 8;
            CursorTy tmpcur_7248 = *(CursorTy *) tmpaftercur_7247;
            CursorTy tmpaftercur_7249 = tmpaftercur_7247 + 8;
            CursorTy jump_4191 = tmpaftercur_7247 + 8;
            CursorTy jump_4190 = tmpcur_7209 + 8;
            unsigned char wildcard_882_1491_1812 = print_symbol(6170);
            CursorProd tmp_struct_156 =
                        _print_Content(end_r_2986, tmpaftercur_7249);
            CursorTy pvrtmp_7250 = tmp_struct_156.field0;
            CursorProd tmp_struct_157 =  _print_Tags(end_r_2986, tmpcur_7246);
            CursorTy pvrtmp_7251 = tmp_struct_157.field0;
            CursorProd tmp_struct_158 =  _print_Adt(end_r_2986, tmpcur_7248);
            CursorTy pvrtmp_7252 = tmp_struct_158.field0;
            unsigned char wildcard_883_1495_1816 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7252};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_7253 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7254 = tmpcur_7209 + 8;
            CursorTy tmpcur_7255 = *(CursorTy *) tmpaftercur_7254;
            CursorTy tmpaftercur_7256 = tmpaftercur_7254 + 8;
            CursorTy jump_4197 = tmpaftercur_7254 + 8;
            CursorTy jump_4196 = tmpcur_7209 + 8;
            unsigned char wildcard_890_1499_1820 = print_symbol(6171);
            CursorProd tmp_struct_159 =
                        _print_Content(end_r_2986, tmpaftercur_7256);
            CursorTy pvrtmp_7257 = tmp_struct_159.field0;
            CursorProd tmp_struct_160 =  _print_Adt(end_r_2986, tmpcur_7253);
            CursorTy pvrtmp_7258 = tmp_struct_160.field0;
            CursorProd tmp_struct_161 =  _print_Tags(end_r_2986, tmpcur_7255);
            CursorTy pvrtmp_7259 = tmp_struct_161.field0;
            unsigned char wildcard_891_1503_1824 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7259};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7260 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7261 = tmpcur_7209 + 8;
            CursorTy jump_4353 = tmpcur_7209 + 8;
            unsigned char wildcard_4356 = print_symbol(6177);
            CursorProd tmp_struct_162 =  _print_Adt(end_r_2986, tmpcur_7260);
            CursorTy pvrtmp_7262 = tmp_struct_162.field0;
            
            return (CursorProd) {jump_4353};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7263 = *(CursorTy *) tmpcur_7209;
            CursorTy tmpaftercur_7264 = tmpcur_7209 + 8;
            unsigned char wildcard_4356 = print_symbol(6176);
            CursorProd tmp_struct_163 =  _print_Adt(end_r_2986, tmpcur_7263);
            CursorTy pvrtmp_7265 = tmp_struct_163.field0;
            
            return (CursorProd) {pvrtmp_7265};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7208");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2989,
                                        CursorTy end_r_2990, CursorTy loc_2988,
                                        CursorTy arg_892_1504_1825)
{
    if (loc_2988 + 32 > end_r_2990) {
        ChunkTy new_chunk_167 = alloc_chunk(end_r_2990);
        CursorTy chunk_start_168 = new_chunk_167.chunk_start;
        CursorTy chunk_end_169 = new_chunk_167.chunk_end;
        
        end_r_2990 = chunk_end_169;
        *(TagTyPacked *) loc_2988 = 255;
        
        CursorTy redir = loc_2988 + 1;
        
        *(CursorTy *) redir = chunk_start_168;
        loc_2988 = chunk_start_168;
    }
    
    CursorTy loc_3689 = loc_2988 + 1;
    CursorTy loc_3690 = loc_3689 + 8;
    TagTyPacked tmpval_7267 = *(TagTyPacked *) arg_892_1504_1825;
    CursorTy tmpcur_7268 = arg_892_1504_1825 + 1;
    
    
  switch_7311:
    ;
    switch (tmpval_7267) {
        
      case 0:
        {
            CursorTy jump_4202 = arg_892_1504_1825 + 1;
            
            *(TagTyPacked *) loc_2988 = 0;
            
            CursorTy writetag_4995 = loc_2988 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2990, jump_4202,
                                                   loc_2988, writetag_4995};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7273 = *(IntTy *) tmpcur_7268;
            CursorTy tmpcur_7274 = tmpcur_7268 + sizeof(IntTy);
            CursorTy jump_4204 = tmpcur_7268 + 8;
            CursorCursorCursorCursorProd tmp_struct_164 =
                                          _copy_Tags(end_r_2989, end_r_2990, loc_3690, tmpcur_7274);
            CursorTy pvrtmp_7275 = tmp_struct_164.field0;
            CursorTy pvrtmp_7276 = tmp_struct_164.field1;
            CursorTy pvrtmp_7277 = tmp_struct_164.field2;
            CursorTy pvrtmp_7278 = tmp_struct_164.field3;
            
            *(TagTyPacked *) loc_2988 = 1;
            
            CursorTy writetag_5000 = loc_2988 + 1;
            
            *(IntTy *) writetag_5000 = tmpval_7273;
            
            CursorTy writecur_5001 = writetag_5000 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7275, pvrtmp_7276,
                                                   loc_2988, pvrtmp_7278};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7287 = *(CursorTy *) tmpcur_7268;
            CursorTy tmpaftercur_7288 = tmpcur_7268 + 8;
            CursorTy jump_4359 = tmpcur_7268 + 8;
            CursorCursorCursorCursorProd tmp_struct_165 =
                                          _copy_Tags(end_r_2989, end_r_2990, loc_2988, tmpcur_7287);
            CursorTy pvrtmp_7289 = tmp_struct_165.field0;
            CursorTy pvrtmp_7290 = tmp_struct_165.field1;
            CursorTy pvrtmp_7291 = tmp_struct_165.field2;
            CursorTy pvrtmp_7292 = tmp_struct_165.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7289, jump_4359,
                                                   pvrtmp_7291, pvrtmp_7292};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7299 = *(CursorTy *) tmpcur_7268;
            CursorTy tmpaftercur_7300 = tmpcur_7268 + 8;
            CursorCursorCursorCursorProd tmp_struct_166 =
                                          _copy_Tags(end_r_2989, end_r_2990, loc_2988, tmpcur_7299);
            CursorTy pvrtmp_7301 = tmp_struct_166.field0;
            CursorTy pvrtmp_7302 = tmp_struct_166.field1;
            CursorTy pvrtmp_7303 = tmp_struct_166.field2;
            CursorTy pvrtmp_7304 = tmp_struct_166.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7301, pvrtmp_7302,
                                                   pvrtmp_7303, pvrtmp_7304};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7267");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2993,
                                                     CursorTy end_r_2994,
                                                     CursorTy loc_2992,
                                                     CursorTy arg_897_1509_1830)
{
    CursorTy loc_3702 = loc_2992 + 1;
    CursorTy loc_3703 = loc_3702 + 8;
    TagTyPacked tmpval_7312 = *(TagTyPacked *) arg_897_1509_1830;
    CursorTy tmpcur_7313 = arg_897_1509_1830 + 1;
    
    
  switch_7356:
    ;
    switch (tmpval_7312) {
        
      case 0:
        {
            CursorTy jump_4207 = arg_897_1509_1830 + 1;
            
            *(TagTyPacked *) loc_2992 = 0;
            
            CursorTy writetag_5011 = loc_2992 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2994, jump_4207,
                                                   loc_2992, writetag_5011};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7318 = *(IntTy *) tmpcur_7313;
            CursorTy tmpcur_7319 = tmpcur_7313 + sizeof(IntTy);
            CursorTy jump_4209 = tmpcur_7313 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _copy_without_ptrs_Tags(end_r_2993, end_r_2994, loc_3703, tmpcur_7319);
            CursorTy pvrtmp_7320 = tmp_struct_170.field0;
            CursorTy pvrtmp_7321 = tmp_struct_170.field1;
            CursorTy pvrtmp_7322 = tmp_struct_170.field2;
            CursorTy pvrtmp_7323 = tmp_struct_170.field3;
            
            *(TagTyPacked *) loc_2992 = 1;
            
            CursorTy writetag_5016 = loc_2992 + 1;
            
            *(IntTy *) writetag_5016 = tmpval_7318;
            
            CursorTy writecur_5017 = writetag_5016 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7320, pvrtmp_7321,
                                                   loc_2992, pvrtmp_7323};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7332 = *(CursorTy *) tmpcur_7313;
            CursorTy tmpaftercur_7333 = tmpcur_7313 + 8;
            CursorTy jump_4365 = tmpcur_7313 + 8;
            CursorCursorCursorCursorProd tmp_struct_171 =
                                          _copy_without_ptrs_Tags(end_r_2993, end_r_2994, loc_2992, tmpcur_7332);
            CursorTy pvrtmp_7334 = tmp_struct_171.field0;
            CursorTy pvrtmp_7335 = tmp_struct_171.field1;
            CursorTy pvrtmp_7336 = tmp_struct_171.field2;
            CursorTy pvrtmp_7337 = tmp_struct_171.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7334, jump_4365,
                                                   pvrtmp_7336, pvrtmp_7337};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7344 = *(CursorTy *) tmpcur_7313;
            CursorTy tmpaftercur_7345 = tmpcur_7313 + 8;
            CursorCursorCursorCursorProd tmp_struct_172 =
                                          _copy_without_ptrs_Tags(end_r_2993, end_r_2994, loc_2992, tmpcur_7344);
            CursorTy pvrtmp_7346 = tmp_struct_172.field0;
            CursorTy pvrtmp_7347 = tmp_struct_172.field1;
            CursorTy pvrtmp_7348 = tmp_struct_172.field2;
            CursorTy pvrtmp_7349 = tmp_struct_172.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7346, pvrtmp_7347,
                                                   pvrtmp_7348, pvrtmp_7349};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7312");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_2996, CursorTy arg_902_1514_1835)
{
    TagTyPacked tmpval_7357 = *(TagTyPacked *) arg_902_1514_1835;
    CursorTy tmpcur_7358 = arg_902_1514_1835 + 1;
    
    
  switch_7368:
    ;
    switch (tmpval_7357) {
        
      case 0:
        {
            CursorTy jump_4212 = arg_902_1514_1835 + 1;
            
            return (CursorProd) {jump_4212};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7359 = *(IntTy *) tmpcur_7358;
            CursorTy tmpcur_7360 = tmpcur_7358 + sizeof(IntTy);
            CursorTy jump_4214 = tmpcur_7358 + 8;
            CursorProd tmp_struct_173 =
                        _traverse_Tags(end_r_2996, tmpcur_7360);
            CursorTy pvrtmp_7361 = tmp_struct_173.field0;
            
            return (CursorProd) {pvrtmp_7361};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7362 = *(CursorTy *) tmpcur_7358;
            CursorTy tmpaftercur_7363 = tmpcur_7358 + 8;
            CursorTy jump_4371 = tmpcur_7358 + 8;
            CursorProd tmp_struct_174 =
                        _traverse_Tags(end_r_2996, tmpcur_7362);
            CursorTy pvrtmp_7364 = tmp_struct_174.field0;
            
            return (CursorProd) {jump_4371};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7365 = *(CursorTy *) tmpcur_7358;
            CursorTy tmpaftercur_7366 = tmpcur_7358 + 8;
            CursorProd tmp_struct_175 =
                        _traverse_Tags(end_r_2996, tmpcur_7365);
            CursorTy pvrtmp_7367 = tmp_struct_175.field0;
            
            return (CursorProd) {pvrtmp_7367};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7357");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_2998, CursorTy arg_907_1518_1839)
{
    TagTyPacked tmpval_7369 = *(TagTyPacked *) arg_907_1518_1839;
    CursorTy tmpcur_7370 = arg_907_1518_1839 + 1;
    
    
  switch_7380:
    ;
    switch (tmpval_7369) {
        
      case 0:
        {
            CursorTy jump_4217 = arg_907_1518_1839 + 1;
            unsigned char wildcard_908_1519_1840 = print_symbol(6165);
            unsigned char wildcard_909_1520_1841 = print_symbol(6160);
            
            return (CursorProd) {jump_4217};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7371 = *(IntTy *) tmpcur_7370;
            CursorTy tmpcur_7372 = tmpcur_7370 + sizeof(IntTy);
            CursorTy jump_4219 = tmpcur_7370 + 8;
            unsigned char wildcard_914_1523_1844 = print_symbol(6162);
            unsigned char y_912_1524_1845 = printf("%lld", tmpval_7371);
            CursorProd tmp_struct_176 =  _print_Tags(end_r_2998, tmpcur_7372);
            CursorTy pvrtmp_7373 = tmp_struct_176.field0;
            unsigned char wildcard_915_1526_1847 = print_symbol(6160);
            
            return (CursorProd) {pvrtmp_7373};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7374 = *(CursorTy *) tmpcur_7370;
            CursorTy tmpaftercur_7375 = tmpcur_7370 + 8;
            CursorTy jump_4377 = tmpcur_7370 + 8;
            unsigned char wildcard_4380 = print_symbol(6177);
            CursorProd tmp_struct_177 =  _print_Tags(end_r_2998, tmpcur_7374);
            CursorTy pvrtmp_7376 = tmp_struct_177.field0;
            
            return (CursorProd) {jump_4377};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7377 = *(CursorTy *) tmpcur_7370;
            CursorTy tmpaftercur_7378 = tmpcur_7370 + 8;
            unsigned char wildcard_4380 = print_symbol(6176);
            CursorProd tmp_struct_178 =  _print_Tags(end_r_2998, tmpcur_7377);
            CursorTy pvrtmp_7379 = tmp_struct_178.field0;
            
            return (CursorProd) {pvrtmp_7379};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7369");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_3001,
                                                              CursorTy end_r_3002,
                                                              CursorTy loc_3000,
                                                              CursorTy arg_2733)
{
    if (loc_3000 + 32 > end_r_3002) {
        ChunkTy new_chunk_182 = alloc_chunk(end_r_3002);
        CursorTy chunk_start_183 = new_chunk_182.chunk_start;
        CursorTy chunk_end_184 = new_chunk_182.chunk_end;
        
        end_r_3002 = chunk_end_184;
        *(TagTyPacked *) loc_3000 = 255;
        
        CursorTy redir = loc_3000 + 1;
        
        *(CursorTy *) redir = chunk_start_183;
        loc_3000 = chunk_start_183;
    }
    
    CursorTy loc_3727 = loc_3000 + 1;
    CursorTy loc_3728 = loc_3727 + 8;
    TagTyPacked tmpval_7381 = *(TagTyPacked *) arg_2733;
    CursorTy tmpcur_7382 = arg_2733 + 1;
    
    
  switch_7425:
    ;
    switch (tmpval_7381) {
        
      case 0:
        {
            CursorTy jump_4222 = arg_2733 + 1;
            
            *(TagTyPacked *) loc_3000 = 0;
            
            CursorTy writetag_5047 = loc_3000 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3002, jump_4222,
                                                   loc_3000, writetag_5047};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7387 = *(IntTy *) tmpcur_7382;
            CursorTy tmpcur_7388 = tmpcur_7382 + sizeof(IntTy);
            CursorTy jump_4224 = tmpcur_7382 + 8;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_String(end_r_3001, end_r_3002, loc_3728, tmpcur_7388);
            CursorTy pvrtmp_7389 = tmp_struct_179.field0;
            CursorTy pvrtmp_7390 = tmp_struct_179.field1;
            CursorTy pvrtmp_7391 = tmp_struct_179.field2;
            CursorTy pvrtmp_7392 = tmp_struct_179.field3;
            
            *(TagTyPacked *) loc_3000 = 1;
            
            CursorTy writetag_5052 = loc_3000 + 1;
            
            *(IntTy *) writetag_5052 = tmpval_7387;
            
            CursorTy writecur_5053 = writetag_5052 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7389, pvrtmp_7390,
                                                   loc_3000, pvrtmp_7392};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7401 = *(CursorTy *) tmpcur_7382;
            CursorTy tmpaftercur_7402 = tmpcur_7382 + 8;
            CursorTy jump_4383 = tmpcur_7382 + 8;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_String(end_r_3001, end_r_3002, loc_3000, tmpcur_7401);
            CursorTy pvrtmp_7403 = tmp_struct_180.field0;
            CursorTy pvrtmp_7404 = tmp_struct_180.field1;
            CursorTy pvrtmp_7405 = tmp_struct_180.field2;
            CursorTy pvrtmp_7406 = tmp_struct_180.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7403, jump_4383,
                                                   pvrtmp_7405, pvrtmp_7406};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7413 = *(CursorTy *) tmpcur_7382;
            CursorTy tmpaftercur_7414 = tmpcur_7382 + 8;
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_String(end_r_3001, end_r_3002, loc_3000, tmpcur_7413);
            CursorTy pvrtmp_7415 = tmp_struct_181.field0;
            CursorTy pvrtmp_7416 = tmp_struct_181.field1;
            CursorTy pvrtmp_7417 = tmp_struct_181.field2;
            CursorTy pvrtmp_7418 = tmp_struct_181.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7415, pvrtmp_7416,
                                                   pvrtmp_7417, pvrtmp_7418};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7381");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_3005,
                                                               CursorTy end_r_3006,
                                                               CursorTy loc_3004,
                                                               CursorTy arg_2738)
{
    if (loc_3004 + 32 > end_r_3006) {
        ChunkTy new_chunk_189 = alloc_chunk(end_r_3006);
        CursorTy chunk_start_190 = new_chunk_189.chunk_start;
        CursorTy chunk_end_191 = new_chunk_189.chunk_end;
        
        end_r_3006 = chunk_end_191;
        *(TagTyPacked *) loc_3004 = 255;
        
        CursorTy redir = loc_3004 + 1;
        
        *(CursorTy *) redir = chunk_start_190;
        loc_3004 = chunk_start_190;
    }
    
    TagTyPacked tmpval_7426 = *(TagTyPacked *) arg_2738;
    CursorTy tmpcur_7427 = arg_2738 + 1;
    
    
  switch_7476:
    ;
    switch (tmpval_7426) {
        
      case 0:
        {
            CursorTy loc_3738 = loc_3004 + 1;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_String(end_r_3005, end_r_3006, loc_3738, tmpcur_7427);
            CursorTy pvrtmp_7428 = tmp_struct_185.field0;
            CursorTy pvrtmp_7429 = tmp_struct_185.field1;
            CursorTy pvrtmp_7430 = tmp_struct_185.field2;
            CursorTy pvrtmp_7431 = tmp_struct_185.field3;
            
            *(TagTyPacked *) loc_3004 = 0;
            
            CursorTy writetag_5064 = loc_3004 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7428, pvrtmp_7429,
                                                   loc_3004, pvrtmp_7431};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3744 = loc_3004 + 1;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_String(end_r_3005, end_r_3006, loc_3744, tmpcur_7427);
            CursorTy pvrtmp_7440 = tmp_struct_186.field0;
            CursorTy pvrtmp_7441 = tmp_struct_186.field1;
            CursorTy pvrtmp_7442 = tmp_struct_186.field2;
            CursorTy pvrtmp_7443 = tmp_struct_186.field3;
            
            *(TagTyPacked *) loc_3004 = 1;
            
            CursorTy writetag_5069 = loc_3004 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7440, pvrtmp_7441,
                                                   loc_3004, pvrtmp_7443};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7452 = *(CursorTy *) tmpcur_7427;
            CursorTy tmpaftercur_7453 = tmpcur_7427 + 8;
            CursorTy jump_4389 = tmpcur_7427 + 8;
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Content(end_r_3005, end_r_3006, loc_3004, tmpcur_7452);
            CursorTy pvrtmp_7454 = tmp_struct_187.field0;
            CursorTy pvrtmp_7455 = tmp_struct_187.field1;
            CursorTy pvrtmp_7456 = tmp_struct_187.field2;
            CursorTy pvrtmp_7457 = tmp_struct_187.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7454, jump_4389,
                                                   pvrtmp_7456, pvrtmp_7457};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7464 = *(CursorTy *) tmpcur_7427;
            CursorTy tmpaftercur_7465 = tmpcur_7427 + 8;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Content(end_r_3005, end_r_3006, loc_3004, tmpcur_7464);
            CursorTy pvrtmp_7466 = tmp_struct_188.field0;
            CursorTy pvrtmp_7467 = tmp_struct_188.field1;
            CursorTy pvrtmp_7468 = tmp_struct_188.field2;
            CursorTy pvrtmp_7469 = tmp_struct_188.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7466, pvrtmp_7467,
                                                   pvrtmp_7468, pvrtmp_7469};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7426");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_3009,
                                                           CursorTy end_r_3010,
                                                           CursorTy loc_3008,
                                                           CursorTy arg_2743)
{
    if (loc_3008 + 32 > end_r_3010) {
        ChunkTy new_chunk_216 = alloc_chunk(end_r_3010);
        CursorTy chunk_start_217 = new_chunk_216.chunk_start;
        CursorTy chunk_end_218 = new_chunk_216.chunk_end;
        
        end_r_3010 = chunk_end_218;
        *(TagTyPacked *) loc_3008 = 255;
        
        CursorTy redir = loc_3008 + 1;
        
        *(CursorTy *) redir = chunk_start_217;
        loc_3008 = chunk_start_217;
    }
    
    CursorTy loc_3757 = loc_3008 + 1;
    CursorTy loc_3758 = loc_3757 + 8;
    CursorTy loc_3759 = loc_3758 + 8;
    CursorTy loc_3775 = loc_3008 + 1;
    CursorTy loc_3776 = loc_3775 + 8;
    CursorTy loc_3777 = loc_3776 + 8;
    CursorTy loc_3797 = loc_3008 + 1;
    CursorTy loc_3798 = loc_3797 + 8;
    CursorTy loc_3799 = loc_3798 + 8;
    CursorTy loc_3800 = loc_3799 + 8;
    CursorTy loc_3824 = loc_3008 + 1;
    CursorTy loc_3825 = loc_3824 + 8;
    CursorTy loc_3826 = loc_3825 + 8;
    CursorTy loc_3827 = loc_3826 + 8;
    CursorTy loc_3851 = loc_3008 + 1;
    CursorTy loc_3852 = loc_3851 + 8;
    CursorTy loc_3853 = loc_3852 + 8;
    CursorTy loc_3854 = loc_3853 + 8;
    CursorTy loc_3878 = loc_3008 + 1;
    CursorTy loc_3879 = loc_3878 + 8;
    CursorTy loc_3880 = loc_3879 + 8;
    CursorTy loc_3881 = loc_3880 + 8;
    CursorTy loc_3905 = loc_3008 + 1;
    CursorTy loc_3906 = loc_3905 + 8;
    CursorTy loc_3907 = loc_3906 + 8;
    CursorTy loc_3908 = loc_3907 + 8;
    CursorTy loc_3932 = loc_3008 + 1;
    CursorTy loc_3933 = loc_3932 + 8;
    CursorTy loc_3934 = loc_3933 + 8;
    CursorTy loc_3935 = loc_3934 + 8;
    TagTyPacked tmpval_7477 = *(TagTyPacked *) arg_2743;
    CursorTy tmpcur_7478 = arg_2743 + 1;
    
    
  switch_7715:
    ;
    switch (tmpval_7477) {
        
      case 0:
        {
            CursorTy jump_4231 = arg_2743 + 1;
            
            *(TagTyPacked *) loc_3008 = 0;
            
            CursorTy writetag_5079 = loc_3008 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3010, jump_4231,
                                                   loc_3008, writetag_5079};
            break;
        }
        
      case 1:
        {
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, end_r_3010, loc_3759, tmpcur_7478);
            CursorTy pvrtmp_7483 = tmp_struct_192.field0;
            CursorTy pvrtmp_7484 = tmp_struct_192.field1;
            CursorTy pvrtmp_7485 = tmp_struct_192.field2;
            CursorTy pvrtmp_7486 = tmp_struct_192.field3;
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, pvrtmp_7483, pvrtmp_7486, pvrtmp_7484);
            CursorTy pvrtmp_7491 = tmp_struct_193.field0;
            CursorTy pvrtmp_7492 = tmp_struct_193.field1;
            CursorTy pvrtmp_7493 = tmp_struct_193.field2;
            CursorTy pvrtmp_7494 = tmp_struct_193.field3;
            IntTy sizeof_y_2746__2748 = pvrtmp_7486 - pvrtmp_7485;
            IntTy sizeof_y_2747__2749 = pvrtmp_7494 - pvrtmp_7493;
            IntTy fltPrm_2837 = sizeof_y_2746__2748 + 0;
            IntTy offset__2750 = 0 + fltPrm_2837;
            IntTy fltPrm_2838 = sizeof_y_2746__2748 + sizeof_y_2747__2749;
            IntTy size_dcon_2751 = 9 + fltPrm_2838;
            
            *(TagTyPacked *) loc_3008 = 160;
            
            CursorTy writetag_5084 = loc_3008 + 1;
            
            *(IntTy *) writetag_5084 = size_dcon_2751;
            
            CursorTy writecur_5085 = writetag_5084 + sizeof(IntTy);
            
            *(IntTy *) writecur_5085 = offset__2750;
            
            CursorTy writecur_5086 = writecur_5085 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7491, pvrtmp_7492,
                                                   loc_3008, pvrtmp_7494};
            break;
        }
        
      case 2:
        {
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, end_r_3010, loc_3777, tmpcur_7478);
            CursorTy pvrtmp_7503 = tmp_struct_194.field0;
            CursorTy pvrtmp_7504 = tmp_struct_194.field1;
            CursorTy pvrtmp_7505 = tmp_struct_194.field2;
            CursorTy pvrtmp_7506 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, pvrtmp_7503, pvrtmp_7506, pvrtmp_7504);
            CursorTy pvrtmp_7511 = tmp_struct_195.field0;
            CursorTy pvrtmp_7512 = tmp_struct_195.field1;
            CursorTy pvrtmp_7513 = tmp_struct_195.field2;
            CursorTy pvrtmp_7514 = tmp_struct_195.field3;
            IntTy sizeof_y_2754__2756 = pvrtmp_7506 - pvrtmp_7505;
            IntTy sizeof_y_2755__2757 = pvrtmp_7514 - pvrtmp_7513;
            IntTy fltPrm_2839 = sizeof_y_2754__2756 + 0;
            IntTy offset__2758 = 0 + fltPrm_2839;
            IntTy fltPrm_2840 = sizeof_y_2754__2756 + sizeof_y_2755__2757;
            IntTy size_dcon_2759 = 9 + fltPrm_2840;
            
            *(TagTyPacked *) loc_3008 = 162;
            
            CursorTy writetag_5093 = loc_3008 + 1;
            
            *(IntTy *) writetag_5093 = size_dcon_2759;
            
            CursorTy writecur_5094 = writetag_5093 + sizeof(IntTy);
            
            *(IntTy *) writecur_5094 = offset__2758;
            
            CursorTy writecur_5095 = writecur_5094 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7511, pvrtmp_7512,
                                                   loc_3008, pvrtmp_7514};
            break;
        }
        
      case 3:
        {
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Tags(end_r_3009, end_r_3010, loc_3800, tmpcur_7478);
            CursorTy pvrtmp_7523 = tmp_struct_196.field0;
            CursorTy pvrtmp_7524 = tmp_struct_196.field1;
            CursorTy pvrtmp_7525 = tmp_struct_196.field2;
            CursorTy pvrtmp_7526 = tmp_struct_196.field3;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, pvrtmp_7523, pvrtmp_7526, pvrtmp_7524);
            CursorTy pvrtmp_7531 = tmp_struct_197.field0;
            CursorTy pvrtmp_7532 = tmp_struct_197.field1;
            CursorTy pvrtmp_7533 = tmp_struct_197.field2;
            CursorTy pvrtmp_7534 = tmp_struct_197.field3;
            CursorCursorCursorCursorProd tmp_struct_198 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, pvrtmp_7531, pvrtmp_7534, pvrtmp_7532);
            CursorTy pvrtmp_7539 = tmp_struct_198.field0;
            CursorTy pvrtmp_7540 = tmp_struct_198.field1;
            CursorTy pvrtmp_7541 = tmp_struct_198.field2;
            CursorTy pvrtmp_7542 = tmp_struct_198.field3;
            IntTy sizeof_y_2763__2766 = pvrtmp_7526 - pvrtmp_7525;
            IntTy sizeof_y_2764__2767 = pvrtmp_7534 - pvrtmp_7533;
            IntTy sizeof_y_2765__2768 = pvrtmp_7542 - pvrtmp_7541;
            IntTy fltPrm_2841 = sizeof_y_2763__2766 + 0;
            IntTy offset__2769 = 8 + fltPrm_2841;
            IntTy fltPrm_2842 = sizeof_y_2763__2766 + sizeof_y_2764__2767;
            IntTy offset__2770 = 0 + fltPrm_2842;
            IntTy fltPrm_2844 = sizeof_y_2764__2767 + sizeof_y_2765__2768;
            IntTy fltPrm_2843 = sizeof_y_2763__2766 + fltPrm_2844;
            IntTy size_dcon_2771 = 17 + fltPrm_2843;
            
            *(TagTyPacked *) loc_3008 = 164;
            
            CursorTy writetag_5103 = loc_3008 + 1;
            
            *(IntTy *) writetag_5103 = size_dcon_2771;
            
            CursorTy writecur_5104 = writetag_5103 + sizeof(IntTy);
            
            *(IntTy *) writecur_5104 = offset__2769;
            
            CursorTy writecur_5105 = writecur_5104 + sizeof(IntTy);
            
            *(IntTy *) writecur_5105 = offset__2770;
            
            CursorTy writecur_5106 = writecur_5105 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7539, pvrtmp_7540,
                                                   loc_3008, pvrtmp_7542};
            break;
        }
        
      case 4:
        {
            CursorCursorCursorCursorProd tmp_struct_199 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, end_r_3010, loc_3827, tmpcur_7478);
            CursorTy pvrtmp_7551 = tmp_struct_199.field0;
            CursorTy pvrtmp_7552 = tmp_struct_199.field1;
            CursorTy pvrtmp_7553 = tmp_struct_199.field2;
            CursorTy pvrtmp_7554 = tmp_struct_199.field3;
            CursorCursorCursorCursorProd tmp_struct_200 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, pvrtmp_7551, pvrtmp_7554, pvrtmp_7552);
            CursorTy pvrtmp_7559 = tmp_struct_200.field0;
            CursorTy pvrtmp_7560 = tmp_struct_200.field1;
            CursorTy pvrtmp_7561 = tmp_struct_200.field2;
            CursorTy pvrtmp_7562 = tmp_struct_200.field3;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_3009, pvrtmp_7559, pvrtmp_7562, pvrtmp_7560);
            CursorTy pvrtmp_7567 = tmp_struct_201.field0;
            CursorTy pvrtmp_7568 = tmp_struct_201.field1;
            CursorTy pvrtmp_7569 = tmp_struct_201.field2;
            CursorTy pvrtmp_7570 = tmp_struct_201.field3;
            IntTy sizeof_y_2775__2778 = pvrtmp_7554 - pvrtmp_7553;
            IntTy sizeof_y_2776__2779 = pvrtmp_7562 - pvrtmp_7561;
            IntTy sizeof_y_2777__2780 = pvrtmp_7570 - pvrtmp_7569;
            IntTy fltPrm_2845 = sizeof_y_2775__2778 + 0;
            IntTy offset__2781 = 8 + fltPrm_2845;
            IntTy fltPrm_2846 = sizeof_y_2775__2778 + sizeof_y_2776__2779;
            IntTy offset__2782 = 0 + fltPrm_2846;
            IntTy fltPrm_2848 = sizeof_y_2776__2779 + sizeof_y_2777__2780;
            IntTy fltPrm_2847 = sizeof_y_2775__2778 + fltPrm_2848;
            IntTy size_dcon_2783 = 17 + fltPrm_2847;
            
            *(TagTyPacked *) loc_3008 = 166;
            
            CursorTy writetag_5115 = loc_3008 + 1;
            
            *(IntTy *) writetag_5115 = size_dcon_2783;
            
            CursorTy writecur_5116 = writetag_5115 + sizeof(IntTy);
            
            *(IntTy *) writecur_5116 = offset__2781;
            
            CursorTy writecur_5117 = writecur_5116 + sizeof(IntTy);
            
            *(IntTy *) writecur_5117 = offset__2782;
            
            CursorTy writecur_5118 = writecur_5117 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7567, pvrtmp_7568,
                                                   loc_3008, pvrtmp_7570};
            break;
        }
        
      case 5:
        {
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_3009, end_r_3010, loc_3854, tmpcur_7478);
            CursorTy pvrtmp_7579 = tmp_struct_202.field0;
            CursorTy pvrtmp_7580 = tmp_struct_202.field1;
            CursorTy pvrtmp_7581 = tmp_struct_202.field2;
            CursorTy pvrtmp_7582 = tmp_struct_202.field3;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, pvrtmp_7579, pvrtmp_7582, pvrtmp_7580);
            CursorTy pvrtmp_7587 = tmp_struct_203.field0;
            CursorTy pvrtmp_7588 = tmp_struct_203.field1;
            CursorTy pvrtmp_7589 = tmp_struct_203.field2;
            CursorTy pvrtmp_7590 = tmp_struct_203.field3;
            CursorCursorCursorCursorProd tmp_struct_204 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, pvrtmp_7587, pvrtmp_7590, pvrtmp_7588);
            CursorTy pvrtmp_7595 = tmp_struct_204.field0;
            CursorTy pvrtmp_7596 = tmp_struct_204.field1;
            CursorTy pvrtmp_7597 = tmp_struct_204.field2;
            CursorTy pvrtmp_7598 = tmp_struct_204.field3;
            IntTy sizeof_y_2787__2790 = pvrtmp_7582 - pvrtmp_7581;
            IntTy sizeof_y_2788__2791 = pvrtmp_7590 - pvrtmp_7589;
            IntTy sizeof_y_2789__2792 = pvrtmp_7598 - pvrtmp_7597;
            IntTy fltPrm_2849 = sizeof_y_2787__2790 + 0;
            IntTy offset__2793 = 8 + fltPrm_2849;
            IntTy fltPrm_2850 = sizeof_y_2787__2790 + sizeof_y_2788__2791;
            IntTy offset__2794 = 0 + fltPrm_2850;
            IntTy fltPrm_2852 = sizeof_y_2788__2791 + sizeof_y_2789__2792;
            IntTy fltPrm_2851 = sizeof_y_2787__2790 + fltPrm_2852;
            IntTy size_dcon_2795 = 17 + fltPrm_2851;
            
            *(TagTyPacked *) loc_3008 = 168;
            
            CursorTy writetag_5127 = loc_3008 + 1;
            
            *(IntTy *) writetag_5127 = size_dcon_2795;
            
            CursorTy writecur_5128 = writetag_5127 + sizeof(IntTy);
            
            *(IntTy *) writecur_5128 = offset__2793;
            
            CursorTy writecur_5129 = writecur_5128 + sizeof(IntTy);
            
            *(IntTy *) writecur_5129 = offset__2794;
            
            CursorTy writecur_5130 = writecur_5129 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7595, pvrtmp_7596,
                                                   loc_3008, pvrtmp_7598};
            break;
        }
        
      case 6:
        {
            CursorCursorCursorCursorProd tmp_struct_205 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, end_r_3010, loc_3881, tmpcur_7478);
            CursorTy pvrtmp_7607 = tmp_struct_205.field0;
            CursorTy pvrtmp_7608 = tmp_struct_205.field1;
            CursorTy pvrtmp_7609 = tmp_struct_205.field2;
            CursorTy pvrtmp_7610 = tmp_struct_205.field3;
            CursorCursorCursorCursorProd tmp_struct_206 =
                                          _add_size_and_rel_offsets_Tags(end_r_3009, pvrtmp_7607, pvrtmp_7610, pvrtmp_7608);
            CursorTy pvrtmp_7615 = tmp_struct_206.field0;
            CursorTy pvrtmp_7616 = tmp_struct_206.field1;
            CursorTy pvrtmp_7617 = tmp_struct_206.field2;
            CursorTy pvrtmp_7618 = tmp_struct_206.field3;
            CursorCursorCursorCursorProd tmp_struct_207 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, pvrtmp_7615, pvrtmp_7618, pvrtmp_7616);
            CursorTy pvrtmp_7623 = tmp_struct_207.field0;
            CursorTy pvrtmp_7624 = tmp_struct_207.field1;
            CursorTy pvrtmp_7625 = tmp_struct_207.field2;
            CursorTy pvrtmp_7626 = tmp_struct_207.field3;
            IntTy sizeof_y_2799__2802 = pvrtmp_7610 - pvrtmp_7609;
            IntTy sizeof_y_2800__2803 = pvrtmp_7618 - pvrtmp_7617;
            IntTy sizeof_y_2801__2804 = pvrtmp_7626 - pvrtmp_7625;
            IntTy fltPrm_2853 = sizeof_y_2799__2802 + 0;
            IntTy offset__2805 = 8 + fltPrm_2853;
            IntTy fltPrm_2854 = sizeof_y_2799__2802 + sizeof_y_2800__2803;
            IntTy offset__2806 = 0 + fltPrm_2854;
            IntTy fltPrm_2856 = sizeof_y_2800__2803 + sizeof_y_2801__2804;
            IntTy fltPrm_2855 = sizeof_y_2799__2802 + fltPrm_2856;
            IntTy size_dcon_2807 = 17 + fltPrm_2855;
            
            *(TagTyPacked *) loc_3008 = 170;
            
            CursorTy writetag_5139 = loc_3008 + 1;
            
            *(IntTy *) writetag_5139 = size_dcon_2807;
            
            CursorTy writecur_5140 = writetag_5139 + sizeof(IntTy);
            
            *(IntTy *) writecur_5140 = offset__2805;
            
            CursorTy writecur_5141 = writecur_5140 + sizeof(IntTy);
            
            *(IntTy *) writecur_5141 = offset__2806;
            
            CursorTy writecur_5142 = writecur_5141 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7623, pvrtmp_7624,
                                                   loc_3008, pvrtmp_7626};
            break;
        }
        
      case 7:
        {
            CursorCursorCursorCursorProd tmp_struct_208 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, end_r_3010, loc_3908, tmpcur_7478);
            CursorTy pvrtmp_7635 = tmp_struct_208.field0;
            CursorTy pvrtmp_7636 = tmp_struct_208.field1;
            CursorTy pvrtmp_7637 = tmp_struct_208.field2;
            CursorTy pvrtmp_7638 = tmp_struct_208.field3;
            CursorCursorCursorCursorProd tmp_struct_209 =
                                          _add_size_and_rel_offsets_Tags(end_r_3009, pvrtmp_7635, pvrtmp_7638, pvrtmp_7636);
            CursorTy pvrtmp_7643 = tmp_struct_209.field0;
            CursorTy pvrtmp_7644 = tmp_struct_209.field1;
            CursorTy pvrtmp_7645 = tmp_struct_209.field2;
            CursorTy pvrtmp_7646 = tmp_struct_209.field3;
            CursorCursorCursorCursorProd tmp_struct_210 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, pvrtmp_7643, pvrtmp_7646, pvrtmp_7644);
            CursorTy pvrtmp_7651 = tmp_struct_210.field0;
            CursorTy pvrtmp_7652 = tmp_struct_210.field1;
            CursorTy pvrtmp_7653 = tmp_struct_210.field2;
            CursorTy pvrtmp_7654 = tmp_struct_210.field3;
            IntTy sizeof_y_2811__2814 = pvrtmp_7638 - pvrtmp_7637;
            IntTy sizeof_y_2812__2815 = pvrtmp_7646 - pvrtmp_7645;
            IntTy sizeof_y_2813__2816 = pvrtmp_7654 - pvrtmp_7653;
            IntTy fltPrm_2857 = sizeof_y_2811__2814 + 0;
            IntTy offset__2817 = 8 + fltPrm_2857;
            IntTy fltPrm_2858 = sizeof_y_2811__2814 + sizeof_y_2812__2815;
            IntTy offset__2818 = 0 + fltPrm_2858;
            IntTy fltPrm_2860 = sizeof_y_2812__2815 + sizeof_y_2813__2816;
            IntTy fltPrm_2859 = sizeof_y_2811__2814 + fltPrm_2860;
            IntTy size_dcon_2819 = 17 + fltPrm_2859;
            
            *(TagTyPacked *) loc_3008 = 172;
            
            CursorTy writetag_5151 = loc_3008 + 1;
            
            *(IntTy *) writetag_5151 = size_dcon_2819;
            
            CursorTy writecur_5152 = writetag_5151 + sizeof(IntTy);
            
            *(IntTy *) writecur_5152 = offset__2817;
            
            CursorTy writecur_5153 = writecur_5152 + sizeof(IntTy);
            
            *(IntTy *) writecur_5153 = offset__2818;
            
            CursorTy writecur_5154 = writecur_5153 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7651, pvrtmp_7652,
                                                   loc_3008, pvrtmp_7654};
            break;
        }
        
      case 8:
        {
            CursorCursorCursorCursorProd tmp_struct_211 =
                                          _add_size_and_rel_offsets_Content(end_r_3009, end_r_3010, loc_3935, tmpcur_7478);
            CursorTy pvrtmp_7663 = tmp_struct_211.field0;
            CursorTy pvrtmp_7664 = tmp_struct_211.field1;
            CursorTy pvrtmp_7665 = tmp_struct_211.field2;
            CursorTy pvrtmp_7666 = tmp_struct_211.field3;
            CursorCursorCursorCursorProd tmp_struct_212 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, pvrtmp_7663, pvrtmp_7666, pvrtmp_7664);
            CursorTy pvrtmp_7671 = tmp_struct_212.field0;
            CursorTy pvrtmp_7672 = tmp_struct_212.field1;
            CursorTy pvrtmp_7673 = tmp_struct_212.field2;
            CursorTy pvrtmp_7674 = tmp_struct_212.field3;
            CursorCursorCursorCursorProd tmp_struct_213 =
                                          _add_size_and_rel_offsets_Tags(end_r_3009, pvrtmp_7671, pvrtmp_7674, pvrtmp_7672);
            CursorTy pvrtmp_7679 = tmp_struct_213.field0;
            CursorTy pvrtmp_7680 = tmp_struct_213.field1;
            CursorTy pvrtmp_7681 = tmp_struct_213.field2;
            CursorTy pvrtmp_7682 = tmp_struct_213.field3;
            IntTy sizeof_y_2823__2826 = pvrtmp_7666 - pvrtmp_7665;
            IntTy sizeof_y_2824__2827 = pvrtmp_7674 - pvrtmp_7673;
            IntTy sizeof_y_2825__2828 = pvrtmp_7682 - pvrtmp_7681;
            IntTy fltPrm_2861 = sizeof_y_2823__2826 + 0;
            IntTy offset__2829 = 8 + fltPrm_2861;
            IntTy fltPrm_2862 = sizeof_y_2823__2826 + sizeof_y_2824__2827;
            IntTy offset__2830 = 0 + fltPrm_2862;
            IntTy fltPrm_2864 = sizeof_y_2824__2827 + sizeof_y_2825__2828;
            IntTy fltPrm_2863 = sizeof_y_2823__2826 + fltPrm_2864;
            IntTy size_dcon_2831 = 17 + fltPrm_2863;
            
            *(TagTyPacked *) loc_3008 = 174;
            
            CursorTy writetag_5163 = loc_3008 + 1;
            
            *(IntTy *) writetag_5163 = size_dcon_2831;
            
            CursorTy writecur_5164 = writetag_5163 + sizeof(IntTy);
            
            *(IntTy *) writecur_5164 = offset__2829;
            
            CursorTy writecur_5165 = writecur_5164 + sizeof(IntTy);
            
            *(IntTy *) writecur_5165 = offset__2830;
            
            CursorTy writecur_5166 = writecur_5165 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7679, pvrtmp_7680,
                                                   loc_3008, pvrtmp_7682};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7691 = *(CursorTy *) tmpcur_7478;
            CursorTy tmpaftercur_7692 = tmpcur_7478 + 8;
            CursorTy jump_4395 = tmpcur_7478 + 8;
            CursorCursorCursorCursorProd tmp_struct_214 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, end_r_3010, loc_3008, tmpcur_7691);
            CursorTy pvrtmp_7693 = tmp_struct_214.field0;
            CursorTy pvrtmp_7694 = tmp_struct_214.field1;
            CursorTy pvrtmp_7695 = tmp_struct_214.field2;
            CursorTy pvrtmp_7696 = tmp_struct_214.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7693, jump_4395,
                                                   pvrtmp_7695, pvrtmp_7696};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7703 = *(CursorTy *) tmpcur_7478;
            CursorTy tmpaftercur_7704 = tmpcur_7478 + 8;
            CursorCursorCursorCursorProd tmp_struct_215 =
                                          _add_size_and_rel_offsets_Adt(end_r_3009, end_r_3010, loc_3008, tmpcur_7703);
            CursorTy pvrtmp_7705 = tmp_struct_215.field0;
            CursorTy pvrtmp_7706 = tmp_struct_215.field1;
            CursorTy pvrtmp_7707 = tmp_struct_215.field2;
            CursorTy pvrtmp_7708 = tmp_struct_215.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7705, pvrtmp_7706,
                                                   pvrtmp_7707, pvrtmp_7708};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7477");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_3013,
                                                            CursorTy end_r_3014,
                                                            CursorTy loc_3012,
                                                            CursorTy arg_2832)
{
    if (loc_3012 + 32 > end_r_3014) {
        ChunkTy new_chunk_222 = alloc_chunk(end_r_3014);
        CursorTy chunk_start_223 = new_chunk_222.chunk_start;
        CursorTy chunk_end_224 = new_chunk_222.chunk_end;
        
        end_r_3014 = chunk_end_224;
        *(TagTyPacked *) loc_3012 = 255;
        
        CursorTy redir = loc_3012 + 1;
        
        *(CursorTy *) redir = chunk_start_223;
        loc_3012 = chunk_start_223;
    }
    
    CursorTy loc_3955 = loc_3012 + 1;
    CursorTy loc_3956 = loc_3955 + 8;
    TagTyPacked tmpval_7716 = *(TagTyPacked *) arg_2832;
    CursorTy tmpcur_7717 = arg_2832 + 1;
    
    
  switch_7760:
    ;
    switch (tmpval_7716) {
        
      case 0:
        {
            CursorTy jump_4263 = arg_2832 + 1;
            
            *(TagTyPacked *) loc_3012 = 0;
            
            CursorTy writetag_5178 = loc_3012 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_3014, jump_4263,
                                                   loc_3012, writetag_5178};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7722 = *(IntTy *) tmpcur_7717;
            CursorTy tmpcur_7723 = tmpcur_7717 + sizeof(IntTy);
            CursorTy jump_4265 = tmpcur_7717 + 8;
            CursorCursorCursorCursorProd tmp_struct_219 =
                                          _add_size_and_rel_offsets_Tags(end_r_3013, end_r_3014, loc_3956, tmpcur_7723);
            CursorTy pvrtmp_7724 = tmp_struct_219.field0;
            CursorTy pvrtmp_7725 = tmp_struct_219.field1;
            CursorTy pvrtmp_7726 = tmp_struct_219.field2;
            CursorTy pvrtmp_7727 = tmp_struct_219.field3;
            
            *(TagTyPacked *) loc_3012 = 1;
            
            CursorTy writetag_5183 = loc_3012 + 1;
            
            *(IntTy *) writetag_5183 = tmpval_7722;
            
            CursorTy writecur_5184 = writetag_5183 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7724, pvrtmp_7725,
                                                   loc_3012, pvrtmp_7727};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7736 = *(CursorTy *) tmpcur_7717;
            CursorTy tmpaftercur_7737 = tmpcur_7717 + 8;
            CursorTy jump_4401 = tmpcur_7717 + 8;
            CursorCursorCursorCursorProd tmp_struct_220 =
                                          _add_size_and_rel_offsets_Tags(end_r_3013, end_r_3014, loc_3012, tmpcur_7736);
            CursorTy pvrtmp_7738 = tmp_struct_220.field0;
            CursorTy pvrtmp_7739 = tmp_struct_220.field1;
            CursorTy pvrtmp_7740 = tmp_struct_220.field2;
            CursorTy pvrtmp_7741 = tmp_struct_220.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7738, jump_4401,
                                                   pvrtmp_7740, pvrtmp_7741};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7748 = *(CursorTy *) tmpcur_7717;
            CursorTy tmpaftercur_7749 = tmpcur_7717 + 8;
            CursorCursorCursorCursorProd tmp_struct_221 =
                                          _add_size_and_rel_offsets_Tags(end_r_3013, end_r_3014, loc_3012, tmpcur_7748);
            CursorTy pvrtmp_7750 = tmp_struct_221.field0;
            CursorTy pvrtmp_7751 = tmp_struct_221.field1;
            CursorTy pvrtmp_7752 = tmp_struct_221.field2;
            CursorTy pvrtmp_7753 = tmp_struct_221.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7750, pvrtmp_7751,
                                                   pvrtmp_7752, pvrtmp_7753};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7716");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(6160, ")");
    add_symbol(6161, "(Text ");
    add_symbol(6162, "(Tag ");
    add_symbol(6163, "(TCA ");
    add_symbol(6164, "(TAC ");
    add_symbol(6165, "(Nul ");
    add_symbol(6166, "(Nil ");
    add_symbol(6167, "(Image ");
    add_symbol(6168, "(End ");
    add_symbol(6169, "(Char ");
    add_symbol(6170, "(CTA ");
    add_symbol(6171, "(CAT ");
    add_symbol(6172, "(CA ");
    add_symbol(6173, "(ATC ");
    add_symbol(6174, "(ACT ");
    add_symbol(6175, "(AC ");
    add_symbol(6176, " ->r ");
    add_symbol(6177, " ->i ");
    
    RegionTy *region_6178 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3024 = region_6178->reg_heap;
    IntTy sizeof_end_r_3024_6179 = global_init_inf_buf_size;
    CursorTy end_r_3024 = r_3024 + sizeof_end_r_3024_6179;
    RegionTy *region_6180 = alloc_region(global_init_inf_buf_size);
    CursorTy r_3023 = region_6180->reg_heap;
    IntTy sizeof_end_r_3023_6181 = global_init_inf_buf_size;
    CursorTy end_r_3023 = r_3023 + sizeof_end_r_3023_6181;
    CursorCursorCursorProd tmp_struct_225 =
                            mkTACList(end_r_3024, r_3024, 100000, 10, 2000);
    CursorTy pvrtmp_6182 = tmp_struct_225.field0;
    CursorTy pvrtmp_6183 = tmp_struct_225.field1;
    CursorTy pvrtmp_6184 = tmp_struct_225.field2;
    CursorTy pvrtmp_6198;
    CursorTy pvrtmp_6199;
    CursorTy pvrtmp_6200;
    VectorTy *times_230 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_pvrtmp_6198;
    struct timespec end_pvrtmp_6198;
    
    start_counters();
    for (long long iters_pvrtmp_6198 = 0; iters_pvrtmp_6198 <
         global_iters_param; iters_pvrtmp_6198++) {
        if (iters_pvrtmp_6198 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_6198);
        
        CursorCursorCursorProd tmp_struct_226 =
                                addValTagsAdt(pvrtmp_6182, end_r_3023, r_3023, pvrtmp_6183);
        CursorTy pvrtmp_6189 = tmp_struct_226.field0;
        CursorTy pvrtmp_6190 = tmp_struct_226.field1;
        CursorTy pvrtmp_6191 = tmp_struct_226.field2;
        
        pvrtmp_6198 = pvrtmp_6189;
        pvrtmp_6199 = pvrtmp_6190;
        pvrtmp_6200 = pvrtmp_6191;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_6198);
        if (iters_pvrtmp_6198 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_227 = difftimespecs(&begin_pvrtmp_6198,
                                            &end_pvrtmp_6198);
        
        vector_inplace_update(times_230, iters_pvrtmp_6198, &itertime_227);
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
