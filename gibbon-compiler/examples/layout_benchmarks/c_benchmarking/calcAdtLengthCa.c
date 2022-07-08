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
IntTy getLengthTR(CursorTy end_r_2860, CursorTy adt_31_923_1539,
                  IntTy accumulator_32_924_1540);
CursorCursorCursorProd mkCAList(CursorTy end_r_2862, CursorTy loc_2861,
                                IntTy len_35_927_1544,
                                IntTy strLen_36_928_1545);
CursorCursorCursorProd mkString(CursorTy end_r_2864, CursorTy loc_2863,
                                IntTy len_188_1080_1550);
CursorCursorCursorProd mkContentText(CursorTy end_r_2866, CursorTy loc_2865,
                                     IntTy n_202_1094_1556);
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2869,
                                          CursorTy end_r_2870,
                                          CursorTy loc_2868,
                                          CursorTy arg_637_1249_1558);
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2873,
                                                       CursorTy end_r_2874,
                                                       CursorTy loc_2872,
                                                       CursorTy arg_642_1254_1563);
CursorProd _traverse_String(CursorTy end_r_2876, CursorTy arg_647_1259_1568);
CursorProd _print_String(CursorTy end_r_2878, CursorTy arg_652_1263_1572);
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2881,
                                           CursorTy end_r_2882,
                                           CursorTy loc_2880,
                                           CursorTy arg_661_1272_1581);
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2885,
                                                        CursorTy end_r_2886,
                                                        CursorTy loc_2884,
                                                        CursorTy arg_666_1277_1586);
CursorProd _traverse_Content(CursorTy end_r_2888, CursorTy arg_671_1282_1591);
CursorProd _print_Content(CursorTy end_r_2890, CursorTy arg_676_1287_1596);
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2893, CursorTy end_r_2894,
                                       CursorTy loc_2892,
                                       CursorTy arg_685_1296_1605);
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2897,
                                                    CursorTy end_r_2898,
                                                    CursorTy loc_2896,
                                                    CursorTy arg_730_1341_1650);
CursorProd _traverse_Adt(CursorTy end_r_2900, CursorTy arg_775_1386_1695);
CursorProd _print_Adt(CursorTy end_r_2902, CursorTy arg_820_1431_1740);
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2905,
                                        CursorTy end_r_2906, CursorTy loc_2904,
                                        CursorTy arg_883_1494_1803);
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2909,
                                                     CursorTy end_r_2910,
                                                     CursorTy loc_2908,
                                                     CursorTy arg_888_1499_1808);
CursorProd _traverse_Tags(CursorTy end_r_2912, CursorTy arg_893_1504_1813);
CursorProd _print_Tags(CursorTy end_r_2914, CursorTy arg_898_1508_1817);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_String(CursorTy end_r_2917, CursorTy end_r_2918,
                                 CursorTy loc_2916, CursorTy arg_2657);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Content(CursorTy end_r_2921, CursorTy end_r_2922,
                                  CursorTy loc_2920, CursorTy arg_2662);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2925,
                                                           CursorTy end_r_2926,
                                                           CursorTy loc_2924,
                                                           CursorTy arg_2667);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2929,
                                                            CursorTy end_r_2930,
                                                            CursorTy loc_2928,
                                                            CursorTy arg_2756);
IntTy getLengthTR(CursorTy end_r_2860, CursorTy adt_31_923_1539,
                  IntTy accumulator_32_924_1540)
{
    TagTyPacked tmpval_5889 = *(TagTyPacked *) adt_31_923_1539;
    CursorTy tmpcur_5890 = adt_31_923_1539 + 1;
    
    
  switch_5897:
    ;
    switch (tmpval_5889) {
        
      case 0:
        {
            CursorTy jump_3833 = adt_31_923_1539 + 1;
            
            return accumulator_32_924_1540;
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_5891 = *(CursorTy *) tmpcur_5890;
            CursorTy tmpaftercur_5892 = tmpcur_5890 + 8;
            CursorTy jump_3834 = tmpcur_5890 + 8;
            IntTy fltAppE_1525_1543 = 1 + accumulator_32_924_1540;
            IntTy tailapp_3835 =
                   getLengthTR(end_r_2860, tmpcur_5891, fltAppE_1525_1543);
            
            return tailapp_3835;
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5893 = *(CursorTy *) tmpcur_5890;
            CursorTy tmpaftercur_5894 = tmpcur_5890 + 8;
            CursorTy jump_4135 = tmpcur_5890 + 8;
            IntTy call_4136 =
                   getLengthTR(end_r_2860, tmpcur_5893, accumulator_32_924_1540);
            
            return call_4136;
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5895 = *(CursorTy *) tmpcur_5890;
            CursorTy tmpaftercur_5896 = tmpcur_5890 + 8;
            IntTy call_4136 =
                   getLengthTR(end_r_2860, tmpcur_5895, accumulator_32_924_1540);
            
            return call_4136;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5889");
            exit(1);
        }
    }
}
CursorCursorCursorProd mkCAList(CursorTy end_r_2862, CursorTy loc_2861,
                                IntTy len_35_927_1544, IntTy strLen_36_928_1545)
{
    if (loc_2861 + 32 > end_r_2862) {
        ChunkTy new_chunk_2 = alloc_chunk(end_r_2862);
        CursorTy chunk_start_3 = new_chunk_2.chunk_start;
        CursorTy chunk_end_4 = new_chunk_2.chunk_end;
        
        end_r_2862 = chunk_end_4;
        *(TagTyPacked *) loc_2861 = 255;
        
        CursorTy redir = loc_2861 + 1;
        
        *(CursorTy *) redir = chunk_start_3;
        loc_2861 = chunk_start_3;
    }
    
    CursorTy loc_2947 = loc_2861 + 1;
    CursorTy loc_2948 = loc_2947 + 8;
    BoolTy fltIf_1526_1546 = len_35_927_1544 <= 0;
    
    if (fltIf_1526_1546) {
        *(TagTyPacked *) loc_2861 = 0;
        
        CursorTy writetag_4372 = loc_2861 + 1;
        
        return (CursorCursorCursorProd) {end_r_2862, loc_2861, writetag_4372};
    } else {
        CursorCursorCursorProd tmp_struct_0 =
                                mkContentText(end_r_2862, loc_2948, strLen_36_928_1545);
        CursorTy pvrtmp_5902 = tmp_struct_0.field0;
        CursorTy pvrtmp_5903 = tmp_struct_0.field1;
        CursorTy pvrtmp_5904 = tmp_struct_0.field2;
        IntTy fltAppE_1527_1548 = len_35_927_1544 - 1;
        CursorCursorCursorProd tmp_struct_1 =
                                mkCAList(pvrtmp_5902, pvrtmp_5904, fltAppE_1527_1548, strLen_36_928_1545);
        CursorTy pvrtmp_5909 = tmp_struct_1.field0;
        CursorTy pvrtmp_5910 = tmp_struct_1.field1;
        CursorTy pvrtmp_5911 = tmp_struct_1.field2;
        
        *(TagTyPacked *) loc_2861 = 9;
        
        CursorTy writetag_4376 = loc_2861 + 1;
        
        *(CursorTy *) writetag_4376 = pvrtmp_5904;
        
        CursorTy writecur_4377 = writetag_4376 + 8;
        
        return (CursorCursorCursorProd) {pvrtmp_5909, loc_2861, pvrtmp_5911};
    }
}
CursorCursorCursorProd mkString(CursorTy end_r_2864, CursorTy loc_2863,
                                IntTy len_188_1080_1550)
{
    if (loc_2863 + 32 > end_r_2864) {
        ChunkTy new_chunk_6 = alloc_chunk(end_r_2864);
        CursorTy chunk_start_7 = new_chunk_6.chunk_start;
        CursorTy chunk_end_8 = new_chunk_6.chunk_end;
        
        end_r_2864 = chunk_end_8;
        *(TagTyPacked *) loc_2863 = 255;
        
        CursorTy redir = loc_2863 + 1;
        
        *(CursorTy *) redir = chunk_start_7;
        loc_2863 = chunk_start_7;
    }
    
    CursorTy loc_2956 = loc_2863 + 1;
    CursorTy loc_2957 = loc_2956 + 8;
    BoolTy fltIf_1528_1551 = len_188_1080_1550 <= 0;
    
    if (fltIf_1528_1551) {
        *(TagTyPacked *) loc_2863 = 0;
        
        CursorTy writetag_4381 = loc_2863 + 1;
        
        return (CursorCursorCursorProd) {end_r_2864, loc_2863, writetag_4381};
    } else {
        IntTy fltPrm_1529_1552 = rand();
        IntTy randomChar_189_1081_1553 = fltPrm_1529_1552 % 128;
        IntTy fltAppE_1530_1554 = len_188_1080_1550 - 1;
        CursorCursorCursorProd tmp_struct_5 =
                                mkString(end_r_2864, loc_2957, fltAppE_1530_1554);
        CursorTy pvrtmp_5924 = tmp_struct_5.field0;
        CursorTy pvrtmp_5925 = tmp_struct_5.field1;
        CursorTy pvrtmp_5926 = tmp_struct_5.field2;
        
        *(TagTyPacked *) loc_2863 = 1;
        
        CursorTy writetag_4384 = loc_2863 + 1;
        
        *(IntTy *) writetag_4384 = randomChar_189_1081_1553;
        
        CursorTy writecur_4385 = writetag_4384 + sizeof(IntTy);
        
        return (CursorCursorCursorProd) {pvrtmp_5924, loc_2863, pvrtmp_5926};
    }
}
CursorCursorCursorProd mkContentText(CursorTy end_r_2866, CursorTy loc_2865,
                                     IntTy n_202_1094_1556)
{
    if (loc_2865 + 32 > end_r_2866) {
        ChunkTy new_chunk_10 = alloc_chunk(end_r_2866);
        CursorTy chunk_start_11 = new_chunk_10.chunk_start;
        CursorTy chunk_end_12 = new_chunk_10.chunk_end;
        
        end_r_2866 = chunk_end_12;
        *(TagTyPacked *) loc_2865 = 255;
        
        CursorTy redir = loc_2865 + 1;
        
        *(CursorTy *) redir = chunk_start_11;
        loc_2865 = chunk_start_11;
    }
    
    CursorTy loc_2962 = loc_2865 + 1;
    CursorCursorCursorProd tmp_struct_9 =
                            mkString(end_r_2866, loc_2962, n_202_1094_1556);
    CursorTy pvrtmp_5935 = tmp_struct_9.field0;
    CursorTy pvrtmp_5936 = tmp_struct_9.field1;
    CursorTy pvrtmp_5937 = tmp_struct_9.field2;
    
    *(TagTyPacked *) loc_2865 = 1;
    
    CursorTy writetag_4389 = loc_2865 + 1;
    
    return (CursorCursorCursorProd) {pvrtmp_5935, loc_2865, pvrtmp_5937};
}
CursorCursorCursorCursorProd _copy_String(CursorTy end_r_2869,
                                          CursorTy end_r_2870,
                                          CursorTy loc_2868,
                                          CursorTy arg_637_1249_1558)
{
    if (loc_2868 + 32 > end_r_2870) {
        ChunkTy new_chunk_16 = alloc_chunk(end_r_2870);
        CursorTy chunk_start_17 = new_chunk_16.chunk_start;
        CursorTy chunk_end_18 = new_chunk_16.chunk_end;
        
        end_r_2870 = chunk_end_18;
        *(TagTyPacked *) loc_2868 = 255;
        
        CursorTy redir = loc_2868 + 1;
        
        *(CursorTy *) redir = chunk_start_17;
        loc_2868 = chunk_start_17;
    }
    
    CursorTy loc_2972 = loc_2868 + 1;
    CursorTy loc_2973 = loc_2972 + 8;
    TagTyPacked tmpval_5946 = *(TagTyPacked *) arg_637_1249_1558;
    CursorTy tmpcur_5947 = arg_637_1249_1558 + 1;
    
    
  switch_5990:
    ;
    switch (tmpval_5946) {
        
      case 0:
        {
            CursorTy jump_3841 = arg_637_1249_1558 + 1;
            
            *(TagTyPacked *) loc_2868 = 0;
            
            CursorTy writetag_4393 = loc_2868 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2870, jump_3841,
                                                   loc_2868, writetag_4393};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_5952 = *(IntTy *) tmpcur_5947;
            CursorTy tmpcur_5953 = tmpcur_5947 + sizeof(IntTy);
            CursorTy jump_3843 = tmpcur_5947 + 8;
            CursorCursorCursorCursorProd tmp_struct_13 =
                                          _copy_String(end_r_2869, end_r_2870, loc_2973, tmpcur_5953);
            CursorTy pvrtmp_5954 = tmp_struct_13.field0;
            CursorTy pvrtmp_5955 = tmp_struct_13.field1;
            CursorTy pvrtmp_5956 = tmp_struct_13.field2;
            CursorTy pvrtmp_5957 = tmp_struct_13.field3;
            
            *(TagTyPacked *) loc_2868 = 1;
            
            CursorTy writetag_4398 = loc_2868 + 1;
            
            *(IntTy *) writetag_4398 = tmpval_5952;
            
            CursorTy writecur_4399 = writetag_4398 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5954, pvrtmp_5955,
                                                   loc_2868, pvrtmp_5957};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_5966 = *(CursorTy *) tmpcur_5947;
            CursorTy tmpaftercur_5967 = tmpcur_5947 + 8;
            CursorTy jump_4140 = tmpcur_5947 + 8;
            CursorCursorCursorCursorProd tmp_struct_14 =
                                          _copy_String(end_r_2869, end_r_2870, loc_2868, tmpcur_5966);
            CursorTy pvrtmp_5968 = tmp_struct_14.field0;
            CursorTy pvrtmp_5969 = tmp_struct_14.field1;
            CursorTy pvrtmp_5970 = tmp_struct_14.field2;
            CursorTy pvrtmp_5971 = tmp_struct_14.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5968, jump_4140,
                                                   pvrtmp_5970, pvrtmp_5971};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_5978 = *(CursorTy *) tmpcur_5947;
            CursorTy tmpaftercur_5979 = tmpcur_5947 + 8;
            CursorCursorCursorCursorProd tmp_struct_15 =
                                          _copy_String(end_r_2869, end_r_2870, loc_2868, tmpcur_5978);
            CursorTy pvrtmp_5980 = tmp_struct_15.field0;
            CursorTy pvrtmp_5981 = tmp_struct_15.field1;
            CursorTy pvrtmp_5982 = tmp_struct_15.field2;
            CursorTy pvrtmp_5983 = tmp_struct_15.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5980, pvrtmp_5981,
                                                   pvrtmp_5982, pvrtmp_5983};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5946");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_String(CursorTy end_r_2873,
                                                       CursorTy end_r_2874,
                                                       CursorTy loc_2872,
                                                       CursorTy arg_642_1254_1563)
{
    CursorTy loc_2985 = loc_2872 + 1;
    CursorTy loc_2986 = loc_2985 + 8;
    TagTyPacked tmpval_5991 = *(TagTyPacked *) arg_642_1254_1563;
    CursorTy tmpcur_5992 = arg_642_1254_1563 + 1;
    
    
  switch_6035:
    ;
    switch (tmpval_5991) {
        
      case 0:
        {
            CursorTy jump_3846 = arg_642_1254_1563 + 1;
            
            *(TagTyPacked *) loc_2872 = 0;
            
            CursorTy writetag_4409 = loc_2872 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2874, jump_3846,
                                                   loc_2872, writetag_4409};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_5997 = *(IntTy *) tmpcur_5992;
            CursorTy tmpcur_5998 = tmpcur_5992 + sizeof(IntTy);
            CursorTy jump_3848 = tmpcur_5992 + 8;
            CursorCursorCursorCursorProd tmp_struct_19 =
                                          _copy_without_ptrs_String(end_r_2873, end_r_2874, loc_2986, tmpcur_5998);
            CursorTy pvrtmp_5999 = tmp_struct_19.field0;
            CursorTy pvrtmp_6000 = tmp_struct_19.field1;
            CursorTy pvrtmp_6001 = tmp_struct_19.field2;
            CursorTy pvrtmp_6002 = tmp_struct_19.field3;
            
            *(TagTyPacked *) loc_2872 = 1;
            
            CursorTy writetag_4414 = loc_2872 + 1;
            
            *(IntTy *) writetag_4414 = tmpval_5997;
            
            CursorTy writecur_4415 = writetag_4414 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_5999, pvrtmp_6000,
                                                   loc_2872, pvrtmp_6002};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6011 = *(CursorTy *) tmpcur_5992;
            CursorTy tmpaftercur_6012 = tmpcur_5992 + 8;
            CursorTy jump_4146 = tmpcur_5992 + 8;
            CursorCursorCursorCursorProd tmp_struct_20 =
                                          _copy_without_ptrs_String(end_r_2873, end_r_2874, loc_2872, tmpcur_6011);
            CursorTy pvrtmp_6013 = tmp_struct_20.field0;
            CursorTy pvrtmp_6014 = tmp_struct_20.field1;
            CursorTy pvrtmp_6015 = tmp_struct_20.field2;
            CursorTy pvrtmp_6016 = tmp_struct_20.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6013, jump_4146,
                                                   pvrtmp_6015, pvrtmp_6016};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6023 = *(CursorTy *) tmpcur_5992;
            CursorTy tmpaftercur_6024 = tmpcur_5992 + 8;
            CursorCursorCursorCursorProd tmp_struct_21 =
                                          _copy_without_ptrs_String(end_r_2873, end_r_2874, loc_2872, tmpcur_6023);
            CursorTy pvrtmp_6025 = tmp_struct_21.field0;
            CursorTy pvrtmp_6026 = tmp_struct_21.field1;
            CursorTy pvrtmp_6027 = tmp_struct_21.field2;
            CursorTy pvrtmp_6028 = tmp_struct_21.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6025, pvrtmp_6026,
                                                   pvrtmp_6027, pvrtmp_6028};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_5991");
            exit(1);
        }
    }
}
CursorProd _traverse_String(CursorTy end_r_2876, CursorTy arg_647_1259_1568)
{
    TagTyPacked tmpval_6036 = *(TagTyPacked *) arg_647_1259_1568;
    CursorTy tmpcur_6037 = arg_647_1259_1568 + 1;
    
    
  switch_6047:
    ;
    switch (tmpval_6036) {
        
      case 0:
        {
            CursorTy jump_3851 = arg_647_1259_1568 + 1;
            
            return (CursorProd) {jump_3851};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6038 = *(IntTy *) tmpcur_6037;
            CursorTy tmpcur_6039 = tmpcur_6037 + sizeof(IntTy);
            CursorTy jump_3853 = tmpcur_6037 + 8;
            CursorProd tmp_struct_22 =
                        _traverse_String(end_r_2876, tmpcur_6039);
            CursorTy pvrtmp_6040 = tmp_struct_22.field0;
            
            return (CursorProd) {pvrtmp_6040};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6041 = *(CursorTy *) tmpcur_6037;
            CursorTy tmpaftercur_6042 = tmpcur_6037 + 8;
            CursorTy jump_4152 = tmpcur_6037 + 8;
            CursorProd tmp_struct_23 =
                        _traverse_String(end_r_2876, tmpcur_6041);
            CursorTy pvrtmp_6043 = tmp_struct_23.field0;
            
            return (CursorProd) {jump_4152};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6044 = *(CursorTy *) tmpcur_6037;
            CursorTy tmpaftercur_6045 = tmpcur_6037 + 8;
            CursorProd tmp_struct_24 =
                        _traverse_String(end_r_2876, tmpcur_6044);
            CursorTy pvrtmp_6046 = tmp_struct_24.field0;
            
            return (CursorProd) {pvrtmp_6046};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6036");
            exit(1);
        }
    }
}
CursorProd _print_String(CursorTy end_r_2878, CursorTy arg_652_1263_1572)
{
    TagTyPacked tmpval_6048 = *(TagTyPacked *) arg_652_1263_1572;
    CursorTy tmpcur_6049 = arg_652_1263_1572 + 1;
    
    
  switch_6059:
    ;
    switch (tmpval_6048) {
        
      case 0:
        {
            CursorTy jump_3856 = arg_652_1263_1572 + 1;
            unsigned char wildcard_653_1264_1573 = print_symbol(5870);
            unsigned char wildcard_654_1265_1574 = print_symbol(5862);
            
            return (CursorProd) {jump_3856};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6050 = *(IntTy *) tmpcur_6049;
            CursorTy tmpcur_6051 = tmpcur_6049 + sizeof(IntTy);
            CursorTy jump_3858 = tmpcur_6049 + 8;
            unsigned char wildcard_659_1268_1577 = print_symbol(5871);
            unsigned char y_657_1269_1578 = printf("%lld", tmpval_6050);
            CursorProd tmp_struct_25 =  _print_String(end_r_2878, tmpcur_6051);
            CursorTy pvrtmp_6052 = tmp_struct_25.field0;
            unsigned char wildcard_660_1271_1580 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6052};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6053 = *(CursorTy *) tmpcur_6049;
            CursorTy tmpaftercur_6054 = tmpcur_6049 + 8;
            CursorTy jump_4158 = tmpcur_6049 + 8;
            unsigned char wildcard_4161 = print_symbol(5879);
            CursorProd tmp_struct_26 =  _print_String(end_r_2878, tmpcur_6053);
            CursorTy pvrtmp_6055 = tmp_struct_26.field0;
            
            return (CursorProd) {jump_4158};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6056 = *(CursorTy *) tmpcur_6049;
            CursorTy tmpaftercur_6057 = tmpcur_6049 + 8;
            unsigned char wildcard_4161 = print_symbol(5878);
            CursorProd tmp_struct_27 =  _print_String(end_r_2878, tmpcur_6056);
            CursorTy pvrtmp_6058 = tmp_struct_27.field0;
            
            return (CursorProd) {pvrtmp_6058};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6048");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Content(CursorTy end_r_2881,
                                           CursorTy end_r_2882,
                                           CursorTy loc_2880,
                                           CursorTy arg_661_1272_1581)
{
    if (loc_2880 + 32 > end_r_2882) {
        ChunkTy new_chunk_32 = alloc_chunk(end_r_2882);
        CursorTy chunk_start_33 = new_chunk_32.chunk_start;
        CursorTy chunk_end_34 = new_chunk_32.chunk_end;
        
        end_r_2882 = chunk_end_34;
        *(TagTyPacked *) loc_2880 = 255;
        
        CursorTy redir = loc_2880 + 1;
        
        *(CursorTy *) redir = chunk_start_33;
        loc_2880 = chunk_start_33;
    }
    
    TagTyPacked tmpval_6060 = *(TagTyPacked *) arg_661_1272_1581;
    CursorTy tmpcur_6061 = arg_661_1272_1581 + 1;
    
    
  switch_6110:
    ;
    switch (tmpval_6060) {
        
      case 0:
        {
            CursorTy loc_3008 = loc_2880 + 1;
            CursorCursorCursorCursorProd tmp_struct_28 =
                                          _copy_String(end_r_2881, end_r_2882, loc_3008, tmpcur_6061);
            CursorTy pvrtmp_6062 = tmp_struct_28.field0;
            CursorTy pvrtmp_6063 = tmp_struct_28.field1;
            CursorTy pvrtmp_6064 = tmp_struct_28.field2;
            CursorTy pvrtmp_6065 = tmp_struct_28.field3;
            
            *(TagTyPacked *) loc_2880 = 0;
            
            CursorTy writetag_4446 = loc_2880 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6062, pvrtmp_6063,
                                                   loc_2880, pvrtmp_6065};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3014 = loc_2880 + 1;
            CursorCursorCursorCursorProd tmp_struct_29 =
                                          _copy_String(end_r_2881, end_r_2882, loc_3014, tmpcur_6061);
            CursorTy pvrtmp_6074 = tmp_struct_29.field0;
            CursorTy pvrtmp_6075 = tmp_struct_29.field1;
            CursorTy pvrtmp_6076 = tmp_struct_29.field2;
            CursorTy pvrtmp_6077 = tmp_struct_29.field3;
            
            *(TagTyPacked *) loc_2880 = 1;
            
            CursorTy writetag_4451 = loc_2880 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6074, pvrtmp_6075,
                                                   loc_2880, pvrtmp_6077};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6086 = *(CursorTy *) tmpcur_6061;
            CursorTy tmpaftercur_6087 = tmpcur_6061 + 8;
            CursorTy jump_4164 = tmpcur_6061 + 8;
            CursorCursorCursorCursorProd tmp_struct_30 =
                                          _copy_Content(end_r_2881, end_r_2882, loc_2880, tmpcur_6086);
            CursorTy pvrtmp_6088 = tmp_struct_30.field0;
            CursorTy pvrtmp_6089 = tmp_struct_30.field1;
            CursorTy pvrtmp_6090 = tmp_struct_30.field2;
            CursorTy pvrtmp_6091 = tmp_struct_30.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6088, jump_4164,
                                                   pvrtmp_6090, pvrtmp_6091};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6098 = *(CursorTy *) tmpcur_6061;
            CursorTy tmpaftercur_6099 = tmpcur_6061 + 8;
            CursorCursorCursorCursorProd tmp_struct_31 =
                                          _copy_Content(end_r_2881, end_r_2882, loc_2880, tmpcur_6098);
            CursorTy pvrtmp_6100 = tmp_struct_31.field0;
            CursorTy pvrtmp_6101 = tmp_struct_31.field1;
            CursorTy pvrtmp_6102 = tmp_struct_31.field2;
            CursorTy pvrtmp_6103 = tmp_struct_31.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6100, pvrtmp_6101,
                                                   pvrtmp_6102, pvrtmp_6103};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6060");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Content(CursorTy end_r_2885,
                                                        CursorTy end_r_2886,
                                                        CursorTy loc_2884,
                                                        CursorTy arg_666_1277_1586)
{
    TagTyPacked tmpval_6111 = *(TagTyPacked *) arg_666_1277_1586;
    CursorTy tmpcur_6112 = arg_666_1277_1586 + 1;
    
    
  switch_6161:
    ;
    switch (tmpval_6111) {
        
      case 0:
        {
            CursorTy loc_3022 = loc_2884 + 1;
            CursorCursorCursorCursorProd tmp_struct_35 =
                                          _copy_without_ptrs_String(end_r_2885, end_r_2886, loc_3022, tmpcur_6112);
            CursorTy pvrtmp_6113 = tmp_struct_35.field0;
            CursorTy pvrtmp_6114 = tmp_struct_35.field1;
            CursorTy pvrtmp_6115 = tmp_struct_35.field2;
            CursorTy pvrtmp_6116 = tmp_struct_35.field3;
            
            *(TagTyPacked *) loc_2884 = 0;
            
            CursorTy writetag_4462 = loc_2884 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6113, pvrtmp_6114,
                                                   loc_2884, pvrtmp_6116};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3028 = loc_2884 + 1;
            CursorCursorCursorCursorProd tmp_struct_36 =
                                          _copy_without_ptrs_String(end_r_2885, end_r_2886, loc_3028, tmpcur_6112);
            CursorTy pvrtmp_6125 = tmp_struct_36.field0;
            CursorTy pvrtmp_6126 = tmp_struct_36.field1;
            CursorTy pvrtmp_6127 = tmp_struct_36.field2;
            CursorTy pvrtmp_6128 = tmp_struct_36.field3;
            
            *(TagTyPacked *) loc_2884 = 1;
            
            CursorTy writetag_4467 = loc_2884 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6125, pvrtmp_6126,
                                                   loc_2884, pvrtmp_6128};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6137 = *(CursorTy *) tmpcur_6112;
            CursorTy tmpaftercur_6138 = tmpcur_6112 + 8;
            CursorTy jump_4170 = tmpcur_6112 + 8;
            CursorCursorCursorCursorProd tmp_struct_37 =
                                          _copy_without_ptrs_Content(end_r_2885, end_r_2886, loc_2884, tmpcur_6137);
            CursorTy pvrtmp_6139 = tmp_struct_37.field0;
            CursorTy pvrtmp_6140 = tmp_struct_37.field1;
            CursorTy pvrtmp_6141 = tmp_struct_37.field2;
            CursorTy pvrtmp_6142 = tmp_struct_37.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6139, jump_4170,
                                                   pvrtmp_6141, pvrtmp_6142};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6149 = *(CursorTy *) tmpcur_6112;
            CursorTy tmpaftercur_6150 = tmpcur_6112 + 8;
            CursorCursorCursorCursorProd tmp_struct_38 =
                                          _copy_without_ptrs_Content(end_r_2885, end_r_2886, loc_2884, tmpcur_6149);
            CursorTy pvrtmp_6151 = tmp_struct_38.field0;
            CursorTy pvrtmp_6152 = tmp_struct_38.field1;
            CursorTy pvrtmp_6153 = tmp_struct_38.field2;
            CursorTy pvrtmp_6154 = tmp_struct_38.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6151, pvrtmp_6152,
                                                   pvrtmp_6153, pvrtmp_6154};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6111");
            exit(1);
        }
    }
}
CursorProd _traverse_Content(CursorTy end_r_2888, CursorTy arg_671_1282_1591)
{
    TagTyPacked tmpval_6162 = *(TagTyPacked *) arg_671_1282_1591;
    CursorTy tmpcur_6163 = arg_671_1282_1591 + 1;
    
    
  switch_6172:
    ;
    switch (tmpval_6162) {
        
      case 0:
        {
            CursorProd tmp_struct_39 =
                        _traverse_String(end_r_2888, tmpcur_6163);
            CursorTy pvrtmp_6164 = tmp_struct_39.field0;
            
            return (CursorProd) {pvrtmp_6164};
            break;
        }
        
      case 1:
        {
            CursorProd tmp_struct_40 =
                        _traverse_String(end_r_2888, tmpcur_6163);
            CursorTy pvrtmp_6165 = tmp_struct_40.field0;
            
            return (CursorProd) {pvrtmp_6165};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6166 = *(CursorTy *) tmpcur_6163;
            CursorTy tmpaftercur_6167 = tmpcur_6163 + 8;
            CursorTy jump_4176 = tmpcur_6163 + 8;
            CursorProd tmp_struct_41 =
                        _traverse_Content(end_r_2888, tmpcur_6166);
            CursorTy pvrtmp_6168 = tmp_struct_41.field0;
            
            return (CursorProd) {jump_4176};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6169 = *(CursorTy *) tmpcur_6163;
            CursorTy tmpaftercur_6170 = tmpcur_6163 + 8;
            CursorProd tmp_struct_42 =
                        _traverse_Content(end_r_2888, tmpcur_6169);
            CursorTy pvrtmp_6171 = tmp_struct_42.field0;
            
            return (CursorProd) {pvrtmp_6171};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6162");
            exit(1);
        }
    }
}
CursorProd _print_Content(CursorTy end_r_2890, CursorTy arg_676_1287_1596)
{
    TagTyPacked tmpval_6173 = *(TagTyPacked *) arg_676_1287_1596;
    CursorTy tmpcur_6174 = arg_676_1287_1596 + 1;
    
    
  switch_6183:
    ;
    switch (tmpval_6173) {
        
      case 0:
        {
            unsigned char wildcard_679_1289_1598 = print_symbol(5869);
            CursorProd tmp_struct_43 =  _print_String(end_r_2890, tmpcur_6174);
            CursorTy pvrtmp_6175 = tmp_struct_43.field0;
            unsigned char wildcard_680_1291_1600 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6175};
            break;
        }
        
      case 1:
        {
            unsigned char wildcard_683_1293_1602 = print_symbol(5863);
            CursorProd tmp_struct_44 =  _print_String(end_r_2890, tmpcur_6174);
            CursorTy pvrtmp_6176 = tmp_struct_44.field0;
            unsigned char wildcard_684_1295_1604 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6176};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6177 = *(CursorTy *) tmpcur_6174;
            CursorTy tmpaftercur_6178 = tmpcur_6174 + 8;
            CursorTy jump_4182 = tmpcur_6174 + 8;
            unsigned char wildcard_4185 = print_symbol(5879);
            CursorProd tmp_struct_45 =  _print_Content(end_r_2890, tmpcur_6177);
            CursorTy pvrtmp_6179 = tmp_struct_45.field0;
            
            return (CursorProd) {jump_4182};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6180 = *(CursorTy *) tmpcur_6174;
            CursorTy tmpaftercur_6181 = tmpcur_6174 + 8;
            unsigned char wildcard_4185 = print_symbol(5878);
            CursorProd tmp_struct_46 =  _print_Content(end_r_2890, tmpcur_6180);
            CursorTy pvrtmp_6182 = tmp_struct_46.field0;
            
            return (CursorProd) {pvrtmp_6182};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6173");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Adt(CursorTy end_r_2893, CursorTy end_r_2894,
                                       CursorTy loc_2892,
                                       CursorTy arg_685_1296_1605)
{
    if (loc_2892 + 32 > end_r_2894) {
        ChunkTy new_chunk_71 = alloc_chunk(end_r_2894);
        CursorTy chunk_start_72 = new_chunk_71.chunk_start;
        CursorTy chunk_end_73 = new_chunk_71.chunk_end;
        
        end_r_2894 = chunk_end_73;
        *(TagTyPacked *) loc_2892 = 255;
        
        CursorTy redir = loc_2892 + 1;
        
        *(CursorTy *) redir = chunk_start_72;
        loc_2892 = chunk_start_72;
    }
    
    CursorTy loc_3058 = loc_2892 + 1;
    CursorTy loc_3059 = loc_3058 + 8;
    CursorTy loc_3074 = loc_2892 + 1;
    CursorTy loc_3075 = loc_3074 + 8;
    CursorTy loc_3095 = loc_2892 + 1;
    CursorTy loc_3096 = loc_3095 + 8;
    CursorTy loc_3097 = loc_3096 + 8;
    CursorTy loc_3121 = loc_2892 + 1;
    CursorTy loc_3122 = loc_3121 + 8;
    CursorTy loc_3123 = loc_3122 + 8;
    CursorTy loc_3147 = loc_2892 + 1;
    CursorTy loc_3148 = loc_3147 + 8;
    CursorTy loc_3149 = loc_3148 + 8;
    CursorTy loc_3173 = loc_2892 + 1;
    CursorTy loc_3174 = loc_3173 + 8;
    CursorTy loc_3175 = loc_3174 + 8;
    CursorTy loc_3199 = loc_2892 + 1;
    CursorTy loc_3200 = loc_3199 + 8;
    CursorTy loc_3201 = loc_3200 + 8;
    CursorTy loc_3225 = loc_2892 + 1;
    CursorTy loc_3226 = loc_3225 + 8;
    CursorTy loc_3227 = loc_3226 + 8;
    TagTyPacked tmpval_6184 = *(TagTyPacked *) arg_685_1296_1605;
    CursorTy tmpcur_6185 = arg_685_1296_1605 + 1;
    
    
  switch_6450:
    ;
    switch (tmpval_6184) {
        
      case 0:
        {
            CursorTy jump_3877 = arg_685_1296_1605 + 1;
            
            *(TagTyPacked *) loc_2892 = 0;
            
            CursorTy writetag_4497 = loc_2892 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2894, jump_3877,
                                                   loc_2892, writetag_4497};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6190 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6191 = tmpcur_6185 + 8;
            CursorTy jump_3879 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_47 =
                                          _copy_Content(end_r_2893, end_r_2894, loc_3059, tmpaftercur_6191);
            CursorTy pvrtmp_6192 = tmp_struct_47.field0;
            CursorTy pvrtmp_6193 = tmp_struct_47.field1;
            CursorTy pvrtmp_6194 = tmp_struct_47.field2;
            CursorTy pvrtmp_6195 = tmp_struct_47.field3;
            CursorCursorCursorCursorProd tmp_struct_48 =
                                          _copy_Adt(end_r_2893, pvrtmp_6192, pvrtmp_6195, tmpcur_6190);
            CursorTy pvrtmp_6200 = tmp_struct_48.field0;
            CursorTy pvrtmp_6201 = tmp_struct_48.field1;
            CursorTy pvrtmp_6202 = tmp_struct_48.field2;
            CursorTy pvrtmp_6203 = tmp_struct_48.field3;
            
            *(TagTyPacked *) loc_2892 = 9;
            
            CursorTy writetag_4503 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4503 = pvrtmp_6195;
            
            CursorTy writecur_4504 = writetag_4503 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6200, pvrtmp_6201,
                                                   loc_2892, pvrtmp_6203};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6212 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6213 = tmpcur_6185 + 8;
            CursorTy jump_3883 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_49 =
                                          _copy_Adt(end_r_2893, end_r_2894, loc_3075, tmpaftercur_6213);
            CursorTy pvrtmp_6214 = tmp_struct_49.field0;
            CursorTy pvrtmp_6215 = tmp_struct_49.field1;
            CursorTy pvrtmp_6216 = tmp_struct_49.field2;
            CursorTy pvrtmp_6217 = tmp_struct_49.field3;
            CursorCursorCursorCursorProd tmp_struct_50 =
                                          _copy_Content(end_r_2893, pvrtmp_6214, pvrtmp_6217, tmpcur_6212);
            CursorTy pvrtmp_6222 = tmp_struct_50.field0;
            CursorTy pvrtmp_6223 = tmp_struct_50.field1;
            CursorTy pvrtmp_6224 = tmp_struct_50.field2;
            CursorTy pvrtmp_6225 = tmp_struct_50.field3;
            
            *(TagTyPacked *) loc_2892 = 11;
            
            CursorTy writetag_4512 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4512 = pvrtmp_6217;
            
            CursorTy writecur_4513 = writetag_4512 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6222, pvrtmp_6223,
                                                   loc_2892, pvrtmp_6225};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6234 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6235 = tmpcur_6185 + 8;
            CursorTy tmpcur_6236 = *(CursorTy *) tmpaftercur_6235;
            CursorTy tmpaftercur_6237 = tmpaftercur_6235 + 8;
            CursorTy jump_3888 = tmpaftercur_6235 + 8;
            CursorTy jump_3887 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_51 =
                                          _copy_Tags(end_r_2893, end_r_2894, loc_3097, tmpaftercur_6237);
            CursorTy pvrtmp_6238 = tmp_struct_51.field0;
            CursorTy pvrtmp_6239 = tmp_struct_51.field1;
            CursorTy pvrtmp_6240 = tmp_struct_51.field2;
            CursorTy pvrtmp_6241 = tmp_struct_51.field3;
            CursorCursorCursorCursorProd tmp_struct_52 =
                                          _copy_Content(end_r_2893, pvrtmp_6238, pvrtmp_6241, tmpcur_6234);
            CursorTy pvrtmp_6246 = tmp_struct_52.field0;
            CursorTy pvrtmp_6247 = tmp_struct_52.field1;
            CursorTy pvrtmp_6248 = tmp_struct_52.field2;
            CursorTy pvrtmp_6249 = tmp_struct_52.field3;
            CursorCursorCursorCursorProd tmp_struct_53 =
                                          _copy_Adt(end_r_2893, pvrtmp_6246, pvrtmp_6249, tmpcur_6236);
            CursorTy pvrtmp_6254 = tmp_struct_53.field0;
            CursorTy pvrtmp_6255 = tmp_struct_53.field1;
            CursorTy pvrtmp_6256 = tmp_struct_53.field2;
            CursorTy pvrtmp_6257 = tmp_struct_53.field3;
            
            *(TagTyPacked *) loc_2892 = 13;
            
            CursorTy writetag_4523 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4523 = pvrtmp_6241;
            
            CursorTy writecur_4524 = writetag_4523 + 8;
            
            *(CursorTy *) writecur_4524 = pvrtmp_6249;
            
            CursorTy writecur_4525 = writecur_4524 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6254, pvrtmp_6255,
                                                   loc_2892, pvrtmp_6257};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6266 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6267 = tmpcur_6185 + 8;
            CursorTy tmpcur_6268 = *(CursorTy *) tmpaftercur_6267;
            CursorTy tmpaftercur_6269 = tmpaftercur_6267 + 8;
            CursorTy jump_3894 = tmpaftercur_6267 + 8;
            CursorTy jump_3893 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_54 =
                                          _copy_Adt(end_r_2893, end_r_2894, loc_3123, tmpaftercur_6269);
            CursorTy pvrtmp_6270 = tmp_struct_54.field0;
            CursorTy pvrtmp_6271 = tmp_struct_54.field1;
            CursorTy pvrtmp_6272 = tmp_struct_54.field2;
            CursorTy pvrtmp_6273 = tmp_struct_54.field3;
            CursorCursorCursorCursorProd tmp_struct_55 =
                                          _copy_Content(end_r_2893, pvrtmp_6270, pvrtmp_6273, tmpcur_6266);
            CursorTy pvrtmp_6278 = tmp_struct_55.field0;
            CursorTy pvrtmp_6279 = tmp_struct_55.field1;
            CursorTy pvrtmp_6280 = tmp_struct_55.field2;
            CursorTy pvrtmp_6281 = tmp_struct_55.field3;
            CursorCursorCursorCursorProd tmp_struct_56 =
                                          _copy_Tags(end_r_2893, pvrtmp_6278, pvrtmp_6281, tmpcur_6268);
            CursorTy pvrtmp_6286 = tmp_struct_56.field0;
            CursorTy pvrtmp_6287 = tmp_struct_56.field1;
            CursorTy pvrtmp_6288 = tmp_struct_56.field2;
            CursorTy pvrtmp_6289 = tmp_struct_56.field3;
            
            *(TagTyPacked *) loc_2892 = 15;
            
            CursorTy writetag_4536 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4536 = pvrtmp_6273;
            
            CursorTy writecur_4537 = writetag_4536 + 8;
            
            *(CursorTy *) writecur_4537 = pvrtmp_6281;
            
            CursorTy writecur_4538 = writecur_4537 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6286, pvrtmp_6287,
                                                   loc_2892, pvrtmp_6289};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6298 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6299 = tmpcur_6185 + 8;
            CursorTy tmpcur_6300 = *(CursorTy *) tmpaftercur_6299;
            CursorTy tmpaftercur_6301 = tmpaftercur_6299 + 8;
            CursorTy jump_3900 = tmpaftercur_6299 + 8;
            CursorTy jump_3899 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_57 =
                                          _copy_Tags(end_r_2893, end_r_2894, loc_3149, tmpaftercur_6301);
            CursorTy pvrtmp_6302 = tmp_struct_57.field0;
            CursorTy pvrtmp_6303 = tmp_struct_57.field1;
            CursorTy pvrtmp_6304 = tmp_struct_57.field2;
            CursorTy pvrtmp_6305 = tmp_struct_57.field3;
            CursorCursorCursorCursorProd tmp_struct_58 =
                                          _copy_Adt(end_r_2893, pvrtmp_6302, pvrtmp_6305, tmpcur_6298);
            CursorTy pvrtmp_6310 = tmp_struct_58.field0;
            CursorTy pvrtmp_6311 = tmp_struct_58.field1;
            CursorTy pvrtmp_6312 = tmp_struct_58.field2;
            CursorTy pvrtmp_6313 = tmp_struct_58.field3;
            CursorCursorCursorCursorProd tmp_struct_59 =
                                          _copy_Content(end_r_2893, pvrtmp_6310, pvrtmp_6313, tmpcur_6300);
            CursorTy pvrtmp_6318 = tmp_struct_59.field0;
            CursorTy pvrtmp_6319 = tmp_struct_59.field1;
            CursorTy pvrtmp_6320 = tmp_struct_59.field2;
            CursorTy pvrtmp_6321 = tmp_struct_59.field3;
            
            *(TagTyPacked *) loc_2892 = 17;
            
            CursorTy writetag_4549 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4549 = pvrtmp_6305;
            
            CursorTy writecur_4550 = writetag_4549 + 8;
            
            *(CursorTy *) writecur_4550 = pvrtmp_6313;
            
            CursorTy writecur_4551 = writecur_4550 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6318, pvrtmp_6319,
                                                   loc_2892, pvrtmp_6321};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6330 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6331 = tmpcur_6185 + 8;
            CursorTy tmpcur_6332 = *(CursorTy *) tmpaftercur_6331;
            CursorTy tmpaftercur_6333 = tmpaftercur_6331 + 8;
            CursorTy jump_3906 = tmpaftercur_6331 + 8;
            CursorTy jump_3905 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_60 =
                                          _copy_Adt(end_r_2893, end_r_2894, loc_3175, tmpaftercur_6333);
            CursorTy pvrtmp_6334 = tmp_struct_60.field0;
            CursorTy pvrtmp_6335 = tmp_struct_60.field1;
            CursorTy pvrtmp_6336 = tmp_struct_60.field2;
            CursorTy pvrtmp_6337 = tmp_struct_60.field3;
            CursorCursorCursorCursorProd tmp_struct_61 =
                                          _copy_Tags(end_r_2893, pvrtmp_6334, pvrtmp_6337, tmpcur_6330);
            CursorTy pvrtmp_6342 = tmp_struct_61.field0;
            CursorTy pvrtmp_6343 = tmp_struct_61.field1;
            CursorTy pvrtmp_6344 = tmp_struct_61.field2;
            CursorTy pvrtmp_6345 = tmp_struct_61.field3;
            CursorCursorCursorCursorProd tmp_struct_62 =
                                          _copy_Content(end_r_2893, pvrtmp_6342, pvrtmp_6345, tmpcur_6332);
            CursorTy pvrtmp_6350 = tmp_struct_62.field0;
            CursorTy pvrtmp_6351 = tmp_struct_62.field1;
            CursorTy pvrtmp_6352 = tmp_struct_62.field2;
            CursorTy pvrtmp_6353 = tmp_struct_62.field3;
            
            *(TagTyPacked *) loc_2892 = 19;
            
            CursorTy writetag_4562 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4562 = pvrtmp_6337;
            
            CursorTy writecur_4563 = writetag_4562 + 8;
            
            *(CursorTy *) writecur_4563 = pvrtmp_6345;
            
            CursorTy writecur_4564 = writecur_4563 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6350, pvrtmp_6351,
                                                   loc_2892, pvrtmp_6353};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6362 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6363 = tmpcur_6185 + 8;
            CursorTy tmpcur_6364 = *(CursorTy *) tmpaftercur_6363;
            CursorTy tmpaftercur_6365 = tmpaftercur_6363 + 8;
            CursorTy jump_3912 = tmpaftercur_6363 + 8;
            CursorTy jump_3911 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_63 =
                                          _copy_Content(end_r_2893, end_r_2894, loc_3201, tmpaftercur_6365);
            CursorTy pvrtmp_6366 = tmp_struct_63.field0;
            CursorTy pvrtmp_6367 = tmp_struct_63.field1;
            CursorTy pvrtmp_6368 = tmp_struct_63.field2;
            CursorTy pvrtmp_6369 = tmp_struct_63.field3;
            CursorCursorCursorCursorProd tmp_struct_64 =
                                          _copy_Tags(end_r_2893, pvrtmp_6366, pvrtmp_6369, tmpcur_6362);
            CursorTy pvrtmp_6374 = tmp_struct_64.field0;
            CursorTy pvrtmp_6375 = tmp_struct_64.field1;
            CursorTy pvrtmp_6376 = tmp_struct_64.field2;
            CursorTy pvrtmp_6377 = tmp_struct_64.field3;
            CursorCursorCursorCursorProd tmp_struct_65 =
                                          _copy_Adt(end_r_2893, pvrtmp_6374, pvrtmp_6377, tmpcur_6364);
            CursorTy pvrtmp_6382 = tmp_struct_65.field0;
            CursorTy pvrtmp_6383 = tmp_struct_65.field1;
            CursorTy pvrtmp_6384 = tmp_struct_65.field2;
            CursorTy pvrtmp_6385 = tmp_struct_65.field3;
            
            *(TagTyPacked *) loc_2892 = 21;
            
            CursorTy writetag_4575 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4575 = pvrtmp_6369;
            
            CursorTy writecur_4576 = writetag_4575 + 8;
            
            *(CursorTy *) writecur_4576 = pvrtmp_6377;
            
            CursorTy writecur_4577 = writecur_4576 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6382, pvrtmp_6383,
                                                   loc_2892, pvrtmp_6385};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6394 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6395 = tmpcur_6185 + 8;
            CursorTy tmpcur_6396 = *(CursorTy *) tmpaftercur_6395;
            CursorTy tmpaftercur_6397 = tmpaftercur_6395 + 8;
            CursorTy jump_3918 = tmpaftercur_6395 + 8;
            CursorTy jump_3917 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_66 =
                                          _copy_Content(end_r_2893, end_r_2894, loc_3227, tmpaftercur_6397);
            CursorTy pvrtmp_6398 = tmp_struct_66.field0;
            CursorTy pvrtmp_6399 = tmp_struct_66.field1;
            CursorTy pvrtmp_6400 = tmp_struct_66.field2;
            CursorTy pvrtmp_6401 = tmp_struct_66.field3;
            CursorCursorCursorCursorProd tmp_struct_67 =
                                          _copy_Adt(end_r_2893, pvrtmp_6398, pvrtmp_6401, tmpcur_6394);
            CursorTy pvrtmp_6406 = tmp_struct_67.field0;
            CursorTy pvrtmp_6407 = tmp_struct_67.field1;
            CursorTy pvrtmp_6408 = tmp_struct_67.field2;
            CursorTy pvrtmp_6409 = tmp_struct_67.field3;
            CursorCursorCursorCursorProd tmp_struct_68 =
                                          _copy_Tags(end_r_2893, pvrtmp_6406, pvrtmp_6409, tmpcur_6396);
            CursorTy pvrtmp_6414 = tmp_struct_68.field0;
            CursorTy pvrtmp_6415 = tmp_struct_68.field1;
            CursorTy pvrtmp_6416 = tmp_struct_68.field2;
            CursorTy pvrtmp_6417 = tmp_struct_68.field3;
            
            *(TagTyPacked *) loc_2892 = 23;
            
            CursorTy writetag_4588 = loc_2892 + 1;
            
            *(CursorTy *) writetag_4588 = pvrtmp_6401;
            
            CursorTy writecur_4589 = writetag_4588 + 8;
            
            *(CursorTy *) writecur_4589 = pvrtmp_6409;
            
            CursorTy writecur_4590 = writecur_4589 + 8;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6414, pvrtmp_6415,
                                                   loc_2892, pvrtmp_6417};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6426 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6427 = tmpcur_6185 + 8;
            CursorTy jump_4188 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_69 =
                                          _copy_Adt(end_r_2893, end_r_2894, loc_2892, tmpcur_6426);
            CursorTy pvrtmp_6428 = tmp_struct_69.field0;
            CursorTy pvrtmp_6429 = tmp_struct_69.field1;
            CursorTy pvrtmp_6430 = tmp_struct_69.field2;
            CursorTy pvrtmp_6431 = tmp_struct_69.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6428, jump_4188,
                                                   pvrtmp_6430, pvrtmp_6431};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6438 = *(CursorTy *) tmpcur_6185;
            CursorTy tmpaftercur_6439 = tmpcur_6185 + 8;
            CursorCursorCursorCursorProd tmp_struct_70 =
                                          _copy_Adt(end_r_2893, end_r_2894, loc_2892, tmpcur_6438);
            CursorTy pvrtmp_6440 = tmp_struct_70.field0;
            CursorTy pvrtmp_6441 = tmp_struct_70.field1;
            CursorTy pvrtmp_6442 = tmp_struct_70.field2;
            CursorTy pvrtmp_6443 = tmp_struct_70.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6440, pvrtmp_6441,
                                                   pvrtmp_6442, pvrtmp_6443};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6184");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Adt(CursorTy end_r_2897,
                                                    CursorTy end_r_2898,
                                                    CursorTy loc_2896,
                                                    CursorTy arg_730_1341_1650)
{
    TagTyPacked tmpval_6451 = *(TagTyPacked *) arg_730_1341_1650;
    CursorTy tmpcur_6452 = arg_730_1341_1650 + 1;
    
    
  switch_6717:
    ;
    switch (tmpval_6451) {
        
      case 0:
        {
            CursorTy jump_3923 = arg_730_1341_1650 + 1;
            
            *(TagTyPacked *) loc_2896 = 0;
            
            CursorTy writetag_4602 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2898, jump_3923,
                                                   loc_2896, writetag_4602};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6457 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6458 = tmpcur_6452 + 8;
            CursorTy jump_3925 = tmpcur_6452 + 8;
            CursorTy loc_3249 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_74 =
                                          _copy_without_ptrs_Content(end_r_2897, end_r_2898, loc_3249, tmpaftercur_6458);
            CursorTy pvrtmp_6459 = tmp_struct_74.field0;
            CursorTy pvrtmp_6460 = tmp_struct_74.field1;
            CursorTy pvrtmp_6461 = tmp_struct_74.field2;
            CursorTy pvrtmp_6462 = tmp_struct_74.field3;
            CursorCursorCursorCursorProd tmp_struct_75 =
                                          _copy_without_ptrs_Adt(end_r_2897, pvrtmp_6459, pvrtmp_6462, tmpcur_6457);
            CursorTy pvrtmp_6467 = tmp_struct_75.field0;
            CursorTy pvrtmp_6468 = tmp_struct_75.field1;
            CursorTy pvrtmp_6469 = tmp_struct_75.field2;
            CursorTy pvrtmp_6470 = tmp_struct_75.field3;
            
            *(TagTyPacked *) loc_2896 = 1;
            
            CursorTy writetag_4608 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6467, pvrtmp_6468,
                                                   loc_2896, pvrtmp_6470};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6479 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6480 = tmpcur_6452 + 8;
            CursorTy jump_3929 = tmpcur_6452 + 8;
            CursorTy loc_3262 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_76 =
                                          _copy_without_ptrs_Adt(end_r_2897, end_r_2898, loc_3262, tmpaftercur_6480);
            CursorTy pvrtmp_6481 = tmp_struct_76.field0;
            CursorTy pvrtmp_6482 = tmp_struct_76.field1;
            CursorTy pvrtmp_6483 = tmp_struct_76.field2;
            CursorTy pvrtmp_6484 = tmp_struct_76.field3;
            CursorCursorCursorCursorProd tmp_struct_77 =
                                          _copy_without_ptrs_Content(end_r_2897, pvrtmp_6481, pvrtmp_6484, tmpcur_6479);
            CursorTy pvrtmp_6489 = tmp_struct_77.field0;
            CursorTy pvrtmp_6490 = tmp_struct_77.field1;
            CursorTy pvrtmp_6491 = tmp_struct_77.field2;
            CursorTy pvrtmp_6492 = tmp_struct_77.field3;
            
            *(TagTyPacked *) loc_2896 = 2;
            
            CursorTy writetag_4616 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6489, pvrtmp_6490,
                                                   loc_2896, pvrtmp_6492};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6501 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6502 = tmpcur_6452 + 8;
            CursorTy tmpcur_6503 = *(CursorTy *) tmpaftercur_6502;
            CursorTy tmpaftercur_6504 = tmpaftercur_6502 + 8;
            CursorTy jump_3934 = tmpaftercur_6502 + 8;
            CursorTy jump_3933 = tmpcur_6452 + 8;
            CursorTy loc_3280 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_78 =
                                          _copy_without_ptrs_Tags(end_r_2897, end_r_2898, loc_3280, tmpaftercur_6504);
            CursorTy pvrtmp_6505 = tmp_struct_78.field0;
            CursorTy pvrtmp_6506 = tmp_struct_78.field1;
            CursorTy pvrtmp_6507 = tmp_struct_78.field2;
            CursorTy pvrtmp_6508 = tmp_struct_78.field3;
            CursorCursorCursorCursorProd tmp_struct_79 =
                                          _copy_without_ptrs_Content(end_r_2897, pvrtmp_6505, pvrtmp_6508, tmpcur_6501);
            CursorTy pvrtmp_6513 = tmp_struct_79.field0;
            CursorTy pvrtmp_6514 = tmp_struct_79.field1;
            CursorTy pvrtmp_6515 = tmp_struct_79.field2;
            CursorTy pvrtmp_6516 = tmp_struct_79.field3;
            CursorCursorCursorCursorProd tmp_struct_80 =
                                          _copy_without_ptrs_Adt(end_r_2897, pvrtmp_6513, pvrtmp_6516, tmpcur_6503);
            CursorTy pvrtmp_6521 = tmp_struct_80.field0;
            CursorTy pvrtmp_6522 = tmp_struct_80.field1;
            CursorTy pvrtmp_6523 = tmp_struct_80.field2;
            CursorTy pvrtmp_6524 = tmp_struct_80.field3;
            
            *(TagTyPacked *) loc_2896 = 3;
            
            CursorTy writetag_4626 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6521, pvrtmp_6522,
                                                   loc_2896, pvrtmp_6524};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6533 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6534 = tmpcur_6452 + 8;
            CursorTy tmpcur_6535 = *(CursorTy *) tmpaftercur_6534;
            CursorTy tmpaftercur_6536 = tmpaftercur_6534 + 8;
            CursorTy jump_3940 = tmpaftercur_6534 + 8;
            CursorTy jump_3939 = tmpcur_6452 + 8;
            CursorTy loc_3300 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_81 =
                                          _copy_without_ptrs_Adt(end_r_2897, end_r_2898, loc_3300, tmpaftercur_6536);
            CursorTy pvrtmp_6537 = tmp_struct_81.field0;
            CursorTy pvrtmp_6538 = tmp_struct_81.field1;
            CursorTy pvrtmp_6539 = tmp_struct_81.field2;
            CursorTy pvrtmp_6540 = tmp_struct_81.field3;
            CursorCursorCursorCursorProd tmp_struct_82 =
                                          _copy_without_ptrs_Content(end_r_2897, pvrtmp_6537, pvrtmp_6540, tmpcur_6533);
            CursorTy pvrtmp_6545 = tmp_struct_82.field0;
            CursorTy pvrtmp_6546 = tmp_struct_82.field1;
            CursorTy pvrtmp_6547 = tmp_struct_82.field2;
            CursorTy pvrtmp_6548 = tmp_struct_82.field3;
            CursorCursorCursorCursorProd tmp_struct_83 =
                                          _copy_without_ptrs_Tags(end_r_2897, pvrtmp_6545, pvrtmp_6548, tmpcur_6535);
            CursorTy pvrtmp_6553 = tmp_struct_83.field0;
            CursorTy pvrtmp_6554 = tmp_struct_83.field1;
            CursorTy pvrtmp_6555 = tmp_struct_83.field2;
            CursorTy pvrtmp_6556 = tmp_struct_83.field3;
            
            *(TagTyPacked *) loc_2896 = 4;
            
            CursorTy writetag_4637 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6553, pvrtmp_6554,
                                                   loc_2896, pvrtmp_6556};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6565 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6566 = tmpcur_6452 + 8;
            CursorTy tmpcur_6567 = *(CursorTy *) tmpaftercur_6566;
            CursorTy tmpaftercur_6568 = tmpaftercur_6566 + 8;
            CursorTy jump_3946 = tmpaftercur_6566 + 8;
            CursorTy jump_3945 = tmpcur_6452 + 8;
            CursorTy loc_3320 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_84 =
                                          _copy_without_ptrs_Tags(end_r_2897, end_r_2898, loc_3320, tmpaftercur_6568);
            CursorTy pvrtmp_6569 = tmp_struct_84.field0;
            CursorTy pvrtmp_6570 = tmp_struct_84.field1;
            CursorTy pvrtmp_6571 = tmp_struct_84.field2;
            CursorTy pvrtmp_6572 = tmp_struct_84.field3;
            CursorCursorCursorCursorProd tmp_struct_85 =
                                          _copy_without_ptrs_Adt(end_r_2897, pvrtmp_6569, pvrtmp_6572, tmpcur_6565);
            CursorTy pvrtmp_6577 = tmp_struct_85.field0;
            CursorTy pvrtmp_6578 = tmp_struct_85.field1;
            CursorTy pvrtmp_6579 = tmp_struct_85.field2;
            CursorTy pvrtmp_6580 = tmp_struct_85.field3;
            CursorCursorCursorCursorProd tmp_struct_86 =
                                          _copy_without_ptrs_Content(end_r_2897, pvrtmp_6577, pvrtmp_6580, tmpcur_6567);
            CursorTy pvrtmp_6585 = tmp_struct_86.field0;
            CursorTy pvrtmp_6586 = tmp_struct_86.field1;
            CursorTy pvrtmp_6587 = tmp_struct_86.field2;
            CursorTy pvrtmp_6588 = tmp_struct_86.field3;
            
            *(TagTyPacked *) loc_2896 = 5;
            
            CursorTy writetag_4648 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6585, pvrtmp_6586,
                                                   loc_2896, pvrtmp_6588};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6597 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6598 = tmpcur_6452 + 8;
            CursorTy tmpcur_6599 = *(CursorTy *) tmpaftercur_6598;
            CursorTy tmpaftercur_6600 = tmpaftercur_6598 + 8;
            CursorTy jump_3952 = tmpaftercur_6598 + 8;
            CursorTy jump_3951 = tmpcur_6452 + 8;
            CursorTy loc_3340 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_87 =
                                          _copy_without_ptrs_Adt(end_r_2897, end_r_2898, loc_3340, tmpaftercur_6600);
            CursorTy pvrtmp_6601 = tmp_struct_87.field0;
            CursorTy pvrtmp_6602 = tmp_struct_87.field1;
            CursorTy pvrtmp_6603 = tmp_struct_87.field2;
            CursorTy pvrtmp_6604 = tmp_struct_87.field3;
            CursorCursorCursorCursorProd tmp_struct_88 =
                                          _copy_without_ptrs_Tags(end_r_2897, pvrtmp_6601, pvrtmp_6604, tmpcur_6597);
            CursorTy pvrtmp_6609 = tmp_struct_88.field0;
            CursorTy pvrtmp_6610 = tmp_struct_88.field1;
            CursorTy pvrtmp_6611 = tmp_struct_88.field2;
            CursorTy pvrtmp_6612 = tmp_struct_88.field3;
            CursorCursorCursorCursorProd tmp_struct_89 =
                                          _copy_without_ptrs_Content(end_r_2897, pvrtmp_6609, pvrtmp_6612, tmpcur_6599);
            CursorTy pvrtmp_6617 = tmp_struct_89.field0;
            CursorTy pvrtmp_6618 = tmp_struct_89.field1;
            CursorTy pvrtmp_6619 = tmp_struct_89.field2;
            CursorTy pvrtmp_6620 = tmp_struct_89.field3;
            
            *(TagTyPacked *) loc_2896 = 6;
            
            CursorTy writetag_4659 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6617, pvrtmp_6618,
                                                   loc_2896, pvrtmp_6620};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6629 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6630 = tmpcur_6452 + 8;
            CursorTy tmpcur_6631 = *(CursorTy *) tmpaftercur_6630;
            CursorTy tmpaftercur_6632 = tmpaftercur_6630 + 8;
            CursorTy jump_3958 = tmpaftercur_6630 + 8;
            CursorTy jump_3957 = tmpcur_6452 + 8;
            CursorTy loc_3360 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_90 =
                                          _copy_without_ptrs_Content(end_r_2897, end_r_2898, loc_3360, tmpaftercur_6632);
            CursorTy pvrtmp_6633 = tmp_struct_90.field0;
            CursorTy pvrtmp_6634 = tmp_struct_90.field1;
            CursorTy pvrtmp_6635 = tmp_struct_90.field2;
            CursorTy pvrtmp_6636 = tmp_struct_90.field3;
            CursorCursorCursorCursorProd tmp_struct_91 =
                                          _copy_without_ptrs_Tags(end_r_2897, pvrtmp_6633, pvrtmp_6636, tmpcur_6629);
            CursorTy pvrtmp_6641 = tmp_struct_91.field0;
            CursorTy pvrtmp_6642 = tmp_struct_91.field1;
            CursorTy pvrtmp_6643 = tmp_struct_91.field2;
            CursorTy pvrtmp_6644 = tmp_struct_91.field3;
            CursorCursorCursorCursorProd tmp_struct_92 =
                                          _copy_without_ptrs_Adt(end_r_2897, pvrtmp_6641, pvrtmp_6644, tmpcur_6631);
            CursorTy pvrtmp_6649 = tmp_struct_92.field0;
            CursorTy pvrtmp_6650 = tmp_struct_92.field1;
            CursorTy pvrtmp_6651 = tmp_struct_92.field2;
            CursorTy pvrtmp_6652 = tmp_struct_92.field3;
            
            *(TagTyPacked *) loc_2896 = 7;
            
            CursorTy writetag_4670 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6649, pvrtmp_6650,
                                                   loc_2896, pvrtmp_6652};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6661 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6662 = tmpcur_6452 + 8;
            CursorTy tmpcur_6663 = *(CursorTy *) tmpaftercur_6662;
            CursorTy tmpaftercur_6664 = tmpaftercur_6662 + 8;
            CursorTy jump_3964 = tmpaftercur_6662 + 8;
            CursorTy jump_3963 = tmpcur_6452 + 8;
            CursorTy loc_3380 = loc_2896 + 1;
            CursorCursorCursorCursorProd tmp_struct_93 =
                                          _copy_without_ptrs_Content(end_r_2897, end_r_2898, loc_3380, tmpaftercur_6664);
            CursorTy pvrtmp_6665 = tmp_struct_93.field0;
            CursorTy pvrtmp_6666 = tmp_struct_93.field1;
            CursorTy pvrtmp_6667 = tmp_struct_93.field2;
            CursorTy pvrtmp_6668 = tmp_struct_93.field3;
            CursorCursorCursorCursorProd tmp_struct_94 =
                                          _copy_without_ptrs_Adt(end_r_2897, pvrtmp_6665, pvrtmp_6668, tmpcur_6661);
            CursorTy pvrtmp_6673 = tmp_struct_94.field0;
            CursorTy pvrtmp_6674 = tmp_struct_94.field1;
            CursorTy pvrtmp_6675 = tmp_struct_94.field2;
            CursorTy pvrtmp_6676 = tmp_struct_94.field3;
            CursorCursorCursorCursorProd tmp_struct_95 =
                                          _copy_without_ptrs_Tags(end_r_2897, pvrtmp_6673, pvrtmp_6676, tmpcur_6663);
            CursorTy pvrtmp_6681 = tmp_struct_95.field0;
            CursorTy pvrtmp_6682 = tmp_struct_95.field1;
            CursorTy pvrtmp_6683 = tmp_struct_95.field2;
            CursorTy pvrtmp_6684 = tmp_struct_95.field3;
            
            *(TagTyPacked *) loc_2896 = 8;
            
            CursorTy writetag_4681 = loc_2896 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6681, pvrtmp_6682,
                                                   loc_2896, pvrtmp_6684};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6693 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6694 = tmpcur_6452 + 8;
            CursorTy jump_4194 = tmpcur_6452 + 8;
            CursorCursorCursorCursorProd tmp_struct_96 =
                                          _copy_without_ptrs_Adt(end_r_2897, end_r_2898, loc_2896, tmpcur_6693);
            CursorTy pvrtmp_6695 = tmp_struct_96.field0;
            CursorTy pvrtmp_6696 = tmp_struct_96.field1;
            CursorTy pvrtmp_6697 = tmp_struct_96.field2;
            CursorTy pvrtmp_6698 = tmp_struct_96.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6695, jump_4194,
                                                   pvrtmp_6697, pvrtmp_6698};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6705 = *(CursorTy *) tmpcur_6452;
            CursorTy tmpaftercur_6706 = tmpcur_6452 + 8;
            CursorCursorCursorCursorProd tmp_struct_97 =
                                          _copy_without_ptrs_Adt(end_r_2897, end_r_2898, loc_2896, tmpcur_6705);
            CursorTy pvrtmp_6707 = tmp_struct_97.field0;
            CursorTy pvrtmp_6708 = tmp_struct_97.field1;
            CursorTy pvrtmp_6709 = tmp_struct_97.field2;
            CursorTy pvrtmp_6710 = tmp_struct_97.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6707, pvrtmp_6708,
                                                   pvrtmp_6709, pvrtmp_6710};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6451");
            exit(1);
        }
    }
}
CursorProd _traverse_Adt(CursorTy end_r_2900, CursorTy arg_775_1386_1695)
{
    TagTyPacked tmpval_6718 = *(TagTyPacked *) arg_775_1386_1695;
    CursorTy tmpcur_6719 = arg_775_1386_1695 + 1;
    
    
  switch_6776:
    ;
    switch (tmpval_6718) {
        
      case 0:
        {
            CursorTy jump_3969 = arg_775_1386_1695 + 1;
            
            return (CursorProd) {jump_3969};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6720 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6721 = tmpcur_6719 + 8;
            CursorTy jump_3971 = tmpcur_6719 + 8;
            CursorProd tmp_struct_98 =
                        _traverse_Content(end_r_2900, tmpaftercur_6721);
            CursorTy pvrtmp_6722 = tmp_struct_98.field0;
            CursorProd tmp_struct_99 =  _traverse_Adt(end_r_2900, tmpcur_6720);
            CursorTy pvrtmp_6723 = tmp_struct_99.field0;
            
            return (CursorProd) {pvrtmp_6723};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6724 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6725 = tmpcur_6719 + 8;
            CursorTy jump_3975 = tmpcur_6719 + 8;
            CursorProd tmp_struct_100 =
                        _traverse_Adt(end_r_2900, tmpaftercur_6725);
            CursorTy pvrtmp_6726 = tmp_struct_100.field0;
            CursorProd tmp_struct_101 =
                        _traverse_Content(end_r_2900, tmpcur_6724);
            CursorTy pvrtmp_6727 = tmp_struct_101.field0;
            
            return (CursorProd) {pvrtmp_6727};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6728 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6729 = tmpcur_6719 + 8;
            CursorTy tmpcur_6730 = *(CursorTy *) tmpaftercur_6729;
            CursorTy tmpaftercur_6731 = tmpaftercur_6729 + 8;
            CursorTy jump_3980 = tmpaftercur_6729 + 8;
            CursorTy jump_3979 = tmpcur_6719 + 8;
            CursorProd tmp_struct_102 =
                        _traverse_Tags(end_r_2900, tmpaftercur_6731);
            CursorTy pvrtmp_6732 = tmp_struct_102.field0;
            CursorProd tmp_struct_103 =
                        _traverse_Content(end_r_2900, tmpcur_6728);
            CursorTy pvrtmp_6733 = tmp_struct_103.field0;
            CursorProd tmp_struct_104 =  _traverse_Adt(end_r_2900, tmpcur_6730);
            CursorTy pvrtmp_6734 = tmp_struct_104.field0;
            
            return (CursorProd) {pvrtmp_6734};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6735 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6736 = tmpcur_6719 + 8;
            CursorTy tmpcur_6737 = *(CursorTy *) tmpaftercur_6736;
            CursorTy tmpaftercur_6738 = tmpaftercur_6736 + 8;
            CursorTy jump_3986 = tmpaftercur_6736 + 8;
            CursorTy jump_3985 = tmpcur_6719 + 8;
            CursorProd tmp_struct_105 =
                        _traverse_Adt(end_r_2900, tmpaftercur_6738);
            CursorTy pvrtmp_6739 = tmp_struct_105.field0;
            CursorProd tmp_struct_106 =
                        _traverse_Content(end_r_2900, tmpcur_6735);
            CursorTy pvrtmp_6740 = tmp_struct_106.field0;
            CursorProd tmp_struct_107 =
                        _traverse_Tags(end_r_2900, tmpcur_6737);
            CursorTy pvrtmp_6741 = tmp_struct_107.field0;
            
            return (CursorProd) {pvrtmp_6741};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6742 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6743 = tmpcur_6719 + 8;
            CursorTy tmpcur_6744 = *(CursorTy *) tmpaftercur_6743;
            CursorTy tmpaftercur_6745 = tmpaftercur_6743 + 8;
            CursorTy jump_3992 = tmpaftercur_6743 + 8;
            CursorTy jump_3991 = tmpcur_6719 + 8;
            CursorProd tmp_struct_108 =
                        _traverse_Tags(end_r_2900, tmpaftercur_6745);
            CursorTy pvrtmp_6746 = tmp_struct_108.field0;
            CursorProd tmp_struct_109 =  _traverse_Adt(end_r_2900, tmpcur_6742);
            CursorTy pvrtmp_6747 = tmp_struct_109.field0;
            CursorProd tmp_struct_110 =
                        _traverse_Content(end_r_2900, tmpcur_6744);
            CursorTy pvrtmp_6748 = tmp_struct_110.field0;
            
            return (CursorProd) {pvrtmp_6748};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6749 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6750 = tmpcur_6719 + 8;
            CursorTy tmpcur_6751 = *(CursorTy *) tmpaftercur_6750;
            CursorTy tmpaftercur_6752 = tmpaftercur_6750 + 8;
            CursorTy jump_3998 = tmpaftercur_6750 + 8;
            CursorTy jump_3997 = tmpcur_6719 + 8;
            CursorProd tmp_struct_111 =
                        _traverse_Adt(end_r_2900, tmpaftercur_6752);
            CursorTy pvrtmp_6753 = tmp_struct_111.field0;
            CursorProd tmp_struct_112 =
                        _traverse_Tags(end_r_2900, tmpcur_6749);
            CursorTy pvrtmp_6754 = tmp_struct_112.field0;
            CursorProd tmp_struct_113 =
                        _traverse_Content(end_r_2900, tmpcur_6751);
            CursorTy pvrtmp_6755 = tmp_struct_113.field0;
            
            return (CursorProd) {pvrtmp_6755};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6756 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6757 = tmpcur_6719 + 8;
            CursorTy tmpcur_6758 = *(CursorTy *) tmpaftercur_6757;
            CursorTy tmpaftercur_6759 = tmpaftercur_6757 + 8;
            CursorTy jump_4004 = tmpaftercur_6757 + 8;
            CursorTy jump_4003 = tmpcur_6719 + 8;
            CursorProd tmp_struct_114 =
                        _traverse_Content(end_r_2900, tmpaftercur_6759);
            CursorTy pvrtmp_6760 = tmp_struct_114.field0;
            CursorProd tmp_struct_115 =
                        _traverse_Tags(end_r_2900, tmpcur_6756);
            CursorTy pvrtmp_6761 = tmp_struct_115.field0;
            CursorProd tmp_struct_116 =  _traverse_Adt(end_r_2900, tmpcur_6758);
            CursorTy pvrtmp_6762 = tmp_struct_116.field0;
            
            return (CursorProd) {pvrtmp_6762};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6763 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6764 = tmpcur_6719 + 8;
            CursorTy tmpcur_6765 = *(CursorTy *) tmpaftercur_6764;
            CursorTy tmpaftercur_6766 = tmpaftercur_6764 + 8;
            CursorTy jump_4010 = tmpaftercur_6764 + 8;
            CursorTy jump_4009 = tmpcur_6719 + 8;
            CursorProd tmp_struct_117 =
                        _traverse_Content(end_r_2900, tmpaftercur_6766);
            CursorTy pvrtmp_6767 = tmp_struct_117.field0;
            CursorProd tmp_struct_118 =  _traverse_Adt(end_r_2900, tmpcur_6763);
            CursorTy pvrtmp_6768 = tmp_struct_118.field0;
            CursorProd tmp_struct_119 =
                        _traverse_Tags(end_r_2900, tmpcur_6765);
            CursorTy pvrtmp_6769 = tmp_struct_119.field0;
            
            return (CursorProd) {pvrtmp_6769};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6770 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6771 = tmpcur_6719 + 8;
            CursorTy jump_4200 = tmpcur_6719 + 8;
            CursorProd tmp_struct_120 =  _traverse_Adt(end_r_2900, tmpcur_6770);
            CursorTy pvrtmp_6772 = tmp_struct_120.field0;
            
            return (CursorProd) {jump_4200};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6773 = *(CursorTy *) tmpcur_6719;
            CursorTy tmpaftercur_6774 = tmpcur_6719 + 8;
            CursorProd tmp_struct_121 =  _traverse_Adt(end_r_2900, tmpcur_6773);
            CursorTy pvrtmp_6775 = tmp_struct_121.field0;
            
            return (CursorProd) {pvrtmp_6775};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6718");
            exit(1);
        }
    }
}
CursorProd _print_Adt(CursorTy end_r_2902, CursorTy arg_820_1431_1740)
{
    TagTyPacked tmpval_6777 = *(TagTyPacked *) arg_820_1431_1740;
    CursorTy tmpcur_6778 = arg_820_1431_1740 + 1;
    
    
  switch_6835:
    ;
    switch (tmpval_6777) {
        
      case 0:
        {
            CursorTy jump_4015 = arg_820_1431_1740 + 1;
            unsigned char wildcard_821_1432_1741 = print_symbol(5868);
            unsigned char wildcard_822_1433_1742 = print_symbol(5862);
            
            return (CursorProd) {jump_4015};
            break;
        }
        
      case 9:
        {
            CursorTy tmpcur_6779 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6780 = tmpcur_6778 + 8;
            CursorTy jump_4017 = tmpcur_6778 + 8;
            unsigned char wildcard_827_1436_1745 = print_symbol(5874);
            CursorProd tmp_struct_122 =
                        _print_Content(end_r_2902, tmpaftercur_6780);
            CursorTy pvrtmp_6781 = tmp_struct_122.field0;
            CursorProd tmp_struct_123 =  _print_Adt(end_r_2902, tmpcur_6779);
            CursorTy pvrtmp_6782 = tmp_struct_123.field0;
            unsigned char wildcard_828_1439_1748 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6782};
            break;
        }
        
      case 11:
        {
            CursorTy tmpcur_6783 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6784 = tmpcur_6778 + 8;
            CursorTy jump_4021 = tmpcur_6778 + 8;
            unsigned char wildcard_833_1442_1751 = print_symbol(5877);
            CursorProd tmp_struct_124 =
                        _print_Adt(end_r_2902, tmpaftercur_6784);
            CursorTy pvrtmp_6785 = tmp_struct_124.field0;
            CursorProd tmp_struct_125 =
                        _print_Content(end_r_2902, tmpcur_6783);
            CursorTy pvrtmp_6786 = tmp_struct_125.field0;
            unsigned char wildcard_834_1445_1754 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6786};
            break;
        }
        
      case 13:
        {
            CursorTy tmpcur_6787 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6788 = tmpcur_6778 + 8;
            CursorTy tmpcur_6789 = *(CursorTy *) tmpaftercur_6788;
            CursorTy tmpaftercur_6790 = tmpaftercur_6788 + 8;
            CursorTy jump_4026 = tmpaftercur_6788 + 8;
            CursorTy jump_4025 = tmpcur_6778 + 8;
            unsigned char wildcard_841_1449_1758 = print_symbol(5865);
            CursorProd tmp_struct_126 =
                        _print_Tags(end_r_2902, tmpaftercur_6790);
            CursorTy pvrtmp_6791 = tmp_struct_126.field0;
            CursorProd tmp_struct_127 =
                        _print_Content(end_r_2902, tmpcur_6787);
            CursorTy pvrtmp_6792 = tmp_struct_127.field0;
            CursorProd tmp_struct_128 =  _print_Adt(end_r_2902, tmpcur_6789);
            CursorTy pvrtmp_6793 = tmp_struct_128.field0;
            unsigned char wildcard_842_1453_1762 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6793};
            break;
        }
        
      case 15:
        {
            CursorTy tmpcur_6794 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6795 = tmpcur_6778 + 8;
            CursorTy tmpcur_6796 = *(CursorTy *) tmpaftercur_6795;
            CursorTy tmpaftercur_6797 = tmpaftercur_6795 + 8;
            CursorTy jump_4032 = tmpaftercur_6795 + 8;
            CursorTy jump_4031 = tmpcur_6778 + 8;
            unsigned char wildcard_849_1457_1766 = print_symbol(5876);
            CursorProd tmp_struct_129 =
                        _print_Adt(end_r_2902, tmpaftercur_6797);
            CursorTy pvrtmp_6798 = tmp_struct_129.field0;
            CursorProd tmp_struct_130 =
                        _print_Content(end_r_2902, tmpcur_6794);
            CursorTy pvrtmp_6799 = tmp_struct_130.field0;
            CursorProd tmp_struct_131 =  _print_Tags(end_r_2902, tmpcur_6796);
            CursorTy pvrtmp_6800 = tmp_struct_131.field0;
            unsigned char wildcard_850_1461_1770 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6800};
            break;
        }
        
      case 17:
        {
            CursorTy tmpcur_6801 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6802 = tmpcur_6778 + 8;
            CursorTy tmpcur_6803 = *(CursorTy *) tmpaftercur_6802;
            CursorTy tmpaftercur_6804 = tmpaftercur_6802 + 8;
            CursorTy jump_4038 = tmpaftercur_6802 + 8;
            CursorTy jump_4037 = tmpcur_6778 + 8;
            unsigned char wildcard_857_1465_1774 = print_symbol(5866);
            CursorProd tmp_struct_132 =
                        _print_Tags(end_r_2902, tmpaftercur_6804);
            CursorTy pvrtmp_6805 = tmp_struct_132.field0;
            CursorProd tmp_struct_133 =  _print_Adt(end_r_2902, tmpcur_6801);
            CursorTy pvrtmp_6806 = tmp_struct_133.field0;
            CursorProd tmp_struct_134 =
                        _print_Content(end_r_2902, tmpcur_6803);
            CursorTy pvrtmp_6807 = tmp_struct_134.field0;
            unsigned char wildcard_858_1469_1778 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6807};
            break;
        }
        
      case 19:
        {
            CursorTy tmpcur_6808 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6809 = tmpcur_6778 + 8;
            CursorTy tmpcur_6810 = *(CursorTy *) tmpaftercur_6809;
            CursorTy tmpaftercur_6811 = tmpaftercur_6809 + 8;
            CursorTy jump_4044 = tmpaftercur_6809 + 8;
            CursorTy jump_4043 = tmpcur_6778 + 8;
            unsigned char wildcard_865_1473_1782 = print_symbol(5875);
            CursorProd tmp_struct_135 =
                        _print_Adt(end_r_2902, tmpaftercur_6811);
            CursorTy pvrtmp_6812 = tmp_struct_135.field0;
            CursorProd tmp_struct_136 =  _print_Tags(end_r_2902, tmpcur_6808);
            CursorTy pvrtmp_6813 = tmp_struct_136.field0;
            CursorProd tmp_struct_137 =
                        _print_Content(end_r_2902, tmpcur_6810);
            CursorTy pvrtmp_6814 = tmp_struct_137.field0;
            unsigned char wildcard_866_1477_1786 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6814};
            break;
        }
        
      case 21:
        {
            CursorTy tmpcur_6815 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6816 = tmpcur_6778 + 8;
            CursorTy tmpcur_6817 = *(CursorTy *) tmpaftercur_6816;
            CursorTy tmpaftercur_6818 = tmpaftercur_6816 + 8;
            CursorTy jump_4050 = tmpaftercur_6816 + 8;
            CursorTy jump_4049 = tmpcur_6778 + 8;
            unsigned char wildcard_873_1481_1790 = print_symbol(5872);
            CursorProd tmp_struct_138 =
                        _print_Content(end_r_2902, tmpaftercur_6818);
            CursorTy pvrtmp_6819 = tmp_struct_138.field0;
            CursorProd tmp_struct_139 =  _print_Tags(end_r_2902, tmpcur_6815);
            CursorTy pvrtmp_6820 = tmp_struct_139.field0;
            CursorProd tmp_struct_140 =  _print_Adt(end_r_2902, tmpcur_6817);
            CursorTy pvrtmp_6821 = tmp_struct_140.field0;
            unsigned char wildcard_874_1485_1794 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6821};
            break;
        }
        
      case 23:
        {
            CursorTy tmpcur_6822 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6823 = tmpcur_6778 + 8;
            CursorTy tmpcur_6824 = *(CursorTy *) tmpaftercur_6823;
            CursorTy tmpaftercur_6825 = tmpaftercur_6823 + 8;
            CursorTy jump_4056 = tmpaftercur_6823 + 8;
            CursorTy jump_4055 = tmpcur_6778 + 8;
            unsigned char wildcard_881_1489_1798 = print_symbol(5873);
            CursorProd tmp_struct_141 =
                        _print_Content(end_r_2902, tmpaftercur_6825);
            CursorTy pvrtmp_6826 = tmp_struct_141.field0;
            CursorProd tmp_struct_142 =  _print_Adt(end_r_2902, tmpcur_6822);
            CursorTy pvrtmp_6827 = tmp_struct_142.field0;
            CursorProd tmp_struct_143 =  _print_Tags(end_r_2902, tmpcur_6824);
            CursorTy pvrtmp_6828 = tmp_struct_143.field0;
            unsigned char wildcard_882_1493_1802 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6828};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6829 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6830 = tmpcur_6778 + 8;
            CursorTy jump_4206 = tmpcur_6778 + 8;
            unsigned char wildcard_4209 = print_symbol(5879);
            CursorProd tmp_struct_144 =  _print_Adt(end_r_2902, tmpcur_6829);
            CursorTy pvrtmp_6831 = tmp_struct_144.field0;
            
            return (CursorProd) {jump_4206};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6832 = *(CursorTy *) tmpcur_6778;
            CursorTy tmpaftercur_6833 = tmpcur_6778 + 8;
            unsigned char wildcard_4209 = print_symbol(5878);
            CursorProd tmp_struct_145 =  _print_Adt(end_r_2902, tmpcur_6832);
            CursorTy pvrtmp_6834 = tmp_struct_145.field0;
            
            return (CursorProd) {pvrtmp_6834};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6777");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Tags(CursorTy end_r_2905,
                                        CursorTy end_r_2906, CursorTy loc_2904,
                                        CursorTy arg_883_1494_1803)
{
    if (loc_2904 + 32 > end_r_2906) {
        ChunkTy new_chunk_149 = alloc_chunk(end_r_2906);
        CursorTy chunk_start_150 = new_chunk_149.chunk_start;
        CursorTy chunk_end_151 = new_chunk_149.chunk_end;
        
        end_r_2906 = chunk_end_151;
        *(TagTyPacked *) loc_2904 = 255;
        
        CursorTy redir = loc_2904 + 1;
        
        *(CursorTy *) redir = chunk_start_150;
        loc_2904 = chunk_start_150;
    }
    
    CursorTy loc_3558 = loc_2904 + 1;
    CursorTy loc_3559 = loc_3558 + 8;
    TagTyPacked tmpval_6836 = *(TagTyPacked *) arg_883_1494_1803;
    CursorTy tmpcur_6837 = arg_883_1494_1803 + 1;
    
    
  switch_6880:
    ;
    switch (tmpval_6836) {
        
      case 0:
        {
            CursorTy jump_4061 = arg_883_1494_1803 + 1;
            
            *(TagTyPacked *) loc_2904 = 0;
            
            CursorTy writetag_4795 = loc_2904 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2906, jump_4061,
                                                   loc_2904, writetag_4795};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6842 = *(IntTy *) tmpcur_6837;
            CursorTy tmpcur_6843 = tmpcur_6837 + sizeof(IntTy);
            CursorTy jump_4063 = tmpcur_6837 + 8;
            CursorCursorCursorCursorProd tmp_struct_146 =
                                          _copy_Tags(end_r_2905, end_r_2906, loc_3559, tmpcur_6843);
            CursorTy pvrtmp_6844 = tmp_struct_146.field0;
            CursorTy pvrtmp_6845 = tmp_struct_146.field1;
            CursorTy pvrtmp_6846 = tmp_struct_146.field2;
            CursorTy pvrtmp_6847 = tmp_struct_146.field3;
            
            *(TagTyPacked *) loc_2904 = 1;
            
            CursorTy writetag_4800 = loc_2904 + 1;
            
            *(IntTy *) writetag_4800 = tmpval_6842;
            
            CursorTy writecur_4801 = writetag_4800 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6844, pvrtmp_6845,
                                                   loc_2904, pvrtmp_6847};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6856 = *(CursorTy *) tmpcur_6837;
            CursorTy tmpaftercur_6857 = tmpcur_6837 + 8;
            CursorTy jump_4212 = tmpcur_6837 + 8;
            CursorCursorCursorCursorProd tmp_struct_147 =
                                          _copy_Tags(end_r_2905, end_r_2906, loc_2904, tmpcur_6856);
            CursorTy pvrtmp_6858 = tmp_struct_147.field0;
            CursorTy pvrtmp_6859 = tmp_struct_147.field1;
            CursorTy pvrtmp_6860 = tmp_struct_147.field2;
            CursorTy pvrtmp_6861 = tmp_struct_147.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6858, jump_4212,
                                                   pvrtmp_6860, pvrtmp_6861};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6868 = *(CursorTy *) tmpcur_6837;
            CursorTy tmpaftercur_6869 = tmpcur_6837 + 8;
            CursorCursorCursorCursorProd tmp_struct_148 =
                                          _copy_Tags(end_r_2905, end_r_2906, loc_2904, tmpcur_6868);
            CursorTy pvrtmp_6870 = tmp_struct_148.field0;
            CursorTy pvrtmp_6871 = tmp_struct_148.field1;
            CursorTy pvrtmp_6872 = tmp_struct_148.field2;
            CursorTy pvrtmp_6873 = tmp_struct_148.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6870, pvrtmp_6871,
                                                   pvrtmp_6872, pvrtmp_6873};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6836");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_without_ptrs_Tags(CursorTy end_r_2909,
                                                     CursorTy end_r_2910,
                                                     CursorTy loc_2908,
                                                     CursorTy arg_888_1499_1808)
{
    CursorTy loc_3571 = loc_2908 + 1;
    CursorTy loc_3572 = loc_3571 + 8;
    TagTyPacked tmpval_6881 = *(TagTyPacked *) arg_888_1499_1808;
    CursorTy tmpcur_6882 = arg_888_1499_1808 + 1;
    
    
  switch_6925:
    ;
    switch (tmpval_6881) {
        
      case 0:
        {
            CursorTy jump_4066 = arg_888_1499_1808 + 1;
            
            *(TagTyPacked *) loc_2908 = 0;
            
            CursorTy writetag_4811 = loc_2908 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2910, jump_4066,
                                                   loc_2908, writetag_4811};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6887 = *(IntTy *) tmpcur_6882;
            CursorTy tmpcur_6888 = tmpcur_6882 + sizeof(IntTy);
            CursorTy jump_4068 = tmpcur_6882 + 8;
            CursorCursorCursorCursorProd tmp_struct_152 =
                                          _copy_without_ptrs_Tags(end_r_2909, end_r_2910, loc_3572, tmpcur_6888);
            CursorTy pvrtmp_6889 = tmp_struct_152.field0;
            CursorTy pvrtmp_6890 = tmp_struct_152.field1;
            CursorTy pvrtmp_6891 = tmp_struct_152.field2;
            CursorTy pvrtmp_6892 = tmp_struct_152.field3;
            
            *(TagTyPacked *) loc_2908 = 1;
            
            CursorTy writetag_4816 = loc_2908 + 1;
            
            *(IntTy *) writetag_4816 = tmpval_6887;
            
            CursorTy writecur_4817 = writetag_4816 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6889, pvrtmp_6890,
                                                   loc_2908, pvrtmp_6892};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6901 = *(CursorTy *) tmpcur_6882;
            CursorTy tmpaftercur_6902 = tmpcur_6882 + 8;
            CursorTy jump_4218 = tmpcur_6882 + 8;
            CursorCursorCursorCursorProd tmp_struct_153 =
                                          _copy_without_ptrs_Tags(end_r_2909, end_r_2910, loc_2908, tmpcur_6901);
            CursorTy pvrtmp_6903 = tmp_struct_153.field0;
            CursorTy pvrtmp_6904 = tmp_struct_153.field1;
            CursorTy pvrtmp_6905 = tmp_struct_153.field2;
            CursorTy pvrtmp_6906 = tmp_struct_153.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6903, jump_4218,
                                                   pvrtmp_6905, pvrtmp_6906};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6913 = *(CursorTy *) tmpcur_6882;
            CursorTy tmpaftercur_6914 = tmpcur_6882 + 8;
            CursorCursorCursorCursorProd tmp_struct_154 =
                                          _copy_without_ptrs_Tags(end_r_2909, end_r_2910, loc_2908, tmpcur_6913);
            CursorTy pvrtmp_6915 = tmp_struct_154.field0;
            CursorTy pvrtmp_6916 = tmp_struct_154.field1;
            CursorTy pvrtmp_6917 = tmp_struct_154.field2;
            CursorTy pvrtmp_6918 = tmp_struct_154.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6915, pvrtmp_6916,
                                                   pvrtmp_6917, pvrtmp_6918};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6881");
            exit(1);
        }
    }
}
CursorProd _traverse_Tags(CursorTy end_r_2912, CursorTy arg_893_1504_1813)
{
    TagTyPacked tmpval_6926 = *(TagTyPacked *) arg_893_1504_1813;
    CursorTy tmpcur_6927 = arg_893_1504_1813 + 1;
    
    
  switch_6937:
    ;
    switch (tmpval_6926) {
        
      case 0:
        {
            CursorTy jump_4071 = arg_893_1504_1813 + 1;
            
            return (CursorProd) {jump_4071};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6928 = *(IntTy *) tmpcur_6927;
            CursorTy tmpcur_6929 = tmpcur_6927 + sizeof(IntTy);
            CursorTy jump_4073 = tmpcur_6927 + 8;
            CursorProd tmp_struct_155 =
                        _traverse_Tags(end_r_2912, tmpcur_6929);
            CursorTy pvrtmp_6930 = tmp_struct_155.field0;
            
            return (CursorProd) {pvrtmp_6930};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6931 = *(CursorTy *) tmpcur_6927;
            CursorTy tmpaftercur_6932 = tmpcur_6927 + 8;
            CursorTy jump_4224 = tmpcur_6927 + 8;
            CursorProd tmp_struct_156 =
                        _traverse_Tags(end_r_2912, tmpcur_6931);
            CursorTy pvrtmp_6933 = tmp_struct_156.field0;
            
            return (CursorProd) {jump_4224};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6934 = *(CursorTy *) tmpcur_6927;
            CursorTy tmpaftercur_6935 = tmpcur_6927 + 8;
            CursorProd tmp_struct_157 =
                        _traverse_Tags(end_r_2912, tmpcur_6934);
            CursorTy pvrtmp_6936 = tmp_struct_157.field0;
            
            return (CursorProd) {pvrtmp_6936};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6926");
            exit(1);
        }
    }
}
CursorProd _print_Tags(CursorTy end_r_2914, CursorTy arg_898_1508_1817)
{
    TagTyPacked tmpval_6938 = *(TagTyPacked *) arg_898_1508_1817;
    CursorTy tmpcur_6939 = arg_898_1508_1817 + 1;
    
    
  switch_6949:
    ;
    switch (tmpval_6938) {
        
      case 0:
        {
            CursorTy jump_4076 = arg_898_1508_1817 + 1;
            unsigned char wildcard_899_1509_1818 = print_symbol(5867);
            unsigned char wildcard_900_1510_1819 = print_symbol(5862);
            
            return (CursorProd) {jump_4076};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6940 = *(IntTy *) tmpcur_6939;
            CursorTy tmpcur_6941 = tmpcur_6939 + sizeof(IntTy);
            CursorTy jump_4078 = tmpcur_6939 + 8;
            unsigned char wildcard_905_1513_1822 = print_symbol(5864);
            unsigned char y_903_1514_1823 = printf("%lld", tmpval_6940);
            CursorProd tmp_struct_158 =  _print_Tags(end_r_2914, tmpcur_6941);
            CursorTy pvrtmp_6942 = tmp_struct_158.field0;
            unsigned char wildcard_906_1516_1825 = print_symbol(5862);
            
            return (CursorProd) {pvrtmp_6942};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6943 = *(CursorTy *) tmpcur_6939;
            CursorTy tmpaftercur_6944 = tmpcur_6939 + 8;
            CursorTy jump_4230 = tmpcur_6939 + 8;
            unsigned char wildcard_4233 = print_symbol(5879);
            CursorProd tmp_struct_159 =  _print_Tags(end_r_2914, tmpcur_6943);
            CursorTy pvrtmp_6945 = tmp_struct_159.field0;
            
            return (CursorProd) {jump_4230};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6946 = *(CursorTy *) tmpcur_6939;
            CursorTy tmpaftercur_6947 = tmpcur_6939 + 8;
            unsigned char wildcard_4233 = print_symbol(5878);
            CursorProd tmp_struct_160 =  _print_Tags(end_r_2914, tmpcur_6946);
            CursorTy pvrtmp_6948 = tmp_struct_160.field0;
            
            return (CursorProd) {pvrtmp_6948};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6938");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_String(CursorTy end_r_2917,
                                                              CursorTy end_r_2918,
                                                              CursorTy loc_2916,
                                                              CursorTy arg_2657)
{
    if (loc_2916 + 32 > end_r_2918) {
        ChunkTy new_chunk_164 = alloc_chunk(end_r_2918);
        CursorTy chunk_start_165 = new_chunk_164.chunk_start;
        CursorTy chunk_end_166 = new_chunk_164.chunk_end;
        
        end_r_2918 = chunk_end_166;
        *(TagTyPacked *) loc_2916 = 255;
        
        CursorTy redir = loc_2916 + 1;
        
        *(CursorTy *) redir = chunk_start_165;
        loc_2916 = chunk_start_165;
    }
    
    CursorTy loc_3596 = loc_2916 + 1;
    CursorTy loc_3597 = loc_3596 + 8;
    TagTyPacked tmpval_6950 = *(TagTyPacked *) arg_2657;
    CursorTy tmpcur_6951 = arg_2657 + 1;
    
    
  switch_6994:
    ;
    switch (tmpval_6950) {
        
      case 0:
        {
            CursorTy jump_4081 = arg_2657 + 1;
            
            *(TagTyPacked *) loc_2916 = 0;
            
            CursorTy writetag_4847 = loc_2916 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2918, jump_4081,
                                                   loc_2916, writetag_4847};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_6956 = *(IntTy *) tmpcur_6951;
            CursorTy tmpcur_6957 = tmpcur_6951 + sizeof(IntTy);
            CursorTy jump_4083 = tmpcur_6951 + 8;
            CursorCursorCursorCursorProd tmp_struct_161 =
                                          _add_size_and_rel_offsets_String(end_r_2917, end_r_2918, loc_3597, tmpcur_6957);
            CursorTy pvrtmp_6958 = tmp_struct_161.field0;
            CursorTy pvrtmp_6959 = tmp_struct_161.field1;
            CursorTy pvrtmp_6960 = tmp_struct_161.field2;
            CursorTy pvrtmp_6961 = tmp_struct_161.field3;
            
            *(TagTyPacked *) loc_2916 = 1;
            
            CursorTy writetag_4852 = loc_2916 + 1;
            
            *(IntTy *) writetag_4852 = tmpval_6956;
            
            CursorTy writecur_4853 = writetag_4852 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6958, pvrtmp_6959,
                                                   loc_2916, pvrtmp_6961};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_6970 = *(CursorTy *) tmpcur_6951;
            CursorTy tmpaftercur_6971 = tmpcur_6951 + 8;
            CursorTy jump_4236 = tmpcur_6951 + 8;
            CursorCursorCursorCursorProd tmp_struct_162 =
                                          _add_size_and_rel_offsets_String(end_r_2917, end_r_2918, loc_2916, tmpcur_6970);
            CursorTy pvrtmp_6972 = tmp_struct_162.field0;
            CursorTy pvrtmp_6973 = tmp_struct_162.field1;
            CursorTy pvrtmp_6974 = tmp_struct_162.field2;
            CursorTy pvrtmp_6975 = tmp_struct_162.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6972, jump_4236,
                                                   pvrtmp_6974, pvrtmp_6975};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_6982 = *(CursorTy *) tmpcur_6951;
            CursorTy tmpaftercur_6983 = tmpcur_6951 + 8;
            CursorCursorCursorCursorProd tmp_struct_163 =
                                          _add_size_and_rel_offsets_String(end_r_2917, end_r_2918, loc_2916, tmpcur_6982);
            CursorTy pvrtmp_6984 = tmp_struct_163.field0;
            CursorTy pvrtmp_6985 = tmp_struct_163.field1;
            CursorTy pvrtmp_6986 = tmp_struct_163.field2;
            CursorTy pvrtmp_6987 = tmp_struct_163.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6984, pvrtmp_6985,
                                                   pvrtmp_6986, pvrtmp_6987};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6950");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Content(CursorTy end_r_2921,
                                                               CursorTy end_r_2922,
                                                               CursorTy loc_2920,
                                                               CursorTy arg_2662)
{
    if (loc_2920 + 32 > end_r_2922) {
        ChunkTy new_chunk_171 = alloc_chunk(end_r_2922);
        CursorTy chunk_start_172 = new_chunk_171.chunk_start;
        CursorTy chunk_end_173 = new_chunk_171.chunk_end;
        
        end_r_2922 = chunk_end_173;
        *(TagTyPacked *) loc_2920 = 255;
        
        CursorTy redir = loc_2920 + 1;
        
        *(CursorTy *) redir = chunk_start_172;
        loc_2920 = chunk_start_172;
    }
    
    TagTyPacked tmpval_6995 = *(TagTyPacked *) arg_2662;
    CursorTy tmpcur_6996 = arg_2662 + 1;
    
    
  switch_7045:
    ;
    switch (tmpval_6995) {
        
      case 0:
        {
            CursorTy loc_3607 = loc_2920 + 1;
            CursorCursorCursorCursorProd tmp_struct_167 =
                                          _add_size_and_rel_offsets_String(end_r_2921, end_r_2922, loc_3607, tmpcur_6996);
            CursorTy pvrtmp_6997 = tmp_struct_167.field0;
            CursorTy pvrtmp_6998 = tmp_struct_167.field1;
            CursorTy pvrtmp_6999 = tmp_struct_167.field2;
            CursorTy pvrtmp_7000 = tmp_struct_167.field3;
            
            *(TagTyPacked *) loc_2920 = 0;
            
            CursorTy writetag_4864 = loc_2920 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_6997, pvrtmp_6998,
                                                   loc_2920, pvrtmp_7000};
            break;
        }
        
      case 1:
        {
            CursorTy loc_3613 = loc_2920 + 1;
            CursorCursorCursorCursorProd tmp_struct_168 =
                                          _add_size_and_rel_offsets_String(end_r_2921, end_r_2922, loc_3613, tmpcur_6996);
            CursorTy pvrtmp_7009 = tmp_struct_168.field0;
            CursorTy pvrtmp_7010 = tmp_struct_168.field1;
            CursorTy pvrtmp_7011 = tmp_struct_168.field2;
            CursorTy pvrtmp_7012 = tmp_struct_168.field3;
            
            *(TagTyPacked *) loc_2920 = 1;
            
            CursorTy writetag_4869 = loc_2920 + 1;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7009, pvrtmp_7010,
                                                   loc_2920, pvrtmp_7012};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7021 = *(CursorTy *) tmpcur_6996;
            CursorTy tmpaftercur_7022 = tmpcur_6996 + 8;
            CursorTy jump_4242 = tmpcur_6996 + 8;
            CursorCursorCursorCursorProd tmp_struct_169 =
                                          _add_size_and_rel_offsets_Content(end_r_2921, end_r_2922, loc_2920, tmpcur_7021);
            CursorTy pvrtmp_7023 = tmp_struct_169.field0;
            CursorTy pvrtmp_7024 = tmp_struct_169.field1;
            CursorTy pvrtmp_7025 = tmp_struct_169.field2;
            CursorTy pvrtmp_7026 = tmp_struct_169.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7023, jump_4242,
                                                   pvrtmp_7025, pvrtmp_7026};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7033 = *(CursorTy *) tmpcur_6996;
            CursorTy tmpaftercur_7034 = tmpcur_6996 + 8;
            CursorCursorCursorCursorProd tmp_struct_170 =
                                          _add_size_and_rel_offsets_Content(end_r_2921, end_r_2922, loc_2920, tmpcur_7033);
            CursorTy pvrtmp_7035 = tmp_struct_170.field0;
            CursorTy pvrtmp_7036 = tmp_struct_170.field1;
            CursorTy pvrtmp_7037 = tmp_struct_170.field2;
            CursorTy pvrtmp_7038 = tmp_struct_170.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7035, pvrtmp_7036,
                                                   pvrtmp_7037, pvrtmp_7038};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_6995");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Adt(CursorTy end_r_2925,
                                                           CursorTy end_r_2926,
                                                           CursorTy loc_2924,
                                                           CursorTy arg_2667)
{
    if (loc_2924 + 32 > end_r_2926) {
        ChunkTy new_chunk_198 = alloc_chunk(end_r_2926);
        CursorTy chunk_start_199 = new_chunk_198.chunk_start;
        CursorTy chunk_end_200 = new_chunk_198.chunk_end;
        
        end_r_2926 = chunk_end_200;
        *(TagTyPacked *) loc_2924 = 255;
        
        CursorTy redir = loc_2924 + 1;
        
        *(CursorTy *) redir = chunk_start_199;
        loc_2924 = chunk_start_199;
    }
    
    CursorTy loc_3626 = loc_2924 + 1;
    CursorTy loc_3627 = loc_3626 + 8;
    CursorTy loc_3628 = loc_3627 + 8;
    CursorTy loc_3644 = loc_2924 + 1;
    CursorTy loc_3645 = loc_3644 + 8;
    CursorTy loc_3646 = loc_3645 + 8;
    CursorTy loc_3666 = loc_2924 + 1;
    CursorTy loc_3667 = loc_3666 + 8;
    CursorTy loc_3668 = loc_3667 + 8;
    CursorTy loc_3669 = loc_3668 + 8;
    CursorTy loc_3693 = loc_2924 + 1;
    CursorTy loc_3694 = loc_3693 + 8;
    CursorTy loc_3695 = loc_3694 + 8;
    CursorTy loc_3696 = loc_3695 + 8;
    CursorTy loc_3720 = loc_2924 + 1;
    CursorTy loc_3721 = loc_3720 + 8;
    CursorTy loc_3722 = loc_3721 + 8;
    CursorTy loc_3723 = loc_3722 + 8;
    CursorTy loc_3747 = loc_2924 + 1;
    CursorTy loc_3748 = loc_3747 + 8;
    CursorTy loc_3749 = loc_3748 + 8;
    CursorTy loc_3750 = loc_3749 + 8;
    CursorTy loc_3774 = loc_2924 + 1;
    CursorTy loc_3775 = loc_3774 + 8;
    CursorTy loc_3776 = loc_3775 + 8;
    CursorTy loc_3777 = loc_3776 + 8;
    CursorTy loc_3801 = loc_2924 + 1;
    CursorTy loc_3802 = loc_3801 + 8;
    CursorTy loc_3803 = loc_3802 + 8;
    CursorTy loc_3804 = loc_3803 + 8;
    TagTyPacked tmpval_7046 = *(TagTyPacked *) arg_2667;
    CursorTy tmpcur_7047 = arg_2667 + 1;
    
    
  switch_7284:
    ;
    switch (tmpval_7046) {
        
      case 0:
        {
            CursorTy jump_4090 = arg_2667 + 1;
            
            *(TagTyPacked *) loc_2924 = 0;
            
            CursorTy writetag_4879 = loc_2924 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2926, jump_4090,
                                                   loc_2924, writetag_4879};
            break;
        }
        
      case 1:
        {
            CursorCursorCursorCursorProd tmp_struct_174 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, end_r_2926, loc_3628, tmpcur_7047);
            CursorTy pvrtmp_7052 = tmp_struct_174.field0;
            CursorTy pvrtmp_7053 = tmp_struct_174.field1;
            CursorTy pvrtmp_7054 = tmp_struct_174.field2;
            CursorTy pvrtmp_7055 = tmp_struct_174.field3;
            CursorCursorCursorCursorProd tmp_struct_175 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, pvrtmp_7052, pvrtmp_7055, pvrtmp_7053);
            CursorTy pvrtmp_7060 = tmp_struct_175.field0;
            CursorTy pvrtmp_7061 = tmp_struct_175.field1;
            CursorTy pvrtmp_7062 = tmp_struct_175.field2;
            CursorTy pvrtmp_7063 = tmp_struct_175.field3;
            IntTy sizeof_y_2670__2672 = pvrtmp_7055 - pvrtmp_7054;
            IntTy sizeof_y_2671__2673 = pvrtmp_7063 - pvrtmp_7062;
            IntTy fltPrm_2761 = sizeof_y_2670__2672 + 0;
            IntTy offset__2674 = 0 + fltPrm_2761;
            IntTy fltPrm_2762 = sizeof_y_2670__2672 + sizeof_y_2671__2673;
            IntTy size_dcon_2675 = 9 + fltPrm_2762;
            
            *(TagTyPacked *) loc_2924 = 160;
            
            CursorTy writetag_4884 = loc_2924 + 1;
            
            *(IntTy *) writetag_4884 = size_dcon_2675;
            
            CursorTy writecur_4885 = writetag_4884 + sizeof(IntTy);
            
            *(IntTy *) writecur_4885 = offset__2674;
            
            CursorTy writecur_4886 = writecur_4885 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7060, pvrtmp_7061,
                                                   loc_2924, pvrtmp_7063};
            break;
        }
        
      case 2:
        {
            CursorCursorCursorCursorProd tmp_struct_176 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, end_r_2926, loc_3646, tmpcur_7047);
            CursorTy pvrtmp_7072 = tmp_struct_176.field0;
            CursorTy pvrtmp_7073 = tmp_struct_176.field1;
            CursorTy pvrtmp_7074 = tmp_struct_176.field2;
            CursorTy pvrtmp_7075 = tmp_struct_176.field3;
            CursorCursorCursorCursorProd tmp_struct_177 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, pvrtmp_7072, pvrtmp_7075, pvrtmp_7073);
            CursorTy pvrtmp_7080 = tmp_struct_177.field0;
            CursorTy pvrtmp_7081 = tmp_struct_177.field1;
            CursorTy pvrtmp_7082 = tmp_struct_177.field2;
            CursorTy pvrtmp_7083 = tmp_struct_177.field3;
            IntTy sizeof_y_2678__2680 = pvrtmp_7075 - pvrtmp_7074;
            IntTy sizeof_y_2679__2681 = pvrtmp_7083 - pvrtmp_7082;
            IntTy fltPrm_2763 = sizeof_y_2678__2680 + 0;
            IntTy offset__2682 = 0 + fltPrm_2763;
            IntTy fltPrm_2764 = sizeof_y_2678__2680 + sizeof_y_2679__2681;
            IntTy size_dcon_2683 = 9 + fltPrm_2764;
            
            *(TagTyPacked *) loc_2924 = 162;
            
            CursorTy writetag_4893 = loc_2924 + 1;
            
            *(IntTy *) writetag_4893 = size_dcon_2683;
            
            CursorTy writecur_4894 = writetag_4893 + sizeof(IntTy);
            
            *(IntTy *) writecur_4894 = offset__2682;
            
            CursorTy writecur_4895 = writecur_4894 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7080, pvrtmp_7081,
                                                   loc_2924, pvrtmp_7083};
            break;
        }
        
      case 3:
        {
            CursorCursorCursorCursorProd tmp_struct_178 =
                                          _add_size_and_rel_offsets_Tags(end_r_2925, end_r_2926, loc_3669, tmpcur_7047);
            CursorTy pvrtmp_7092 = tmp_struct_178.field0;
            CursorTy pvrtmp_7093 = tmp_struct_178.field1;
            CursorTy pvrtmp_7094 = tmp_struct_178.field2;
            CursorTy pvrtmp_7095 = tmp_struct_178.field3;
            CursorCursorCursorCursorProd tmp_struct_179 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, pvrtmp_7092, pvrtmp_7095, pvrtmp_7093);
            CursorTy pvrtmp_7100 = tmp_struct_179.field0;
            CursorTy pvrtmp_7101 = tmp_struct_179.field1;
            CursorTy pvrtmp_7102 = tmp_struct_179.field2;
            CursorTy pvrtmp_7103 = tmp_struct_179.field3;
            CursorCursorCursorCursorProd tmp_struct_180 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, pvrtmp_7100, pvrtmp_7103, pvrtmp_7101);
            CursorTy pvrtmp_7108 = tmp_struct_180.field0;
            CursorTy pvrtmp_7109 = tmp_struct_180.field1;
            CursorTy pvrtmp_7110 = tmp_struct_180.field2;
            CursorTy pvrtmp_7111 = tmp_struct_180.field3;
            IntTy sizeof_y_2687__2690 = pvrtmp_7095 - pvrtmp_7094;
            IntTy sizeof_y_2688__2691 = pvrtmp_7103 - pvrtmp_7102;
            IntTy sizeof_y_2689__2692 = pvrtmp_7111 - pvrtmp_7110;
            IntTy fltPrm_2765 = sizeof_y_2687__2690 + 0;
            IntTy offset__2693 = 8 + fltPrm_2765;
            IntTy fltPrm_2766 = sizeof_y_2687__2690 + sizeof_y_2688__2691;
            IntTy offset__2694 = 0 + fltPrm_2766;
            IntTy fltPrm_2768 = sizeof_y_2688__2691 + sizeof_y_2689__2692;
            IntTy fltPrm_2767 = sizeof_y_2687__2690 + fltPrm_2768;
            IntTy size_dcon_2695 = 17 + fltPrm_2767;
            
            *(TagTyPacked *) loc_2924 = 164;
            
            CursorTy writetag_4903 = loc_2924 + 1;
            
            *(IntTy *) writetag_4903 = size_dcon_2695;
            
            CursorTy writecur_4904 = writetag_4903 + sizeof(IntTy);
            
            *(IntTy *) writecur_4904 = offset__2693;
            
            CursorTy writecur_4905 = writecur_4904 + sizeof(IntTy);
            
            *(IntTy *) writecur_4905 = offset__2694;
            
            CursorTy writecur_4906 = writecur_4905 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7108, pvrtmp_7109,
                                                   loc_2924, pvrtmp_7111};
            break;
        }
        
      case 4:
        {
            CursorCursorCursorCursorProd tmp_struct_181 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, end_r_2926, loc_3696, tmpcur_7047);
            CursorTy pvrtmp_7120 = tmp_struct_181.field0;
            CursorTy pvrtmp_7121 = tmp_struct_181.field1;
            CursorTy pvrtmp_7122 = tmp_struct_181.field2;
            CursorTy pvrtmp_7123 = tmp_struct_181.field3;
            CursorCursorCursorCursorProd tmp_struct_182 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, pvrtmp_7120, pvrtmp_7123, pvrtmp_7121);
            CursorTy pvrtmp_7128 = tmp_struct_182.field0;
            CursorTy pvrtmp_7129 = tmp_struct_182.field1;
            CursorTy pvrtmp_7130 = tmp_struct_182.field2;
            CursorTy pvrtmp_7131 = tmp_struct_182.field3;
            CursorCursorCursorCursorProd tmp_struct_183 =
                                          _add_size_and_rel_offsets_Tags(end_r_2925, pvrtmp_7128, pvrtmp_7131, pvrtmp_7129);
            CursorTy pvrtmp_7136 = tmp_struct_183.field0;
            CursorTy pvrtmp_7137 = tmp_struct_183.field1;
            CursorTy pvrtmp_7138 = tmp_struct_183.field2;
            CursorTy pvrtmp_7139 = tmp_struct_183.field3;
            IntTy sizeof_y_2699__2702 = pvrtmp_7123 - pvrtmp_7122;
            IntTy sizeof_y_2700__2703 = pvrtmp_7131 - pvrtmp_7130;
            IntTy sizeof_y_2701__2704 = pvrtmp_7139 - pvrtmp_7138;
            IntTy fltPrm_2769 = sizeof_y_2699__2702 + 0;
            IntTy offset__2705 = 8 + fltPrm_2769;
            IntTy fltPrm_2770 = sizeof_y_2699__2702 + sizeof_y_2700__2703;
            IntTy offset__2706 = 0 + fltPrm_2770;
            IntTy fltPrm_2772 = sizeof_y_2700__2703 + sizeof_y_2701__2704;
            IntTy fltPrm_2771 = sizeof_y_2699__2702 + fltPrm_2772;
            IntTy size_dcon_2707 = 17 + fltPrm_2771;
            
            *(TagTyPacked *) loc_2924 = 166;
            
            CursorTy writetag_4915 = loc_2924 + 1;
            
            *(IntTy *) writetag_4915 = size_dcon_2707;
            
            CursorTy writecur_4916 = writetag_4915 + sizeof(IntTy);
            
            *(IntTy *) writecur_4916 = offset__2705;
            
            CursorTy writecur_4917 = writecur_4916 + sizeof(IntTy);
            
            *(IntTy *) writecur_4917 = offset__2706;
            
            CursorTy writecur_4918 = writecur_4917 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7136, pvrtmp_7137,
                                                   loc_2924, pvrtmp_7139};
            break;
        }
        
      case 5:
        {
            CursorCursorCursorCursorProd tmp_struct_184 =
                                          _add_size_and_rel_offsets_Tags(end_r_2925, end_r_2926, loc_3723, tmpcur_7047);
            CursorTy pvrtmp_7148 = tmp_struct_184.field0;
            CursorTy pvrtmp_7149 = tmp_struct_184.field1;
            CursorTy pvrtmp_7150 = tmp_struct_184.field2;
            CursorTy pvrtmp_7151 = tmp_struct_184.field3;
            CursorCursorCursorCursorProd tmp_struct_185 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, pvrtmp_7148, pvrtmp_7151, pvrtmp_7149);
            CursorTy pvrtmp_7156 = tmp_struct_185.field0;
            CursorTy pvrtmp_7157 = tmp_struct_185.field1;
            CursorTy pvrtmp_7158 = tmp_struct_185.field2;
            CursorTy pvrtmp_7159 = tmp_struct_185.field3;
            CursorCursorCursorCursorProd tmp_struct_186 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, pvrtmp_7156, pvrtmp_7159, pvrtmp_7157);
            CursorTy pvrtmp_7164 = tmp_struct_186.field0;
            CursorTy pvrtmp_7165 = tmp_struct_186.field1;
            CursorTy pvrtmp_7166 = tmp_struct_186.field2;
            CursorTy pvrtmp_7167 = tmp_struct_186.field3;
            IntTy sizeof_y_2711__2714 = pvrtmp_7151 - pvrtmp_7150;
            IntTy sizeof_y_2712__2715 = pvrtmp_7159 - pvrtmp_7158;
            IntTy sizeof_y_2713__2716 = pvrtmp_7167 - pvrtmp_7166;
            IntTy fltPrm_2773 = sizeof_y_2711__2714 + 0;
            IntTy offset__2717 = 8 + fltPrm_2773;
            IntTy fltPrm_2774 = sizeof_y_2711__2714 + sizeof_y_2712__2715;
            IntTy offset__2718 = 0 + fltPrm_2774;
            IntTy fltPrm_2776 = sizeof_y_2712__2715 + sizeof_y_2713__2716;
            IntTy fltPrm_2775 = sizeof_y_2711__2714 + fltPrm_2776;
            IntTy size_dcon_2719 = 17 + fltPrm_2775;
            
            *(TagTyPacked *) loc_2924 = 168;
            
            CursorTy writetag_4927 = loc_2924 + 1;
            
            *(IntTy *) writetag_4927 = size_dcon_2719;
            
            CursorTy writecur_4928 = writetag_4927 + sizeof(IntTy);
            
            *(IntTy *) writecur_4928 = offset__2717;
            
            CursorTy writecur_4929 = writecur_4928 + sizeof(IntTy);
            
            *(IntTy *) writecur_4929 = offset__2718;
            
            CursorTy writecur_4930 = writecur_4929 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7164, pvrtmp_7165,
                                                   loc_2924, pvrtmp_7167};
            break;
        }
        
      case 6:
        {
            CursorCursorCursorCursorProd tmp_struct_187 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, end_r_2926, loc_3750, tmpcur_7047);
            CursorTy pvrtmp_7176 = tmp_struct_187.field0;
            CursorTy pvrtmp_7177 = tmp_struct_187.field1;
            CursorTy pvrtmp_7178 = tmp_struct_187.field2;
            CursorTy pvrtmp_7179 = tmp_struct_187.field3;
            CursorCursorCursorCursorProd tmp_struct_188 =
                                          _add_size_and_rel_offsets_Tags(end_r_2925, pvrtmp_7176, pvrtmp_7179, pvrtmp_7177);
            CursorTy pvrtmp_7184 = tmp_struct_188.field0;
            CursorTy pvrtmp_7185 = tmp_struct_188.field1;
            CursorTy pvrtmp_7186 = tmp_struct_188.field2;
            CursorTy pvrtmp_7187 = tmp_struct_188.field3;
            CursorCursorCursorCursorProd tmp_struct_189 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, pvrtmp_7184, pvrtmp_7187, pvrtmp_7185);
            CursorTy pvrtmp_7192 = tmp_struct_189.field0;
            CursorTy pvrtmp_7193 = tmp_struct_189.field1;
            CursorTy pvrtmp_7194 = tmp_struct_189.field2;
            CursorTy pvrtmp_7195 = tmp_struct_189.field3;
            IntTy sizeof_y_2723__2726 = pvrtmp_7179 - pvrtmp_7178;
            IntTy sizeof_y_2724__2727 = pvrtmp_7187 - pvrtmp_7186;
            IntTy sizeof_y_2725__2728 = pvrtmp_7195 - pvrtmp_7194;
            IntTy fltPrm_2777 = sizeof_y_2723__2726 + 0;
            IntTy offset__2729 = 8 + fltPrm_2777;
            IntTy fltPrm_2778 = sizeof_y_2723__2726 + sizeof_y_2724__2727;
            IntTy offset__2730 = 0 + fltPrm_2778;
            IntTy fltPrm_2780 = sizeof_y_2724__2727 + sizeof_y_2725__2728;
            IntTy fltPrm_2779 = sizeof_y_2723__2726 + fltPrm_2780;
            IntTy size_dcon_2731 = 17 + fltPrm_2779;
            
            *(TagTyPacked *) loc_2924 = 170;
            
            CursorTy writetag_4939 = loc_2924 + 1;
            
            *(IntTy *) writetag_4939 = size_dcon_2731;
            
            CursorTy writecur_4940 = writetag_4939 + sizeof(IntTy);
            
            *(IntTy *) writecur_4940 = offset__2729;
            
            CursorTy writecur_4941 = writecur_4940 + sizeof(IntTy);
            
            *(IntTy *) writecur_4941 = offset__2730;
            
            CursorTy writecur_4942 = writecur_4941 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7192, pvrtmp_7193,
                                                   loc_2924, pvrtmp_7195};
            break;
        }
        
      case 7:
        {
            CursorCursorCursorCursorProd tmp_struct_190 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, end_r_2926, loc_3777, tmpcur_7047);
            CursorTy pvrtmp_7204 = tmp_struct_190.field0;
            CursorTy pvrtmp_7205 = tmp_struct_190.field1;
            CursorTy pvrtmp_7206 = tmp_struct_190.field2;
            CursorTy pvrtmp_7207 = tmp_struct_190.field3;
            CursorCursorCursorCursorProd tmp_struct_191 =
                                          _add_size_and_rel_offsets_Tags(end_r_2925, pvrtmp_7204, pvrtmp_7207, pvrtmp_7205);
            CursorTy pvrtmp_7212 = tmp_struct_191.field0;
            CursorTy pvrtmp_7213 = tmp_struct_191.field1;
            CursorTy pvrtmp_7214 = tmp_struct_191.field2;
            CursorTy pvrtmp_7215 = tmp_struct_191.field3;
            CursorCursorCursorCursorProd tmp_struct_192 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, pvrtmp_7212, pvrtmp_7215, pvrtmp_7213);
            CursorTy pvrtmp_7220 = tmp_struct_192.field0;
            CursorTy pvrtmp_7221 = tmp_struct_192.field1;
            CursorTy pvrtmp_7222 = tmp_struct_192.field2;
            CursorTy pvrtmp_7223 = tmp_struct_192.field3;
            IntTy sizeof_y_2735__2738 = pvrtmp_7207 - pvrtmp_7206;
            IntTy sizeof_y_2736__2739 = pvrtmp_7215 - pvrtmp_7214;
            IntTy sizeof_y_2737__2740 = pvrtmp_7223 - pvrtmp_7222;
            IntTy fltPrm_2781 = sizeof_y_2735__2738 + 0;
            IntTy offset__2741 = 8 + fltPrm_2781;
            IntTy fltPrm_2782 = sizeof_y_2735__2738 + sizeof_y_2736__2739;
            IntTy offset__2742 = 0 + fltPrm_2782;
            IntTy fltPrm_2784 = sizeof_y_2736__2739 + sizeof_y_2737__2740;
            IntTy fltPrm_2783 = sizeof_y_2735__2738 + fltPrm_2784;
            IntTy size_dcon_2743 = 17 + fltPrm_2783;
            
            *(TagTyPacked *) loc_2924 = 172;
            
            CursorTy writetag_4951 = loc_2924 + 1;
            
            *(IntTy *) writetag_4951 = size_dcon_2743;
            
            CursorTy writecur_4952 = writetag_4951 + sizeof(IntTy);
            
            *(IntTy *) writecur_4952 = offset__2741;
            
            CursorTy writecur_4953 = writecur_4952 + sizeof(IntTy);
            
            *(IntTy *) writecur_4953 = offset__2742;
            
            CursorTy writecur_4954 = writecur_4953 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7220, pvrtmp_7221,
                                                   loc_2924, pvrtmp_7223};
            break;
        }
        
      case 8:
        {
            CursorCursorCursorCursorProd tmp_struct_193 =
                                          _add_size_and_rel_offsets_Content(end_r_2925, end_r_2926, loc_3804, tmpcur_7047);
            CursorTy pvrtmp_7232 = tmp_struct_193.field0;
            CursorTy pvrtmp_7233 = tmp_struct_193.field1;
            CursorTy pvrtmp_7234 = tmp_struct_193.field2;
            CursorTy pvrtmp_7235 = tmp_struct_193.field3;
            CursorCursorCursorCursorProd tmp_struct_194 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, pvrtmp_7232, pvrtmp_7235, pvrtmp_7233);
            CursorTy pvrtmp_7240 = tmp_struct_194.field0;
            CursorTy pvrtmp_7241 = tmp_struct_194.field1;
            CursorTy pvrtmp_7242 = tmp_struct_194.field2;
            CursorTy pvrtmp_7243 = tmp_struct_194.field3;
            CursorCursorCursorCursorProd tmp_struct_195 =
                                          _add_size_and_rel_offsets_Tags(end_r_2925, pvrtmp_7240, pvrtmp_7243, pvrtmp_7241);
            CursorTy pvrtmp_7248 = tmp_struct_195.field0;
            CursorTy pvrtmp_7249 = tmp_struct_195.field1;
            CursorTy pvrtmp_7250 = tmp_struct_195.field2;
            CursorTy pvrtmp_7251 = tmp_struct_195.field3;
            IntTy sizeof_y_2747__2750 = pvrtmp_7235 - pvrtmp_7234;
            IntTy sizeof_y_2748__2751 = pvrtmp_7243 - pvrtmp_7242;
            IntTy sizeof_y_2749__2752 = pvrtmp_7251 - pvrtmp_7250;
            IntTy fltPrm_2785 = sizeof_y_2747__2750 + 0;
            IntTy offset__2753 = 8 + fltPrm_2785;
            IntTy fltPrm_2786 = sizeof_y_2747__2750 + sizeof_y_2748__2751;
            IntTy offset__2754 = 0 + fltPrm_2786;
            IntTy fltPrm_2788 = sizeof_y_2748__2751 + sizeof_y_2749__2752;
            IntTy fltPrm_2787 = sizeof_y_2747__2750 + fltPrm_2788;
            IntTy size_dcon_2755 = 17 + fltPrm_2787;
            
            *(TagTyPacked *) loc_2924 = 174;
            
            CursorTy writetag_4963 = loc_2924 + 1;
            
            *(IntTy *) writetag_4963 = size_dcon_2755;
            
            CursorTy writecur_4964 = writetag_4963 + sizeof(IntTy);
            
            *(IntTy *) writecur_4964 = offset__2753;
            
            CursorTy writecur_4965 = writecur_4964 + sizeof(IntTy);
            
            *(IntTy *) writecur_4965 = offset__2754;
            
            CursorTy writecur_4966 = writecur_4965 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7248, pvrtmp_7249,
                                                   loc_2924, pvrtmp_7251};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7260 = *(CursorTy *) tmpcur_7047;
            CursorTy tmpaftercur_7261 = tmpcur_7047 + 8;
            CursorTy jump_4248 = tmpcur_7047 + 8;
            CursorCursorCursorCursorProd tmp_struct_196 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, end_r_2926, loc_2924, tmpcur_7260);
            CursorTy pvrtmp_7262 = tmp_struct_196.field0;
            CursorTy pvrtmp_7263 = tmp_struct_196.field1;
            CursorTy pvrtmp_7264 = tmp_struct_196.field2;
            CursorTy pvrtmp_7265 = tmp_struct_196.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7262, jump_4248,
                                                   pvrtmp_7264, pvrtmp_7265};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7272 = *(CursorTy *) tmpcur_7047;
            CursorTy tmpaftercur_7273 = tmpcur_7047 + 8;
            CursorCursorCursorCursorProd tmp_struct_197 =
                                          _add_size_and_rel_offsets_Adt(end_r_2925, end_r_2926, loc_2924, tmpcur_7272);
            CursorTy pvrtmp_7274 = tmp_struct_197.field0;
            CursorTy pvrtmp_7275 = tmp_struct_197.field1;
            CursorTy pvrtmp_7276 = tmp_struct_197.field2;
            CursorTy pvrtmp_7277 = tmp_struct_197.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7274, pvrtmp_7275,
                                                   pvrtmp_7276, pvrtmp_7277};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7046");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Tags(CursorTy end_r_2929,
                                                            CursorTy end_r_2930,
                                                            CursorTy loc_2928,
                                                            CursorTy arg_2756)
{
    if (loc_2928 + 32 > end_r_2930) {
        ChunkTy new_chunk_204 = alloc_chunk(end_r_2930);
        CursorTy chunk_start_205 = new_chunk_204.chunk_start;
        CursorTy chunk_end_206 = new_chunk_204.chunk_end;
        
        end_r_2930 = chunk_end_206;
        *(TagTyPacked *) loc_2928 = 255;
        
        CursorTy redir = loc_2928 + 1;
        
        *(CursorTy *) redir = chunk_start_205;
        loc_2928 = chunk_start_205;
    }
    
    CursorTy loc_3824 = loc_2928 + 1;
    CursorTy loc_3825 = loc_3824 + 8;
    TagTyPacked tmpval_7285 = *(TagTyPacked *) arg_2756;
    CursorTy tmpcur_7286 = arg_2756 + 1;
    
    
  switch_7329:
    ;
    switch (tmpval_7285) {
        
      case 0:
        {
            CursorTy jump_4122 = arg_2756 + 1;
            
            *(TagTyPacked *) loc_2928 = 0;
            
            CursorTy writetag_4978 = loc_2928 + 1;
            
            return (CursorCursorCursorCursorProd) {end_r_2930, jump_4122,
                                                   loc_2928, writetag_4978};
            break;
        }
        
      case 1:
        {
            IntTy tmpval_7291 = *(IntTy *) tmpcur_7286;
            CursorTy tmpcur_7292 = tmpcur_7286 + sizeof(IntTy);
            CursorTy jump_4124 = tmpcur_7286 + 8;
            CursorCursorCursorCursorProd tmp_struct_201 =
                                          _add_size_and_rel_offsets_Tags(end_r_2929, end_r_2930, loc_3825, tmpcur_7292);
            CursorTy pvrtmp_7293 = tmp_struct_201.field0;
            CursorTy pvrtmp_7294 = tmp_struct_201.field1;
            CursorTy pvrtmp_7295 = tmp_struct_201.field2;
            CursorTy pvrtmp_7296 = tmp_struct_201.field3;
            
            *(TagTyPacked *) loc_2928 = 1;
            
            CursorTy writetag_4983 = loc_2928 + 1;
            
            *(IntTy *) writetag_4983 = tmpval_7291;
            
            CursorTy writecur_4984 = writetag_4983 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7293, pvrtmp_7294,
                                                   loc_2928, pvrtmp_7296};
            break;
        }
        
      case INDIRECTION_TAG:
        {
            CursorTy tmpcur_7305 = *(CursorTy *) tmpcur_7286;
            CursorTy tmpaftercur_7306 = tmpcur_7286 + 8;
            CursorTy jump_4254 = tmpcur_7286 + 8;
            CursorCursorCursorCursorProd tmp_struct_202 =
                                          _add_size_and_rel_offsets_Tags(end_r_2929, end_r_2930, loc_2928, tmpcur_7305);
            CursorTy pvrtmp_7307 = tmp_struct_202.field0;
            CursorTy pvrtmp_7308 = tmp_struct_202.field1;
            CursorTy pvrtmp_7309 = tmp_struct_202.field2;
            CursorTy pvrtmp_7310 = tmp_struct_202.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7307, jump_4254,
                                                   pvrtmp_7309, pvrtmp_7310};
            break;
        }
        
      case REDIRECTION_TAG:
        {
            CursorTy tmpcur_7317 = *(CursorTy *) tmpcur_7286;
            CursorTy tmpaftercur_7318 = tmpcur_7286 + 8;
            CursorCursorCursorCursorProd tmp_struct_203 =
                                          _add_size_and_rel_offsets_Tags(end_r_2929, end_r_2930, loc_2928, tmpcur_7317);
            CursorTy pvrtmp_7319 = tmp_struct_203.field0;
            CursorTy pvrtmp_7320 = tmp_struct_203.field1;
            CursorTy pvrtmp_7321 = tmp_struct_203.field2;
            CursorTy pvrtmp_7322 = tmp_struct_203.field3;
            
            return (CursorCursorCursorCursorProd) {pvrtmp_7319, pvrtmp_7320,
                                                   pvrtmp_7321, pvrtmp_7322};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_7285");
            exit(1);
        }
    }
}
int __main_expr()
{
    add_symbol(5859, "Time for Adt: CA");
    set_newline(5860);
    add_symbol(5861, "Count of Adt CA is: ");
    add_symbol(5862, ")");
    add_symbol(5863, "(Text ");
    add_symbol(5864, "(Tag ");
    add_symbol(5865, "(TCA ");
    add_symbol(5866, "(TAC ");
    add_symbol(5867, "(Nul ");
    add_symbol(5868, "(Nil ");
    add_symbol(5869, "(Image ");
    add_symbol(5870, "(End ");
    add_symbol(5871, "(Char ");
    add_symbol(5872, "(CTA ");
    add_symbol(5873, "(CAT ");
    add_symbol(5874, "(CA ");
    add_symbol(5875, "(ATC ");
    add_symbol(5876, "(ACT ");
    add_symbol(5877, "(AC ");
    add_symbol(5878, " ->r ");
    add_symbol(5879, " ->i ");
    
    RegionTy *region_5880 = alloc_region(global_init_inf_buf_size);
    CursorTy r_2936 = region_5880->reg_heap;
    IntTy sizeof_end_r_2936_5881 = global_init_inf_buf_size;
    CursorTy end_r_2936 = r_2936 + sizeof_end_r_2936_5881;
    CursorCursorCursorProd tmp_struct_207 =
                            mkCAList(end_r_2936, r_2936, 1000000, 100);
    CursorTy pvrtmp_5882 = tmp_struct_207.field0;
    CursorTy pvrtmp_5883 = tmp_struct_207.field1;
    CursorTy pvrtmp_5884 = tmp_struct_207.field2;
    unsigned char wildcard__17_22_914_1533 = print_symbol(5859);
    unsigned char wildcard__15_23_915_1534 = print_symbol(5860);
    IntTy timed_5282;
    VectorTy *times_211 = vector_alloc(global_iters_param, sizeof(double));
    struct timespec begin_timed_5282;
    struct timespec end_timed_5282;
    
    for (long long iters_timed_5282 = 0; iters_timed_5282 < global_iters_param;
         iters_timed_5282++) {
        if (iters_timed_5282 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_5282);
        
        IntTy tailapp_4127 =  getLengthTR(pvrtmp_5882, pvrtmp_5883, 0);
        
        timed_5282 = tailapp_4127;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_5282);
        if (iters_timed_5282 != global_iters_param - 1)
            restore_alloc_state();
        
        double itertime_208 = difftimespecs(&begin_timed_5282, &end_timed_5282);
        
        vector_inplace_update(times_211, iters_timed_5282, &itertime_208);
    }
    vector_inplace_sort(times_211, compare_doubles);
    
    double *tmp_212 = (double *) vector_nth(times_211, global_iters_param / 2);
    double selftimed_210 = *tmp_212;
    double batchtime_209 = sum_timing_array(times_211);
    
    print_timing_array(times_211);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime_209);
    printf("SELFTIMED: %e\n", selftimed_210);
    
    unsigned char wildcard__11_25_917_1536 = print_symbol(5861);
    unsigned char wildcard__9_26_918_1537 = printf("%lld", timed_5282);
    unsigned char wildcard__7_27_919_1538 = print_symbol(5860);
    
    printf("'#()");
    printf("\n");
    free_symtable();
    return 0;
}