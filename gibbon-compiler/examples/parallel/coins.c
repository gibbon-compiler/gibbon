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

#define KB 1000lu
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

// Initial size of BigInfinite buffers
static long long global_init_biginf_buf_size = (1 * GB);

// Initial size of Infinite buffers
static long long global_init_inf_buf_size = 64 * KB;

// Maximum size of a chunk, see GitHub #110.
long long global_inf_buf_max_chunk_size = 1 * GB;

static long long global_size_param = 1;
static long long global_iters_param = 1;

static char* global_benchfile_param = NULL;
static char* global_arrayfile_param = NULL;

// Sequential for now:
static const int num_workers = 1;

#define REDIRECTION_NODE_SIZE 9
#define MAX(a,b) (((a)>(b))?(a):(b))

// A region with this refcount has already been garbage collected.
#define REG_FREED -100


// -------------------------------------
// Allocators
// -------------------------------------


#ifdef BUMPALLOC
// #define DEBUG
#warning "Using bump allocator."

  char* heap_ptr = (char*)NULL;

  char* saved_heap_ptr_stack[100];
  int num_saved_heap_ptr = 0;

  // Requires -std=gnu11
  int dbgprintf(const char *format, ...)
  {
      int code = 0;
      va_list args;
      va_start(args, format);
  #ifdef DEBUG
      code = vprintf(format, args);
  #endif
      va_end(args);
      return code;
  }

  // For simplicity just use a single large slab:
  void INITALLOC() {
    if (! heap_ptr)
    {
      // Use a fixed address in debug mode for easy reading:
      #ifdef DEBUG
      // heap_ptr = (char*)mmap(0x010000000000, global_init_biginf_buf_size, PROT_READ|PROT_WRITE, MAP_FIXED | MAP_ANONYMOUS, -1, 0);
        heap_ptr = (char*)mmap(0x010000000000, global_init_biginf_buf_size, PROT_READ|PROT_WRITE, MAP_ANONYMOUS | MAP_PRIVATE, -1, 0);
        if (heap_ptr == MAP_FAILED) {
          fprintf(stderr, "Error: mmap failed: %s\n", strerror(errno));
          abort();
        }
      #else
        heap_ptr = (char*)malloc(global_init_biginf_buf_size);
      #endif
      dbgprintf("Arena size for bump alloc: %lld\n", global_init_biginf_buf_size);
    }
    dbgprintf("BUMPALLOC/INITALLOC DONE: heap_ptr = %p\n", heap_ptr);
  }

  #ifdef DEBUG
    char* my_abort() {
      fprintf(stderr, "Error: this thread's heap was not initalized.\n");
      abort();
      return NULL;
    }
    void* ALLOC(int n) {
      if (!heap_ptr) my_abort();
      char* old = heap_ptr;
      printf("ALLOC: %d bytes, returning %p\n", n, old);
      // heap_ptr += 16 * n; // Optional padding for debugging.
      heap_ptr += n;
      return old;
    }
  #else
    // #define ALLOC(n) (do heap_ptr += n)
    void* ALLOC(int n) { char* old= heap_ptr; heap_ptr += n; return old; }
  #endif // DEBUG

  // Snapshot the current heap pointer value across all threads.
  void save_alloc_state() {
    dbgprintf("   Saving(%p): pos %d", heap_ptr, num_saved_heap_ptr);
    saved_heap_ptr_stack[num_saved_heap_ptr] = heap_ptr;
    num_saved_heap_ptr++;
    dbgprintf("\n");
  }

  void restore_alloc_state() {
    if(num_saved_heap_ptr <= 0) {
      fprintf(stderr, "Bad call to restore_alloc_state!  Saved stack empty!\ne");
      abort();
    }
    num_saved_heap_ptr--;
    dbgprintf("Restoring(%p): pos %d, discarding %p",
              saved_heap_ptr_stack[num_saved_heap_ptr], num_saved_heap_ptr, heap_ptr);
    heap_ptr = saved_heap_ptr_stack[num_saved_heap_ptr];
  }

#else
  // Regular malloc mode:
  void INITALLOC() {}

  void save_alloc_state() {}
  void restore_alloc_state() {}

#ifdef _POINTER
#define ALLOC(n) GC_MALLOC(n)
#else
#define ALLOC(n) malloc(n)
#endif

#endif // BUMPALLOC

#define ALLOC_PACKED(n) ALLOC(n)


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

typedef char TagTyPacked;   // Must be consistent with codegen in Target.hs
typedef char TagTyBoxed;    // Must be consistent with codegen in Target.hs
typedef long long IntTy;    // Int64 in Haskell
typedef float FloatTy;
typedef int SymTy;          // Word16 in Haskell. This could actually be a
                            // uint16_t. However, uthash's HASH_*_INT macros
                            // only work with proper int's.
typedef bool BoolTy;
typedef char* PtrTy;
typedef char* CursorTy;

// -------------------------------------
// Arenas and dictionaries
// -------------------------------------

typedef struct mem_arena {
  int ind;
  char* mem; // TODO: make this a list of chunks?
  void* reflist;
} mem_arena_t;

typedef mem_arena_t* ArenaTy;

ArenaTy alloc_arena() {
  ArenaTy ar = malloc(sizeof(mem_arena_t));
  ar->ind = 0;
  ar->mem = malloc(global_inf_buf_max_chunk_size);
  ar->reflist = 0;
  return ar;
}

void free_arena(ArenaTy ar) {
  free(ar->mem);
  // TODO: free everything in ar->reflist
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
  printf("Error, key %d not found!\n",key);
  exit(1);
}

// -------------------------------------
// Helpers
// -------------------------------------

char* read_benchfile_param() {
  if (global_benchfile_param == NULL) {
    fprintf(stderr, "read_benchfile_param: benchmark input file was not set!\n");
    exit(1);
  } else
    return global_benchfile_param;
}

char* read_arrayfile_param() {
  if (global_arrayfile_param == NULL) {
    fprintf(stderr, "read_arrayfile_param: array input file was not set!\n");
    exit(1);
  } else
    return global_arrayfile_param;
}


// fun fact: __ prefix is actually reserved and this is an undefined behavior.
// These functions must be provided by the code generator.
void __main_expr();


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

#define global_max_symbol_len 50

// Invariant: should always be equal to max(sym_table_keys)
static SymTy global_gensym_counter = 0;

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
    s = malloc(sizeof(struct SymTable_elem));
    s->idx = idx;
    strcpy(s->value, value);
    HASH_ADD_INT( global_sym_table, idx, s );
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
    HASH_FIND_INT( global_sym_table, &idx, s );
    return printf("%s", s->value);
  }
}

SymTy gensym() {
    global_gensym_counter += 1;
    SymTy idx = global_gensym_counter;
    char value[global_max_symbol_len];
    sprintf(value, "gensym_%d",idx);
    add_symbol(idx, value);
    return idx;
}

void free_symtable() {
    struct SymTable_elem *elt, *tmp;
    HASH_ITER(hh, global_sym_table, elt, tmp) {
        HASH_DEL(global_sym_table,elt);
        free(elt);
    }
}

/*

----------------------------------------
Garbage collection
----------------------------------------

   Gibbon has "growing regions" i.e each logical region is backed by a doubly linked-list
   of smaller chunks which grows as required. In addition to actual data, each chunk
   stores some additional metadata (RegionFooter) -- to chain the chunks together in a list
   and also for garbage collection. Representation of a footer at runtime:

   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
   serialized data | seq_no | size | refcount_ptr | outset_ptr | next_ptr | prev_ptr
   ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

   The metadata after the serialized data serves various purposes:

   - next_ptr / prev_ptr: Point to the next and previous chunk respectively.

   - seq_no: The index of this particular chunk in the list.

   - size: Used during bounds checking to calculate the size of the next region in
     the linked list.

   - refcount and outset: Whenever an inter-region indirection is created, we record that information
     using these two fields. Suppose we have an indirection from region A that points to some chunk
     in region B. Then A's outset will store a pointer to that chunk's footer, and B's refcount will
     be bumped by 1. Note that all there's only 1 refcount cell, and 1 outset per logical region,
     and chunks only store a pointer to them.


There are two ways in which a region may be freed:

(1) Whenever it goes out of scope

  The RTS tries to free a region whenever it goes out of scope. But this doesn't always succeed as
  regions sometimes contain values that "escape". One reason why this'll happen is if there's an
  indirection from A->B, and A lives longer than B. (CSK: do we have a program to test this?).
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
arbitrary chunk in the chain. However, we want call free_region on the first one to ensure that
all of them are GC'd. So we need pointers to traverse backward get to the first one.
'trav_to_first_chunk' accomplishes this.

 */

typedef struct Outset_elem {
    CursorTy ref;
    struct Outset_elem *prev;
    struct Outset_elem *next;
} Outset_elem;

typedef struct RegionTy_struct {
    int refcount;
    CursorTy start_ptr;
    Outset_elem *outset;
} RegionTy;

typedef struct RegionFooter_struct {
    // This sequence number is not strictly required, but helps with debugging
    // and error messages.
    int seq_no;
    IntTy size;
    int *refcount_ptr;
    Outset_elem *outset_ptr;
    CursorTy next;
    CursorTy prev;
} RegionFooter;

RegionTy *alloc_region(IntTy size) {
    // Allocate the first chunk
    IntTy total_size = size + sizeof(RegionFooter);
    CursorTy start = ALLOC_PACKED(total_size);
    if (start == NULL) {
        printf("alloc_region: malloc failed: %lld", total_size);
        exit(1);
    }
    CursorTy end = start + size;

    RegionTy *reg = malloc(sizeof(RegionTy));
    if (reg == NULL) {
        printf("alloc_region: malloc failed: %ld", sizeof(RegionTy));
        exit(1);
    }
    reg->refcount = 0;
    reg->start_ptr = start;
    reg->outset = NULL;

    // Write the footer
    RegionFooter* footer = (RegionFooter *) end;
    footer->seq_no = 1;
    footer->size = size;
    footer->refcount_ptr = &(reg->refcount);
    footer->outset_ptr = reg->outset;
    footer->next = NULL;
    footer->prev = NULL;
    *(RegionFooter *) end = *footer;

    return reg;
}

typedef struct ChunkTy_struct {
    CursorTy start_ptr;
    CursorTy end_ptr;
} ChunkTy;

ChunkTy alloc_chunk(CursorTy end_old_chunk) {
    // Get size from current footer
    RegionFooter *footer = (RegionFooter *) end_old_chunk;
    IntTy newsize = footer->size * 2;
    // See #110.
    if (newsize > global_inf_buf_max_chunk_size) {
        newsize = global_inf_buf_max_chunk_size;
    }
    IntTy total_size = newsize + sizeof(RegionFooter);

    // Allocate
    CursorTy start = ALLOC_PACKED(total_size);
    if (start == NULL) {
        printf("alloc_chunk: malloc failed: %lld", total_size);
        exit(1);
    }
    CursorTy end = start + newsize;

    #ifdef DEBUG
    printf("Allocated a chunk: %lld bytes.\n", total_size);
    #endif

    // Link the next chunk's footer
    footer->next = end;

    // Write the footer
    RegionFooter* new_footer = (RegionFooter *) end;
    new_footer->seq_no = footer->seq_no + 1;
    new_footer->size = newsize;
    new_footer->refcount_ptr = footer->refcount_ptr;
    new_footer->outset_ptr = footer->outset_ptr;
    new_footer->next = NULL;
    new_footer->prev = end_old_chunk;

    return (ChunkTy) {start , end};
}

RegionFooter* trav_to_first_chunk(RegionFooter *footer) {
    if (footer->seq_no == 1) {
        return footer;
    } else if (footer->prev == NULL) {
        fprintf(stderr, "No previous chunk found at seq_no: %d", footer->seq_no);
        return NULL;
    } else {
        trav_to_first_chunk((RegionFooter *) footer->prev);
    }
    return NULL;
}

int get_ref_count(CursorTy end_ptr) {
    RegionFooter footer = *(RegionFooter *) end_ptr;
    return *(footer.refcount_ptr);
}

// B is the pointer, and A is the pointee (i.e B -> A) --
// bump A's refcount, and update B's outset ptr.
IntTy bump_ref_count(CursorTy end_b, CursorTy end_a) {
    // Bump refcount
    RegionFooter *footer_a = (RegionFooter *) end_a;
    int refcount = *(footer_a->refcount_ptr);
    int new_refcount = refcount + 1;
    *(footer_a->refcount_ptr) = new_refcount;

    // Grab B's outset
    RegionFooter *footer_b = (RegionFooter *) end_b;
    Outset_elem *head = footer_b->outset_ptr;

    #ifdef DEBUG
    Outset_elem *elt;
    int count;
    DL_COUNT(head, elt, count);
    printf("bump_ref_count: old-refcount=%d, old-outset-len=%d:\n", refcount, count);
    assert(refcount == count);
    #endif

    // Add A to B's outset
    Outset_elem *add = malloc(sizeof(Outset_elem));
    add->ref = end_a;
    add->next = NULL;
    add->prev = NULL;
    DL_APPEND(head, add);

    // As far as I can tell, DL_APPEND updates "head" after an append. Or maybe
    // only after the first one, possibly to change NULL to some struct.
    // In any case, we update outset_ptr here.
    footer_b->outset_ptr = head;

    #ifdef DEBUG
    int new_count;
    DL_COUNT(head, elt, new_count);
    printf("bump_ref_count: new-refcount=%d, new-outset-len=%d:\n", new_refcount, new_count);
    assert(new_refcount == new_count);
    #endif

    return refcount;
}

void free_region(CursorTy end_reg) {
    RegionFooter footer = *(RegionFooter *) end_reg;
    CursorTy first_chunk = end_reg - footer.size;
    CursorTy next_chunk = footer.next;

    // Decrement refcounts of all regions `reg` points to
    if (footer.outset_ptr != NULL) {
        // Grab the outset, and decrement refcounts.
        Outset_elem *elt, *tmp;
        Outset_elem *head = (footer.outset_ptr);

        #ifdef DEBUG
        int count;
        DL_COUNT(head, elt, count);
        printf("free_region: outset-len: %d\n", count);
        #endif

        // Decrement refcounts, free regions with refcount==0 and also free
        // elements of the outset.
        DL_FOREACH_SAFE(head,elt,tmp) {
            RegionFooter *elt_footer = (RegionFooter *) elt->ref;
            *(elt_footer->refcount_ptr) = *(elt_footer->refcount_ptr) - 1;
            if (*(elt_footer->refcount_ptr) == 0) {
                // See [Why is it a doubly linked-list?] above
                RegionFooter *first_chunk = trav_to_first_chunk(elt_footer);
                if (first_chunk != NULL) {
                    free_region((CursorTy) first_chunk);
                }
            }
            DL_DELETE(head,elt);
            free(elt);
        }
    }

    // Free all chunks if recount is 0
    if (*(footer.refcount_ptr) == 0) {

        #ifdef DEBUG
        // Bookkeeping
        int num_chunks = 1;
        IntTy total_bytesize = footer.size;
        #endif

        // Indicate that this region has been garbage collected.
        *(footer.refcount_ptr) = REG_FREED;

        // Free the first chunk
        free(first_chunk);

        // Now, all the others
        while (next_chunk != NULL) {
            footer = *(RegionFooter *) next_chunk;
            free(next_chunk - footer.size);
            next_chunk = footer.next;

            #ifdef DEBUG
            num_chunks++;
            total_bytesize = total_bytesize + footer.size;
            #endif
        }

        #ifdef DEBUG
        printf("GC: Freed %lld bytes across %d chunks.\n",total_bytesize,num_chunks);
        #endif
    } else {
        #ifdef DEBUG
        printf("free_region: non-zero refcount: %d.\n", *(footer.refcount_ptr));
        #endif
    }
}

BoolTy is_big(CursorTy cur) {
    return false;
}

// -------------------------------------
// Dynamic Arrays
// -------------------------------------



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
      abort();
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

    // TODO: atoi() error checking

    int got_numargs = 0; // How many numeric arguments have we got.

    int i;
    for (i = 1; i < argc; ++i)
    {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
          show_usage(argv);
          exit(0);
        }
        else if (strcmp(argv[i], "--buffer-size") == 0 && i < argc - 1)
        {
            global_init_biginf_buf_size = atoll(argv[i + 1]);
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

    INITALLOC();
#ifdef BUMPALLOC
    //    save_alloc_state();
#endif
    __main_expr();

    return 0;
}

// -----------------------------------------------------------------------------
// Program starts here
// -----------------------------------------------------------------------------

UT_icd IntTy_icd = {sizeof(IntTy), NULL, NULL, NULL};

typedef struct IntTyIntTyProd_struct {
    IntTy val;
    IntTy quant;
} Coin;

UT_icd Coin_icd = {sizeof(Coin), NULL, NULL, NULL};

typedef struct CursorCursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
} CursorCursorCursorProd;

IntTy lenA_seq(CursorTy end_in_reg, CursorTy in_cur);
IntTy lenA(CursorTy end_in_reg, CursorTy in_cur, IntTy depth, IntTy c);
CursorCursorCursorProd payA_seq(CursorTy end_out_reg, CursorTy out_cur,
                                IntTy val, UT_array *coins, UT_array *acc);
CursorCursorCursorProd payA(CursorTy end_out_reg, CursorTy out_cur,
                            IntTy val, UT_array *coins, UT_array *acc,
                            IntTy depth);
void print_intlist(UT_array *ls);
void print_coins(UT_array *ls);
CursorTy _print_AList(CursorTy cur);

// -----------------------------------------------------------------------------

IntTy lenA_seq(CursorTy end_in_reg, CursorTy in_cur) {
    TagTyPacked tag = *(TagTyPacked *) in_cur;
    CursorTy tail = in_cur + 1;

    switch1:
      ;
      switch (tag) {
        case 0:
        {
            return 0;
        }

        case 1:
        {
            return 1;
        }

        case 3:
        {
            CursorTy tree2 = *(CursorTy *) tail;
            tail += 8;
            CursorTy tree1 = tail;
            IntTy l = lenA_seq(end_in_reg, tree1);
            IntTy r = lenA_seq(end_in_reg, tree2);
            return (l + r);
        }

        // AppendLNil
        case 4:
        {
            CursorTy tree2 = *(CursorTy *) tail;
            tail += 8;
            CursorTy tree1 = tail;
            IntTy r = lenA_seq(end_in_reg, tree2);
            return r;
        }

        // AppendRNil
        case 5:
        {
            CursorTy tree2 = *(CursorTy *) tail;
            tail += 8;
            CursorTy tree1 = tail;
            IntTy l = lenA_seq(end_in_reg, tree1);
            return l;
        }

        // AppendBothNil
        case 6:
        {
            return 0;
        }

        case 100:
        {
            CursorTy new_in_cur = *(CursorTy *) tail;
            tag = *(TagTyPacked *) new_in_cur;
            tail = new_in_cur + 1;
            goto switch1;
            break;
        }

        case 90:
        {
            CursorTy new_in_cur = *(CursorTy *) tail;
            tag = *(TagTyPacked *) new_in_cur;
            tail = new_in_cur + 1;
            goto switch1;
            break;
        }
        default:
        {
           printf("lenA: Unknown tag: %d", tag);
           exit(1);
        }
      }
}

IntTy lenA(CursorTy end_in_reg, CursorTy in_cur, IntTy depth, IntTy c) {

    if (depth >= c) {
        return lenA_seq(end_in_reg, in_cur);
    }

    TagTyPacked tag = *(TagTyPacked *) in_cur;
    CursorTy tail = in_cur + 1;

    switch1:
      ;
      switch (tag) {
        case 0:
        {
            return 0;
        }

        case 1:
        {
            return 1;
        }

        case 3:
        {
            CursorTy tree2 = *(CursorTy *) tail;
            tail += 8;
            CursorTy tree1 = tail;
            IntTy l = cilk_spawn lenA(end_in_reg, tree1, depth+1, c);
            IntTy r = lenA(end_in_reg, tree2, depth+1, c);
            cilk_sync;
            return (l + r);
        }

        // AppendLNil
        case 4:
        {
            CursorTy tree2 = *(CursorTy *) tail;
            tail += 8;
            CursorTy tree1 = tail;
            IntTy r = lenA(end_in_reg, tree2, depth+1, c);
            return r;
        }

        // AppendRNil
        case 5:
        {
            CursorTy tree2 = *(CursorTy *) tail;
            tail += 8;
            CursorTy tree1 = tail;
            IntTy l = lenA(end_in_reg, tree1, depth+1, c);
            return l;
        }

        // AppendBothNil
        case 6:
        {
            return 0;
        }

        case 100:
        {
            CursorTy new_in_cur = *(CursorTy *) tail;
            tag = *(TagTyPacked *) new_in_cur;
            tail = new_in_cur + 1;
            goto switch1;
            break;
        }

        case 90:
        {
            CursorTy new_in_cur = *(CursorTy *) tail;
            tag = *(TagTyPacked *) new_in_cur;
            tail = new_in_cur + 1;
            goto switch1;
            break;
        }
        default:
        {
           printf("lenA: Unknown tag: %d", tag);
           exit(1);
        }
      }
}


// UT_array *get_coins_rst(UT_array *coins) {
//     IntTy len = (IntTy) utarray_len(coins);
//     UT_array *coins_rst = coins;
//     utarray_erase(coins_rst, len-1, 1);
//     return coins_rst;
// }

// UT_array *get_coins1(UT_array *coins_rst) {
//     UT_array *coins1;
//     utarray_new(coins1, &Coin_icd);
//     utarray_concat(coins1, coins_rst);
//     return coins1;
// }

CursorCursorCursorProd payA_seq(CursorTy end_out_reg, CursorTy out_cur,
                                IntTy val, UT_array *coins, UT_array *acc) {

    // Allocator ran out of space
    if ((out_cur + 24) > end_out_reg) {
        ChunkTy new_chunk = alloc_chunk(end_out_reg);
        CursorTy chunk_start = new_chunk.start_ptr;
        CursorTy chunk_end = new_chunk.end_ptr;

        end_out_reg = chunk_end;
        *(TagTyPacked *) out_cur = 100;
        out_cur += 1;
        *(CursorTy *) out_cur = chunk_start;
        out_cur = chunk_start;
    }

    if (val == 0) {
        // ASing acc
        CursorTy cur = out_cur;

        *(TagTyPacked *) cur = 1;
        cur += 1;
        *(UT_array **) cur = acc;
        cur += sizeof(UT_array *);
        return (CursorCursorCursorProd) {end_out_reg, out_cur, cur};

    } else if (utarray_len(coins) == 0) {
        // ANil
        *(TagTyPacked *) out_cur = 0;
        return (CursorCursorCursorProd) {end_out_reg, out_cur, out_cur+1};

    } else {
        IntTy len = (IntTy) utarray_len(coins);
        Coin *coin = (Coin*) utarray_back(coins);
        UT_array *coins_rst = coins;
        utarray_erase(coins_rst, len-1, 1);
        // UT_array *coins_rst = get_coins_rst(coins);

        if (coin->val > val) {
            return payA_seq(end_out_reg, out_cur, val, coins_rst, acc);
        } else {
            // Append
            CursorTy cur = out_cur;
            CursorTy ran_cur = cur+1;
            cur += 9;

            UT_array *coins1;
            utarray_new(coins1, &Coin_icd);
            utarray_concat(coins1, coins_rst);
            // UT_array *coins1 = get_coins1(coins_rst);
            if (coin->quant != 1) {
                Coin ctmp = (Coin) {coin->val, coin->quant - 1};
                utarray_push_back(coins1, &ctmp);
            }

            IntTy val_left = val - coin->val;
            CursorCursorCursorProd left =
                payA_seq(end_out_reg, cur, val_left, coins1, acc);
            CursorCursorCursorProd right =
                payA_seq(left.field0, left.field2, val, coins_rst, acc);
            *(CursorTy *) ran_cur = right.field1;

            // TagTyPacked tl, tr;
            // tl = *(TagTyPacked *) left.field1;
            // tr = *(TagTyPacked *) right.field1;
            // if (tl == 0 && tr == 0) {
            //     // AppendBothNil
            //     *(TagTyPacked *) out_cur = 6;
            // } else if (tl == 0) {
            //     // AppendLNil
            //     *(TagTyPacked *) out_cur = 4;
            // } else if (tr == 0) {
            //     // AppendLNil
            //     *(TagTyPacked *) out_cur = 5;
            // } else {
            //     // Append
            //     *(TagTyPacked *) out_cur = 3;
            // }
            *(TagTyPacked *) out_cur = 3;

            utarray_free(coins1);

            return (CursorCursorCursorProd) {right.field0, out_cur, right.field2};
        }
    }
}

// IntTy max_depth = 0;

CursorCursorCursorProd payA(CursorTy end_out_reg, CursorTy out_cur,
                            IntTy val, UT_array *coins, UT_array *acc,
                            IntTy depth) {

    if (depth == 0) {
        return payA_seq(end_out_reg, out_cur, val, coins, acc);
    }

    // Allocator ran out of space
    if ((out_cur + 24) > end_out_reg) {
        ChunkTy new_chunk = alloc_chunk(end_out_reg);
        CursorTy chunk_start = new_chunk.start_ptr;
        CursorTy chunk_end = new_chunk.end_ptr;

        end_out_reg = chunk_end;
        *(TagTyPacked *) out_cur = 100;
        out_cur += 1;
        *(CursorTy *) out_cur = chunk_start;
        out_cur = chunk_start;
    }

    if (val == 0) {
        // ASing acc
        CursorTy cur = out_cur;

        *(TagTyPacked *) cur = 1;
        cur += 1;
        *(UT_array **) cur = acc;
        cur += sizeof(UT_array *);
        return (CursorCursorCursorProd) {end_out_reg, out_cur, cur};

    } else if (utarray_len(coins) == 0) {
        // ANil
        *(TagTyPacked *) out_cur = 0;
        return (CursorCursorCursorProd) {end_out_reg, out_cur, out_cur+1};
    } else {
        IntTy len = (IntTy) utarray_len(coins);
        Coin *coin = (Coin*) utarray_back(coins);
        UT_array *coins_rst = coins;
        utarray_erase(coins_rst, len-1, 1);

        if (coin->val > val) {
            return payA(end_out_reg, out_cur, val, coins_rst, acc, depth);
        } else {
            // Append
            CursorTy cur = out_cur;
            CursorTy ran_cur = cur + 1;
            cur += 9;

            UT_array *coins1;
            utarray_new(coins1, &Coin_icd);
            utarray_concat(coins1, coins_rst);
            IntTy depth_left = depth - 1;
            if (coin->quant != 1) {
                Coin ctmp = (Coin) {coin->val, coin->quant - 1};
                utarray_push_back(coins1, &ctmp);
                depth_left = depth - 1;
            }

            IntTy val_left = val - coin->val;
            IntTy parent_id = __cilkrts_get_worker_number();
            CursorCursorCursorProd left =
                cilk_spawn payA(end_out_reg, cur, val_left, coins1, acc, depth_left);
            IntTy cont_id = __cilkrts_get_worker_number();

            CursorCursorCursorProd right;

            if (parent_id == cont_id) {
                // left not stolen
                right = payA(left.field0, left.field2, val, coins_rst, acc, depth-1);
                cilk_sync;
            } else {
                // left stolen
                RegionTy *region2 = alloc_region(global_init_inf_buf_size);
                CursorTy reg2 = region2->start_ptr;
                CursorTy end_reg2 = reg2 + global_init_inf_buf_size;
                right = payA(end_reg2, reg2, val, coins_rst, acc, depth-1);
                cilk_sync;

                CursorTy end_left = left.field2;
                *(TagTyPacked *) end_left = 90;
                end_left += 1;
                *(CursorTy *) end_left = reg2;
            }

            *(CursorTy *) ran_cur = right.field1;
            TagTyPacked tl = *(TagTyPacked *) left.field1;
            TagTyPacked tr = *(TagTyPacked *) right.field1;

            // if (tl == 0 && tr == 0) {
            //     // AppendBothNil
            //     *(TagTyPacked *) out_cur = 6;
            // } else if (tl == 0) {
            //     // AppendLNil
            //     *(TagTyPacked *) out_cur = 4;
            // } else if (tr == 0) {
            //     // AppendLNil
            //     *(TagTyPacked *) out_cur = 5;
            // } else {
            //     // Append
            //     *(TagTyPacked *) out_cur = 3;
            // }
            *(TagTyPacked *) out_cur = 3;

            utarray_free(coins1);

            return (CursorCursorCursorProd) {right.field0, out_cur, right.field2};
        }
    }
}

void print_intlist(UT_array *ls) {
    IntTy *i;
    fputs("[", stdout);
    for(i=(IntTy*)utarray_front(ls);
        i!=NULL;
        i=(IntTy*)utarray_next(ls,i)) {
        fprintf(stdout, "%lld,", *i);
    }
    fputs("]", stdout);
}

void print_coins(UT_array *ls) {
    Coin *c;
    fputs("[", stdout);
    for(c=(Coin*)utarray_front(ls);
        c!=NULL;
        c=(Coin*)utarray_next(ls,c)) {
        fprintf(stdout, "(%lld, %lld),", c->val, c->quant);
    }
    fputs("]", stdout);
}

// data AList = ANil | ASing [Int] | Append AList AList
CursorTy _print_AList(CursorTy cur) {
    fflush(stdout);
    TagTyPacked tag = *(TagTyPacked *) cur;
    CursorTy tail = cur + 1;

    switch1:
      ;
      switch(tag) {
        case 0:
        {
            fputs("(ANil)", stdout);
            return tail;
            break;
        }

        case 1:
        {
            fputs("(ASing ", stdout);
            UT_array *ls = *(UT_array **) tail;
            print_intlist(ls);
            fputs(")", stdout);
            return (tail + sizeof(UT_array *));
            break;
        }

        case 3:
        {
            fputs("(Append ", stdout);
            tail += 8;
            CursorTy tree2 = _print_AList(tail);
            fputs(" ", stdout);
            CursorTy end_tree2 = _print_AList(tree2);
            fputs(")", stdout);

            return end_tree2;
            break;
        }

        case 4:
        {
            fputs("(AppendLNil ", stdout);
            tail += 8;
            CursorTy tree2 = _print_AList(tail);
            fputs(" ", stdout);
            CursorTy end_tree2 = _print_AList(tree2);
            fputs(")", stdout);

            return end_tree2;
            break;
        }

        case 5:
        {
            fputs("(AppendRNil ", stdout);
            tail += 8;
            CursorTy tree2 = _print_AList(tail);
            fputs(" ", stdout);
            CursorTy end_tree2 = _print_AList(tree2);
            fputs(")", stdout);

            return end_tree2;
            break;
        }

        case 6:
        {
            fputs("(AppendBothNil ", stdout);
            tail += 8;
            CursorTy tree2 = _print_AList(tail);
            fputs(" ", stdout);
            CursorTy end_tree2 = _print_AList(tree2);
            fputs(")", stdout);

            return end_tree2;
            break;
        }

        case 100:
        {
            fputs(" -> ", stdout);

            CursorTy tmpcur3431 = *(CursorTy *) tail;
            TagTyPacked tagtmp3433 = *(TagTyPacked *) tmpcur3431;
            CursorTy tailtmp3434 = tmpcur3431 + 1;

            tag = tagtmp3433;
            tail = tailtmp3434;
            goto switch1;
            break;
        }

        case 90:
        {
            fputs(" -> ", stdout);

            CursorTy tmpcur3431 = *(CursorTy *) tail;
            TagTyPacked tagtmp3433 = *(TagTyPacked *) tmpcur3431;
            CursorTy tailtmp3434 = tmpcur3431 + 1;

            tag = tagtmp3433;
            tail = tailtmp3434;
            goto switch1;
        }

        default:
        {
            printf("_print_AList: unknown tag: %d", tag);
            exit(1);
        }
      }
}

// -----------------------------------------------------------------------------

void __main_expr() {
    UT_array *coins;
    utarray_new(coins, &Coin_icd);
    Coin c;
    c = (Coin) {250, 55};
    utarray_push_back(coins, &c);
    c = (Coin) {100, 88};
    utarray_push_back(coins, &c);
    c = (Coin) {25, 88};
    utarray_push_back(coins, &c);
    c = (Coin) {10, 99};
    utarray_push_back(coins, &c);
    c = (Coin) {5, 122};
    utarray_push_back(coins, &c);
    c = (Coin) {1, 177};
    utarray_push_back(coins, &c);

    IntTy val = global_size_param;
    UT_array *acc;
    utarray_new(acc, &IntTy_icd);
    CursorCursorCursorProd paid;
    RegionTy *region = alloc_region(global_init_inf_buf_size);
    CursorTy reg = region->start_ptr;
    CursorTy end_reg = reg + global_init_inf_buf_size;
    IntTy len;

    struct timespec begin_timed2661;
    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed2661);

    UT_array *coins2;
    for (int i = 0; i < global_iters_param; i++) {
        utarray_new(coins2, &Coin_icd);
        utarray_concat(coins2, coins);
        // paid = payA_seq(end_reg, reg, val, coins, acc);
        paid = payA(end_reg, reg, val, coins2, acc, 3);
        // _print_AList(paid.field1);
        utarray_free(coins2);
    }
    struct timespec end_timed2661;
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed2661);
    double batchtime = difftimespecs(&begin_timed2661, &end_timed2661);
    double selftimed = batchtime / global_iters_param;
    len = lenA(paid.field0, paid.field1, 3, 0);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime);
    printf("SELFTIMED: %e\n", selftimed);

    // printf("max_depth: %lld", max_depth);
    printf("len: %lld", len);
}
