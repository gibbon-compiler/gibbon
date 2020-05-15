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

#ifdef _PARALLEL
#define ALLOC(n) malloc(n)
#else
  #ifdef _POINTER
#define ALLOC(n) GC_MALLOC(n)
  #else
#define ALLOC(n) malloc(n)
  #endif
#endif // _PARALLEL

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

// Must be consistent with sizeOfTy defined in Gibbon.Language.Syntax.

typedef unsigned char TagTyPacked;
typedef unsigned char TagTyBoxed;
typedef long long IntTy;
typedef float FloatTy;
typedef IntTy SymTy;
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
  printf("Error, key %lld not found!\n",key);
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

UT_icd double_icd = {sizeof(double), NULL, NULL, NULL};

void print_timing_array(UT_array *times) {
    printf("BATCHTIME: [");
    double *d;
    for(d=(double*)utarray_front(times);
        d!=NULL;
        d=(double*)utarray_next(times,d)) {
        printf("%f, ",*d);
    }
    printf("]\n");
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
  return printf("abcde");
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
    HASH_FIND(hh, global_sym_table, &idx, sizeof(IntTy), s);
    return printf("%s", s->value);
  }
}

SymTy gensym() {
    global_gensym_counter += 1;
    SymTy idx = global_gensym_counter;
    char value[global_max_symbol_len];
    sprintf(value, "gensym_%lld",idx);
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
typedef struct TagProd_struct {
            TagTyPacked field0;
        } TagProd;
typedef struct TagInt64Prod_struct {
            TagTyPacked field0;
            IntTy field1;
        } TagInt64Prod;
typedef struct TagCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
        } TagCursorProd;
typedef struct TagCursorCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
            CursorTy field2;
        } TagCursorCursorProd;
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
typedef struct PtrCursorProd_struct {
            PtrTy field0;
            CursorTy field1;
        } PtrCursorProd;
UT_icd Int64Int64Prod_icd = {sizeof(Int64Int64Prod), NULL, NULL, NULL};
typedef struct ProdInt64Int64Prod_struct {
            Int64Int64Prod field0;
        } ProdInt64Int64Prod;
CursorInt64Prod lenA(CursorTy end_r222, CursorTy ls84);
CursorCursorCursorProd payA_par(CursorTy end_r224, CursorTy loc223,
                                IntTy depth88, IntTy amt89, UT_array *coins90);
CursorCursorCursorProd payA(CursorTy end_r226, CursorTy loc225, IntTy amt101,
                            UT_array *coins102);
UT_array *getCoinsRst(UT_array *coins111);
IntTy getDepth1(IntTy q113, IntTy depth114);
UT_array *getCoins1(IntTy c115, IntTy q116, UT_array *coins117);
CursorCursorCursorCursorProd _copy_AList(CursorTy end_r229, CursorTy end_r230,
                                         CursorTy loc228, CursorTy arg205);
CursorInt64Prod _traverse_AList(CursorTy end_r232, CursorTy arg212);
PtrCursorProd _unpack_AList(CursorTy p700);
CursorTy _print_AList(CursorTy p713);
CursorInt64Prod lenA(CursorTy end_r222, CursorTy ls84)
{
    CursorTy loc221 = (CursorTy) ls84;
    TagTyPacked tmpval559 = *(TagTyPacked *) ls84;
    CursorTy tmpcur560 = ls84 + 1;


  switch567:
    ;
    switch (tmpval559) {

      case 0:
        {
            CursorTy field_cur355 = (CursorTy) tmpcur560;
            CursorTy jump306 = loc221 + 1;
            IntTy fltLitTail307 = (IntTy) 0;

            return (CursorInt64Prod) {jump306, fltLitTail307};
            break;
        }

      case 1:
        {
            CursorTy field_cur356 = (CursorTy) tmpcur560;
            CursorTy case242 = (CursorTy) field_cur356;
            IntTy tmpval561 = *(IntTy *) case242;
            CursorTy tmpcur562 = case242 + sizeof(IntTy);
            IntTy i85 = (IntTy) tmpval561;
            CursorTy end_i85 = (CursorTy) tmpcur562;
            CursorTy jump308 = case242 + 8;
            IntTy fltLitTail309 = (IntTy) 1;

            return (CursorInt64Prod) {jump308, fltLitTail309};
            break;
        }

      case 2:
        {
            CursorTy field_cur358 = (CursorTy) tmpcur560;
            CursorTy case243 = (CursorTy) field_cur358;
            CursorTy l86 = (CursorTy) case243;
            CursorInt64Prod tmp_struct0 =  lenA(end_r222, l86);
            CursorTy pvrtmp563 = tmp_struct0.field0;
            IntTy pvrtmp564 = tmp_struct0.field1;
            CursorTy endof310 = (CursorTy) pvrtmp563;
            IntTy fltPrm185 = (IntTy) pvrtmp564;
            CursorTy case244 = (CursorTy) endof310;
            CursorTy r87 = (CursorTy) case244;
            CursorInt64Prod tmp_struct1 =  lenA(end_r222, r87);
            CursorTy pvrtmp565 = tmp_struct1.field0;
            IntTy pvrtmp566 = tmp_struct1.field1;
            CursorTy endof311 = (CursorTy) pvrtmp565;
            IntTy fltPrm186 = (IntTy) pvrtmp566;
            IntTy tailprim312 = fltPrm185 + fltPrm186;

            return (CursorInt64Prod) {endof311, tailprim312};
            break;
        }

      case 255:
        {
            CursorTy tmpcur721 = *(CursorTy *) tmpcur560;
            CursorTy tmpaftercur722 = tmpcur560 + 8;
            TagTyPacked tagtmp723 = *(TagTyPacked *) tmpcur721;
            CursorTy tailtmp724 = tmpcur721 + 1;

            tmpval559 = tagtmp723;
            tmpcur560 = tailtmp724;
            goto switch567;
            break;
        }

      case 254:
        {
            CursorTy tmpcur721 = *(CursorTy *) tmpcur560;
            CursorTy tmpaftercur722 = tmpcur560 + 8;
            TagTyPacked tagtmp723 = *(TagTyPacked *) tmpcur721;
            CursorTy tailtmp724 = tmpcur721 + 1;

            tmpval559 = tagtmp723;
            tmpcur560 = tailtmp724;
            goto switch567;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval559");
            exit(1);
        }
    }
}
CursorCursorCursorProd payA_par(CursorTy end_r224, CursorTy loc223,
                                IntTy depth88, IntTy amt89, UT_array *coins90)
{
    BoolTy fltIf187 = depth88 == 0;

    if (fltIf187) {
        CursorCursorCursorProd tmp_struct2 =
                                payA(end_r224, loc223, amt89, coins90);
        CursorTy pvrtmp568 = tmp_struct2.field0;
        CursorTy pvrtmp569 = tmp_struct2.field1;
        CursorTy pvrtmp570 = tmp_struct2.field2;
        CursorTy fltPrd464 = (CursorTy) pvrtmp569;
        CursorTy fltPrd465 = (CursorTy) pvrtmp570;
        CursorTy pvrtmp572 = (CursorTy) fltPrd465;
        CursorTy pvrtmp571 = (CursorTy) fltPrd464;
        CursorTy tailapp313 = (CursorTy) pvrtmp571;
        CursorTy fltPrd466 = (CursorTy) pvrtmp569;
        CursorTy fltPrd467 = (CursorTy) pvrtmp570;
        CursorTy pvrtmp574 = (CursorTy) fltPrd467;
        CursorTy pvrtmp573 = (CursorTy) fltPrd466;
        CursorTy end_tailapp313 = (CursorTy) pvrtmp574;
        CursorTy end_r224_344 = (CursorTy) pvrtmp568;
        CursorTy pvrtmp576 = (CursorTy) end_tailapp313;
        CursorTy pvrtmp575 = (CursorTy) tailapp313;
        CursorTy fltPrd468 = (CursorTy) pvrtmp575;
        CursorTy fltPrd469 = (CursorTy) pvrtmp576;

        return (CursorCursorCursorProd) {end_r224_344, fltPrd468, fltPrd469};
    } else {
        BoolTy fltIf188 = amt89 == 0;

        if (fltIf188) {
            *(TagTyPacked *) loc223 = 1;

            CursorTy writetag362 = loc223 + 1;

            *(IntTy *) writetag362 = 1;

            CursorTy writecur363 = writetag362 + sizeof(IntTy);
            CursorTy pvrtmp578 = (CursorTy) writecur363;
            CursorTy pvrtmp577 = (CursorTy) loc223;
            CursorTy taildc314 = (CursorTy) pvrtmp577;
            CursorTy end_taildc314 = (CursorTy) pvrtmp578;
            CursorTy pvrtmp580 = (CursorTy) end_taildc314;
            CursorTy pvrtmp579 = (CursorTy) taildc314;
            CursorTy fltPrd470 = (CursorTy) pvrtmp579;
            CursorTy fltPrd471 = (CursorTy) pvrtmp580;

            return (CursorCursorCursorProd) {end_r224, fltPrd470, fltPrd471};
        } else {
            IntTy len91 = (IntTy) utarray_len(coins90);
            BoolTy fltIf189 = len91 == 0;

            if (fltIf189) {
                *(TagTyPacked *) loc223 = 0;

                CursorTy writetag365 = loc223 + 1;
                CursorTy pvrtmp582 = (CursorTy) writetag365;
                CursorTy pvrtmp581 = (CursorTy) loc223;
                CursorTy taildc315 = (CursorTy) pvrtmp581;
                CursorTy end_taildc315 = (CursorTy) pvrtmp582;
                CursorTy pvrtmp584 = (CursorTy) end_taildc315;
                CursorTy pvrtmp583 = (CursorTy) taildc315;
                CursorTy fltPrd472 = (CursorTy) pvrtmp583;
                CursorTy fltPrd473 = (CursorTy) pvrtmp584;

                return (CursorCursorCursorProd) {end_r224, fltPrd472,
                                                 fltPrd473};
            } else {
                IntTy fltPrm190 = len91 - 1;
                Int64Int64Prod *tmp7;

                tmp7 = (Int64Int64Prod *) utarray_eltptr(coins90, fltPrm190);

                Int64Int64Prod tup92 = *tmp7;
                IntTy c93 = (IntTy) tup92.field0;
                IntTy q94 = (IntTy) tup92.field1;
                UT_array *coins_rst95 =  getCoinsRst(coins90);
                BoolTy fltIf191 = c93 > amt89;

                if (fltIf191) {
                    CursorCursorCursorProd tmp_struct3 =
                                            payA(end_r224, loc223, amt89, coins_rst95);
                    CursorTy pvrtmp585 = tmp_struct3.field0;
                    CursorTy pvrtmp586 = tmp_struct3.field1;
                    CursorTy pvrtmp587 = tmp_struct3.field2;
                    CursorTy fltPrd474 = (CursorTy) pvrtmp586;
                    CursorTy fltPrd475 = (CursorTy) pvrtmp587;
                    CursorTy pvrtmp589 = (CursorTy) fltPrd475;
                    CursorTy pvrtmp588 = (CursorTy) fltPrd474;
                    CursorTy tailapp316 = (CursorTy) pvrtmp588;
                    CursorTy fltPrd476 = (CursorTy) pvrtmp586;
                    CursorTy fltPrd477 = (CursorTy) pvrtmp587;
                    CursorTy pvrtmp591 = (CursorTy) fltPrd477;
                    CursorTy pvrtmp590 = (CursorTy) fltPrd476;
                    CursorTy end_tailapp316 = (CursorTy) pvrtmp591;
                    CursorTy end_r224_345 = (CursorTy) pvrtmp585;
                    CursorTy pvrtmp593 = (CursorTy) end_tailapp316;
                    CursorTy pvrtmp592 = (CursorTy) tailapp316;
                    CursorTy fltPrd478 = (CursorTy) pvrtmp592;
                    CursorTy fltPrd479 = (CursorTy) pvrtmp593;

                    utarray_free(coins_rst95);

                    return (CursorCursorCursorProd) {end_r224_345, fltPrd478,
                                                     fltPrd479};
                } else {
                    UT_array *coins196 =  getCoins1(c93, q94, coins_rst95);
                    IntTy depth197 =  getDepth1(q94, depth88);
                    IntTy fltSpawnE192 = amt89 - c93;
                    CursorTy loc257 = loc223 + 1;
                    IntTy parent_id300 = __cilkrts_get_worker_number();
                    CursorCursorCursorProd tmp_struct4 =
                                           cilk_spawn payA_par(end_r224, loc257, depth197, fltSpawnE192, coins196);
                    IntTy cont_id301 = __cilkrts_get_worker_number();
                    BoolTy not_stolen305 = cont_id301 == parent_id300;

                    if (not_stolen305) {
                        CursorTy pvrtmp594 = tmp_struct4.field0;
                        CursorTy pvrtmp595 = tmp_struct4.field1;
                        CursorTy pvrtmp596 = tmp_struct4.field2;
                        CursorTy left98 = (CursorTy) pvrtmp595;
                        CursorTy end_left98 = (CursorTy) pvrtmp596;
                        CursorTy end_r224_346 = (CursorTy) pvrtmp594;
                        CursorTy loc258 = (CursorTy) end_left98;
                        IntTy fltAppE193 = depth88 - 1;
                        CursorCursorCursorProd tmp_struct5 =
                                                payA_par(end_r224_346, loc258, fltAppE193, amt89, coins_rst95);
                        CursorTy pvrtmp597 = tmp_struct5.field0;
                        CursorTy pvrtmp598 = tmp_struct5.field1;
                        CursorTy pvrtmp599 = tmp_struct5.field2;
                        CursorTy right99 = (CursorTy) pvrtmp598;
                        CursorTy end_right99 = (CursorTy) pvrtmp599;
                        CursorTy end_r224_346_347 = (CursorTy) pvrtmp597;

                        cilk_sync;
                        *(TagTyPacked *) loc223 = 2;

                        CursorTy writetag370 = loc223 + 1;
                        CursorTy writecur371 = (CursorTy) end_left98;
                        CursorTy writecur372 = (CursorTy) end_right99;
                        CursorTy pvrtmp601 = (CursorTy) writecur372;
                        CursorTy pvrtmp600 = (CursorTy) loc223;
                        CursorTy taildc317 = (CursorTy) pvrtmp600;
                        CursorTy end_taildc317 = (CursorTy) pvrtmp601;

                        utarray_free(coins_rst95);
                        utarray_free(coins196);

                        return (CursorCursorCursorProd) {end_r224_346_347,
                                                         taildc317,
                                                         end_taildc317};
                    } else {
                        RegionTy *region602 =
                                 alloc_region(global_init_biginf_buf_size);
                        CursorTy rafter302 = region602->start_ptr;
                        IntTy sizeof_end_rafter302603 =
                              global_init_biginf_buf_size;
                        CursorTy end_rafter302 = rafter302 +
                                 sizeof_end_rafter302603;
                        CursorTy loc303 = (CursorTy) rafter302;
                        IntTy fltAppE193 = depth88 - 1;
                        CursorCursorCursorProd tmp_struct6 =
                                                payA_par(end_rafter302, loc303, fltAppE193, amt89, coins_rst95);
                        CursorTy pvrtmp604 = tmp_struct6.field0;
                        CursorTy pvrtmp605 = tmp_struct6.field1;
                        CursorTy pvrtmp606 = tmp_struct6.field2;
                        CursorTy fltPrd480 = (CursorTy) pvrtmp605;
                        CursorTy fltPrd481 = (CursorTy) pvrtmp606;
                        CursorTy pvrtmp608 = (CursorTy) fltPrd481;
                        CursorTy pvrtmp607 = (CursorTy) fltPrd480;
                        CursorTy right99 = (CursorTy) pvrtmp607;
                        CursorTy fltPrd482 = (CursorTy) pvrtmp605;
                        CursorTy fltPrd483 = (CursorTy) pvrtmp606;
                        CursorTy pvrtmp610 = (CursorTy) fltPrd483;
                        CursorTy pvrtmp609 = (CursorTy) fltPrd482;
                        CursorTy end_right99 = (CursorTy) pvrtmp610;
                        CursorTy end_rafter302_348 = (CursorTy) pvrtmp604;

                        cilk_sync;

                        CursorTy pvrtmp594 = tmp_struct4.field0;
                        CursorTy pvrtmp595 = tmp_struct4.field1;
                        CursorTy pvrtmp596 = tmp_struct4.field2;
                        CursorTy fltPrd484 = (CursorTy) pvrtmp595;
                        CursorTy fltPrd485 = (CursorTy) pvrtmp596;
                        CursorTy pvrtmp612 = (CursorTy) fltPrd485;
                        CursorTy pvrtmp611 = (CursorTy) fltPrd484;
                        CursorTy left98 = (CursorTy) pvrtmp611;
                        CursorTy fltPrd486 = (CursorTy) pvrtmp595;
                        CursorTy fltPrd487 = (CursorTy) pvrtmp596;
                        CursorTy pvrtmp614 = (CursorTy) fltPrd487;
                        CursorTy pvrtmp613 = (CursorTy) fltPrd486;
                        CursorTy end_left98 = (CursorTy) pvrtmp614;
                        CursorTy end_r224_346 = (CursorTy) pvrtmp594;
                        CursorTy loc258 = (CursorTy) end_left98;

                        *(TagTyPacked *) loc258 = 254;

                        CursorTy writetag375 = loc258 + 1;

                        *(CursorTy *) writetag375 = loc303;

                        CursorTy writecur376 = writetag375 + 8;
                        CursorTy pvrtmp616 = (CursorTy) writecur376;
                        CursorTy pvrtmp615 = (CursorTy) loc258;
                        CursorTy pindr304 = (CursorTy) pvrtmp615;
                        CursorTy end_pindr304 = (CursorTy) pvrtmp616;

                        *(TagTyPacked *) loc223 = 2;

                        CursorTy writetag378 = loc223 + 1;
                        CursorTy writecur379 = (CursorTy) end_left98;
                        CursorTy writecur380 = (CursorTy) end_right99;
                        CursorTy pvrtmp618 = (CursorTy) writecur380;
                        CursorTy pvrtmp617 = (CursorTy) loc223;
                        CursorTy taildc318 = (CursorTy) pvrtmp617;
                        CursorTy end_taildc318 = (CursorTy) pvrtmp618;
                        CursorTy pvrtmp620 = (CursorTy) end_taildc318;
                        CursorTy pvrtmp619 = (CursorTy) taildc318;
                        CursorTy fltPrd488 = (CursorTy) pvrtmp619;
                        CursorTy fltPrd489 = (CursorTy) pvrtmp620;

                        utarray_free(coins_rst95);
                        utarray_free(coins196);

                        return (CursorCursorCursorProd) {end_rafter302_348,
                                                         fltPrd488, fltPrd489};
                    }
                }
            }
        }
    }
}
CursorCursorCursorProd payA(CursorTy end_r226, CursorTy loc225, IntTy amt101,
                            UT_array *coins102)
{
    BoolTy fltIf194 = amt101 == 0;

    if (fltIf194) {
        *(TagTyPacked *) loc225 = 1;

        CursorTy writetag382 = loc225 + 1;

        *(IntTy *) writetag382 = 1;

        CursorTy writecur383 = writetag382 + sizeof(IntTy);
        CursorTy pvrtmp622 = (CursorTy) writecur383;
        CursorTy pvrtmp621 = (CursorTy) loc225;
        CursorTy taildc319 = (CursorTy) pvrtmp621;
        CursorTy end_taildc319 = (CursorTy) pvrtmp622;
        CursorTy pvrtmp624 = (CursorTy) end_taildc319;
        CursorTy pvrtmp623 = (CursorTy) taildc319;
        CursorTy fltPrd490 = (CursorTy) pvrtmp623;
        CursorTy fltPrd491 = (CursorTy) pvrtmp624;

        return (CursorCursorCursorProd) {end_r226, fltPrd490, fltPrd491};
    } else {
        IntTy len103 = (IntTy) utarray_len(coins102);
        BoolTy fltIf195 = len103 == 0;

        if (fltIf195) {
            *(TagTyPacked *) loc225 = 0;

            CursorTy writetag385 = loc225 + 1;
            CursorTy pvrtmp626 = (CursorTy) writetag385;
            CursorTy pvrtmp625 = (CursorTy) loc225;
            CursorTy taildc320 = (CursorTy) pvrtmp625;
            CursorTy end_taildc320 = (CursorTy) pvrtmp626;
            CursorTy pvrtmp628 = (CursorTy) end_taildc320;
            CursorTy pvrtmp627 = (CursorTy) taildc320;
            CursorTy fltPrd492 = (CursorTy) pvrtmp627;
            CursorTy fltPrd493 = (CursorTy) pvrtmp628;

            return (CursorCursorCursorProd) {end_r226, fltPrd492, fltPrd493};
        } else {
            IntTy fltPrm196 = len103 - 1;
            Int64Int64Prod *tmp14;

            tmp14 = (Int64Int64Prod *) utarray_eltptr(coins102, fltPrm196);

            Int64Int64Prod tup104 = *tmp14;
            IntTy c105 = (IntTy) tup104.field0;
            IntTy q106 = (IntTy) tup104.field1;
            IntTy fltPrm197 = len103 - 1;
            UT_array *coins_rst107;

            utarray_new(coins_rst107, &Int64Int64Prod_icd);
            utarray_inserta(coins_rst107, coins102, 0);

            IntTy from11 = 0;
            IntTy to12 = fltPrm197;
            int len13 = utarray_len(coins_rst107);

            utarray_erase(coins_rst107, 0, from11);
            utarray_erase(coins_rst107, to12, len13 - to12);

            BoolTy fltIf198 = c105 > amt101;

            if (fltIf198) {
                CursorCursorCursorProd tmp_struct8 =
                                        payA(end_r226, loc225, amt101, coins_rst107);
                CursorTy pvrtmp629 = tmp_struct8.field0;
                CursorTy pvrtmp630 = tmp_struct8.field1;
                CursorTy pvrtmp631 = tmp_struct8.field2;
                CursorTy fltPrd494 = (CursorTy) pvrtmp630;
                CursorTy fltPrd495 = (CursorTy) pvrtmp631;
                CursorTy pvrtmp633 = (CursorTy) fltPrd495;
                CursorTy pvrtmp632 = (CursorTy) fltPrd494;
                CursorTy tailapp321 = (CursorTy) pvrtmp632;
                CursorTy fltPrd496 = (CursorTy) pvrtmp630;
                CursorTy fltPrd497 = (CursorTy) pvrtmp631;
                CursorTy pvrtmp635 = (CursorTy) fltPrd497;
                CursorTy pvrtmp634 = (CursorTy) fltPrd496;
                CursorTy end_tailapp321 = (CursorTy) pvrtmp635;
                CursorTy end_r226_349 = (CursorTy) pvrtmp629;
                CursorTy pvrtmp637 = (CursorTy) end_tailapp321;
                CursorTy pvrtmp636 = (CursorTy) tailapp321;
                CursorTy fltPrd498 = (CursorTy) pvrtmp636;
                CursorTy fltPrd499 = (CursorTy) pvrtmp637;

                utarray_free(coins_rst107);

                return (CursorCursorCursorProd) {end_r226_349, fltPrd498,
                                                 fltPrd499};
            } else {
                UT_array *coins1108 =  getCoins1(c105, q106, coins_rst107);
                IntTy fltAppE199 = amt101 - c105;
                CursorTy loc267 = loc225 + 1;
                CursorCursorCursorProd tmp_struct9 =
                                        payA(end_r226, loc267, fltAppE199, coins1108);
                CursorTy pvrtmp638 = tmp_struct9.field0;
                CursorTy pvrtmp639 = tmp_struct9.field1;
                CursorTy pvrtmp640 = tmp_struct9.field2;
                CursorTy fltPrd500 = (CursorTy) pvrtmp639;
                CursorTy fltPrd501 = (CursorTy) pvrtmp640;
                CursorTy pvrtmp642 = (CursorTy) fltPrd501;
                CursorTy pvrtmp641 = (CursorTy) fltPrd500;
                CursorTy left109 = (CursorTy) pvrtmp641;
                CursorTy fltPrd502 = (CursorTy) pvrtmp639;
                CursorTy fltPrd503 = (CursorTy) pvrtmp640;
                CursorTy pvrtmp644 = (CursorTy) fltPrd503;
                CursorTy pvrtmp643 = (CursorTy) fltPrd502;
                CursorTy end_left109 = (CursorTy) pvrtmp644;
                CursorTy end_r226_350 = (CursorTy) pvrtmp638;
                CursorTy loc268 = (CursorTy) end_left109;
                CursorCursorCursorProd tmp_struct10 =
                                        payA(end_r226_350, loc268, amt101, coins_rst107);
                CursorTy pvrtmp645 = tmp_struct10.field0;
                CursorTy pvrtmp646 = tmp_struct10.field1;
                CursorTy pvrtmp647 = tmp_struct10.field2;
                CursorTy fltPrd504 = (CursorTy) pvrtmp646;
                CursorTy fltPrd505 = (CursorTy) pvrtmp647;
                CursorTy pvrtmp649 = (CursorTy) fltPrd505;
                CursorTy pvrtmp648 = (CursorTy) fltPrd504;
                CursorTy right110 = (CursorTy) pvrtmp648;
                CursorTy fltPrd506 = (CursorTy) pvrtmp646;
                CursorTy fltPrd507 = (CursorTy) pvrtmp647;
                CursorTy pvrtmp651 = (CursorTy) fltPrd507;
                CursorTy pvrtmp650 = (CursorTy) fltPrd506;
                CursorTy end_right110 = (CursorTy) pvrtmp651;
                CursorTy end_r226_350_351 = (CursorTy) pvrtmp645;

                *(TagTyPacked *) loc225 = 2;

                CursorTy writetag390 = loc225 + 1;
                CursorTy writecur391 = (CursorTy) end_left109;
                CursorTy writecur392 = (CursorTy) end_right110;
                CursorTy pvrtmp653 = (CursorTy) writecur392;
                CursorTy pvrtmp652 = (CursorTy) loc225;
                CursorTy taildc322 = (CursorTy) pvrtmp652;
                CursorTy end_taildc322 = (CursorTy) pvrtmp653;
                CursorTy pvrtmp655 = (CursorTy) end_taildc322;
                CursorTy pvrtmp654 = (CursorTy) taildc322;
                CursorTy fltPrd508 = (CursorTy) pvrtmp654;
                CursorTy fltPrd509 = (CursorTy) pvrtmp655;

                utarray_free(coins_rst107);
                utarray_free(coins1108);

                return (CursorCursorCursorProd) {end_r226_350_351, fltPrd508,
                                                 fltPrd509};
            }
        }
    }
}
UT_array *getCoinsRst(UT_array *coins111)
{
    IntTy len112 = (IntTy) utarray_len(coins111);
    IntTy fltPrm200 = len112 - 1;
    UT_array *tailprim323;

    utarray_new(tailprim323, &Int64Int64Prod_icd);
    utarray_inserta(tailprim323, coins111, 0);

    IntTy from15 = 0;
    IntTy to16 = fltPrm200;
    int len17 = utarray_len(tailprim323);

    utarray_erase(tailprim323, 0, from15);
    utarray_erase(tailprim323, to16, len17 - to16);
    return tailprim323;
}
IntTy getDepth1(IntTy q113, IntTy depth114)
{
    BoolTy fltIf201 = q113 == 1;

    if (fltIf201) {
        IntTy tailprim324 = depth114 - 1;

        return tailprim324;
    } else {
        return depth114;
    }
}
UT_array *getCoins1(IntTy c115, IntTy q116, UT_array *coins117)
{
    IntTy len118 = (IntTy) utarray_len(coins117);
    BoolTy fltIf202 = q116 == 1;

    if (fltIf202) {
        UT_array *tailprim325;

        utarray_new(tailprim325, &Int64Int64Prod_icd);
        utarray_inserta(tailprim325, coins117, 0);

        IntTy from18 = 0;
        IntTy to19 = len118;
        int len20 = utarray_len(tailprim325);

        utarray_erase(tailprim325, 0, from18);
        utarray_erase(tailprim325, to19, len20 - to19);
        return tailprim325;
    } else {
        IntTy fltPrd204 = q116 - 1;
        IntTy pvrtmp657 = (IntTy) fltPrd204;
        IntTy pvrtmp656 = (IntTy) c115;
        UT_array *tailprim326;

        utarray_new(tailprim326, &Int64Int64Prod_icd);
        utarray_concat(tailprim326, coins117);

        Int64Int64Prod tmp21 = (Int64Int64Prod) {pvrtmp656, pvrtmp657};

        utarray_push_back(tailprim326, &tmp21);
        return tailprim326;
    }
}
CursorCursorCursorCursorProd _copy_AList(CursorTy end_r229, CursorTy end_r230,
                                         CursorTy loc228, CursorTy arg205)
{
    CursorTy loc227 = (CursorTy) arg205;
    TagTyPacked tmpval658 = *(TagTyPacked *) arg205;
    CursorTy tmpcur659 = arg205 + 1;


  switch690:
    ;
    switch (tmpval658) {

      case 0:
        {
            CursorTy field_cur394 = (CursorTy) tmpcur659;
            CursorTy jump327 = loc227 + 1;

            *(TagTyPacked *) loc228 = 0;

            CursorTy writetag395 = loc228 + 1;
            CursorTy pvrtmp661 = (CursorTy) writetag395;
            CursorTy pvrtmp660 = (CursorTy) loc228;
            CursorTy taildc328 = (CursorTy) pvrtmp660;
            CursorTy end_taildc328 = (CursorTy) pvrtmp661;
            CursorTy pvrtmp663 = (CursorTy) end_taildc328;
            CursorTy pvrtmp662 = (CursorTy) taildc328;
            CursorTy fltPrd510 = (CursorTy) pvrtmp662;
            CursorTy fltPrd511 = (CursorTy) pvrtmp663;

            return (CursorCursorCursorCursorProd) {end_r230, jump327, fltPrd510,
                                                   fltPrd511};
            break;
        }

      case 1:
        {
            CursorTy field_cur397 = (CursorTy) tmpcur659;
            CursorTy case274 = (CursorTy) field_cur397;
            IntTy tmpval664 = *(IntTy *) case274;
            CursorTy tmpcur665 = case274 + sizeof(IntTy);
            IntTy x206 = (IntTy) tmpval664;
            CursorTy end_x206 = (CursorTy) tmpcur665;
            CursorTy jump329 = case274 + 8;

            *(TagTyPacked *) loc228 = 1;

            CursorTy writetag399 = loc228 + 1;

            *(IntTy *) writetag399 = x206;

            CursorTy writecur400 = writetag399 + sizeof(IntTy);
            CursorTy pvrtmp667 = (CursorTy) writecur400;
            CursorTy pvrtmp666 = (CursorTy) loc228;
            CursorTy taildc330 = (CursorTy) pvrtmp666;
            CursorTy end_taildc330 = (CursorTy) pvrtmp667;
            CursorTy pvrtmp669 = (CursorTy) end_taildc330;
            CursorTy pvrtmp668 = (CursorTy) taildc330;
            CursorTy fltPrd512 = (CursorTy) pvrtmp668;
            CursorTy fltPrd513 = (CursorTy) pvrtmp669;

            return (CursorCursorCursorCursorProd) {end_r230, jump329, fltPrd512,
                                                   fltPrd513};
            break;
        }

      case 2:
        {
            CursorTy field_cur402 = (CursorTy) tmpcur659;
            CursorTy case278 = (CursorTy) field_cur402;
            CursorTy x208 = (CursorTy) case278;
            CursorTy loc286 = loc228 + 1;
            CursorCursorCursorCursorProd tmp_struct22 =
                                          _copy_AList(end_r229, end_r230, loc286, x208);
            CursorTy pvrtmp670 = tmp_struct22.field0;
            CursorTy pvrtmp671 = tmp_struct22.field1;
            CursorTy pvrtmp672 = tmp_struct22.field2;
            CursorTy pvrtmp673 = tmp_struct22.field3;
            CursorTy fltPrd514 = (CursorTy) pvrtmp672;
            CursorTy fltPrd515 = (CursorTy) pvrtmp673;
            CursorTy pvrtmp675 = (CursorTy) fltPrd515;
            CursorTy pvrtmp674 = (CursorTy) fltPrd514;
            CursorTy y210 = (CursorTy) pvrtmp674;
            CursorTy fltPrd516 = (CursorTy) pvrtmp672;
            CursorTy fltPrd517 = (CursorTy) pvrtmp673;
            CursorTy pvrtmp677 = (CursorTy) fltPrd517;
            CursorTy pvrtmp676 = (CursorTy) fltPrd516;
            CursorTy end_y210 = (CursorTy) pvrtmp677;
            CursorTy end_r230_352 = (CursorTy) pvrtmp670;
            CursorTy endof331 = (CursorTy) pvrtmp671;
            CursorTy case279 = (CursorTy) endof331;
            CursorTy x209 = (CursorTy) case279;
            CursorTy loc287 = (CursorTy) end_y210;
            CursorCursorCursorCursorProd tmp_struct23 =
                                          _copy_AList(end_r229, end_r230_352, loc287, x209);
            CursorTy pvrtmp678 = tmp_struct23.field0;
            CursorTy pvrtmp679 = tmp_struct23.field1;
            CursorTy pvrtmp680 = tmp_struct23.field2;
            CursorTy pvrtmp681 = tmp_struct23.field3;
            CursorTy fltPrd518 = (CursorTy) pvrtmp680;
            CursorTy fltPrd519 = (CursorTy) pvrtmp681;
            CursorTy pvrtmp683 = (CursorTy) fltPrd519;
            CursorTy pvrtmp682 = (CursorTy) fltPrd518;
            CursorTy y211 = (CursorTy) pvrtmp682;
            CursorTy fltPrd520 = (CursorTy) pvrtmp680;
            CursorTy fltPrd521 = (CursorTy) pvrtmp681;
            CursorTy pvrtmp685 = (CursorTy) fltPrd521;
            CursorTy pvrtmp684 = (CursorTy) fltPrd520;
            CursorTy end_y211 = (CursorTy) pvrtmp685;
            CursorTy end_r230_352_353 = (CursorTy) pvrtmp678;
            CursorTy endof332 = (CursorTy) pvrtmp679;

            *(TagTyPacked *) loc228 = 2;

            CursorTy writetag405 = loc228 + 1;
            CursorTy writecur406 = (CursorTy) end_y210;
            CursorTy writecur407 = (CursorTy) end_y211;
            CursorTy pvrtmp687 = (CursorTy) writecur407;
            CursorTy pvrtmp686 = (CursorTy) loc228;
            CursorTy taildc333 = (CursorTy) pvrtmp686;
            CursorTy end_taildc333 = (CursorTy) pvrtmp687;
            CursorTy pvrtmp689 = (CursorTy) end_taildc333;
            CursorTy pvrtmp688 = (CursorTy) taildc333;
            CursorTy fltPrd522 = (CursorTy) pvrtmp688;
            CursorTy fltPrd523 = (CursorTy) pvrtmp689;

            return (CursorCursorCursorCursorProd) {end_r230_352_353, endof332,
                                                   fltPrd522, fltPrd523};
            break;
        }

      case 255:
        {
            CursorTy tmpcur725 = *(CursorTy *) tmpcur659;
            CursorTy tmpaftercur726 = tmpcur659 + 8;
            TagTyPacked tagtmp727 = *(TagTyPacked *) tmpcur725;
            CursorTy tailtmp728 = tmpcur725 + 1;

            tmpval658 = tagtmp727;
            tmpcur659 = tailtmp728;
            goto switch690;
            break;
        }

      case 254:
        {
            CursorTy tmpcur725 = *(CursorTy *) tmpcur659;
            CursorTy tmpaftercur726 = tmpcur659 + 8;
            TagTyPacked tagtmp727 = *(TagTyPacked *) tmpcur725;
            CursorTy tailtmp728 = tmpcur725 + 1;

            tmpval658 = tagtmp727;
            tmpcur659 = tailtmp728;
            goto switch690;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval658");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_AList(CursorTy end_r232, CursorTy arg212)
{
    CursorTy loc231 = (CursorTy) arg212;
    TagTyPacked tmpval691 = *(TagTyPacked *) arg212;
    CursorTy tmpcur692 = arg212 + 1;


  switch699:
    ;
    switch (tmpval691) {

      case 0:
        {
            CursorTy field_cur409 = (CursorTy) tmpcur692;
            CursorTy jump334 = loc231 + 1;
            IntTy fltLitTail335 = (IntTy) 42;

            return (CursorInt64Prod) {jump334, fltLitTail335};
            break;
        }

      case 1:
        {
            CursorTy field_cur410 = (CursorTy) tmpcur692;
            CursorTy case292 = (CursorTy) field_cur410;
            IntTy tmpval693 = *(IntTy *) case292;
            CursorTy tmpcur694 = case292 + sizeof(IntTy);
            IntTy x213 = (IntTy) tmpval693;
            CursorTy end_x213 = (CursorTy) tmpcur694;
            CursorTy jump336 = case292 + 8;
            IntTy fltLitTail337 = (IntTy) 42;

            return (CursorInt64Prod) {jump336, fltLitTail337};
            break;
        }

      case 2:
        {
            CursorTy field_cur412 = (CursorTy) tmpcur692;
            CursorTy case293 = (CursorTy) field_cur412;
            CursorTy x215 = (CursorTy) case293;
            CursorInt64Prod tmp_struct24 =  _traverse_AList(end_r232, x215);
            CursorTy pvrtmp695 = tmp_struct24.field0;
            IntTy pvrtmp696 = tmp_struct24.field1;
            CursorTy endof338 = (CursorTy) pvrtmp695;
            IntTy y217 = (IntTy) pvrtmp696;
            CursorTy case294 = (CursorTy) endof338;
            CursorTy x216 = (CursorTy) case294;
            CursorInt64Prod tmp_struct25 =  _traverse_AList(end_r232, x216);
            CursorTy pvrtmp697 = tmp_struct25.field0;
            IntTy pvrtmp698 = tmp_struct25.field1;
            CursorTy endof340 = (CursorTy) pvrtmp697;
            IntTy y218 = (IntTy) pvrtmp698;
            IntTy fltLitTail339 = (IntTy) 42;

            return (CursorInt64Prod) {endof340, fltLitTail339};
            break;
        }

      case 255:
        {
            CursorTy tmpcur729 = *(CursorTy *) tmpcur692;
            CursorTy tmpaftercur730 = tmpcur692 + 8;
            TagTyPacked tagtmp731 = *(TagTyPacked *) tmpcur729;
            CursorTy tailtmp732 = tmpcur729 + 1;

            tmpval691 = tagtmp731;
            tmpcur692 = tailtmp732;
            goto switch699;
            break;
        }

      case 254:
        {
            CursorTy tmpcur729 = *(CursorTy *) tmpcur692;
            CursorTy tmpaftercur730 = tmpcur692 + 8;
            TagTyPacked tagtmp731 = *(TagTyPacked *) tmpcur729;
            CursorTy tailtmp732 = tmpcur729 + 1;

            tmpval691 = tagtmp731;
            tmpcur692 = tailtmp732;
            goto switch699;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval691");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_AList(CursorTy p700)
{
    TagTyPacked tag701 = *(TagTyPacked *) p700;
    CursorTy tail702 = p700 + 1;


  switch712:
    ;
    switch (tag701) {

      case 0:
        {
            PtrTy ptr703 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr703)->field0 = tag701;
            return (PtrCursorProd) {ptr703, tail702};
            break;
        }

      case 1:
        {
            IntTy val704 = *(IntTy *) tail702;
            CursorTy tail705 = tail702 + sizeof(IntTy);
            PtrTy ptr706 = ALLOC(sizeof(TagInt64Prod));

            ((TagInt64Prod *) ptr706)->field0 = tag701;
            ((TagInt64Prod *) ptr706)->field1 = val704;
            return (PtrCursorProd) {ptr706, tail705};
            break;
        }

      case 2:
        {
            PtrCursorProd tmp_struct26 =  _unpack_AList(tail702);
            PtrTy ptr707 = tmp_struct26.field0;
            CursorTy tail708 = tmp_struct26.field1;
            PtrCursorProd tmp_struct27 =  _unpack_AList(tail708);
            PtrTy ptr709 = tmp_struct27.field0;
            CursorTy tail710 = tmp_struct27.field1;
            PtrTy ptr711 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr711)->field0 = tag701;
            ((TagCursorCursorProd *) ptr711)->field1 = ptr707;
            ((TagCursorCursorProd *) ptr711)->field2 = ptr709;
            return (PtrCursorProd) {ptr711, tail710};
            break;
        }

      case 255:
        {
            CursorTy tmpcur733 = *(CursorTy *) tail702;
            CursorTy tmpaftercur734 = tail702 + 8;
            TagTyPacked tagtmp735 = *(TagTyPacked *) tmpcur733;
            CursorTy tailtmp736 = tmpcur733 + 1;

            tag701 = tagtmp735;
            tail702 = tailtmp736;
            goto switch712;
            break;
        }

      case 254:
        {
            CursorTy tmpcur733 = *(CursorTy *) tail702;
            CursorTy tmpaftercur734 = tail702 + 8;
            TagTyPacked tagtmp735 = *(TagTyPacked *) tmpcur733;
            CursorTy tailtmp736 = tmpcur733 + 1;

            tag701 = tagtmp735;
            tail702 = tailtmp736;
            goto switch712;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch712");
            exit(1);
        }
    }
}
CursorTy _print_AList(CursorTy p713)
{
    TagTyPacked tag714 = *(TagTyPacked *) p713;
    CursorTy tail715 = p713 + 1;


  switch720:
    ;
    switch (tag714) {

      case 0:
        {
            fputs("(ANil ", stdout);
            fputs(")", stdout);
            return tail715;
            break;
        }

      case 1:
        {
            fputs("(ASing ", stdout);

            IntTy val716 = *(IntTy *) tail715;
            CursorTy tail717 = tail715 + sizeof(IntTy);

            printf("%lld", val716);
            fputs(")", stdout);
            return tail717;
            break;
        }

      case 2:
        {
            fputs("(Append ", stdout);

            CursorTy tail718 =  _print_AList(tail715);

            fputs(" ", stdout);

            CursorTy tail719 =  _print_AList(tail718);

            fputs(")", stdout);
            return tail719;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur737 = *(CursorTy *) tail715;
            CursorTy tmpaftercur738 = tail715 + 8;
            TagTyPacked tagtmp739 = *(TagTyPacked *) tmpcur737;
            CursorTy tailtmp740 = tmpcur737 + 1;

            tag714 = tagtmp739;
            tail715 = tailtmp740;
            goto switch720;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur737 = *(CursorTy *) tail715;
            CursorTy tmpaftercur738 = tail715 + 8;
            TagTyPacked tagtmp739 = *(TagTyPacked *) tmpcur737;
            CursorTy tailtmp740 = tmpcur737 + 1;

            tag714 = tagtmp739;
            tail715 = tailtmp740;
            goto switch720;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch720");
            exit(1);
        }
    }
}
void __main_expr()
{
    RegionTy *region524 = alloc_region(global_init_biginf_buf_size);
    CursorTy r239 = region524->start_ptr;
    IntTy sizeof_end_r239525 = global_init_biginf_buf_size;
    CursorTy end_r239 = r239 + sizeof_end_r239525;
    UT_array *coins75;

    utarray_new(coins75, &Int64Int64Prod_icd);

    IntTy pvrtmp527 = (IntTy) 55;
    IntTy pvrtmp526 = (IntTy) 250;
    Int64Int64Prod tmp39 = (Int64Int64Prod) {pvrtmp526, pvrtmp527};

    utarray_push_back(coins75, &tmp39);

    IntTy pvrtmp529 = (IntTy) 88;
    IntTy pvrtmp528 = (IntTy) 100;
    Int64Int64Prod tmp38 = (Int64Int64Prod) {pvrtmp528, pvrtmp529};

    utarray_push_back(coins75, &tmp38);

    IntTy pvrtmp531 = (IntTy) 88;
    IntTy pvrtmp530 = (IntTy) 25;
    Int64Int64Prod tmp37 = (Int64Int64Prod) {pvrtmp530, pvrtmp531};

    utarray_push_back(coins75, &tmp37);

    IntTy pvrtmp533 = (IntTy) 99;
    IntTy pvrtmp532 = (IntTy) 10;
    Int64Int64Prod tmp36 = (Int64Int64Prod) {pvrtmp532, pvrtmp533};

    utarray_push_back(coins75, &tmp36);

    IntTy pvrtmp535 = (IntTy) 122;
    IntTy pvrtmp534 = (IntTy) 5;
    Int64Int64Prod tmp35 = (Int64Int64Prod) {pvrtmp534, pvrtmp535};

    utarray_push_back(coins75, &tmp35);

    IntTy pvrtmp537 = (IntTy) 177;
    IntTy pvrtmp536 = (IntTy) 1;
    Int64Int64Prod tmp34 = (Int64Int64Prod) {pvrtmp536, pvrtmp537};

    utarray_push_back(coins75, &tmp34);

    IntTy amt82 = global_size_param;
    CursorTy loc236 = (CursorTy) r239;
    CursorTy pvrtmp547;
    CursorTy pvrtmp548;
    CursorTy pvrtmp549;
    UT_array *times31;

    utarray_new(times31, &double_icd);

    struct timespec begin_pvrtmp547;
    struct timespec end_pvrtmp547;

    for (long long iters_pvrtmp547 = 0; iters_pvrtmp547 < global_iters_param;
         iters_pvrtmp547++) {
        if (iters_pvrtmp547 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp547);

        CursorCursorCursorProd tmp_struct28 =
                                payA_par(end_r239, loc236, 3, amt82, coins75);
        CursorTy pvrtmp538 = tmp_struct28.field0;
        CursorTy pvrtmp539 = tmp_struct28.field1;
        CursorTy pvrtmp540 = tmp_struct28.field2;
        CursorTy fltPrd454 = (CursorTy) pvrtmp539;
        CursorTy fltPrd455 = (CursorTy) pvrtmp540;
        CursorTy pvrtmp542 = (CursorTy) fltPrd455;
        CursorTy pvrtmp541 = (CursorTy) fltPrd454;
        CursorTy tailapp341 = (CursorTy) pvrtmp541;
        CursorTy fltPrd456 = (CursorTy) pvrtmp539;
        CursorTy fltPrd457 = (CursorTy) pvrtmp540;
        CursorTy pvrtmp544 = (CursorTy) fltPrd457;
        CursorTy pvrtmp543 = (CursorTy) fltPrd456;
        CursorTy end_tailapp341 = (CursorTy) pvrtmp544;
        CursorTy end_r239_354 = (CursorTy) pvrtmp538;
        CursorTy pvrtmp546 = (CursorTy) end_tailapp341;
        CursorTy pvrtmp545 = (CursorTy) tailapp341;
        CursorTy fltPrd458 = (CursorTy) pvrtmp545;
        CursorTy fltPrd459 = (CursorTy) pvrtmp546;

        pvrtmp547 = end_r239_354;
        pvrtmp548 = fltPrd458;
        pvrtmp549 = fltPrd459;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp547);
        if (iters_pvrtmp547 != global_iters_param - 1)
            restore_alloc_state();

        double batchtime29 = difftimespecs(&begin_pvrtmp547, &end_pvrtmp547);

        utarray_push_back(times31, &batchtime29);
    }
    utarray_sort(times31, compare_doubles);

    double *tmp32 = (double *) utarray_eltptr(times31, global_iters_param / 2);
    double selftimed30 = *tmp32;

    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("SELFTIMED: %e\n", selftimed30);

    CursorTy pvrtmp552 = (CursorTy) pvrtmp549;
    CursorTy pvrtmp551 = (CursorTy) pvrtmp548;
    CursorTy pvrtmp550 = (CursorTy) pvrtmp547;
    CursorTy fltPrd460 = (CursorTy) pvrtmp551;
    CursorTy fltPrd461 = (CursorTy) pvrtmp552;
    CursorTy pvrtmp554 = (CursorTy) fltPrd461;
    CursorTy pvrtmp553 = (CursorTy) fltPrd460;
    CursorTy tr83 = (CursorTy) pvrtmp553;
    CursorTy fltPrd462 = (CursorTy) pvrtmp551;
    CursorTy fltPrd463 = (CursorTy) pvrtmp552;
    CursorTy pvrtmp556 = (CursorTy) fltPrd463;
    CursorTy pvrtmp555 = (CursorTy) fltPrd462;
    CursorTy end_tr83 = (CursorTy) pvrtmp556;
    CursorTy end_r239_354 = (CursorTy) pvrtmp550;
    CursorInt64Prod tmp_struct33 =  lenA(end_r239, tr83);
    CursorTy pvrtmp557 = tmp_struct33.field0;
    IntTy pvrtmp558 = tmp_struct33.field1;
    CursorTy endof343 = (CursorTy) pvrtmp557;
    IntTy tailapp342 = (IntTy) pvrtmp558;

    printf("%lld", tailapp342);
    fputs("\n", stdout);
    free_symtable();
    return;
}
