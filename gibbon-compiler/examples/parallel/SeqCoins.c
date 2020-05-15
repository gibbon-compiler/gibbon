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
typedef struct TagInt64Int64CursorProd_struct {
            TagTyPacked field0;
            IntTy field1;
            IntTy field2;
            CursorTy field3;
        } TagInt64Int64CursorProd;
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
CursorInt64Prod lenA(CursorTy end_r167, CursorTy ls62);
CursorCursorCursorProd payA(CursorTy end_r169, CursorTy loc168, IntTy amt66,
                            UT_array *coins67);
UT_array *getCoinsRst(UT_array *coins76);
UT_array *getCoins1(IntTy c78, IntTy q79, UT_array *coins80);
CursorCursorCursorCursorProd _copy_AList(CursorTy end_r172, CursorTy end_r173,
                                         CursorTy loc171, CursorTy arg135);
CursorInt64Prod _traverse_AList(CursorTy end_r175, CursorTy arg142);
CursorCursorCursorCursorProd _copy_Coins(CursorTy end_r178, CursorTy end_r179,
                                         CursorTy loc177, CursorTy arg149);
CursorInt64Prod _traverse_Coins(CursorTy end_r181, CursorTy arg156);
PtrCursorProd _unpack_AList(CursorTy p605);
PtrCursorProd _unpack_Coins(CursorTy p618);
CursorTy _print_AList(CursorTy p630);
CursorTy _print_Coins(CursorTy p638);
CursorInt64Prod lenA(CursorTy end_r167, CursorTy ls62)
{
    CursorTy loc166 = (CursorTy) ls62;
    TagTyPacked tmpval485 = *(TagTyPacked *) ls62;
    CursorTy tmpcur486 = ls62 + 1;


  switch493:
    ;
    switch (tmpval485) {

      case 0:
        {
            CursorTy field_cur312 = (CursorTy) tmpcur486;
            CursorTy jump262 = loc166 + 1;
            IntTy fltLitTail263 = (IntTy) 0;

            return (CursorInt64Prod) {jump262, fltLitTail263};
            break;
        }

      case 1:
        {
            CursorTy field_cur313 = (CursorTy) tmpcur486;
            CursorTy case191 = (CursorTy) field_cur313;
            IntTy tmpval487 = *(IntTy *) case191;
            CursorTy tmpcur488 = case191 + sizeof(IntTy);
            IntTy i63 = (IntTy) tmpval487;
            CursorTy end_i63 = (CursorTy) tmpcur488;
            CursorTy jump264 = case191 + 8;
            IntTy fltLitTail265 = (IntTy) 1;

            return (CursorInt64Prod) {jump264, fltLitTail265};
            break;
        }

      case 2:
        {
            CursorTy field_cur315 = (CursorTy) tmpcur486;
            CursorTy case192 = (CursorTy) field_cur315;
            CursorTy l64 = (CursorTy) case192;
            CursorInt64Prod tmp_struct0 =  lenA(end_r167, l64);
            CursorTy pvrtmp489 = tmp_struct0.field0;
            IntTy pvrtmp490 = tmp_struct0.field1;
            CursorTy endof266 = (CursorTy) pvrtmp489;
            IntTy fltPrm124 = (IntTy) pvrtmp490;
            CursorTy case193 = (CursorTy) endof266;
            CursorTy r65 = (CursorTy) case193;
            CursorInt64Prod tmp_struct1 =  lenA(end_r167, r65);
            CursorTy pvrtmp491 = tmp_struct1.field0;
            IntTy pvrtmp492 = tmp_struct1.field1;
            CursorTy endof267 = (CursorTy) pvrtmp491;
            IntTy fltPrm125 = (IntTy) pvrtmp492;
            IntTy tailprim268 = fltPrm124 + fltPrm125;

            return (CursorInt64Prod) {endof267, tailprim268};
            break;
        }

      case 255:
        {
            CursorTy tmpcur647 = *(CursorTy *) tmpcur486;
            CursorTy tmpaftercur648 = tmpcur486 + 8;
            TagTyPacked tagtmp649 = *(TagTyPacked *) tmpcur647;
            CursorTy tailtmp650 = tmpcur647 + 1;

            tmpval485 = tagtmp649;
            tmpcur486 = tailtmp650;
            goto switch493;
            break;
        }

      case 254:
        {
            CursorTy tmpcur647 = *(CursorTy *) tmpcur486;
            CursorTy tmpaftercur648 = tmpcur486 + 8;
            TagTyPacked tagtmp649 = *(TagTyPacked *) tmpcur647;
            CursorTy tailtmp650 = tmpcur647 + 1;

            tmpval485 = tagtmp649;
            tmpcur486 = tailtmp650;
            goto switch493;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval485");
            exit(1);
        }
    }
}
CursorCursorCursorProd payA(CursorTy end_r169, CursorTy loc168, IntTy amt66,
                            UT_array *coins67)
{
    BoolTy fltIf126 = amt66 == 0;

    if (fltIf126) {
        *(TagTyPacked *) loc168 = 1;

        CursorTy writetag318 = loc168 + 1;

        *(IntTy *) writetag318 = 1;

        CursorTy writecur319 = writetag318 + sizeof(IntTy);
        CursorTy pvrtmp495 = (CursorTy) writecur319;
        CursorTy pvrtmp494 = (CursorTy) loc168;
        CursorTy taildc269 = (CursorTy) pvrtmp494;
        CursorTy end_taildc269 = (CursorTy) pvrtmp495;
        CursorTy pvrtmp497 = (CursorTy) end_taildc269;
        CursorTy pvrtmp496 = (CursorTy) taildc269;
        CursorTy fltPrd408 = (CursorTy) pvrtmp496;
        CursorTy fltPrd409 = (CursorTy) pvrtmp497;

        return (CursorCursorCursorProd) {end_r169, fltPrd408, fltPrd409};
    } else {
        IntTy len68 = (IntTy) utarray_len(coins67);
        BoolTy fltIf127 = len68 == 0;

        if (fltIf127) {
            *(TagTyPacked *) loc168 = 0;

            CursorTy writetag321 = loc168 + 1;
            CursorTy pvrtmp499 = (CursorTy) writetag321;
            CursorTy pvrtmp498 = (CursorTy) loc168;
            CursorTy taildc270 = (CursorTy) pvrtmp498;
            CursorTy end_taildc270 = (CursorTy) pvrtmp499;
            CursorTy pvrtmp501 = (CursorTy) end_taildc270;
            CursorTy pvrtmp500 = (CursorTy) taildc270;
            CursorTy fltPrd410 = (CursorTy) pvrtmp500;
            CursorTy fltPrd411 = (CursorTy) pvrtmp501;

            return (CursorCursorCursorProd) {end_r169, fltPrd410, fltPrd411};
        } else {
            IntTy fltPrm128 = len68 - 1;
            Int64Int64Prod *tmp5;

            tmp5 = (Int64Int64Prod *) utarray_eltptr(coins67, fltPrm128);

            Int64Int64Prod tup69 = *tmp5;
            IntTy c70 = (IntTy) tup69.field0;
            IntTy q71 = (IntTy) tup69.field1;
            UT_array *coins_rst72 =  getCoinsRst(coins67);
            BoolTy fltIf129 = c70 > amt66;

            if (fltIf129) {
                CursorCursorCursorProd tmp_struct2 =
                                        payA(end_r169, loc168, amt66, coins_rst72);
                CursorTy pvrtmp502 = tmp_struct2.field0;
                CursorTy pvrtmp503 = tmp_struct2.field1;
                CursorTy pvrtmp504 = tmp_struct2.field2;
                CursorTy fltPrd412 = (CursorTy) pvrtmp503;
                CursorTy fltPrd413 = (CursorTy) pvrtmp504;
                CursorTy pvrtmp506 = (CursorTy) fltPrd413;
                CursorTy pvrtmp505 = (CursorTy) fltPrd412;
                CursorTy tailapp271 = (CursorTy) pvrtmp505;
                CursorTy fltPrd414 = (CursorTy) pvrtmp503;
                CursorTy fltPrd415 = (CursorTy) pvrtmp504;
                CursorTy pvrtmp508 = (CursorTy) fltPrd415;
                CursorTy pvrtmp507 = (CursorTy) fltPrd414;
                CursorTy end_tailapp271 = (CursorTy) pvrtmp508;
                CursorTy end_r169_305 = (CursorTy) pvrtmp502;
                CursorTy pvrtmp510 = (CursorTy) end_tailapp271;
                CursorTy pvrtmp509 = (CursorTy) tailapp271;
                CursorTy fltPrd416 = (CursorTy) pvrtmp509;
                CursorTy fltPrd417 = (CursorTy) pvrtmp510;

                utarray_free(coins_rst72);

                return (CursorCursorCursorProd) {end_r169_305, fltPrd416,
                                                 fltPrd417};
            } else {
                UT_array *coins173 =  getCoins1(c70, q71, coins_rst72);
                IntTy fltAppE130 = amt66 - c70;
                CursorTy loc204 = loc168 + 1;
                CursorCursorCursorProd tmp_struct3 =
                                        payA(end_r169, loc204, fltAppE130, coins173);
                CursorTy pvrtmp511 = tmp_struct3.field0;
                CursorTy pvrtmp512 = tmp_struct3.field1;
                CursorTy pvrtmp513 = tmp_struct3.field2;
                CursorTy fltPrd418 = (CursorTy) pvrtmp512;
                CursorTy fltPrd419 = (CursorTy) pvrtmp513;
                CursorTy pvrtmp515 = (CursorTy) fltPrd419;
                CursorTy pvrtmp514 = (CursorTy) fltPrd418;
                CursorTy left74 = (CursorTy) pvrtmp514;
                CursorTy fltPrd420 = (CursorTy) pvrtmp512;
                CursorTy fltPrd421 = (CursorTy) pvrtmp513;
                CursorTy pvrtmp517 = (CursorTy) fltPrd421;
                CursorTy pvrtmp516 = (CursorTy) fltPrd420;
                CursorTy end_left74 = (CursorTy) pvrtmp517;
                CursorTy end_r169_306 = (CursorTy) pvrtmp511;
                CursorTy loc205 = (CursorTy) end_left74;
                CursorCursorCursorProd tmp_struct4 =
                                        payA(end_r169_306, loc205, amt66, coins_rst72);
                CursorTy pvrtmp518 = tmp_struct4.field0;
                CursorTy pvrtmp519 = tmp_struct4.field1;
                CursorTy pvrtmp520 = tmp_struct4.field2;
                CursorTy fltPrd422 = (CursorTy) pvrtmp519;
                CursorTy fltPrd423 = (CursorTy) pvrtmp520;
                CursorTy pvrtmp522 = (CursorTy) fltPrd423;
                CursorTy pvrtmp521 = (CursorTy) fltPrd422;
                CursorTy right75 = (CursorTy) pvrtmp521;
                CursorTy fltPrd424 = (CursorTy) pvrtmp519;
                CursorTy fltPrd425 = (CursorTy) pvrtmp520;
                CursorTy pvrtmp524 = (CursorTy) fltPrd425;
                CursorTy pvrtmp523 = (CursorTy) fltPrd424;
                CursorTy end_right75 = (CursorTy) pvrtmp524;
                CursorTy end_r169_306_307 = (CursorTy) pvrtmp518;

                *(TagTyPacked *) loc168 = 2;

                CursorTy writetag326 = loc168 + 1;
                CursorTy writecur327 = (CursorTy) end_left74;
                CursorTy writecur328 = (CursorTy) end_right75;
                CursorTy pvrtmp526 = (CursorTy) writecur328;
                CursorTy pvrtmp525 = (CursorTy) loc168;
                CursorTy taildc272 = (CursorTy) pvrtmp525;
                CursorTy end_taildc272 = (CursorTy) pvrtmp526;
                CursorTy pvrtmp528 = (CursorTy) end_taildc272;
                CursorTy pvrtmp527 = (CursorTy) taildc272;
                CursorTy fltPrd426 = (CursorTy) pvrtmp527;
                CursorTy fltPrd427 = (CursorTy) pvrtmp528;

                utarray_free(coins_rst72);
                utarray_free(coins173);
                return (CursorCursorCursorProd) {end_r169_306_307, fltPrd426,
                                                 fltPrd427};
            }
        }
    }
}
UT_array *getCoinsRst(UT_array *coins76)
{
    IntTy len77 = (IntTy) utarray_len(coins76);
    IntTy fltPrm131 = len77 - 1;
    UT_array *tailprim273;

    utarray_new(tailprim273, &Int64Int64Prod_icd);
    utarray_inserta(tailprim273, coins76, 0);

    IntTy from6 = 0;
    IntTy to7 = fltPrm131;
    int len8 = utarray_len(tailprim273);

    utarray_erase(tailprim273, 0, from6);
    utarray_erase(tailprim273, to7, len8 - to7);
    return tailprim273;
}
UT_array *getCoins1(IntTy c78, IntTy q79, UT_array *coins80)
{
    IntTy len81 = (IntTy) utarray_len(coins80);
    BoolTy fltIf132 = q79 == 1;

    if (fltIf132) {
        UT_array *tailprim274;

        utarray_new(tailprim274, &Int64Int64Prod_icd);
        utarray_inserta(tailprim274, coins80, 0);

        IntTy from9 = 0;
        IntTy to10 = len81;
        int len11 = utarray_len(tailprim274);

        utarray_erase(tailprim274, 0, from9);
        utarray_erase(tailprim274, to10, len11 - to10);
        return tailprim274;
    } else {
        IntTy fltPrd134 = q79 - 1;
        IntTy pvrtmp530 = (IntTy) fltPrd134;
        IntTy pvrtmp529 = (IntTy) c78;
        UT_array *tailprim275;

        utarray_new(tailprim275, &Int64Int64Prod_icd);
        utarray_concat(tailprim275, coins80);

        Int64Int64Prod tmp12 = (Int64Int64Prod) {pvrtmp529, pvrtmp530};

        utarray_push_back(tailprim275, &tmp12);
        return tailprim275;
    }
}
CursorCursorCursorCursorProd _copy_AList(CursorTy end_r172, CursorTy end_r173,
                                         CursorTy loc171, CursorTy arg135)
{
    CursorTy loc170 = (CursorTy) arg135;
    TagTyPacked tmpval531 = *(TagTyPacked *) arg135;
    CursorTy tmpcur532 = arg135 + 1;


  switch563:
    ;
    switch (tmpval531) {

      case 0:
        {
            CursorTy field_cur330 = (CursorTy) tmpcur532;
            CursorTy jump276 = loc170 + 1;

            *(TagTyPacked *) loc171 = 0;

            CursorTy writetag331 = loc171 + 1;
            CursorTy pvrtmp534 = (CursorTy) writetag331;
            CursorTy pvrtmp533 = (CursorTy) loc171;
            CursorTy taildc277 = (CursorTy) pvrtmp533;
            CursorTy end_taildc277 = (CursorTy) pvrtmp534;
            CursorTy pvrtmp536 = (CursorTy) end_taildc277;
            CursorTy pvrtmp535 = (CursorTy) taildc277;
            CursorTy fltPrd428 = (CursorTy) pvrtmp535;
            CursorTy fltPrd429 = (CursorTy) pvrtmp536;

            return (CursorCursorCursorCursorProd) {end_r173, jump276, fltPrd428,
                                                   fltPrd429};
            break;
        }

      case 1:
        {
            CursorTy field_cur333 = (CursorTy) tmpcur532;
            CursorTy case211 = (CursorTy) field_cur333;
            IntTy tmpval537 = *(IntTy *) case211;
            CursorTy tmpcur538 = case211 + sizeof(IntTy);
            IntTy x136 = (IntTy) tmpval537;
            CursorTy end_x136 = (CursorTy) tmpcur538;
            CursorTy jump278 = case211 + 8;

            *(TagTyPacked *) loc171 = 1;

            CursorTy writetag335 = loc171 + 1;

            *(IntTy *) writetag335 = x136;

            CursorTy writecur336 = writetag335 + sizeof(IntTy);
            CursorTy pvrtmp540 = (CursorTy) writecur336;
            CursorTy pvrtmp539 = (CursorTy) loc171;
            CursorTy taildc279 = (CursorTy) pvrtmp539;
            CursorTy end_taildc279 = (CursorTy) pvrtmp540;
            CursorTy pvrtmp542 = (CursorTy) end_taildc279;
            CursorTy pvrtmp541 = (CursorTy) taildc279;
            CursorTy fltPrd430 = (CursorTy) pvrtmp541;
            CursorTy fltPrd431 = (CursorTy) pvrtmp542;

            return (CursorCursorCursorCursorProd) {end_r173, jump278, fltPrd430,
                                                   fltPrd431};
            break;
        }

      case 2:
        {
            CursorTy field_cur338 = (CursorTy) tmpcur532;
            CursorTy case215 = (CursorTy) field_cur338;
            CursorTy x138 = (CursorTy) case215;
            CursorTy loc223 = loc171 + 1;
            CursorCursorCursorCursorProd tmp_struct13 =
                                          _copy_AList(end_r172, end_r173, loc223, x138);
            CursorTy pvrtmp543 = tmp_struct13.field0;
            CursorTy pvrtmp544 = tmp_struct13.field1;
            CursorTy pvrtmp545 = tmp_struct13.field2;
            CursorTy pvrtmp546 = tmp_struct13.field3;
            CursorTy fltPrd432 = (CursorTy) pvrtmp545;
            CursorTy fltPrd433 = (CursorTy) pvrtmp546;
            CursorTy pvrtmp548 = (CursorTy) fltPrd433;
            CursorTy pvrtmp547 = (CursorTy) fltPrd432;
            CursorTy y140 = (CursorTy) pvrtmp547;
            CursorTy fltPrd434 = (CursorTy) pvrtmp545;
            CursorTy fltPrd435 = (CursorTy) pvrtmp546;
            CursorTy pvrtmp550 = (CursorTy) fltPrd435;
            CursorTy pvrtmp549 = (CursorTy) fltPrd434;
            CursorTy end_y140 = (CursorTy) pvrtmp550;
            CursorTy end_r173_308 = (CursorTy) pvrtmp543;
            CursorTy endof280 = (CursorTy) pvrtmp544;
            CursorTy case216 = (CursorTy) endof280;
            CursorTy x139 = (CursorTy) case216;
            CursorTy loc224 = (CursorTy) end_y140;
            CursorCursorCursorCursorProd tmp_struct14 =
                                          _copy_AList(end_r172, end_r173_308, loc224, x139);
            CursorTy pvrtmp551 = tmp_struct14.field0;
            CursorTy pvrtmp552 = tmp_struct14.field1;
            CursorTy pvrtmp553 = tmp_struct14.field2;
            CursorTy pvrtmp554 = tmp_struct14.field3;
            CursorTy fltPrd436 = (CursorTy) pvrtmp553;
            CursorTy fltPrd437 = (CursorTy) pvrtmp554;
            CursorTy pvrtmp556 = (CursorTy) fltPrd437;
            CursorTy pvrtmp555 = (CursorTy) fltPrd436;
            CursorTy y141 = (CursorTy) pvrtmp555;
            CursorTy fltPrd438 = (CursorTy) pvrtmp553;
            CursorTy fltPrd439 = (CursorTy) pvrtmp554;
            CursorTy pvrtmp558 = (CursorTy) fltPrd439;
            CursorTy pvrtmp557 = (CursorTy) fltPrd438;
            CursorTy end_y141 = (CursorTy) pvrtmp558;
            CursorTy end_r173_308_309 = (CursorTy) pvrtmp551;
            CursorTy endof281 = (CursorTy) pvrtmp552;

            *(TagTyPacked *) loc171 = 2;

            CursorTy writetag341 = loc171 + 1;
            CursorTy writecur342 = (CursorTy) end_y140;
            CursorTy writecur343 = (CursorTy) end_y141;
            CursorTy pvrtmp560 = (CursorTy) writecur343;
            CursorTy pvrtmp559 = (CursorTy) loc171;
            CursorTy taildc282 = (CursorTy) pvrtmp559;
            CursorTy end_taildc282 = (CursorTy) pvrtmp560;
            CursorTy pvrtmp562 = (CursorTy) end_taildc282;
            CursorTy pvrtmp561 = (CursorTy) taildc282;
            CursorTy fltPrd440 = (CursorTy) pvrtmp561;
            CursorTy fltPrd441 = (CursorTy) pvrtmp562;

            return (CursorCursorCursorCursorProd) {end_r173_308_309, endof281,
                                                   fltPrd440, fltPrd441};
            break;
        }

      case 255:
        {
            CursorTy tmpcur651 = *(CursorTy *) tmpcur532;
            CursorTy tmpaftercur652 = tmpcur532 + 8;
            TagTyPacked tagtmp653 = *(TagTyPacked *) tmpcur651;
            CursorTy tailtmp654 = tmpcur651 + 1;

            tmpval531 = tagtmp653;
            tmpcur532 = tailtmp654;
            goto switch563;
            break;
        }

      case 254:
        {
            CursorTy tmpcur651 = *(CursorTy *) tmpcur532;
            CursorTy tmpaftercur652 = tmpcur532 + 8;
            TagTyPacked tagtmp653 = *(TagTyPacked *) tmpcur651;
            CursorTy tailtmp654 = tmpcur651 + 1;

            tmpval531 = tagtmp653;
            tmpcur532 = tailtmp654;
            goto switch563;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval531");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_AList(CursorTy end_r175, CursorTy arg142)
{
    CursorTy loc174 = (CursorTy) arg142;
    TagTyPacked tmpval564 = *(TagTyPacked *) arg142;
    CursorTy tmpcur565 = arg142 + 1;


  switch572:
    ;
    switch (tmpval564) {

      case 0:
        {
            CursorTy field_cur345 = (CursorTy) tmpcur565;
            CursorTy jump283 = loc174 + 1;
            IntTy fltLitTail284 = (IntTy) 42;

            return (CursorInt64Prod) {jump283, fltLitTail284};
            break;
        }

      case 1:
        {
            CursorTy field_cur346 = (CursorTy) tmpcur565;
            CursorTy case229 = (CursorTy) field_cur346;
            IntTy tmpval566 = *(IntTy *) case229;
            CursorTy tmpcur567 = case229 + sizeof(IntTy);
            IntTy x143 = (IntTy) tmpval566;
            CursorTy end_x143 = (CursorTy) tmpcur567;
            CursorTy jump285 = case229 + 8;
            IntTy fltLitTail286 = (IntTy) 42;

            return (CursorInt64Prod) {jump285, fltLitTail286};
            break;
        }

      case 2:
        {
            CursorTy field_cur348 = (CursorTy) tmpcur565;
            CursorTy case230 = (CursorTy) field_cur348;
            CursorTy x145 = (CursorTy) case230;
            CursorInt64Prod tmp_struct15 =  _traverse_AList(end_r175, x145);
            CursorTy pvrtmp568 = tmp_struct15.field0;
            IntTy pvrtmp569 = tmp_struct15.field1;
            CursorTy endof287 = (CursorTy) pvrtmp568;
            IntTy y147 = (IntTy) pvrtmp569;
            CursorTy case231 = (CursorTy) endof287;
            CursorTy x146 = (CursorTy) case231;
            CursorInt64Prod tmp_struct16 =  _traverse_AList(end_r175, x146);
            CursorTy pvrtmp570 = tmp_struct16.field0;
            IntTy pvrtmp571 = tmp_struct16.field1;
            CursorTy endof289 = (CursorTy) pvrtmp570;
            IntTy y148 = (IntTy) pvrtmp571;
            IntTy fltLitTail288 = (IntTy) 42;

            return (CursorInt64Prod) {endof289, fltLitTail288};
            break;
        }

      case 255:
        {
            CursorTy tmpcur655 = *(CursorTy *) tmpcur565;
            CursorTy tmpaftercur656 = tmpcur565 + 8;
            TagTyPacked tagtmp657 = *(TagTyPacked *) tmpcur655;
            CursorTy tailtmp658 = tmpcur655 + 1;

            tmpval564 = tagtmp657;
            tmpcur565 = tailtmp658;
            goto switch572;
            break;
        }

      case 254:
        {
            CursorTy tmpcur655 = *(CursorTy *) tmpcur565;
            CursorTy tmpaftercur656 = tmpcur565 + 8;
            TagTyPacked tagtmp657 = *(TagTyPacked *) tmpcur655;
            CursorTy tailtmp658 = tmpcur655 + 1;

            tmpval564 = tagtmp657;
            tmpcur565 = tailtmp658;
            goto switch572;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval564");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Coins(CursorTy end_r178, CursorTy end_r179,
                                         CursorTy loc177, CursorTy arg149)
{
    CursorTy loc176 = (CursorTy) arg149;
    CursorTy loc244 = loc177 + 1;
    CursorTy loc245 = loc244 + 8;
    CursorTy loc246 = loc245 + 8;
    TagTyPacked tmpval573 = *(TagTyPacked *) arg149;
    CursorTy tmpcur574 = arg149 + 1;


  switch595:
    ;
    switch (tmpval573) {

      case 0:
        {
            CursorTy field_cur351 = (CursorTy) tmpcur574;
            CursorTy case238 = (CursorTy) field_cur351;
            IntTy tmpval575 = *(IntTy *) case238;
            CursorTy tmpcur576 = case238 + sizeof(IntTy);
            IntTy x150 = (IntTy) tmpval575;
            CursorTy end_x150 = (CursorTy) tmpcur576;
            CursorTy case239 = (CursorTy) end_x150;
            IntTy tmpval577 = *(IntTy *) case239;
            CursorTy tmpcur578 = case239 + sizeof(IntTy);
            IntTy x151 = (IntTy) tmpval577;
            CursorTy end_x151 = (CursorTy) tmpcur578;
            CursorTy case240 = (CursorTy) end_x151;
            CursorTy x152 = (CursorTy) case240;
            CursorTy jump291 = case239 + 8;
            CursorTy jump290 = case238 + 8;
            CursorCursorCursorCursorProd tmp_struct17 =
                                          _copy_Coins(end_r178, end_r179, loc246, x152);
            CursorTy pvrtmp579 = tmp_struct17.field0;
            CursorTy pvrtmp580 = tmp_struct17.field1;
            CursorTy pvrtmp581 = tmp_struct17.field2;
            CursorTy pvrtmp582 = tmp_struct17.field3;
            CursorTy fltPrd442 = (CursorTy) pvrtmp581;
            CursorTy fltPrd443 = (CursorTy) pvrtmp582;
            CursorTy pvrtmp584 = (CursorTy) fltPrd443;
            CursorTy pvrtmp583 = (CursorTy) fltPrd442;
            CursorTy y155 = (CursorTy) pvrtmp583;
            CursorTy fltPrd444 = (CursorTy) pvrtmp581;
            CursorTy fltPrd445 = (CursorTy) pvrtmp582;
            CursorTy pvrtmp586 = (CursorTy) fltPrd445;
            CursorTy pvrtmp585 = (CursorTy) fltPrd444;
            CursorTy end_y155 = (CursorTy) pvrtmp586;
            CursorTy end_r179_310 = (CursorTy) pvrtmp579;
            CursorTy endof292 = (CursorTy) pvrtmp580;

            *(TagTyPacked *) loc177 = 0;

            CursorTy writetag355 = loc177 + 1;

            *(IntTy *) writetag355 = x150;

            CursorTy writecur356 = writetag355 + sizeof(IntTy);

            *(IntTy *) writecur356 = x151;

            CursorTy writecur357 = writecur356 + sizeof(IntTy);
            CursorTy writecur358 = (CursorTy) end_y155;
            CursorTy pvrtmp588 = (CursorTy) writecur358;
            CursorTy pvrtmp587 = (CursorTy) loc177;
            CursorTy taildc293 = (CursorTy) pvrtmp587;
            CursorTy end_taildc293 = (CursorTy) pvrtmp588;
            CursorTy pvrtmp590 = (CursorTy) end_taildc293;
            CursorTy pvrtmp589 = (CursorTy) taildc293;
            CursorTy fltPrd446 = (CursorTy) pvrtmp589;
            CursorTy fltPrd447 = (CursorTy) pvrtmp590;

            return (CursorCursorCursorCursorProd) {end_r179_310, endof292,
                                                   fltPrd446, fltPrd447};
            break;
        }

      case 1:
        {
            CursorTy field_cur360 = (CursorTy) tmpcur574;
            CursorTy jump294 = loc176 + 1;

            *(TagTyPacked *) loc177 = 1;

            CursorTy writetag361 = loc177 + 1;
            CursorTy pvrtmp592 = (CursorTy) writetag361;
            CursorTy pvrtmp591 = (CursorTy) loc177;
            CursorTy taildc295 = (CursorTy) pvrtmp591;
            CursorTy end_taildc295 = (CursorTy) pvrtmp592;
            CursorTy pvrtmp594 = (CursorTy) end_taildc295;
            CursorTy pvrtmp593 = (CursorTy) taildc295;
            CursorTy fltPrd448 = (CursorTy) pvrtmp593;
            CursorTy fltPrd449 = (CursorTy) pvrtmp594;

            return (CursorCursorCursorCursorProd) {end_r179, jump294, fltPrd448,
                                                   fltPrd449};
            break;
        }

      case 255:
        {
            CursorTy tmpcur659 = *(CursorTy *) tmpcur574;
            CursorTy tmpaftercur660 = tmpcur574 + 8;
            TagTyPacked tagtmp661 = *(TagTyPacked *) tmpcur659;
            CursorTy tailtmp662 = tmpcur659 + 1;

            tmpval573 = tagtmp661;
            tmpcur574 = tailtmp662;
            goto switch595;
            break;
        }

      case 254:
        {
            CursorTy tmpcur659 = *(CursorTy *) tmpcur574;
            CursorTy tmpaftercur660 = tmpcur574 + 8;
            TagTyPacked tagtmp661 = *(TagTyPacked *) tmpcur659;
            CursorTy tailtmp662 = tmpcur659 + 1;

            tmpval573 = tagtmp661;
            tmpcur574 = tailtmp662;
            goto switch595;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval573");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Coins(CursorTy end_r181, CursorTy arg156)
{
    CursorTy loc180 = (CursorTy) arg156;
    TagTyPacked tmpval596 = *(TagTyPacked *) arg156;
    CursorTy tmpcur597 = arg156 + 1;


  switch604:
    ;
    switch (tmpval596) {

      case 0:
        {
            CursorTy field_cur363 = (CursorTy) tmpcur597;
            CursorTy case255 = (CursorTy) field_cur363;
            IntTy tmpval598 = *(IntTy *) case255;
            CursorTy tmpcur599 = case255 + sizeof(IntTy);
            IntTy x157 = (IntTy) tmpval598;
            CursorTy end_x157 = (CursorTy) tmpcur599;
            CursorTy case256 = (CursorTy) end_x157;
            IntTy tmpval600 = *(IntTy *) case256;
            CursorTy tmpcur601 = case256 + sizeof(IntTy);
            IntTy x158 = (IntTy) tmpval600;
            CursorTy end_x158 = (CursorTy) tmpcur601;
            CursorTy case257 = (CursorTy) end_x158;
            CursorTy x159 = (CursorTy) case257;
            CursorTy jump297 = case256 + 8;
            CursorTy jump296 = case255 + 8;
            CursorInt64Prod tmp_struct18 =  _traverse_Coins(end_r181, x159);
            CursorTy pvrtmp602 = tmp_struct18.field0;
            IntTy pvrtmp603 = tmp_struct18.field1;
            CursorTy endof299 = (CursorTy) pvrtmp602;
            IntTy y162 = (IntTy) pvrtmp603;
            IntTy fltLitTail298 = (IntTy) 42;

            return (CursorInt64Prod) {endof299, fltLitTail298};
            break;
        }

      case 1:
        {
            CursorTy field_cur367 = (CursorTy) tmpcur597;
            CursorTy jump300 = loc180 + 1;
            IntTy fltLitTail301 = (IntTy) 42;

            return (CursorInt64Prod) {jump300, fltLitTail301};
            break;
        }

      case 255:
        {
            CursorTy tmpcur663 = *(CursorTy *) tmpcur597;
            CursorTy tmpaftercur664 = tmpcur597 + 8;
            TagTyPacked tagtmp665 = *(TagTyPacked *) tmpcur663;
            CursorTy tailtmp666 = tmpcur663 + 1;

            tmpval596 = tagtmp665;
            tmpcur597 = tailtmp666;
            goto switch604;
            break;
        }

      case 254:
        {
            CursorTy tmpcur663 = *(CursorTy *) tmpcur597;
            CursorTy tmpaftercur664 = tmpcur597 + 8;
            TagTyPacked tagtmp665 = *(TagTyPacked *) tmpcur663;
            CursorTy tailtmp666 = tmpcur663 + 1;

            tmpval596 = tagtmp665;
            tmpcur597 = tailtmp666;
            goto switch604;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval596");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_AList(CursorTy p605)
{
    TagTyPacked tag606 = *(TagTyPacked *) p605;
    CursorTy tail607 = p605 + 1;


  switch617:
    ;
    switch (tag606) {

      case 0:
        {
            PtrTy ptr608 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr608)->field0 = tag606;
            return (PtrCursorProd) {ptr608, tail607};
            break;
        }

      case 1:
        {
            IntTy val609 = *(IntTy *) tail607;
            CursorTy tail610 = tail607 + sizeof(IntTy);
            PtrTy ptr611 = ALLOC(sizeof(TagInt64Prod));

            ((TagInt64Prod *) ptr611)->field0 = tag606;
            ((TagInt64Prod *) ptr611)->field1 = val609;
            return (PtrCursorProd) {ptr611, tail610};
            break;
        }

      case 2:
        {
            PtrCursorProd tmp_struct19 =  _unpack_AList(tail607);
            PtrTy ptr612 = tmp_struct19.field0;
            CursorTy tail613 = tmp_struct19.field1;
            PtrCursorProd tmp_struct20 =  _unpack_AList(tail613);
            PtrTy ptr614 = tmp_struct20.field0;
            CursorTy tail615 = tmp_struct20.field1;
            PtrTy ptr616 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr616)->field0 = tag606;
            ((TagCursorCursorProd *) ptr616)->field1 = ptr612;
            ((TagCursorCursorProd *) ptr616)->field2 = ptr614;
            return (PtrCursorProd) {ptr616, tail615};
            break;
        }

      case 255:
        {
            CursorTy tmpcur667 = *(CursorTy *) tail607;
            CursorTy tmpaftercur668 = tail607 + 8;
            TagTyPacked tagtmp669 = *(TagTyPacked *) tmpcur667;
            CursorTy tailtmp670 = tmpcur667 + 1;

            tag606 = tagtmp669;
            tail607 = tailtmp670;
            goto switch617;
            break;
        }

      case 254:
        {
            CursorTy tmpcur667 = *(CursorTy *) tail607;
            CursorTy tmpaftercur668 = tail607 + 8;
            TagTyPacked tagtmp669 = *(TagTyPacked *) tmpcur667;
            CursorTy tailtmp670 = tmpcur667 + 1;

            tag606 = tagtmp669;
            tail607 = tailtmp670;
            goto switch617;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch617");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Coins(CursorTy p618)
{
    TagTyPacked tag619 = *(TagTyPacked *) p618;
    CursorTy tail620 = p618 + 1;


  switch629:
    ;
    switch (tag619) {

      case 0:
        {
            IntTy val621 = *(IntTy *) tail620;
            CursorTy tail622 = tail620 + sizeof(IntTy);
            IntTy val623 = *(IntTy *) tail622;
            CursorTy tail624 = tail622 + sizeof(IntTy);
            PtrCursorProd tmp_struct21 =  _unpack_Coins(tail624);
            PtrTy ptr625 = tmp_struct21.field0;
            CursorTy tail626 = tmp_struct21.field1;
            PtrTy ptr627 = ALLOC(sizeof(TagInt64Int64CursorProd));

            ((TagInt64Int64CursorProd *) ptr627)->field0 = tag619;
            ((TagInt64Int64CursorProd *) ptr627)->field1 = val621;
            ((TagInt64Int64CursorProd *) ptr627)->field2 = val623;
            ((TagInt64Int64CursorProd *) ptr627)->field3 = ptr625;
            return (PtrCursorProd) {ptr627, tail626};
            break;
        }

      case 1:
        {
            PtrTy ptr628 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr628)->field0 = tag619;
            return (PtrCursorProd) {ptr628, tail620};
            break;
        }

      case 255:
        {
            CursorTy tmpcur671 = *(CursorTy *) tail620;
            CursorTy tmpaftercur672 = tail620 + 8;
            TagTyPacked tagtmp673 = *(TagTyPacked *) tmpcur671;
            CursorTy tailtmp674 = tmpcur671 + 1;

            tag619 = tagtmp673;
            tail620 = tailtmp674;
            goto switch629;
            break;
        }

      case 254:
        {
            CursorTy tmpcur671 = *(CursorTy *) tail620;
            CursorTy tmpaftercur672 = tail620 + 8;
            TagTyPacked tagtmp673 = *(TagTyPacked *) tmpcur671;
            CursorTy tailtmp674 = tmpcur671 + 1;

            tag619 = tagtmp673;
            tail620 = tailtmp674;
            goto switch629;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch629");
            exit(1);
        }
    }
}
CursorTy _print_AList(CursorTy p630)
{
    TagTyPacked tag631 = *(TagTyPacked *) p630;
    CursorTy tail632 = p630 + 1;


  switch637:
    ;
    switch (tag631) {

      case 0:
        {
            fputs("(ANil ", stdout);
            fputs(")", stdout);
            return tail632;
            break;
        }

      case 1:
        {
            fputs("(ASing ", stdout);

            IntTy val633 = *(IntTy *) tail632;
            CursorTy tail634 = tail632 + sizeof(IntTy);

            printf("%lld", val633);
            fputs(")", stdout);
            return tail634;
            break;
        }

      case 2:
        {
            fputs("(Append ", stdout);

            CursorTy tail635 =  _print_AList(tail632);

            fputs(" ", stdout);

            CursorTy tail636 =  _print_AList(tail635);

            fputs(")", stdout);
            return tail636;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur675 = *(CursorTy *) tail632;
            CursorTy tmpaftercur676 = tail632 + 8;
            TagTyPacked tagtmp677 = *(TagTyPacked *) tmpcur675;
            CursorTy tailtmp678 = tmpcur675 + 1;

            tag631 = tagtmp677;
            tail632 = tailtmp678;
            goto switch637;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur675 = *(CursorTy *) tail632;
            CursorTy tmpaftercur676 = tail632 + 8;
            TagTyPacked tagtmp677 = *(TagTyPacked *) tmpcur675;
            CursorTy tailtmp678 = tmpcur675 + 1;

            tag631 = tagtmp677;
            tail632 = tailtmp678;
            goto switch637;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch637");
            exit(1);
        }
    }
}
CursorTy _print_Coins(CursorTy p638)
{
    TagTyPacked tag639 = *(TagTyPacked *) p638;
    CursorTy tail640 = p638 + 1;


  switch646:
    ;
    switch (tag639) {

      case 0:
        {
            fputs("(Cons ", stdout);

            IntTy val641 = *(IntTy *) tail640;
            CursorTy tail642 = tail640 + sizeof(IntTy);

            printf("%lld", val641);
            fputs(" ", stdout);

            IntTy val643 = *(IntTy *) tail642;
            CursorTy tail644 = tail642 + sizeof(IntTy);

            printf("%lld", val643);
            fputs(" ", stdout);

            CursorTy tail645 =  _print_Coins(tail644);

            fputs(")", stdout);
            return tail645;
            break;
        }

      case 1:
        {
            fputs("(Nil ", stdout);
            fputs(")", stdout);
            return tail640;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur679 = *(CursorTy *) tail640;
            CursorTy tmpaftercur680 = tail640 + 8;
            TagTyPacked tagtmp681 = *(TagTyPacked *) tmpcur679;
            CursorTy tailtmp682 = tmpcur679 + 1;

            tag639 = tagtmp681;
            tail640 = tailtmp682;
            goto switch646;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur679 = *(CursorTy *) tail640;
            CursorTy tmpaftercur680 = tail640 + 8;
            TagTyPacked tagtmp681 = *(TagTyPacked *) tmpcur679;
            CursorTy tailtmp682 = tmpcur679 + 1;

            tag639 = tagtmp681;
            tail640 = tailtmp682;
            goto switch646;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch646");
            exit(1);
        }
    }
}
void __main_expr()
{
    RegionTy *region450 = alloc_region(global_init_biginf_buf_size);
    CursorTy r188 = region450->start_ptr;
    IntTy sizeof_end_r188451 = global_init_biginf_buf_size;
    CursorTy end_r188 = r188 + sizeof_end_r188451;
    UT_array *coins53;

    utarray_new(coins53, &Int64Int64Prod_icd);

    IntTy pvrtmp453 = (IntTy) 55;
    IntTy pvrtmp452 = (IntTy) 250;
    Int64Int64Prod tmp33 = (Int64Int64Prod) {pvrtmp452, pvrtmp453};

    utarray_push_back(coins53, &tmp33);

    IntTy pvrtmp455 = (IntTy) 88;
    IntTy pvrtmp454 = (IntTy) 100;
    Int64Int64Prod tmp32 = (Int64Int64Prod) {pvrtmp454, pvrtmp455};

    utarray_push_back(coins53, &tmp32);

    IntTy pvrtmp457 = (IntTy) 88;
    IntTy pvrtmp456 = (IntTy) 25;
    Int64Int64Prod tmp31 = (Int64Int64Prod) {pvrtmp456, pvrtmp457};

    utarray_push_back(coins53, &tmp31);

    IntTy pvrtmp459 = (IntTy) 99;
    IntTy pvrtmp458 = (IntTy) 10;
    Int64Int64Prod tmp30 = (Int64Int64Prod) {pvrtmp458, pvrtmp459};

    utarray_push_back(coins53, &tmp30);

    IntTy pvrtmp461 = (IntTy) 122;
    IntTy pvrtmp460 = (IntTy) 5;
    Int64Int64Prod tmp29 = (Int64Int64Prod) {pvrtmp460, pvrtmp461};

    utarray_push_back(coins53, &tmp29);

    IntTy pvrtmp463 = (IntTy) 177;
    IntTy pvrtmp462 = (IntTy) 1;
    Int64Int64Prod tmp28 = (Int64Int64Prod) {pvrtmp462, pvrtmp463};

    utarray_push_back(coins53, &tmp28);

    IntTy amt60 = global_size_param;
    CursorTy loc185 = (CursorTy) r188;
    CursorTy pvrtmp473;
    CursorTy pvrtmp474;
    CursorTy pvrtmp475;
    UT_array *times25;

    utarray_new(times25, &double_icd);

    struct timespec begin_pvrtmp473;
    struct timespec end_pvrtmp473;

    for (long long iters_pvrtmp473 = 0; iters_pvrtmp473 < global_iters_param;
         iters_pvrtmp473++) {
        if (iters_pvrtmp473 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp473);

        CursorCursorCursorProd tmp_struct22 =
                                payA(end_r188, loc185, amt60, coins53);
        CursorTy pvrtmp464 = tmp_struct22.field0;
        CursorTy pvrtmp465 = tmp_struct22.field1;
        CursorTy pvrtmp466 = tmp_struct22.field2;
        CursorTy fltPrd398 = (CursorTy) pvrtmp465;
        CursorTy fltPrd399 = (CursorTy) pvrtmp466;
        CursorTy pvrtmp468 = (CursorTy) fltPrd399;
        CursorTy pvrtmp467 = (CursorTy) fltPrd398;
        CursorTy tailapp302 = (CursorTy) pvrtmp467;
        CursorTy fltPrd400 = (CursorTy) pvrtmp465;
        CursorTy fltPrd401 = (CursorTy) pvrtmp466;
        CursorTy pvrtmp470 = (CursorTy) fltPrd401;
        CursorTy pvrtmp469 = (CursorTy) fltPrd400;
        CursorTy end_tailapp302 = (CursorTy) pvrtmp470;
        CursorTy end_r188_311 = (CursorTy) pvrtmp464;
        CursorTy pvrtmp472 = (CursorTy) end_tailapp302;
        CursorTy pvrtmp471 = (CursorTy) tailapp302;
        CursorTy fltPrd402 = (CursorTy) pvrtmp471;
        CursorTy fltPrd403 = (CursorTy) pvrtmp472;

        pvrtmp473 = end_r188_311;
        pvrtmp474 = fltPrd402;
        pvrtmp475 = fltPrd403;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp473);
        if (iters_pvrtmp473 != global_iters_param - 1)
            restore_alloc_state();

        double batchtime23 = difftimespecs(&begin_pvrtmp473, &end_pvrtmp473);

        utarray_push_back(times25, &batchtime23);
    }
    utarray_sort(times25, compare_doubles);

    double *tmp26 = (double *) utarray_eltptr(times25, global_iters_param / 2);
    double selftimed24 = *tmp26;

    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("SELFTIMED: %e\n", selftimed24);

    CursorTy pvrtmp478 = (CursorTy) pvrtmp475;
    CursorTy pvrtmp477 = (CursorTy) pvrtmp474;
    CursorTy pvrtmp476 = (CursorTy) pvrtmp473;
    CursorTy fltPrd404 = (CursorTy) pvrtmp477;
    CursorTy fltPrd405 = (CursorTy) pvrtmp478;
    CursorTy pvrtmp480 = (CursorTy) fltPrd405;
    CursorTy pvrtmp479 = (CursorTy) fltPrd404;
    CursorTy tr61 = (CursorTy) pvrtmp479;
    CursorTy fltPrd406 = (CursorTy) pvrtmp477;
    CursorTy fltPrd407 = (CursorTy) pvrtmp478;
    CursorTy pvrtmp482 = (CursorTy) fltPrd407;
    CursorTy pvrtmp481 = (CursorTy) fltPrd406;
    CursorTy end_tr61 = (CursorTy) pvrtmp482;
    CursorTy end_r188_311 = (CursorTy) pvrtmp476;
    CursorInt64Prod tmp_struct27 =  lenA(end_r188, tr61);
    CursorTy pvrtmp483 = tmp_struct27.field0;
    IntTy pvrtmp484 = tmp_struct27.field1;
    CursorTy endof304 = (CursorTy) pvrtmp483;
    IntTy tailapp303 = (IntTy) pvrtmp484;

    printf("%lld", tailapp303);
    fputs("\n", stdout);
    free_symtable();
    return;
}
