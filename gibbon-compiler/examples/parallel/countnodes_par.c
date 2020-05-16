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
typedef struct TagInt64Int64CursorCursorProd_struct {
            TagTyPacked field0;
            IntTy field1;
            IntTy field2;
            CursorTy field3;
            CursorTy field4;
        } TagInt64Int64CursorCursorProd;
typedef struct TagSymProd_struct {
            TagTyPacked field0;
            SymTy field1;
        } TagSymProd;
typedef struct TagSymCursorProd_struct {
            TagTyPacked field0;
            SymTy field1;
            CursorTy field2;
        } TagSymCursorProd;
typedef struct TagCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
        } TagCursorProd;
typedef struct TagCursorSymProd_struct {
            TagTyPacked field0;
            CursorTy field1;
            SymTy field2;
        } TagCursorSymProd;
typedef struct TagCursorCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
            CursorTy field2;
        } TagCursorCursorProd;
typedef struct TagCursorCursorCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
            CursorTy field2;
            CursorTy field3;
        } TagCursorCursorCursorProd;
typedef struct SymCursorProd_struct {
            SymTy field0;
            CursorTy field1;
        } SymCursorProd;
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
CursorInt64Prod formals(CursorTy end_r1821, CursorTy f77);
CursorInt64Prod loopSyms(CursorTy end_r1823, CursorTy ls82);
CursorInt64Prod datum(CursorTy end_r1825, CursorTy d85);
CursorInt64Prod expr(CursorTy end_r1827, CursorTy e87);
CursorInt64Prod top(CursorTy end_r1829, CursorTy e115);
CursorInt64Prod loopLVBIND(CursorTy end_r1831, CursorTy ls122);
CursorInt64Prod loopLambdaCase(CursorTy end_r1833, CursorTy ls126);
CursorInt64Prod loopExpr(CursorTy end_r1835, CursorTy ls130);
CursorInt64Prod loopTopLvl(CursorTy end_r1837, CursorTy ls133);
CursorInt64Prod countnodes(CursorTy end_r1839, CursorTy e0136);
IntTy par_loopTopLvl(CursorTy end_r1841, IntTy height61, CursorTy ls62);
IntTy par_top(CursorTy end_r1843, IntTy height68, CursorTy e69);
IntTy par_countnodes(CursorTy end_r1845, CursorTy e076);
CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r1848,
                                           CursorTy end_r1849, CursorTy loc1847,
                                           CursorTy arg1527);
CursorInt64Prod _traverse_ListSym(CursorTy end_r1851, CursorTy arg1532);
CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r1854,
                                            CursorTy end_r1855,
                                            CursorTy loc1853, CursorTy arg1537);
CursorInt64Prod _traverse_ListExpr(CursorTy end_r1857, CursorTy arg1542);
CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r1860,
                                              CursorTy end_r1861,
                                              CursorTy loc1859,
                                              CursorTy arg1547);
CursorInt64Prod _traverse_ListToplvl(CursorTy end_r1863, CursorTy arg1566);
CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r1866,
                                           CursorTy end_r1867, CursorTy loc1865,
                                           CursorTy arg1585);
CursorInt64Prod _traverse_Formals(CursorTy end_r1869, CursorTy arg1594);
CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r1872, CursorTy end_r1873,
                                         CursorTy loc1871, CursorTy arg1603);
CursorInt64Prod _traverse_Datum(CursorTy end_r1875, CursorTy arg1606);
CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r1878,
                                              CursorTy end_r1879,
                                              CursorTy loc1877,
                                              CursorTy arg1609);
CursorInt64Prod _traverse_LAMBDACASE(CursorTy end_r1881, CursorTy arg1616);
CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r1884,
                                          CursorTy end_r1885, CursorTy loc1883,
                                          CursorTy arg1623);
CursorInt64Prod _traverse_LVBIND(CursorTy end_r1887, CursorTy arg1630);
CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r1890, CursorTy end_r1891,
                                        CursorTy loc1889, CursorTy arg1637);
CursorInt64Prod _traverse_Expr(CursorTy end_r1893, CursorTy arg1692);
CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r1896,
                                          CursorTy end_r1897, CursorTy loc1895,
                                          CursorTy arg1747);
CursorInt64Prod _traverse_Toplvl(CursorTy end_r1899, CursorTy arg1760);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_ListSym(CursorTy end_r1902, CursorTy end_r1903,
                                  CursorTy loc1901, CursorTy arg1414);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_ListExpr(CursorTy end_r1906, CursorTy end_r1907,
                                   CursorTy loc1905, CursorTy arg1419);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_ListToplvl(CursorTy end_r1910, CursorTy end_r1911,
                                     CursorTy loc1909, CursorTy arg1424);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Formals(CursorTy end_r1914, CursorTy end_r1915,
                                  CursorTy loc1913, CursorTy arg1433);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Datum(CursorTy end_r1918,
                                                             CursorTy end_r1919,
                                                             CursorTy loc1917,
                                                             CursorTy arg1442);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_LAMBDACASE(CursorTy end_r1922, CursorTy end_r1923,
                                     CursorTy loc1921, CursorTy arg1445);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_LVBIND(CursorTy end_r1926, CursorTy end_r1927,
                                 CursorTy loc1925, CursorTy arg1452);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Expr(CursorTy end_r1930,
                                                            CursorTy end_r1931,
                                                            CursorTy loc1929,
                                                            CursorTy arg1459);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Toplvl(CursorTy end_r1934, CursorTy end_r1935,
                                 CursorTy loc1933, CursorTy arg1514);
PtrCursorProd _unpack_ListSym(CursorTy p6246);
PtrCursorProd _unpack_ListExpr(CursorTy p6256);
PtrCursorProd _unpack_ListToplvl(CursorTy p6266);
PtrCursorProd _unpack_Formals(CursorTy p6292);
PtrCursorProd _unpack_Datum(CursorTy p6307);
PtrCursorProd _unpack_LAMBDACASE(CursorTy p6314);
PtrCursorProd _unpack_LVBIND(CursorTy p6326);
PtrCursorProd _unpack_Expr(CursorTy p6338);
PtrCursorProd _unpack_Toplvl(CursorTy p6414);
CursorTy _print_ListSym(CursorTy p6434);
CursorTy _print_ListExpr(CursorTy p6441);
CursorTy _print_ListToplvl(CursorTy p6447);
CursorTy _print_Formals(CursorTy p6462);
CursorTy _print_Datum(CursorTy p6472);
CursorTy _print_LAMBDACASE(CursorTy p6478);
CursorTy _print_LVBIND(CursorTy p6485);
CursorTy _print_Expr(CursorTy p6492);
CursorTy _print_Toplvl(CursorTy p6528);
CursorInt64Prod formals(CursorTy end_r1821, CursorTy f77)
{
    CursorTy loc1820 = (CursorTy) f77;
    TagTyPacked tmpval4862 = *(TagTyPacked *) f77;
    CursorTy tmpcur4863 = f77 + 1;


  switch4872:
    ;
    switch (tmpval4862) {

      case 0:
        {
            CursorTy field_cur3472 = (CursorTy) tmpcur4863;
            CursorTy case1943 = (CursorTy) field_cur3472;
            CursorTy ls78 = (CursorTy) case1943;
            CursorInt64Prod tmp_struct0 =  loopSyms(end_r1821, ls78);
            CursorTy pvrtmp4864 = tmp_struct0.field0;
            IntTy pvrtmp4865 = tmp_struct0.field1;
            CursorTy endof2973 = (CursorTy) pvrtmp4864;
            IntTy fltPrm345 = (IntTy) pvrtmp4865;
            IntTy tailprim2974 = 1 + fltPrm345;

            return (CursorInt64Prod) {endof2973, tailprim2974};
            break;
        }

      case 1:
        {
            CursorTy field_cur3474 = (CursorTy) tmpcur4863;
            CursorTy case1946 = (CursorTy) field_cur3474;
            CursorTy ls79 = (CursorTy) case1946;
            CursorInt64Prod tmp_struct1 =  loopSyms(end_r1821, ls79);
            CursorTy pvrtmp4866 = tmp_struct1.field0;
            IntTy pvrtmp4867 = tmp_struct1.field1;
            CursorTy endof2976 = (CursorTy) pvrtmp4866;
            IntTy fltPrm347 = (IntTy) pvrtmp4867;
            CursorTy case1947 = (CursorTy) endof2976;
            CursorTy jump2975 = case1947 + 8;
            SymTy tmpval4868 = *(SymTy *) case1947;
            CursorTy tmpcur4869 = case1947 + sizeof(SymTy);
            SymTy s80 = (SymTy) tmpval4868;
            CursorTy end_s80 = (CursorTy) tmpcur4869;
            IntTy fltPrm346 = fltPrm347 + 0;
            IntTy tailprim2977 = 1 + fltPrm346;

            return (CursorInt64Prod) {jump2975, tailprim2977};
            break;
        }

      case 2:
        {
            CursorTy field_cur3477 = (CursorTy) tmpcur4863;
            CursorTy case1950 = (CursorTy) field_cur3477;
            SymTy tmpval4870 = *(SymTy *) case1950;
            CursorTy tmpcur4871 = case1950 + sizeof(SymTy);
            SymTy s81 = (SymTy) tmpval4870;
            CursorTy end_s81 = (CursorTy) tmpcur4871;
            CursorTy jump2978 = case1950 + 8;
            IntTy tailprim2979 = 1 + 0;

            return (CursorInt64Prod) {jump2978, tailprim2979};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6538 = *(CursorTy *) tmpcur4863;
            CursorTy tmpaftercur6539 = tmpcur4863 + 8;
            TagTyPacked tagtmp6540 = *(TagTyPacked *) tmpcur6538;
            CursorTy tailtmp6541 = tmpcur6538 + 1;

            tmpval4862 = tagtmp6540;
            tmpcur4863 = tailtmp6541;
            goto switch4872;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6538 = *(CursorTy *) tmpcur4863;
            CursorTy tmpaftercur6539 = tmpcur4863 + 8;
            TagTyPacked tagtmp6540 = *(TagTyPacked *) tmpcur6538;
            CursorTy tailtmp6541 = tmpcur6538 + 1;

            tmpval4862 = tagtmp6540;
            tmpcur4863 = tailtmp6541;
            goto switch4872;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4862");
            exit(1);
        }
    }
}
CursorInt64Prod loopSyms(CursorTy end_r1823, CursorTy ls82)
{
    CursorTy loc1822 = (CursorTy) ls82;
    TagTyPacked tmpval4873 = *(TagTyPacked *) ls82;
    CursorTy tmpcur4874 = ls82 + 1;


  switch4879:
    ;
    switch (tmpval4873) {

      case 0:
        {
            CursorTy field_cur3479 = (CursorTy) tmpcur4874;
            CursorTy case1953 = (CursorTy) field_cur3479;
            SymTy tmpval4875 = *(SymTy *) case1953;
            CursorTy tmpcur4876 = case1953 + sizeof(SymTy);
            SymTy s83 = (SymTy) tmpval4875;
            CursorTy end_s83 = (CursorTy) tmpcur4876;
            CursorTy case1954 = (CursorTy) end_s83;
            CursorTy ls84 = (CursorTy) case1954;
            CursorTy jump2980 = case1953 + 8;
            CursorInt64Prod tmp_struct2 =  loopSyms(end_r1823, ls84);
            CursorTy pvrtmp4877 = tmp_struct2.field0;
            IntTy pvrtmp4878 = tmp_struct2.field1;
            CursorTy endof2981 = (CursorTy) pvrtmp4877;
            IntTy fltPrm349 = (IntTy) pvrtmp4878;
            IntTy fltPrm348 = 0 + fltPrm349;
            IntTy tailprim2982 = 1 + fltPrm348;

            return (CursorInt64Prod) {endof2981, tailprim2982};
            break;
        }

      case 1:
        {
            CursorTy field_cur3482 = (CursorTy) tmpcur4874;
            CursorTy jump2983 = loc1822 + 1;
            IntTy fltLitTail2984 = (IntTy) 1;

            return (CursorInt64Prod) {jump2983, fltLitTail2984};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6542 = *(CursorTy *) tmpcur4874;
            CursorTy tmpaftercur6543 = tmpcur4874 + 8;
            TagTyPacked tagtmp6544 = *(TagTyPacked *) tmpcur6542;
            CursorTy tailtmp6545 = tmpcur6542 + 1;

            tmpval4873 = tagtmp6544;
            tmpcur4874 = tailtmp6545;
            goto switch4879;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6542 = *(CursorTy *) tmpcur4874;
            CursorTy tmpaftercur6543 = tmpcur4874 + 8;
            TagTyPacked tagtmp6544 = *(TagTyPacked *) tmpcur6542;
            CursorTy tailtmp6545 = tmpcur6542 + 1;

            tmpval4873 = tagtmp6544;
            tmpcur4874 = tailtmp6545;
            goto switch4879;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4873");
            exit(1);
        }
    }
}
CursorInt64Prod datum(CursorTy end_r1825, CursorTy d85)
{
    CursorTy loc1824 = (CursorTy) d85;
    TagTyPacked tmpval4880 = *(TagTyPacked *) d85;
    CursorTy tmpcur4881 = d85 + 1;


  switch4884:
    ;
    switch (tmpval4880) {

      case 0:
        {
            CursorTy field_cur3483 = (CursorTy) tmpcur4881;
            CursorTy case1959 = (CursorTy) field_cur3483;
            IntTy tmpval4882 = *(IntTy *) case1959;
            CursorTy tmpcur4883 = case1959 + sizeof(IntTy);
            IntTy i86 = (IntTy) tmpval4882;
            CursorTy end_i86 = (CursorTy) tmpcur4883;
            CursorTy jump2985 = case1959 + 8;
            IntTy tailprim2986 = 1 + 0;

            return (CursorInt64Prod) {jump2985, tailprim2986};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6546 = *(CursorTy *) tmpcur4881;
            CursorTy tmpaftercur6547 = tmpcur4881 + 8;
            TagTyPacked tagtmp6548 = *(TagTyPacked *) tmpcur6546;
            CursorTy tailtmp6549 = tmpcur6546 + 1;

            tmpval4880 = tagtmp6548;
            tmpcur4881 = tailtmp6549;
            goto switch4884;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6546 = *(CursorTy *) tmpcur4881;
            CursorTy tmpaftercur6547 = tmpcur4881 + 8;
            TagTyPacked tagtmp6548 = *(TagTyPacked *) tmpcur6546;
            CursorTy tailtmp6549 = tmpcur6546 + 1;

            tmpval4880 = tagtmp6548;
            tmpcur4881 = tailtmp6549;
            goto switch4884;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4880");
            exit(1);
        }
    }
}
CursorInt64Prod expr(CursorTy end_r1827, CursorTy e87)
{
    CursorTy loc1826 = (CursorTy) e87;
    TagTyPacked tmpval4885 = *(TagTyPacked *) e87;
    CursorTy tmpcur4886 = e87 + 1;


  switch4941:
    ;
    switch (tmpval4885) {

      case 0:
        {
            CursorTy field_cur3485 = (CursorTy) tmpcur4886;
            CursorTy case1962 = (CursorTy) field_cur3485;
            SymTy tmpval4887 = *(SymTy *) case1962;
            CursorTy tmpcur4888 = case1962 + sizeof(SymTy);
            SymTy s88 = (SymTy) tmpval4887;
            CursorTy end_s88 = (CursorTy) tmpcur4888;
            CursorTy jump2987 = case1962 + 8;
            IntTy tailprim2988 = 1 + 0;

            return (CursorInt64Prod) {jump2987, tailprim2988};
            break;
        }

      case 14:
        {
            CursorTy field_cur3487 = (CursorTy) tmpcur4886;
            CursorTy case1963 = (CursorTy) field_cur3487;
            SymTy tmpval4889 = *(SymTy *) case1963;
            CursorTy tmpcur4890 = case1963 + sizeof(SymTy);
            SymTy s89 = (SymTy) tmpval4889;
            CursorTy end_s89 = (CursorTy) tmpcur4890;
            CursorTy jump2989 = case1963 + 8;
            IntTy tailprim2990 = 1 + 0;

            return (CursorInt64Prod) {jump2989, tailprim2990};
            break;
        }

      case 15:
        {
            CursorTy field_cur3489 = (CursorTy) tmpcur4886;
            CursorTy case1964 = (CursorTy) field_cur3489;
            SymTy tmpval4891 = *(SymTy *) case1964;
            CursorTy tmpcur4892 = case1964 + sizeof(SymTy);
            SymTy s90 = (SymTy) tmpval4891;
            CursorTy end_s90 = (CursorTy) tmpcur4892;
            CursorTy jump2991 = case1964 + 8;
            IntTy tailprim2992 = 1 + 0;

            return (CursorInt64Prod) {jump2991, tailprim2992};
            break;
        }

      case 16:
        {
            CursorTy field_cur3491 = (CursorTy) tmpcur4886;
            CursorTy case1965 = (CursorTy) field_cur3491;
            SymTy tmpval4893 = *(SymTy *) case1965;
            CursorTy tmpcur4894 = case1965 + sizeof(SymTy);
            SymTy s91 = (SymTy) tmpval4893;
            CursorTy end_s91 = (CursorTy) tmpcur4894;
            CursorTy jump2993 = case1965 + 8;
            IntTy tailprim2994 = 1 + 0;

            return (CursorInt64Prod) {jump2993, tailprim2994};
            break;
        }

      case 17:
        {
            CursorTy field_cur3493 = (CursorTy) tmpcur4886;
            CursorTy jump2995 = loc1826 + 1;
            IntTy fltLitTail2996 = (IntTy) 1;

            return (CursorInt64Prod) {jump2995, fltLitTail2996};
            break;
        }

      case 9:
        {
            CursorTy field_cur3494 = (CursorTy) tmpcur4886;
            CursorTy case1966 = (CursorTy) field_cur3494;
            CursorTy d92 = (CursorTy) case1966;
            CursorInt64Prod tmp_struct3 =  datum(end_r1827, d92);
            CursorTy pvrtmp4895 = tmp_struct3.field0;
            IntTy pvrtmp4896 = tmp_struct3.field1;
            CursorTy endof2997 = (CursorTy) pvrtmp4895;
            IntTy fltPrm350 = (IntTy) pvrtmp4896;
            IntTy tailprim2998 = 1 + fltPrm350;

            return (CursorInt64Prod) {endof2997, tailprim2998};
            break;
        }

      case 10:
        {
            CursorTy field_cur3496 = (CursorTy) tmpcur4886;
            CursorTy case1969 = (CursorTy) field_cur3496;
            CursorTy d93 = (CursorTy) case1969;
            CursorInt64Prod tmp_struct4 =  datum(end_r1827, d93);
            CursorTy pvrtmp4897 = tmp_struct4.field0;
            IntTy pvrtmp4898 = tmp_struct4.field1;
            CursorTy endof2999 = (CursorTy) pvrtmp4897;
            IntTy fltPrm351 = (IntTy) pvrtmp4898;
            IntTy tailprim3000 = 1 + fltPrm351;

            return (CursorInt64Prod) {endof2999, tailprim3000};
            break;
        }

      case 11:
        {
            CursorTy field_cur3498 = (CursorTy) tmpcur4886;
            CursorTy case1972 = (CursorTy) field_cur3498;
            CursorTy d94 = (CursorTy) case1972;
            CursorInt64Prod tmp_struct5 =  datum(end_r1827, d94);
            CursorTy pvrtmp4899 = tmp_struct5.field0;
            IntTy pvrtmp4900 = tmp_struct5.field1;
            CursorTy endof3001 = (CursorTy) pvrtmp4899;
            IntTy fltPrm352 = (IntTy) pvrtmp4900;
            IntTy tailprim3002 = 1 + fltPrm352;

            return (CursorInt64Prod) {endof3001, tailprim3002};
            break;
        }

      case 1:
        {
            CursorTy field_cur3500 = (CursorTy) tmpcur4886;
            CursorTy case1975 = (CursorTy) field_cur3500;
            CursorTy f95 = (CursorTy) case1975;
            CursorInt64Prod tmp_struct6 =  formals(end_r1827, f95);
            CursorTy pvrtmp4901 = tmp_struct6.field0;
            IntTy pvrtmp4902 = tmp_struct6.field1;
            CursorTy endof3003 = (CursorTy) pvrtmp4901;
            IntTy fltPrm354 = (IntTy) pvrtmp4902;
            CursorTy case1976 = (CursorTy) endof3003;
            CursorTy lse96 = (CursorTy) case1976;
            CursorInt64Prod tmp_struct7 =  loopExpr(end_r1827, lse96);
            CursorTy pvrtmp4903 = tmp_struct7.field0;
            IntTy pvrtmp4904 = tmp_struct7.field1;
            CursorTy endof3004 = (CursorTy) pvrtmp4903;
            IntTy fltPrm355 = (IntTy) pvrtmp4904;
            IntTy fltPrm353 = fltPrm354 + fltPrm355;
            IntTy tailprim3005 = 1 + fltPrm353;

            return (CursorInt64Prod) {endof3004, tailprim3005};
            break;
        }

      case 2:
        {
            CursorTy field_cur3503 = (CursorTy) tmpcur4886;
            CursorTy case1981 = (CursorTy) field_cur3503;
            CursorTy cases97 = (CursorTy) case1981;
            CursorInt64Prod tmp_struct8 =  loopLambdaCase(end_r1827, cases97);
            CursorTy pvrtmp4905 = tmp_struct8.field0;
            IntTy pvrtmp4906 = tmp_struct8.field1;
            CursorTy endof3006 = (CursorTy) pvrtmp4905;
            IntTy fltPrm356 = (IntTy) pvrtmp4906;
            IntTy tailprim3007 = 1 + fltPrm356;

            return (CursorInt64Prod) {endof3006, tailprim3007};
            break;
        }

      case 6:
        {
            CursorTy field_cur3505 = (CursorTy) tmpcur4886;
            CursorTy case1984 = (CursorTy) field_cur3505;
            CursorTy binds98 = (CursorTy) case1984;
            CursorInt64Prod tmp_struct9 =  loopLVBIND(end_r1827, binds98);
            CursorTy pvrtmp4907 = tmp_struct9.field0;
            IntTy pvrtmp4908 = tmp_struct9.field1;
            CursorTy endof3008 = (CursorTy) pvrtmp4907;
            IntTy fltPrm358 = (IntTy) pvrtmp4908;
            CursorTy case1985 = (CursorTy) endof3008;
            CursorTy body99 = (CursorTy) case1985;
            CursorInt64Prod tmp_struct10 =  loopExpr(end_r1827, body99);
            CursorTy pvrtmp4909 = tmp_struct10.field0;
            IntTy pvrtmp4910 = tmp_struct10.field1;
            CursorTy endof3009 = (CursorTy) pvrtmp4909;
            IntTy fltPrm359 = (IntTy) pvrtmp4910;
            IntTy fltPrm357 = fltPrm358 + fltPrm359;
            IntTy tailprim3010 = 1 + fltPrm357;

            return (CursorInt64Prod) {endof3009, tailprim3010};
            break;
        }

      case 7:
        {
            CursorTy field_cur3508 = (CursorTy) tmpcur4886;
            CursorTy case1990 = (CursorTy) field_cur3508;
            CursorTy binds100 = (CursorTy) case1990;
            CursorInt64Prod tmp_struct11 =  loopLVBIND(end_r1827, binds100);
            CursorTy pvrtmp4911 = tmp_struct11.field0;
            IntTy pvrtmp4912 = tmp_struct11.field1;
            CursorTy endof3011 = (CursorTy) pvrtmp4911;
            IntTy fltPrm361 = (IntTy) pvrtmp4912;
            CursorTy case1991 = (CursorTy) endof3011;
            CursorTy body101 = (CursorTy) case1991;
            CursorInt64Prod tmp_struct12 =  loopExpr(end_r1827, body101);
            CursorTy pvrtmp4913 = tmp_struct12.field0;
            IntTy pvrtmp4914 = tmp_struct12.field1;
            CursorTy endof3012 = (CursorTy) pvrtmp4913;
            IntTy fltPrm362 = (IntTy) pvrtmp4914;
            IntTy fltPrm360 = fltPrm361 + fltPrm362;
            IntTy tailprim3013 = 1 + fltPrm360;

            return (CursorInt64Prod) {endof3012, tailprim3013};
            break;
        }

      case 3:
        {
            CursorTy field_cur3511 = (CursorTy) tmpcur4886;
            CursorTy case1996 = (CursorTy) field_cur3511;
            CursorTy cond102 = (CursorTy) case1996;
            CursorInt64Prod tmp_struct13 =  expr(end_r1827, cond102);
            CursorTy pvrtmp4915 = tmp_struct13.field0;
            IntTy pvrtmp4916 = tmp_struct13.field1;
            CursorTy endof3014 = (CursorTy) pvrtmp4915;
            IntTy fltPrm364 = (IntTy) pvrtmp4916;
            CursorTy case1997 = (CursorTy) endof3014;
            CursorTy then103 = (CursorTy) case1997;
            CursorInt64Prod tmp_struct14 =  expr(end_r1827, then103);
            CursorTy pvrtmp4917 = tmp_struct14.field0;
            IntTy pvrtmp4918 = tmp_struct14.field1;
            CursorTy endof3015 = (CursorTy) pvrtmp4917;
            IntTy fltPrm366 = (IntTy) pvrtmp4918;
            CursorTy case1998 = (CursorTy) endof3015;
            CursorTy else104 = (CursorTy) case1998;
            CursorInt64Prod tmp_struct15 =  expr(end_r1827, else104);
            CursorTy pvrtmp4919 = tmp_struct15.field0;
            IntTy pvrtmp4920 = tmp_struct15.field1;
            CursorTy endof3016 = (CursorTy) pvrtmp4919;
            IntTy fltPrm367 = (IntTy) pvrtmp4920;
            IntTy fltPrm365 = fltPrm366 + fltPrm367;
            IntTy fltPrm363 = fltPrm364 + fltPrm365;
            IntTy tailprim3017 = 1 + fltPrm363;

            return (CursorInt64Prod) {endof3016, tailprim3017};
            break;
        }

      case 4:
        {
            CursorTy field_cur3515 = (CursorTy) tmpcur4886;
            CursorTy case2005 = (CursorTy) field_cur3515;
            CursorTy exprs105 = (CursorTy) case2005;
            CursorInt64Prod tmp_struct16 =  loopExpr(end_r1827, exprs105);
            CursorTy pvrtmp4921 = tmp_struct16.field0;
            IntTy pvrtmp4922 = tmp_struct16.field1;
            CursorTy endof3018 = (CursorTy) pvrtmp4921;
            IntTy fltPrm368 = (IntTy) pvrtmp4922;
            IntTy tailprim3019 = 1 + fltPrm368;

            return (CursorInt64Prod) {endof3018, tailprim3019};
            break;
        }

      case 5:
        {
            CursorTy field_cur3517 = (CursorTy) tmpcur4886;
            CursorTy case2008 = (CursorTy) field_cur3517;
            CursorTy e1106 = (CursorTy) case2008;
            CursorInt64Prod tmp_struct17 =  expr(end_r1827, e1106);
            CursorTy pvrtmp4923 = tmp_struct17.field0;
            IntTy pvrtmp4924 = tmp_struct17.field1;
            CursorTy endof3020 = (CursorTy) pvrtmp4923;
            IntTy fltPrm370 = (IntTy) pvrtmp4924;
            CursorTy case2009 = (CursorTy) endof3020;
            CursorTy exprs107 = (CursorTy) case2009;
            CursorInt64Prod tmp_struct18 =  loopExpr(end_r1827, exprs107);
            CursorTy pvrtmp4925 = tmp_struct18.field0;
            IntTy pvrtmp4926 = tmp_struct18.field1;
            CursorTy endof3021 = (CursorTy) pvrtmp4925;
            IntTy fltPrm371 = (IntTy) pvrtmp4926;
            IntTy fltPrm369 = fltPrm370 + fltPrm371;
            IntTy tailprim3022 = 1 + fltPrm369;

            return (CursorInt64Prod) {endof3021, tailprim3022};
            break;
        }

      case 13:
        {
            CursorTy field_cur3520 = (CursorTy) tmpcur4886;
            CursorTy case2014 = (CursorTy) field_cur3520;
            CursorTy e1108 = (CursorTy) case2014;
            CursorInt64Prod tmp_struct19 =  expr(end_r1827, e1108);
            CursorTy pvrtmp4927 = tmp_struct19.field0;
            IntTy pvrtmp4928 = tmp_struct19.field1;
            CursorTy endof3023 = (CursorTy) pvrtmp4927;
            IntTy fltPrm373 = (IntTy) pvrtmp4928;
            CursorTy case2015 = (CursorTy) endof3023;
            CursorTy es109 = (CursorTy) case2015;
            CursorInt64Prod tmp_struct20 =  loopExpr(end_r1827, es109);
            CursorTy pvrtmp4929 = tmp_struct20.field0;
            IntTy pvrtmp4930 = tmp_struct20.field1;
            CursorTy endof3024 = (CursorTy) pvrtmp4929;
            IntTy fltPrm374 = (IntTy) pvrtmp4930;
            IntTy fltPrm372 = fltPrm373 + fltPrm374;
            IntTy tailprim3025 = 1 + fltPrm372;

            return (CursorInt64Prod) {endof3024, tailprim3025};
            break;
        }

      case 8:
        {
            CursorTy field_cur3523 = (CursorTy) tmpcur4886;
            CursorTy case2020 = (CursorTy) field_cur3523;
            SymTy tmpval4931 = *(SymTy *) case2020;
            CursorTy tmpcur4932 = case2020 + sizeof(SymTy);
            SymTy s110 = (SymTy) tmpval4931;
            CursorTy end_s110 = (CursorTy) tmpcur4932;
            CursorTy case2021 = (CursorTy) end_s110;
            CursorTy e111 = (CursorTy) case2021;
            CursorTy jump3026 = case2020 + 8;
            CursorInt64Prod tmp_struct21 =  expr(end_r1827, e111);
            CursorTy pvrtmp4933 = tmp_struct21.field0;
            IntTy pvrtmp4934 = tmp_struct21.field1;
            CursorTy endof3027 = (CursorTy) pvrtmp4933;
            IntTy fltPrm376 = (IntTy) pvrtmp4934;
            IntTy fltPrm375 = 0 + fltPrm376;
            IntTy tailprim3028 = 1 + fltPrm375;

            return (CursorInt64Prod) {endof3027, tailprim3028};
            break;
        }

      case 12:
        {
            CursorTy field_cur3526 = (CursorTy) tmpcur4886;
            CursorTy case2024 = (CursorTy) field_cur3526;
            CursorTy e1112 = (CursorTy) case2024;
            CursorInt64Prod tmp_struct22 =  expr(end_r1827, e1112);
            CursorTy pvrtmp4935 = tmp_struct22.field0;
            IntTy pvrtmp4936 = tmp_struct22.field1;
            CursorTy endof3029 = (CursorTy) pvrtmp4935;
            IntTy fltPrm378 = (IntTy) pvrtmp4936;
            CursorTy case2025 = (CursorTy) endof3029;
            CursorTy e2113 = (CursorTy) case2025;
            CursorInt64Prod tmp_struct23 =  expr(end_r1827, e2113);
            CursorTy pvrtmp4937 = tmp_struct23.field0;
            IntTy pvrtmp4938 = tmp_struct23.field1;
            CursorTy endof3030 = (CursorTy) pvrtmp4937;
            IntTy fltPrm380 = (IntTy) pvrtmp4938;
            CursorTy case2026 = (CursorTy) endof3030;
            CursorTy e3114 = (CursorTy) case2026;
            CursorInt64Prod tmp_struct24 =  expr(end_r1827, e3114);
            CursorTy pvrtmp4939 = tmp_struct24.field0;
            IntTy pvrtmp4940 = tmp_struct24.field1;
            CursorTy endof3031 = (CursorTy) pvrtmp4939;
            IntTy fltPrm381 = (IntTy) pvrtmp4940;
            IntTy fltPrm379 = fltPrm380 + fltPrm381;
            IntTy fltPrm377 = fltPrm378 + fltPrm379;
            IntTy tailprim3032 = 1 + fltPrm377;

            return (CursorInt64Prod) {endof3031, tailprim3032};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6550 = *(CursorTy *) tmpcur4886;
            CursorTy tmpaftercur6551 = tmpcur4886 + 8;
            TagTyPacked tagtmp6552 = *(TagTyPacked *) tmpcur6550;
            CursorTy tailtmp6553 = tmpcur6550 + 1;

            tmpval4885 = tagtmp6552;
            tmpcur4886 = tailtmp6553;
            goto switch4941;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6550 = *(CursorTy *) tmpcur4886;
            CursorTy tmpaftercur6551 = tmpcur4886 + 8;
            TagTyPacked tagtmp6552 = *(TagTyPacked *) tmpcur6550;
            CursorTy tailtmp6553 = tmpcur6550 + 1;

            tmpval4885 = tagtmp6552;
            tmpcur4886 = tailtmp6553;
            goto switch4941;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4885");
            exit(1);
        }
    }
}
CursorInt64Prod top(CursorTy end_r1829, CursorTy e115)
{
    CursorTy loc1828 = (CursorTy) e115;
    TagTyPacked tmpval4942 = *(TagTyPacked *) e115;
    CursorTy tmpcur4943 = e115 + 1;


  switch4956:
    ;
    switch (tmpval4942) {

      case 0:
        {
            CursorTy field_cur3530 = (CursorTy) tmpcur4943;
            CursorTy case2035 = (CursorTy) field_cur3530;
            CursorTy ls116 = (CursorTy) case2035;
            CursorInt64Prod tmp_struct25 =  loopSyms(end_r1829, ls116);
            CursorTy pvrtmp4944 = tmp_struct25.field0;
            IntTy pvrtmp4945 = tmp_struct25.field1;
            CursorTy endof3033 = (CursorTy) pvrtmp4944;
            IntTy fltPrm383 = (IntTy) pvrtmp4945;
            CursorTy case2036 = (CursorTy) endof3033;
            CursorTy e117 = (CursorTy) case2036;
            CursorInt64Prod tmp_struct26 =  expr(end_r1829, e117);
            CursorTy pvrtmp4946 = tmp_struct26.field0;
            IntTy pvrtmp4947 = tmp_struct26.field1;
            CursorTy endof3034 = (CursorTy) pvrtmp4946;
            IntTy fltPrm384 = (IntTy) pvrtmp4947;
            IntTy fltPrm382 = fltPrm383 + fltPrm384;
            IntTy tailprim3035 = 1 + fltPrm382;

            return (CursorInt64Prod) {endof3034, tailprim3035};
            break;
        }

      case 1:
        {
            CursorTy field_cur3533 = (CursorTy) tmpcur4943;
            CursorTy case2041 = (CursorTy) field_cur3533;
            CursorTy ls118 = (CursorTy) case2041;
            CursorInt64Prod tmp_struct27 =  loopSyms(end_r1829, ls118);
            CursorTy pvrtmp4948 = tmp_struct27.field0;
            IntTy pvrtmp4949 = tmp_struct27.field1;
            CursorTy endof3036 = (CursorTy) pvrtmp4948;
            IntTy fltPrm386 = (IntTy) pvrtmp4949;
            CursorTy case2042 = (CursorTy) endof3036;
            CursorTy e119 = (CursorTy) case2042;
            CursorInt64Prod tmp_struct28 =  expr(end_r1829, e119);
            CursorTy pvrtmp4950 = tmp_struct28.field0;
            IntTy pvrtmp4951 = tmp_struct28.field1;
            CursorTy endof3037 = (CursorTy) pvrtmp4950;
            IntTy fltPrm387 = (IntTy) pvrtmp4951;
            IntTy fltPrm385 = fltPrm386 + fltPrm387;
            IntTy tailprim3038 = 1 + fltPrm385;

            return (CursorInt64Prod) {endof3037, tailprim3038};
            break;
        }

      case 2:
        {
            CursorTy field_cur3536 = (CursorTy) tmpcur4943;
            CursorTy case2047 = (CursorTy) field_cur3536;
            CursorTy ls120 = (CursorTy) case2047;
            CursorInt64Prod tmp_struct29 =  loopTopLvl(end_r1829, ls120);
            CursorTy pvrtmp4952 = tmp_struct29.field0;
            IntTy pvrtmp4953 = tmp_struct29.field1;
            CursorTy endof3039 = (CursorTy) pvrtmp4952;
            IntTy fltPrm388 = (IntTy) pvrtmp4953;
            IntTy tailprim3040 = 1 + fltPrm388;

            return (CursorInt64Prod) {endof3039, tailprim3040};
            break;
        }

      case 3:
        {
            CursorTy field_cur3538 = (CursorTy) tmpcur4943;
            CursorTy case2050 = (CursorTy) field_cur3538;
            CursorTy e121 = (CursorTy) case2050;
            CursorInt64Prod tmp_struct30 =  expr(end_r1829, e121);
            CursorTy pvrtmp4954 = tmp_struct30.field0;
            IntTy pvrtmp4955 = tmp_struct30.field1;
            CursorTy endof3042 = (CursorTy) pvrtmp4954;
            IntTy tailapp3041 = (IntTy) pvrtmp4955;

            return (CursorInt64Prod) {endof3042, tailapp3041};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6554 = *(CursorTy *) tmpcur4943;
            CursorTy tmpaftercur6555 = tmpcur4943 + 8;
            TagTyPacked tagtmp6556 = *(TagTyPacked *) tmpcur6554;
            CursorTy tailtmp6557 = tmpcur6554 + 1;

            tmpval4942 = tagtmp6556;
            tmpcur4943 = tailtmp6557;
            goto switch4956;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6554 = *(CursorTy *) tmpcur4943;
            CursorTy tmpaftercur6555 = tmpcur4943 + 8;
            TagTyPacked tagtmp6556 = *(TagTyPacked *) tmpcur6554;
            CursorTy tailtmp6557 = tmpcur6554 + 1;

            tmpval4942 = tagtmp6556;
            tmpcur4943 = tailtmp6557;
            goto switch4956;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4942");
            exit(1);
        }
    }
}
CursorInt64Prod loopLVBIND(CursorTy end_r1831, CursorTy ls122)
{
    CursorTy loc1830 = (CursorTy) ls122;
    TagTyPacked tmpval4957 = *(TagTyPacked *) ls122;
    CursorTy tmpcur4958 = ls122 + 1;


  switch4965:
    ;
    switch (tmpval4957) {

      case 0:
        {
            CursorTy field_cur3540 = (CursorTy) tmpcur4958;
            CursorTy case2055 = (CursorTy) field_cur3540;
            CursorTy syms123 = (CursorTy) case2055;
            CursorInt64Prod tmp_struct31 =  loopSyms(end_r1831, syms123);
            CursorTy pvrtmp4959 = tmp_struct31.field0;
            IntTy pvrtmp4960 = tmp_struct31.field1;
            CursorTy endof3043 = (CursorTy) pvrtmp4959;
            IntTy fltPrm390 = (IntTy) pvrtmp4960;
            CursorTy case2056 = (CursorTy) endof3043;
            CursorTy e124 = (CursorTy) case2056;
            CursorInt64Prod tmp_struct32 =  expr(end_r1831, e124);
            CursorTy pvrtmp4961 = tmp_struct32.field0;
            IntTy pvrtmp4962 = tmp_struct32.field1;
            CursorTy endof3044 = (CursorTy) pvrtmp4961;
            IntTy fltPrm392 = (IntTy) pvrtmp4962;
            CursorTy case2057 = (CursorTy) endof3044;
            CursorTy ls125 = (CursorTy) case2057;
            CursorInt64Prod tmp_struct33 =  loopLVBIND(end_r1831, ls125);
            CursorTy pvrtmp4963 = tmp_struct33.field0;
            IntTy pvrtmp4964 = tmp_struct33.field1;
            CursorTy endof3045 = (CursorTy) pvrtmp4963;
            IntTy fltPrm393 = (IntTy) pvrtmp4964;
            IntTy fltPrm391 = fltPrm392 + fltPrm393;
            IntTy fltPrm389 = fltPrm390 + fltPrm391;
            IntTy tailprim3046 = 1 + fltPrm389;

            return (CursorInt64Prod) {endof3045, tailprim3046};
            break;
        }

      case 1:
        {
            CursorTy field_cur3544 = (CursorTy) tmpcur4958;
            CursorTy jump3047 = loc1830 + 1;
            IntTy fltLitTail3048 = (IntTy) 1;

            return (CursorInt64Prod) {jump3047, fltLitTail3048};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6558 = *(CursorTy *) tmpcur4958;
            CursorTy tmpaftercur6559 = tmpcur4958 + 8;
            TagTyPacked tagtmp6560 = *(TagTyPacked *) tmpcur6558;
            CursorTy tailtmp6561 = tmpcur6558 + 1;

            tmpval4957 = tagtmp6560;
            tmpcur4958 = tailtmp6561;
            goto switch4965;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6558 = *(CursorTy *) tmpcur4958;
            CursorTy tmpaftercur6559 = tmpcur4958 + 8;
            TagTyPacked tagtmp6560 = *(TagTyPacked *) tmpcur6558;
            CursorTy tailtmp6561 = tmpcur6558 + 1;

            tmpval4957 = tagtmp6560;
            tmpcur4958 = tailtmp6561;
            goto switch4965;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4957");
            exit(1);
        }
    }
}
CursorInt64Prod loopLambdaCase(CursorTy end_r1833, CursorTy ls126)
{
    CursorTy loc1832 = (CursorTy) ls126;
    TagTyPacked tmpval4966 = *(TagTyPacked *) ls126;
    CursorTy tmpcur4967 = ls126 + 1;


  switch4974:
    ;
    switch (tmpval4966) {

      case 0:
        {
            CursorTy field_cur3545 = (CursorTy) tmpcur4967;
            CursorTy case2066 = (CursorTy) field_cur3545;
            CursorTy f127 = (CursorTy) case2066;
            CursorInt64Prod tmp_struct34 =  formals(end_r1833, f127);
            CursorTy pvrtmp4968 = tmp_struct34.field0;
            IntTy pvrtmp4969 = tmp_struct34.field1;
            CursorTy endof3049 = (CursorTy) pvrtmp4968;
            IntTy fltPrm395 = (IntTy) pvrtmp4969;
            CursorTy case2067 = (CursorTy) endof3049;
            CursorTy le128 = (CursorTy) case2067;
            CursorInt64Prod tmp_struct35 =  loopExpr(end_r1833, le128);
            CursorTy pvrtmp4970 = tmp_struct35.field0;
            IntTy pvrtmp4971 = tmp_struct35.field1;
            CursorTy endof3050 = (CursorTy) pvrtmp4970;
            IntTy fltPrm397 = (IntTy) pvrtmp4971;
            CursorTy case2068 = (CursorTy) endof3050;
            CursorTy ls129 = (CursorTy) case2068;
            CursorInt64Prod tmp_struct36 =  loopLambdaCase(end_r1833, ls129);
            CursorTy pvrtmp4972 = tmp_struct36.field0;
            IntTy pvrtmp4973 = tmp_struct36.field1;
            CursorTy endof3051 = (CursorTy) pvrtmp4972;
            IntTy fltPrm398 = (IntTy) pvrtmp4973;
            IntTy fltPrm396 = fltPrm397 + fltPrm398;
            IntTy fltPrm394 = fltPrm395 + fltPrm396;
            IntTy tailprim3052 = 1 + fltPrm394;

            return (CursorInt64Prod) {endof3051, tailprim3052};
            break;
        }

      case 1:
        {
            CursorTy field_cur3549 = (CursorTy) tmpcur4967;
            CursorTy jump3053 = loc1832 + 1;
            IntTy fltLitTail3054 = (IntTy) 1;

            return (CursorInt64Prod) {jump3053, fltLitTail3054};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6562 = *(CursorTy *) tmpcur4967;
            CursorTy tmpaftercur6563 = tmpcur4967 + 8;
            TagTyPacked tagtmp6564 = *(TagTyPacked *) tmpcur6562;
            CursorTy tailtmp6565 = tmpcur6562 + 1;

            tmpval4966 = tagtmp6564;
            tmpcur4967 = tailtmp6565;
            goto switch4974;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6562 = *(CursorTy *) tmpcur4967;
            CursorTy tmpaftercur6563 = tmpcur4967 + 8;
            TagTyPacked tagtmp6564 = *(TagTyPacked *) tmpcur6562;
            CursorTy tailtmp6565 = tmpcur6562 + 1;

            tmpval4966 = tagtmp6564;
            tmpcur4967 = tailtmp6565;
            goto switch4974;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4966");
            exit(1);
        }
    }
}
CursorInt64Prod loopExpr(CursorTy end_r1835, CursorTy ls130)
{
    CursorTy loc1834 = (CursorTy) ls130;
    TagTyPacked tmpval4975 = *(TagTyPacked *) ls130;
    CursorTy tmpcur4976 = ls130 + 1;


  switch4981:
    ;
    switch (tmpval4975) {

      case 0:
        {
            CursorTy field_cur3550 = (CursorTy) tmpcur4976;
            CursorTy case2077 = (CursorTy) field_cur3550;
            CursorTy e131 = (CursorTy) case2077;
            CursorInt64Prod tmp_struct37 =  expr(end_r1835, e131);
            CursorTy pvrtmp4977 = tmp_struct37.field0;
            IntTy pvrtmp4978 = tmp_struct37.field1;
            CursorTy endof3055 = (CursorTy) pvrtmp4977;
            IntTy fltPrm400 = (IntTy) pvrtmp4978;
            CursorTy case2078 = (CursorTy) endof3055;
            CursorTy ls132 = (CursorTy) case2078;
            CursorInt64Prod tmp_struct38 =  loopExpr(end_r1835, ls132);
            CursorTy pvrtmp4979 = tmp_struct38.field0;
            IntTy pvrtmp4980 = tmp_struct38.field1;
            CursorTy endof3056 = (CursorTy) pvrtmp4979;
            IntTy fltPrm401 = (IntTy) pvrtmp4980;
            IntTy fltPrm399 = fltPrm400 + fltPrm401;
            IntTy tailprim3057 = 1 + fltPrm399;

            return (CursorInt64Prod) {endof3056, tailprim3057};
            break;
        }

      case 1:
        {
            CursorTy field_cur3553 = (CursorTy) tmpcur4976;
            CursorTy jump3058 = loc1834 + 1;
            IntTy fltLitTail3059 = (IntTy) 1;

            return (CursorInt64Prod) {jump3058, fltLitTail3059};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6566 = *(CursorTy *) tmpcur4976;
            CursorTy tmpaftercur6567 = tmpcur4976 + 8;
            TagTyPacked tagtmp6568 = *(TagTyPacked *) tmpcur6566;
            CursorTy tailtmp6569 = tmpcur6566 + 1;

            tmpval4975 = tagtmp6568;
            tmpcur4976 = tailtmp6569;
            goto switch4981;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6566 = *(CursorTy *) tmpcur4976;
            CursorTy tmpaftercur6567 = tmpcur4976 + 8;
            TagTyPacked tagtmp6568 = *(TagTyPacked *) tmpcur6566;
            CursorTy tailtmp6569 = tmpcur6566 + 1;

            tmpval4975 = tagtmp6568;
            tmpcur4976 = tailtmp6569;
            goto switch4981;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4975");
            exit(1);
        }
    }
}
CursorInt64Prod loopTopLvl(CursorTy end_r1837, CursorTy ls133)
{
    CursorTy loc1836 = (CursorTy) ls133;
    TagTyPacked tmpval4982 = *(TagTyPacked *) ls133;
    CursorTy tmpcur4983 = ls133 + 1;


  switch4998:
    ;
    switch (tmpval4982) {

      case 2:
        {
            CursorTy field_cur3554 = (CursorTy) tmpcur4983;
            CursorTy tmpcur4984 = *(CursorTy *) field_cur3554;
            CursorTy tmpaftercur4985 = field_cur3554 + 8;
            CursorTy case2085 = (CursorTy) field_cur3554;
            CursorTy absran1408 = (CursorTy) tmpcur4984;
            CursorTy end_absran1408 = (CursorTy) tmpaftercur4985;
            CursorTy case2086 = (CursorTy) end_absran1408;
            CursorTy tl134 = (CursorTy) case2086;
            CursorTy case2087 = (CursorTy) absran1408;
            CursorTy ls135 = (CursorTy) case2087;
            CursorTy jump3060 = case2085 + 8;
            CursorInt64Prod tmp_struct39 =  top(end_r1837, tl134);
            CursorTy pvrtmp4986 = tmp_struct39.field0;
            IntTy pvrtmp4987 = tmp_struct39.field1;
            CursorTy endof3061 = (CursorTy) pvrtmp4986;
            IntTy fltPrm403 = (IntTy) pvrtmp4987;
            CursorInt64Prod tmp_struct40 =  loopTopLvl(end_r1837, ls135);
            CursorTy pvrtmp4988 = tmp_struct40.field0;
            IntTy pvrtmp4989 = tmp_struct40.field1;
            CursorTy endof3062 = (CursorTy) pvrtmp4988;
            IntTy fltPrm404 = (IntTy) pvrtmp4989;
            IntTy fltPrm402 = fltPrm403 + fltPrm404;
            IntTy tailprim3063 = 1 + fltPrm402;

            return (CursorInt64Prod) {endof3062, tailprim3063};
            break;
        }

      case 153:
        {
            CursorTy field_cur3558 = (CursorTy) tmpcur4983;
            CursorTy case2092 = (CursorTy) field_cur3558;
            IntTy tmpval4990 = *(IntTy *) case2092;
            CursorTy tmpcur4991 = case2092 + sizeof(IntTy);
            IntTy size1409 = (IntTy) tmpval4990;
            CursorTy end_size1409 = (CursorTy) tmpcur4991;
            CursorTy case2093 = (CursorTy) end_size1409;
            IntTy tmpval4992 = *(IntTy *) case2093;
            CursorTy tmpcur4993 = case2093 + sizeof(IntTy);
            IntTy relran1410 = (IntTy) tmpval4992;
            CursorTy end_relran1410 = (CursorTy) tmpcur4993;
            CursorTy case2094 = (CursorTy) end_relran1410;
            CursorTy tl134 = (CursorTy) case2094;
            CursorTy loc3562 = case2093 + relran1410;
            CursorTy case2095 = loc3562 + 8;
            CursorTy ls135 = (CursorTy) case2095;
            CursorTy jump3065 = case2093 + 8;
            CursorTy jump3064 = case2092 + 8;
            CursorInt64Prod tmp_struct41 =  top(end_r1837, tl134);
            CursorTy pvrtmp4994 = tmp_struct41.field0;
            IntTy pvrtmp4995 = tmp_struct41.field1;
            CursorTy endof3066 = (CursorTy) pvrtmp4994;
            IntTy fltPrm403 = (IntTy) pvrtmp4995;
            CursorInt64Prod tmp_struct42 =  loopTopLvl(end_r1837, ls135);
            CursorTy pvrtmp4996 = tmp_struct42.field0;
            IntTy pvrtmp4997 = tmp_struct42.field1;
            CursorTy endof3067 = (CursorTy) pvrtmp4996;
            IntTy fltPrm404 = (IntTy) pvrtmp4997;
            IntTy fltPrm402 = fltPrm403 + fltPrm404;
            IntTy tailprim3068 = 1 + fltPrm402;

            return (CursorInt64Prod) {endof3067, tailprim3068};
            break;
        }

      case 1:
        {
            CursorTy field_cur3565 = (CursorTy) tmpcur4983;
            CursorTy jump3069 = loc1836 + 1;
            IntTy fltLitTail3070 = (IntTy) 1;

            return (CursorInt64Prod) {jump3069, fltLitTail3070};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6570 = *(CursorTy *) tmpcur4983;
            CursorTy tmpaftercur6571 = tmpcur4983 + 8;
            TagTyPacked tagtmp6572 = *(TagTyPacked *) tmpcur6570;
            CursorTy tailtmp6573 = tmpcur6570 + 1;

            tmpval4982 = tagtmp6572;
            tmpcur4983 = tailtmp6573;
            goto switch4998;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6570 = *(CursorTy *) tmpcur4983;
            CursorTy tmpaftercur6571 = tmpcur4983 + 8;
            TagTyPacked tagtmp6572 = *(TagTyPacked *) tmpcur6570;
            CursorTy tailtmp6573 = tmpcur6570 + 1;

            tmpval4982 = tagtmp6572;
            tmpcur4983 = tailtmp6573;
            goto switch4998;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval4982");
            exit(1);
        }
    }
}
CursorInt64Prod countnodes(CursorTy end_r1839, CursorTy e0136)
{
    CursorTy loc1838 = (CursorTy) e0136;
    CursorInt64Prod tmp_struct43 =  top(end_r1839, e0136);
    CursorTy pvrtmp4999 = tmp_struct43.field0;
    IntTy pvrtmp5000 = tmp_struct43.field1;
    CursorTy endof3072 = (CursorTy) pvrtmp4999;
    IntTy tailapp3071 = (IntTy) pvrtmp5000;

    return (CursorInt64Prod) {endof3072, tailapp3071};
}
IntTy par_loopTopLvl(CursorTy end_r1841, IntTy height61, CursorTy ls62)
{
    CursorTy loc1840 = (CursorTy) ls62;
    BoolTy fltIf405 = height61 > 8;

    if (fltIf405) {
        CursorInt64Prod tmp_struct44 =  loopTopLvl(end_r1841, ls62);
        CursorTy pvrtmp5001 = tmp_struct44.field0;
        IntTy pvrtmp5002 = tmp_struct44.field1;
        CursorTy endof3074 = (CursorTy) pvrtmp5001;
        IntTy tailapp3073 = (IntTy) pvrtmp5002;

        return tailapp3073;
    } else {
        TagTyPacked tmpval5003 = *(TagTyPacked *) ls62;
        CursorTy tmpcur5004 = ls62 + 1;


      switch5011:
        ;
        switch (tmpval5003) {

          case 2:
            {
                CursorTy field_cur3568 = (CursorTy) tmpcur5004;
                CursorTy tmpcur5005 = *(CursorTy *) field_cur3568;
                CursorTy tmpaftercur5006 = field_cur3568 + 8;
                CursorTy case2106 = (CursorTy) field_cur3568;
                CursorTy absran1411 = (CursorTy) tmpcur5005;
                CursorTy end_absran1411 = (CursorTy) tmpaftercur5006;
                CursorTy case2107 = (CursorTy) end_absran1411;
                CursorTy tl63 = (CursorTy) case2107;
                CursorTy case2108 = (CursorTy) absran1411;
                CursorTy ls64 = (CursorTy) case2108;
                CursorTy jump3075 = case2106 + 8;
                IntTy fltSpawnE406 = 1 + height61;
                IntTy parent_id2971 = __cilkrts_get_worker_number();
                IntTy ctl65 = cilk_spawn par_top(end_r1841, fltSpawnE406, tl63);
                IntTy cls66 =  par_loopTopLvl(end_r1841, height61, ls64);

                cilk_sync;

                IntTy fltPrm407 = ctl65 + cls66;
                IntTy tailprim3076 = 1 + fltPrm407;

                return tailprim3076;
                break;
            }

          case 153:
            {
                CursorTy field_cur3570 = (CursorTy) tmpcur5004;
                CursorTy case2113 = (CursorTy) field_cur3570;
                IntTy tmpval5007 = *(IntTy *) case2113;
                CursorTy tmpcur5008 = case2113 + sizeof(IntTy);
                IntTy size1412 = (IntTy) tmpval5007;
                CursorTy end_size1412 = (CursorTy) tmpcur5008;
                CursorTy case2114 = (CursorTy) end_size1412;
                IntTy tmpval5009 = *(IntTy *) case2114;
                CursorTy tmpcur5010 = case2114 + sizeof(IntTy);
                IntTy relran1413 = (IntTy) tmpval5009;
                CursorTy end_relran1413 = (CursorTy) tmpcur5010;
                CursorTy case2115 = (CursorTy) end_relran1413;
                CursorTy tl63 = (CursorTy) case2115;
                CursorTy loc3574 = case2114 + relran1413;
                CursorTy case2116 = loc3574 + 8;
                CursorTy ls64 = (CursorTy) case2116;
                CursorTy jump3078 = case2114 + 8;
                CursorTy jump3077 = case2113 + 8;
                IntTy fltSpawnE406 = 1 + height61;
                IntTy parent_id2972 = __cilkrts_get_worker_number();
                IntTy ctl65 = cilk_spawn par_top(end_r1841, fltSpawnE406, tl63);
                IntTy cls66 =  par_loopTopLvl(end_r1841, height61, ls64);

                cilk_sync;

                IntTy fltPrm407 = ctl65 + cls66;
                IntTy tailprim3079 = 1 + fltPrm407;

                return tailprim3079;
                break;
            }

          case 1:
            {
                CursorTy field_cur3575 = (CursorTy) tmpcur5004;
                CursorTy jump3080 = loc1840 + 1;
                IntTy fltLitTail3081 = (IntTy) 1;

                return fltLitTail3081;
                break;
            }

          case 255:
            {
                CursorTy tmpcur6574 = *(CursorTy *) tmpcur5004;
                CursorTy tmpaftercur6575 = tmpcur5004 + 8;
                TagTyPacked tagtmp6576 = *(TagTyPacked *) tmpcur6574;
                CursorTy tailtmp6577 = tmpcur6574 + 1;

                tmpval5003 = tagtmp6576;
                tmpcur5004 = tailtmp6577;
                goto switch5011;
                break;
            }

          case 254:
            {
                CursorTy tmpcur6574 = *(CursorTy *) tmpcur5004;
                CursorTy tmpaftercur6575 = tmpcur5004 + 8;
                TagTyPacked tagtmp6576 = *(TagTyPacked *) tmpcur6574;
                CursorTy tailtmp6577 = tmpcur6574 + 1;

                tmpval5003 = tagtmp6576;
                tmpcur5004 = tailtmp6577;
                goto switch5011;
                break;
            }

          default:
            {
                printf("%s\n", "Unknown tag in: tmpval5003");
                exit(1);
            }
        }
    }
}
IntTy par_top(CursorTy end_r1843, IntTy height68, CursorTy e69)
{
    CursorTy loc1842 = (CursorTy) e69;
    TagTyPacked tmpval5012 = *(TagTyPacked *) e69;
    CursorTy tmpcur5013 = e69 + 1;


  switch5024:
    ;
    switch (tmpval5012) {

      case 0:
        {
            CursorTy field_cur3576 = (CursorTy) tmpcur5013;
            CursorTy case2123 = (CursorTy) field_cur3576;
            CursorTy ls70 = (CursorTy) case2123;
            CursorInt64Prod tmp_struct45 =  loopSyms(end_r1843, ls70);
            CursorTy pvrtmp5014 = tmp_struct45.field0;
            IntTy pvrtmp5015 = tmp_struct45.field1;
            CursorTy endof3082 = (CursorTy) pvrtmp5014;
            IntTy fltPrm409 = (IntTy) pvrtmp5015;
            CursorTy case2124 = (CursorTy) endof3082;
            CursorTy e271 = (CursorTy) case2124;
            CursorInt64Prod tmp_struct46 =  expr(end_r1843, e271);
            CursorTy pvrtmp5016 = tmp_struct46.field0;
            IntTy pvrtmp5017 = tmp_struct46.field1;
            CursorTy endof3083 = (CursorTy) pvrtmp5016;
            IntTy fltPrm410 = (IntTy) pvrtmp5017;
            IntTy fltPrm408 = fltPrm409 + fltPrm410;
            IntTy tailprim3084 = 1 + fltPrm408;

            return tailprim3084;
            break;
        }

      case 1:
        {
            CursorTy field_cur3579 = (CursorTy) tmpcur5013;
            CursorTy case2129 = (CursorTy) field_cur3579;
            CursorTy ls72 = (CursorTy) case2129;
            CursorInt64Prod tmp_struct47 =  loopSyms(end_r1843, ls72);
            CursorTy pvrtmp5018 = tmp_struct47.field0;
            IntTy pvrtmp5019 = tmp_struct47.field1;
            CursorTy endof3085 = (CursorTy) pvrtmp5018;
            IntTy fltPrm412 = (IntTy) pvrtmp5019;
            CursorTy case2130 = (CursorTy) endof3085;
            CursorTy e273 = (CursorTy) case2130;
            CursorInt64Prod tmp_struct48 =  expr(end_r1843, e273);
            CursorTy pvrtmp5020 = tmp_struct48.field0;
            IntTy pvrtmp5021 = tmp_struct48.field1;
            CursorTy endof3086 = (CursorTy) pvrtmp5020;
            IntTy fltPrm413 = (IntTy) pvrtmp5021;
            IntTy fltPrm411 = fltPrm412 + fltPrm413;
            IntTy tailprim3087 = 1 + fltPrm411;

            return tailprim3087;
            break;
        }

      case 2:
        {
            CursorTy field_cur3582 = (CursorTy) tmpcur5013;
            CursorTy case2135 = (CursorTy) field_cur3582;
            CursorTy ls74 = (CursorTy) case2135;
            IntTy fltPrm414 =  par_loopTopLvl(end_r1843, height68, ls74);
            IntTy tailprim3088 = 1 + fltPrm414;

            return tailprim3088;
            break;
        }

      case 3:
        {
            CursorTy field_cur3583 = (CursorTy) tmpcur5013;
            CursorTy case2138 = (CursorTy) field_cur3583;
            CursorTy e75 = (CursorTy) case2138;
            CursorInt64Prod tmp_struct49 =  expr(end_r1843, e75);
            CursorTy pvrtmp5022 = tmp_struct49.field0;
            IntTy pvrtmp5023 = tmp_struct49.field1;
            CursorTy endof3090 = (CursorTy) pvrtmp5022;
            IntTy tailapp3089 = (IntTy) pvrtmp5023;

            return tailapp3089;
            break;
        }

      case 255:
        {
            CursorTy tmpcur6578 = *(CursorTy *) tmpcur5013;
            CursorTy tmpaftercur6579 = tmpcur5013 + 8;
            TagTyPacked tagtmp6580 = *(TagTyPacked *) tmpcur6578;
            CursorTy tailtmp6581 = tmpcur6578 + 1;

            tmpval5012 = tagtmp6580;
            tmpcur5013 = tailtmp6581;
            goto switch5024;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6578 = *(CursorTy *) tmpcur5013;
            CursorTy tmpaftercur6579 = tmpcur5013 + 8;
            TagTyPacked tagtmp6580 = *(TagTyPacked *) tmpcur6578;
            CursorTy tailtmp6581 = tmpcur6578 + 1;

            tmpval5012 = tagtmp6580;
            tmpcur5013 = tailtmp6581;
            goto switch5024;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5012");
            exit(1);
        }
    }
}
IntTy par_countnodes(CursorTy end_r1845, CursorTy e076)
{
    CursorTy loc1844 = (CursorTy) e076;
    IntTy tailapp3091 =  par_top(end_r1845, 0, e076);

    return tailapp3091;
}
CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r1848,
                                           CursorTy end_r1849, CursorTy loc1847,
                                           CursorTy arg1527)
{
    CursorTy loc1846 = (CursorTy) arg1527;

    if (loc1847 + 18 > end_r1849) {
        ChunkTy new_chunk51 = alloc_chunk(end_r1849);
        CursorTy chunk_start52 = new_chunk51.start_ptr;
        CursorTy chunk_end53 = new_chunk51.end_ptr;

        end_r1849 = chunk_end53;
        *(TagTyPacked *) loc1847 = 255;

        CursorTy redir = loc1847 + 1;

        *(CursorTy *) redir = chunk_start52;
        loc1847 = chunk_start52;
    }

    CursorTy loc2150 = loc1847 + 1;
    CursorTy loc2151 = loc2150 + 8;
    TagTyPacked tmpval5025 = *(TagTyPacked *) arg1527;
    CursorTy tmpcur5026 = arg1527 + 1;


  switch5045:
    ;
    switch (tmpval5025) {

      case 0:
        {
            CursorTy field_cur3585 = (CursorTy) tmpcur5026;
            CursorTy case2145 = (CursorTy) field_cur3585;
            SymTy tmpval5027 = *(SymTy *) case2145;
            CursorTy tmpcur5028 = case2145 + sizeof(SymTy);
            SymTy x1528 = (SymTy) tmpval5027;
            CursorTy end_x1528 = (CursorTy) tmpcur5028;
            CursorTy case2146 = (CursorTy) end_x1528;
            CursorTy x1529 = (CursorTy) case2146;
            CursorTy jump3092 = case2145 + 8;
            CursorCursorCursorCursorProd tmp_struct50 =
                                          _copy_ListSym(end_r1848, end_r1849, loc2151, x1529);
            CursorTy pvrtmp5029 = tmp_struct50.field0;
            CursorTy pvrtmp5030 = tmp_struct50.field1;
            CursorTy pvrtmp5031 = tmp_struct50.field2;
            CursorTy pvrtmp5032 = tmp_struct50.field3;
            CursorTy fltPrd4369 = (CursorTy) pvrtmp5031;
            CursorTy fltPrd4370 = (CursorTy) pvrtmp5032;
            CursorTy pvrtmp5034 = (CursorTy) fltPrd4370;
            CursorTy pvrtmp5033 = (CursorTy) fltPrd4369;
            CursorTy y1531 = (CursorTy) pvrtmp5033;
            CursorTy fltPrd4371 = (CursorTy) pvrtmp5031;
            CursorTy fltPrd4372 = (CursorTy) pvrtmp5032;
            CursorTy pvrtmp5036 = (CursorTy) fltPrd4372;
            CursorTy pvrtmp5035 = (CursorTy) fltPrd4371;
            CursorTy end_y1531 = (CursorTy) pvrtmp5036;
            CursorTy end_r1849_3386 = (CursorTy) pvrtmp5029;
            CursorTy endof3093 = (CursorTy) pvrtmp5030;

            *(TagTyPacked *) loc1847 = 0;

            CursorTy writetag3588 = loc1847 + 1;

            *(SymTy *) writetag3588 = x1528;

            CursorTy writecur3589 = writetag3588 + sizeof(SymTy);
            CursorTy writecur3590 = (CursorTy) end_y1531;
            CursorTy pvrtmp5038 = (CursorTy) writecur3590;
            CursorTy pvrtmp5037 = (CursorTy) loc1847;
            CursorTy taildc3094 = (CursorTy) pvrtmp5037;
            CursorTy end_taildc3094 = (CursorTy) pvrtmp5038;
            CursorTy pvrtmp5040 = (CursorTy) end_taildc3094;
            CursorTy pvrtmp5039 = (CursorTy) taildc3094;
            CursorTy fltPrd4373 = (CursorTy) pvrtmp5039;
            CursorTy fltPrd4374 = (CursorTy) pvrtmp5040;

            return (CursorCursorCursorCursorProd) {end_r1849_3386, endof3093,
                                                   fltPrd4373, fltPrd4374};
            break;
        }

      case 1:
        {
            CursorTy field_cur3592 = (CursorTy) tmpcur5026;
            CursorTy jump3095 = loc1846 + 1;

            *(TagTyPacked *) loc1847 = 1;

            CursorTy writetag3593 = loc1847 + 1;
            CursorTy pvrtmp5042 = (CursorTy) writetag3593;
            CursorTy pvrtmp5041 = (CursorTy) loc1847;
            CursorTy taildc3096 = (CursorTy) pvrtmp5041;
            CursorTy end_taildc3096 = (CursorTy) pvrtmp5042;
            CursorTy pvrtmp5044 = (CursorTy) end_taildc3096;
            CursorTy pvrtmp5043 = (CursorTy) taildc3096;
            CursorTy fltPrd4375 = (CursorTy) pvrtmp5043;
            CursorTy fltPrd4376 = (CursorTy) pvrtmp5044;

            return (CursorCursorCursorCursorProd) {end_r1849, jump3095,
                                                   fltPrd4375, fltPrd4376};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6582 = *(CursorTy *) tmpcur5026;
            CursorTy tmpaftercur6583 = tmpcur5026 + 8;
            TagTyPacked tagtmp6584 = *(TagTyPacked *) tmpcur6582;
            CursorTy tailtmp6585 = tmpcur6582 + 1;

            tmpval5025 = tagtmp6584;
            tmpcur5026 = tailtmp6585;
            goto switch5045;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6582 = *(CursorTy *) tmpcur5026;
            CursorTy tmpaftercur6583 = tmpcur5026 + 8;
            TagTyPacked tagtmp6584 = *(TagTyPacked *) tmpcur6582;
            CursorTy tailtmp6585 = tmpcur6582 + 1;

            tmpval5025 = tagtmp6584;
            tmpcur5026 = tailtmp6585;
            goto switch5045;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5025");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_ListSym(CursorTy end_r1851, CursorTy arg1532)
{
    CursorTy loc1850 = (CursorTy) arg1532;
    TagTyPacked tmpval5046 = *(TagTyPacked *) arg1532;
    CursorTy tmpcur5047 = arg1532 + 1;


  switch5052:
    ;
    switch (tmpval5046) {

      case 0:
        {
            CursorTy field_cur3595 = (CursorTy) tmpcur5047;
            CursorTy case2158 = (CursorTy) field_cur3595;
            SymTy tmpval5048 = *(SymTy *) case2158;
            CursorTy tmpcur5049 = case2158 + sizeof(SymTy);
            SymTy x1533 = (SymTy) tmpval5048;
            CursorTy end_x1533 = (CursorTy) tmpcur5049;
            CursorTy case2159 = (CursorTy) end_x1533;
            CursorTy x1534 = (CursorTy) case2159;
            CursorTy jump3097 = case2158 + 8;
            CursorInt64Prod tmp_struct54 =  _traverse_ListSym(end_r1851, x1534);
            CursorTy pvrtmp5050 = tmp_struct54.field0;
            IntTy pvrtmp5051 = tmp_struct54.field1;
            CursorTy endof3099 = (CursorTy) pvrtmp5050;
            IntTy y1536 = (IntTy) pvrtmp5051;
            IntTy fltLitTail3098 = (IntTy) 42;

            return (CursorInt64Prod) {endof3099, fltLitTail3098};
            break;
        }

      case 1:
        {
            CursorTy field_cur3598 = (CursorTy) tmpcur5047;
            CursorTy jump3100 = loc1850 + 1;
            IntTy fltLitTail3101 = (IntTy) 42;

            return (CursorInt64Prod) {jump3100, fltLitTail3101};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6586 = *(CursorTy *) tmpcur5047;
            CursorTy tmpaftercur6587 = tmpcur5047 + 8;
            TagTyPacked tagtmp6588 = *(TagTyPacked *) tmpcur6586;
            CursorTy tailtmp6589 = tmpcur6586 + 1;

            tmpval5046 = tagtmp6588;
            tmpcur5047 = tailtmp6589;
            goto switch5052;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6586 = *(CursorTy *) tmpcur5047;
            CursorTy tmpaftercur6587 = tmpcur5047 + 8;
            TagTyPacked tagtmp6588 = *(TagTyPacked *) tmpcur6586;
            CursorTy tailtmp6589 = tmpcur6586 + 1;

            tmpval5046 = tagtmp6588;
            tmpcur5047 = tailtmp6589;
            goto switch5052;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5046");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r1854,
                                            CursorTy end_r1855,
                                            CursorTy loc1853, CursorTy arg1537)
{
    CursorTy loc1852 = (CursorTy) arg1537;

    if (loc1853 + 18 > end_r1855) {
        ChunkTy new_chunk57 = alloc_chunk(end_r1855);
        CursorTy chunk_start58 = new_chunk57.start_ptr;
        CursorTy chunk_end59 = new_chunk57.end_ptr;

        end_r1855 = chunk_end59;
        *(TagTyPacked *) loc1853 = 255;

        CursorTy redir = loc1853 + 1;

        *(CursorTy *) redir = chunk_start58;
        loc1853 = chunk_start58;
    }

    TagTyPacked tmpval5053 = *(TagTyPacked *) arg1537;
    CursorTy tmpcur5054 = arg1537 + 1;


  switch5079:
    ;
    switch (tmpval5053) {

      case 0:
        {
            CursorTy field_cur3599 = (CursorTy) tmpcur5054;
            CursorTy case2164 = (CursorTy) field_cur3599;
            CursorTy x1538 = (CursorTy) case2164;
            CursorTy loc2172 = loc1853 + 1;
            CursorCursorCursorCursorProd tmp_struct55 =
                                          _copy_Expr(end_r1854, end_r1855, loc2172, x1538);
            CursorTy pvrtmp5055 = tmp_struct55.field0;
            CursorTy pvrtmp5056 = tmp_struct55.field1;
            CursorTy pvrtmp5057 = tmp_struct55.field2;
            CursorTy pvrtmp5058 = tmp_struct55.field3;
            CursorTy fltPrd4377 = (CursorTy) pvrtmp5057;
            CursorTy fltPrd4378 = (CursorTy) pvrtmp5058;
            CursorTy pvrtmp5060 = (CursorTy) fltPrd4378;
            CursorTy pvrtmp5059 = (CursorTy) fltPrd4377;
            CursorTy y1540 = (CursorTy) pvrtmp5059;
            CursorTy fltPrd4379 = (CursorTy) pvrtmp5057;
            CursorTy fltPrd4380 = (CursorTy) pvrtmp5058;
            CursorTy pvrtmp5062 = (CursorTy) fltPrd4380;
            CursorTy pvrtmp5061 = (CursorTy) fltPrd4379;
            CursorTy end_y1540 = (CursorTy) pvrtmp5062;
            CursorTy end_r1855_3387 = (CursorTy) pvrtmp5055;
            CursorTy endof3102 = (CursorTy) pvrtmp5056;
            CursorTy case2165 = (CursorTy) endof3102;
            CursorTy x1539 = (CursorTy) case2165;
            CursorTy loc2173 = (CursorTy) end_y1540;
            CursorCursorCursorCursorProd tmp_struct56 =
                                          _copy_ListExpr(end_r1854, end_r1855_3387, loc2173, x1539);
            CursorTy pvrtmp5063 = tmp_struct56.field0;
            CursorTy pvrtmp5064 = tmp_struct56.field1;
            CursorTy pvrtmp5065 = tmp_struct56.field2;
            CursorTy pvrtmp5066 = tmp_struct56.field3;
            CursorTy fltPrd4381 = (CursorTy) pvrtmp5065;
            CursorTy fltPrd4382 = (CursorTy) pvrtmp5066;
            CursorTy pvrtmp5068 = (CursorTy) fltPrd4382;
            CursorTy pvrtmp5067 = (CursorTy) fltPrd4381;
            CursorTy y1541 = (CursorTy) pvrtmp5067;
            CursorTy fltPrd4383 = (CursorTy) pvrtmp5065;
            CursorTy fltPrd4384 = (CursorTy) pvrtmp5066;
            CursorTy pvrtmp5070 = (CursorTy) fltPrd4384;
            CursorTy pvrtmp5069 = (CursorTy) fltPrd4383;
            CursorTy end_y1541 = (CursorTy) pvrtmp5070;
            CursorTy end_r1855_3387_3388 = (CursorTy) pvrtmp5063;
            CursorTy endof3103 = (CursorTy) pvrtmp5064;

            *(TagTyPacked *) loc1853 = 0;

            CursorTy writetag3602 = loc1853 + 1;
            CursorTy writecur3603 = (CursorTy) end_y1540;
            CursorTy writecur3604 = (CursorTy) end_y1541;
            CursorTy pvrtmp5072 = (CursorTy) writecur3604;
            CursorTy pvrtmp5071 = (CursorTy) loc1853;
            CursorTy taildc3104 = (CursorTy) pvrtmp5071;
            CursorTy end_taildc3104 = (CursorTy) pvrtmp5072;
            CursorTy pvrtmp5074 = (CursorTy) end_taildc3104;
            CursorTy pvrtmp5073 = (CursorTy) taildc3104;
            CursorTy fltPrd4385 = (CursorTy) pvrtmp5073;
            CursorTy fltPrd4386 = (CursorTy) pvrtmp5074;

            return (CursorCursorCursorCursorProd) {end_r1855_3387_3388,
                                                   endof3103, fltPrd4385,
                                                   fltPrd4386};
            break;
        }

      case 1:
        {
            CursorTy field_cur3606 = (CursorTy) tmpcur5054;
            CursorTy jump3105 = loc1852 + 1;

            *(TagTyPacked *) loc1853 = 1;

            CursorTy writetag3607 = loc1853 + 1;
            CursorTy pvrtmp5076 = (CursorTy) writetag3607;
            CursorTy pvrtmp5075 = (CursorTy) loc1853;
            CursorTy taildc3106 = (CursorTy) pvrtmp5075;
            CursorTy end_taildc3106 = (CursorTy) pvrtmp5076;
            CursorTy pvrtmp5078 = (CursorTy) end_taildc3106;
            CursorTy pvrtmp5077 = (CursorTy) taildc3106;
            CursorTy fltPrd4387 = (CursorTy) pvrtmp5077;
            CursorTy fltPrd4388 = (CursorTy) pvrtmp5078;

            return (CursorCursorCursorCursorProd) {end_r1855, jump3105,
                                                   fltPrd4387, fltPrd4388};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6590 = *(CursorTy *) tmpcur5054;
            CursorTy tmpaftercur6591 = tmpcur5054 + 8;
            TagTyPacked tagtmp6592 = *(TagTyPacked *) tmpcur6590;
            CursorTy tailtmp6593 = tmpcur6590 + 1;

            tmpval5053 = tagtmp6592;
            tmpcur5054 = tailtmp6593;
            goto switch5079;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6590 = *(CursorTy *) tmpcur5054;
            CursorTy tmpaftercur6591 = tmpcur5054 + 8;
            TagTyPacked tagtmp6592 = *(TagTyPacked *) tmpcur6590;
            CursorTy tailtmp6593 = tmpcur6590 + 1;

            tmpval5053 = tagtmp6592;
            tmpcur5054 = tailtmp6593;
            goto switch5079;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5053");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_ListExpr(CursorTy end_r1857, CursorTy arg1542)
{
    CursorTy loc1856 = (CursorTy) arg1542;
    TagTyPacked tmpval5080 = *(TagTyPacked *) arg1542;
    CursorTy tmpcur5081 = arg1542 + 1;


  switch5086:
    ;
    switch (tmpval5080) {

      case 0:
        {
            CursorTy field_cur3609 = (CursorTy) tmpcur5081;
            CursorTy case2179 = (CursorTy) field_cur3609;
            CursorTy x1543 = (CursorTy) case2179;
            CursorInt64Prod tmp_struct60 =  _traverse_Expr(end_r1857, x1543);
            CursorTy pvrtmp5082 = tmp_struct60.field0;
            IntTy pvrtmp5083 = tmp_struct60.field1;
            CursorTy endof3107 = (CursorTy) pvrtmp5082;
            IntTy y1545 = (IntTy) pvrtmp5083;
            CursorTy case2180 = (CursorTy) endof3107;
            CursorTy x1544 = (CursorTy) case2180;
            CursorInt64Prod tmp_struct61 =
                             _traverse_ListExpr(end_r1857, x1544);
            CursorTy pvrtmp5084 = tmp_struct61.field0;
            IntTy pvrtmp5085 = tmp_struct61.field1;
            CursorTy endof3109 = (CursorTy) pvrtmp5084;
            IntTy y1546 = (IntTy) pvrtmp5085;
            IntTy fltLitTail3108 = (IntTy) 42;

            return (CursorInt64Prod) {endof3109, fltLitTail3108};
            break;
        }

      case 1:
        {
            CursorTy field_cur3612 = (CursorTy) tmpcur5081;
            CursorTy jump3110 = loc1856 + 1;
            IntTy fltLitTail3111 = (IntTy) 42;

            return (CursorInt64Prod) {jump3110, fltLitTail3111};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6594 = *(CursorTy *) tmpcur5081;
            CursorTy tmpaftercur6595 = tmpcur5081 + 8;
            TagTyPacked tagtmp6596 = *(TagTyPacked *) tmpcur6594;
            CursorTy tailtmp6597 = tmpcur6594 + 1;

            tmpval5080 = tagtmp6596;
            tmpcur5081 = tailtmp6597;
            goto switch5086;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6594 = *(CursorTy *) tmpcur5081;
            CursorTy tmpaftercur6595 = tmpcur5081 + 8;
            TagTyPacked tagtmp6596 = *(TagTyPacked *) tmpcur6594;
            CursorTy tailtmp6597 = tmpcur6594 + 1;

            tmpval5080 = tagtmp6596;
            tmpcur5081 = tailtmp6597;
            goto switch5086;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5080");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r1860,
                                              CursorTy end_r1861,
                                              CursorTy loc1859,
                                              CursorTy arg1547)
{
    CursorTy loc1858 = (CursorTy) arg1547;

    if (loc1859 + 26 > end_r1861) {
        ChunkTy new_chunk68 = alloc_chunk(end_r1861);
        CursorTy chunk_start69 = new_chunk68.start_ptr;
        CursorTy chunk_end70 = new_chunk68.end_ptr;

        end_r1861 = chunk_end70;
        *(TagTyPacked *) loc1859 = 255;

        CursorTy redir = loc1859 + 1;

        *(CursorTy *) redir = chunk_start69;
        loc1859 = chunk_start69;
    }

    CursorTy loc2209 = loc1859 + 1;
    CursorTy loc2210 = loc2209 + 8;
    CursorTy loc2226 = loc1859 + 1;
    CursorTy loc2227 = loc2226 + 8;
    CursorTy loc2228 = loc2227 + 8;
    TagTyPacked tmpval5087 = *(TagTyPacked *) arg1547;
    CursorTy tmpcur5088 = arg1547 + 1;


  switch5159:
    ;
    switch (tmpval5087) {

      case 0:
        {
            CursorTy field_cur3613 = (CursorTy) tmpcur5088;
            CursorTy case2187 = (CursorTy) field_cur3613;
            CursorTy x1548 = (CursorTy) case2187;
            CursorTy loc2195 = loc1859 + 1;
            CursorCursorCursorCursorProd tmp_struct62 =
                                          _copy_Toplvl(end_r1860, end_r1861, loc2195, x1548);
            CursorTy pvrtmp5089 = tmp_struct62.field0;
            CursorTy pvrtmp5090 = tmp_struct62.field1;
            CursorTy pvrtmp5091 = tmp_struct62.field2;
            CursorTy pvrtmp5092 = tmp_struct62.field3;
            CursorTy fltPrd4389 = (CursorTy) pvrtmp5091;
            CursorTy fltPrd4390 = (CursorTy) pvrtmp5092;
            CursorTy pvrtmp5094 = (CursorTy) fltPrd4390;
            CursorTy pvrtmp5093 = (CursorTy) fltPrd4389;
            CursorTy y1550 = (CursorTy) pvrtmp5093;
            CursorTy fltPrd4391 = (CursorTy) pvrtmp5091;
            CursorTy fltPrd4392 = (CursorTy) pvrtmp5092;
            CursorTy pvrtmp5096 = (CursorTy) fltPrd4392;
            CursorTy pvrtmp5095 = (CursorTy) fltPrd4391;
            CursorTy end_y1550 = (CursorTy) pvrtmp5096;
            CursorTy end_r1861_3389 = (CursorTy) pvrtmp5089;
            CursorTy endof3112 = (CursorTy) pvrtmp5090;
            CursorTy case2188 = (CursorTy) endof3112;
            CursorTy x1549 = (CursorTy) case2188;
            CursorTy loc2196 = (CursorTy) end_y1550;
            CursorCursorCursorCursorProd tmp_struct63 =
                                          _copy_ListToplvl(end_r1860, end_r1861_3389, loc2196, x1549);
            CursorTy pvrtmp5097 = tmp_struct63.field0;
            CursorTy pvrtmp5098 = tmp_struct63.field1;
            CursorTy pvrtmp5099 = tmp_struct63.field2;
            CursorTy pvrtmp5100 = tmp_struct63.field3;
            CursorTy fltPrd4393 = (CursorTy) pvrtmp5099;
            CursorTy fltPrd4394 = (CursorTy) pvrtmp5100;
            CursorTy pvrtmp5102 = (CursorTy) fltPrd4394;
            CursorTy pvrtmp5101 = (CursorTy) fltPrd4393;
            CursorTy y1551 = (CursorTy) pvrtmp5101;
            CursorTy fltPrd4395 = (CursorTy) pvrtmp5099;
            CursorTy fltPrd4396 = (CursorTy) pvrtmp5100;
            CursorTy pvrtmp5104 = (CursorTy) fltPrd4396;
            CursorTy pvrtmp5103 = (CursorTy) fltPrd4395;
            CursorTy end_y1551 = (CursorTy) pvrtmp5104;
            CursorTy end_r1861_3389_3390 = (CursorTy) pvrtmp5097;
            CursorTy endof3113 = (CursorTy) pvrtmp5098;

            *(TagTyPacked *) loc1859 = 0;

            CursorTy writetag3616 = loc1859 + 1;
            CursorTy writecur3617 = (CursorTy) end_y1550;
            CursorTy writecur3618 = (CursorTy) end_y1551;
            CursorTy pvrtmp5106 = (CursorTy) writecur3618;
            CursorTy pvrtmp5105 = (CursorTy) loc1859;
            CursorTy taildc3114 = (CursorTy) pvrtmp5105;
            CursorTy end_taildc3114 = (CursorTy) pvrtmp5106;
            CursorTy pvrtmp5108 = (CursorTy) end_taildc3114;
            CursorTy pvrtmp5107 = (CursorTy) taildc3114;
            CursorTy fltPrd4397 = (CursorTy) pvrtmp5107;
            CursorTy fltPrd4398 = (CursorTy) pvrtmp5108;

            return (CursorCursorCursorCursorProd) {end_r1861_3389_3390,
                                                   endof3113, fltPrd4397,
                                                   fltPrd4398};
            break;
        }

      case 1:
        {
            CursorTy field_cur3620 = (CursorTy) tmpcur5088;
            CursorTy jump3115 = loc1858 + 1;

            *(TagTyPacked *) loc1859 = 1;

            CursorTy writetag3621 = loc1859 + 1;
            CursorTy pvrtmp5110 = (CursorTy) writetag3621;
            CursorTy pvrtmp5109 = (CursorTy) loc1859;
            CursorTy taildc3116 = (CursorTy) pvrtmp5109;
            CursorTy end_taildc3116 = (CursorTy) pvrtmp5110;
            CursorTy pvrtmp5112 = (CursorTy) end_taildc3116;
            CursorTy pvrtmp5111 = (CursorTy) taildc3116;
            CursorTy fltPrd4399 = (CursorTy) pvrtmp5111;
            CursorTy fltPrd4400 = (CursorTy) pvrtmp5112;

            return (CursorCursorCursorCursorProd) {end_r1861, jump3115,
                                                   fltPrd4399, fltPrd4400};
            break;
        }

      case 2:
        {
            CursorTy field_cur3623 = (CursorTy) tmpcur5088;
            CursorTy tmpcur5113 = *(CursorTy *) field_cur3623;
            CursorTy tmpaftercur5114 = field_cur3623 + 8;
            CursorTy case2200 = (CursorTy) field_cur3623;
            CursorTy x1552 = (CursorTy) tmpcur5113;
            CursorTy end_x1552 = (CursorTy) tmpaftercur5114;
            CursorTy case2201 = (CursorTy) end_x1552;
            CursorTy x1553 = (CursorTy) case2201;
            CursorTy case2202 = (CursorTy) x1552;
            CursorTy x1554 = (CursorTy) case2202;
            CursorTy jump3117 = case2200 + 8;
            CursorCursorCursorCursorProd tmp_struct64 =
                                          _copy_Toplvl(end_r1860, end_r1861, loc2210, x1553);
            CursorTy pvrtmp5115 = tmp_struct64.field0;
            CursorTy pvrtmp5116 = tmp_struct64.field1;
            CursorTy pvrtmp5117 = tmp_struct64.field2;
            CursorTy pvrtmp5118 = tmp_struct64.field3;
            CursorTy fltPrd4401 = (CursorTy) pvrtmp5117;
            CursorTy fltPrd4402 = (CursorTy) pvrtmp5118;
            CursorTy pvrtmp5120 = (CursorTy) fltPrd4402;
            CursorTy pvrtmp5119 = (CursorTy) fltPrd4401;
            CursorTy y1556 = (CursorTy) pvrtmp5119;
            CursorTy fltPrd4403 = (CursorTy) pvrtmp5117;
            CursorTy fltPrd4404 = (CursorTy) pvrtmp5118;
            CursorTy pvrtmp5122 = (CursorTy) fltPrd4404;
            CursorTy pvrtmp5121 = (CursorTy) fltPrd4403;
            CursorTy end_y1556 = (CursorTy) pvrtmp5122;
            CursorTy end_r1861_3391 = (CursorTy) pvrtmp5115;
            CursorTy endof3118 = (CursorTy) pvrtmp5116;
            CursorTy loc2211 = (CursorTy) end_y1556;
            CursorCursorCursorCursorProd tmp_struct65 =
                                          _copy_ListToplvl(end_r1860, end_r1861_3391, loc2211, x1554);
            CursorTy pvrtmp5123 = tmp_struct65.field0;
            CursorTy pvrtmp5124 = tmp_struct65.field1;
            CursorTy pvrtmp5125 = tmp_struct65.field2;
            CursorTy pvrtmp5126 = tmp_struct65.field3;
            CursorTy fltPrd4405 = (CursorTy) pvrtmp5125;
            CursorTy fltPrd4406 = (CursorTy) pvrtmp5126;
            CursorTy pvrtmp5128 = (CursorTy) fltPrd4406;
            CursorTy pvrtmp5127 = (CursorTy) fltPrd4405;
            CursorTy y1557 = (CursorTy) pvrtmp5127;
            CursorTy fltPrd4407 = (CursorTy) pvrtmp5125;
            CursorTy fltPrd4408 = (CursorTy) pvrtmp5126;
            CursorTy pvrtmp5130 = (CursorTy) fltPrd4408;
            CursorTy pvrtmp5129 = (CursorTy) fltPrd4407;
            CursorTy end_y1557 = (CursorTy) pvrtmp5130;
            CursorTy end_r1861_3391_3392 = (CursorTy) pvrtmp5123;
            CursorTy endof3119 = (CursorTy) pvrtmp5124;
            CursorTy y1555 = (CursorTy) end_y1556;

            *(TagTyPacked *) loc1859 = 2;

            CursorTy writetag3627 = loc1859 + 1;

            *(CursorTy *) writetag3627 = y1555;

            CursorTy writecur3628 = writetag3627 + 8;
            CursorTy writecur3629 = (CursorTy) end_y1556;
            CursorTy writecur3630 = (CursorTy) end_y1557;
            CursorTy pvrtmp5132 = (CursorTy) writecur3630;
            CursorTy pvrtmp5131 = (CursorTy) loc1859;
            CursorTy taildc3120 = (CursorTy) pvrtmp5131;
            CursorTy end_taildc3120 = (CursorTy) pvrtmp5132;
            CursorTy pvrtmp5134 = (CursorTy) end_taildc3120;
            CursorTy pvrtmp5133 = (CursorTy) taildc3120;
            CursorTy fltPrd4409 = (CursorTy) pvrtmp5133;
            CursorTy fltPrd4410 = (CursorTy) pvrtmp5134;

            return (CursorCursorCursorCursorProd) {end_r1861_3391_3392,
                                                   endof3119, fltPrd4409,
                                                   fltPrd4410};
            break;
        }

      case 153:
        {
            CursorTy field_cur3632 = (CursorTy) tmpcur5088;
            CursorTy case2216 = (CursorTy) field_cur3632;
            IntTy tmpval5135 = *(IntTy *) case2216;
            CursorTy tmpcur5136 = case2216 + sizeof(IntTy);
            IntTy x1558 = (IntTy) tmpval5135;
            CursorTy end_x1558 = (CursorTy) tmpcur5136;
            CursorTy case2217 = (CursorTy) end_x1558;
            IntTy tmpval5137 = *(IntTy *) case2217;
            CursorTy tmpcur5138 = case2217 + sizeof(IntTy);
            IntTy x1559 = (IntTy) tmpval5137;
            CursorTy end_x1559 = (CursorTy) tmpcur5138;
            CursorTy case2218 = (CursorTy) end_x1559;
            CursorTy x1560 = (CursorTy) case2218;
            CursorTy loc3636 = case2217 + x1559;
            CursorTy case2219 = loc3636 + 8;
            CursorTy x1561 = (CursorTy) case2219;
            CursorTy jump3122 = case2217 + 8;
            CursorTy jump3121 = case2216 + 8;
            CursorCursorCursorCursorProd tmp_struct66 =
                                          _copy_Toplvl(end_r1860, end_r1861, loc2228, x1560);
            CursorTy pvrtmp5139 = tmp_struct66.field0;
            CursorTy pvrtmp5140 = tmp_struct66.field1;
            CursorTy pvrtmp5141 = tmp_struct66.field2;
            CursorTy pvrtmp5142 = tmp_struct66.field3;
            CursorTy fltPrd4411 = (CursorTy) pvrtmp5141;
            CursorTy fltPrd4412 = (CursorTy) pvrtmp5142;
            CursorTy pvrtmp5144 = (CursorTy) fltPrd4412;
            CursorTy pvrtmp5143 = (CursorTy) fltPrd4411;
            CursorTy y1564 = (CursorTy) pvrtmp5143;
            CursorTy fltPrd4413 = (CursorTy) pvrtmp5141;
            CursorTy fltPrd4414 = (CursorTy) pvrtmp5142;
            CursorTy pvrtmp5146 = (CursorTy) fltPrd4414;
            CursorTy pvrtmp5145 = (CursorTy) fltPrd4413;
            CursorTy end_y1564 = (CursorTy) pvrtmp5146;
            CursorTy end_r1861_3393 = (CursorTy) pvrtmp5139;
            CursorTy endof3123 = (CursorTy) pvrtmp5140;
            CursorTy loc2229 = (CursorTy) end_y1564;
            CursorCursorCursorCursorProd tmp_struct67 =
                                          _copy_ListToplvl(end_r1860, end_r1861_3393, loc2229, x1561);
            CursorTy pvrtmp5147 = tmp_struct67.field0;
            CursorTy pvrtmp5148 = tmp_struct67.field1;
            CursorTy pvrtmp5149 = tmp_struct67.field2;
            CursorTy pvrtmp5150 = tmp_struct67.field3;
            CursorTy fltPrd4415 = (CursorTy) pvrtmp5149;
            CursorTy fltPrd4416 = (CursorTy) pvrtmp5150;
            CursorTy pvrtmp5152 = (CursorTy) fltPrd4416;
            CursorTy pvrtmp5151 = (CursorTy) fltPrd4415;
            CursorTy y1565 = (CursorTy) pvrtmp5151;
            CursorTy fltPrd4417 = (CursorTy) pvrtmp5149;
            CursorTy fltPrd4418 = (CursorTy) pvrtmp5150;
            CursorTy pvrtmp5154 = (CursorTy) fltPrd4418;
            CursorTy pvrtmp5153 = (CursorTy) fltPrd4417;
            CursorTy end_y1565 = (CursorTy) pvrtmp5154;
            CursorTy end_r1861_3393_3394 = (CursorTy) pvrtmp5147;
            CursorTy endof3124 = (CursorTy) pvrtmp5148;

            *(TagTyPacked *) loc1859 = 153;

            CursorTy writetag3639 = loc1859 + 1;

            *(IntTy *) writetag3639 = x1558;

            CursorTy writecur3640 = writetag3639 + sizeof(IntTy);

            *(IntTy *) writecur3640 = x1559;

            CursorTy writecur3641 = writecur3640 + sizeof(IntTy);
            CursorTy writecur3642 = (CursorTy) end_y1564;
            CursorTy writecur3643 = (CursorTy) end_y1565;
            CursorTy pvrtmp5156 = (CursorTy) writecur3643;
            CursorTy pvrtmp5155 = (CursorTy) loc1859;
            CursorTy taildc3125 = (CursorTy) pvrtmp5155;
            CursorTy end_taildc3125 = (CursorTy) pvrtmp5156;
            CursorTy pvrtmp5158 = (CursorTy) end_taildc3125;
            CursorTy pvrtmp5157 = (CursorTy) taildc3125;
            CursorTy fltPrd4419 = (CursorTy) pvrtmp5157;
            CursorTy fltPrd4420 = (CursorTy) pvrtmp5158;

            return (CursorCursorCursorCursorProd) {end_r1861_3393_3394,
                                                   endof3124, fltPrd4419,
                                                   fltPrd4420};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6598 = *(CursorTy *) tmpcur5088;
            CursorTy tmpaftercur6599 = tmpcur5088 + 8;
            TagTyPacked tagtmp6600 = *(TagTyPacked *) tmpcur6598;
            CursorTy tailtmp6601 = tmpcur6598 + 1;

            tmpval5087 = tagtmp6600;
            tmpcur5088 = tailtmp6601;
            goto switch5159;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6598 = *(CursorTy *) tmpcur5088;
            CursorTy tmpaftercur6599 = tmpcur5088 + 8;
            TagTyPacked tagtmp6600 = *(TagTyPacked *) tmpcur6598;
            CursorTy tailtmp6601 = tmpcur6598 + 1;

            tmpval5087 = tagtmp6600;
            tmpcur5088 = tailtmp6601;
            goto switch5159;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5087");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_ListToplvl(CursorTy end_r1863, CursorTy arg1566)
{
    CursorTy loc1862 = (CursorTy) arg1566;
    TagTyPacked tmpval5160 = *(TagTyPacked *) arg1566;
    CursorTy tmpcur5161 = arg1566 + 1;


  switch5180:
    ;
    switch (tmpval5160) {

      case 0:
        {
            CursorTy field_cur3645 = (CursorTy) tmpcur5161;
            CursorTy case2238 = (CursorTy) field_cur3645;
            CursorTy x1567 = (CursorTy) case2238;
            CursorInt64Prod tmp_struct71 =  _traverse_Toplvl(end_r1863, x1567);
            CursorTy pvrtmp5162 = tmp_struct71.field0;
            IntTy pvrtmp5163 = tmp_struct71.field1;
            CursorTy endof3126 = (CursorTy) pvrtmp5162;
            IntTy y1569 = (IntTy) pvrtmp5163;
            CursorTy case2239 = (CursorTy) endof3126;
            CursorTy x1568 = (CursorTy) case2239;
            CursorInt64Prod tmp_struct72 =
                             _traverse_ListToplvl(end_r1863, x1568);
            CursorTy pvrtmp5164 = tmp_struct72.field0;
            IntTy pvrtmp5165 = tmp_struct72.field1;
            CursorTy endof3128 = (CursorTy) pvrtmp5164;
            IntTy y1570 = (IntTy) pvrtmp5165;
            IntTy fltLitTail3127 = (IntTy) 42;

            return (CursorInt64Prod) {endof3128, fltLitTail3127};
            break;
        }

      case 1:
        {
            CursorTy field_cur3648 = (CursorTy) tmpcur5161;
            CursorTy jump3129 = loc1862 + 1;
            IntTy fltLitTail3130 = (IntTy) 42;

            return (CursorInt64Prod) {jump3129, fltLitTail3130};
            break;
        }

      case 2:
        {
            CursorTy field_cur3649 = (CursorTy) tmpcur5161;
            CursorTy tmpcur5166 = *(CursorTy *) field_cur3649;
            CursorTy tmpaftercur5167 = field_cur3649 + 8;
            CursorTy case2244 = (CursorTy) field_cur3649;
            CursorTy x1571 = (CursorTy) tmpcur5166;
            CursorTy end_x1571 = (CursorTy) tmpaftercur5167;
            CursorTy case2245 = (CursorTy) end_x1571;
            CursorTy x1572 = (CursorTy) case2245;
            CursorTy case2246 = (CursorTy) x1571;
            CursorTy x1573 = (CursorTy) case2246;
            CursorTy jump3131 = case2244 + 8;
            CursorInt64Prod tmp_struct73 =  _traverse_Toplvl(end_r1863, x1572);
            CursorTy pvrtmp5168 = tmp_struct73.field0;
            IntTy pvrtmp5169 = tmp_struct73.field1;
            CursorTy endof3132 = (CursorTy) pvrtmp5168;
            IntTy y1575 = (IntTy) pvrtmp5169;
            CursorInt64Prod tmp_struct74 =
                             _traverse_ListToplvl(end_r1863, x1573);
            CursorTy pvrtmp5170 = tmp_struct74.field0;
            IntTy pvrtmp5171 = tmp_struct74.field1;
            CursorTy endof3134 = (CursorTy) pvrtmp5170;
            IntTy y1576 = (IntTy) pvrtmp5171;
            IntTy fltLitTail3133 = (IntTy) 42;

            return (CursorInt64Prod) {endof3134, fltLitTail3133};
            break;
        }

      case 153:
        {
            CursorTy field_cur3653 = (CursorTy) tmpcur5161;
            CursorTy case2251 = (CursorTy) field_cur3653;
            IntTy tmpval5172 = *(IntTy *) case2251;
            CursorTy tmpcur5173 = case2251 + sizeof(IntTy);
            IntTy x1577 = (IntTy) tmpval5172;
            CursorTy end_x1577 = (CursorTy) tmpcur5173;
            CursorTy case2252 = (CursorTy) end_x1577;
            IntTy tmpval5174 = *(IntTy *) case2252;
            CursorTy tmpcur5175 = case2252 + sizeof(IntTy);
            IntTy x1578 = (IntTy) tmpval5174;
            CursorTy end_x1578 = (CursorTy) tmpcur5175;
            CursorTy case2253 = (CursorTy) end_x1578;
            CursorTy x1579 = (CursorTy) case2253;
            CursorTy loc3657 = case2252 + x1578;
            CursorTy case2254 = loc3657 + 8;
            CursorTy x1580 = (CursorTy) case2254;
            CursorTy jump3136 = case2252 + 8;
            CursorTy jump3135 = case2251 + 8;
            CursorInt64Prod tmp_struct75 =  _traverse_Toplvl(end_r1863, x1579);
            CursorTy pvrtmp5176 = tmp_struct75.field0;
            IntTy pvrtmp5177 = tmp_struct75.field1;
            CursorTy endof3137 = (CursorTy) pvrtmp5176;
            IntTy y1583 = (IntTy) pvrtmp5177;
            CursorInt64Prod tmp_struct76 =
                             _traverse_ListToplvl(end_r1863, x1580);
            CursorTy pvrtmp5178 = tmp_struct76.field0;
            IntTy pvrtmp5179 = tmp_struct76.field1;
            CursorTy endof3139 = (CursorTy) pvrtmp5178;
            IntTy y1584 = (IntTy) pvrtmp5179;
            IntTy fltLitTail3138 = (IntTy) 42;

            return (CursorInt64Prod) {endof3139, fltLitTail3138};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6602 = *(CursorTy *) tmpcur5161;
            CursorTy tmpaftercur6603 = tmpcur5161 + 8;
            TagTyPacked tagtmp6604 = *(TagTyPacked *) tmpcur6602;
            CursorTy tailtmp6605 = tmpcur6602 + 1;

            tmpval5160 = tagtmp6604;
            tmpcur5161 = tailtmp6605;
            goto switch5180;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6602 = *(CursorTy *) tmpcur5161;
            CursorTy tmpaftercur6603 = tmpcur5161 + 8;
            TagTyPacked tagtmp6604 = *(TagTyPacked *) tmpcur6602;
            CursorTy tailtmp6605 = tmpcur6602 + 1;

            tmpval5160 = tagtmp6604;
            tmpcur5161 = tailtmp6605;
            goto switch5180;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5160");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r1866,
                                           CursorTy end_r1867, CursorTy loc1865,
                                           CursorTy arg1585)
{
    CursorTy loc1864 = (CursorTy) arg1585;

    if (loc1865 + 18 > end_r1867) {
        ChunkTy new_chunk79 = alloc_chunk(end_r1867);
        CursorTy chunk_start80 = new_chunk79.start_ptr;
        CursorTy chunk_end81 = new_chunk79.end_ptr;

        end_r1867 = chunk_end81;
        *(TagTyPacked *) loc1865 = 255;

        CursorTy redir = loc1865 + 1;

        *(CursorTy *) redir = chunk_start80;
        loc1865 = chunk_start80;
    }

    TagTyPacked tmpval5181 = *(TagTyPacked *) arg1585;
    CursorTy tmpcur5182 = arg1585 + 1;


  switch5215:
    ;
    switch (tmpval5181) {

      case 0:
        {
            CursorTy field_cur3660 = (CursorTy) tmpcur5182;
            CursorTy case2261 = (CursorTy) field_cur3660;
            CursorTy x1586 = (CursorTy) case2261;
            CursorTy loc2265 = loc1865 + 1;
            CursorCursorCursorCursorProd tmp_struct77 =
                                          _copy_ListSym(end_r1866, end_r1867, loc2265, x1586);
            CursorTy pvrtmp5183 = tmp_struct77.field0;
            CursorTy pvrtmp5184 = tmp_struct77.field1;
            CursorTy pvrtmp5185 = tmp_struct77.field2;
            CursorTy pvrtmp5186 = tmp_struct77.field3;
            CursorTy fltPrd4421 = (CursorTy) pvrtmp5185;
            CursorTy fltPrd4422 = (CursorTy) pvrtmp5186;
            CursorTy pvrtmp5188 = (CursorTy) fltPrd4422;
            CursorTy pvrtmp5187 = (CursorTy) fltPrd4421;
            CursorTy y1587 = (CursorTy) pvrtmp5187;
            CursorTy fltPrd4423 = (CursorTy) pvrtmp5185;
            CursorTy fltPrd4424 = (CursorTy) pvrtmp5186;
            CursorTy pvrtmp5190 = (CursorTy) fltPrd4424;
            CursorTy pvrtmp5189 = (CursorTy) fltPrd4423;
            CursorTy end_y1587 = (CursorTy) pvrtmp5190;
            CursorTy end_r1867_3395 = (CursorTy) pvrtmp5183;
            CursorTy endof3140 = (CursorTy) pvrtmp5184;

            *(TagTyPacked *) loc1865 = 0;

            CursorTy writetag3662 = loc1865 + 1;
            CursorTy writecur3663 = (CursorTy) end_y1587;
            CursorTy pvrtmp5192 = (CursorTy) writecur3663;
            CursorTy pvrtmp5191 = (CursorTy) loc1865;
            CursorTy taildc3141 = (CursorTy) pvrtmp5191;
            CursorTy end_taildc3141 = (CursorTy) pvrtmp5192;
            CursorTy pvrtmp5194 = (CursorTy) end_taildc3141;
            CursorTy pvrtmp5193 = (CursorTy) taildc3141;
            CursorTy fltPrd4425 = (CursorTy) pvrtmp5193;
            CursorTy fltPrd4426 = (CursorTy) pvrtmp5194;

            return (CursorCursorCursorCursorProd) {end_r1867_3395, endof3140,
                                                   fltPrd4425, fltPrd4426};
            break;
        }

      case 1:
        {
            CursorTy field_cur3665 = (CursorTy) tmpcur5182;
            CursorTy case2267 = (CursorTy) field_cur3665;
            CursorTy x1588 = (CursorTy) case2267;
            CursorTy loc2272 = loc1865 + 1;
            CursorCursorCursorCursorProd tmp_struct78 =
                                          _copy_ListSym(end_r1866, end_r1867, loc2272, x1588);
            CursorTy pvrtmp5195 = tmp_struct78.field0;
            CursorTy pvrtmp5196 = tmp_struct78.field1;
            CursorTy pvrtmp5197 = tmp_struct78.field2;
            CursorTy pvrtmp5198 = tmp_struct78.field3;
            CursorTy fltPrd4427 = (CursorTy) pvrtmp5197;
            CursorTy fltPrd4428 = (CursorTy) pvrtmp5198;
            CursorTy pvrtmp5200 = (CursorTy) fltPrd4428;
            CursorTy pvrtmp5199 = (CursorTy) fltPrd4427;
            CursorTy y1590 = (CursorTy) pvrtmp5199;
            CursorTy fltPrd4429 = (CursorTy) pvrtmp5197;
            CursorTy fltPrd4430 = (CursorTy) pvrtmp5198;
            CursorTy pvrtmp5202 = (CursorTy) fltPrd4430;
            CursorTy pvrtmp5201 = (CursorTy) fltPrd4429;
            CursorTy end_y1590 = (CursorTy) pvrtmp5202;
            CursorTy end_r1867_3396 = (CursorTy) pvrtmp5195;
            CursorTy endof3143 = (CursorTy) pvrtmp5196;
            CursorTy case2268 = (CursorTy) endof3143;
            CursorTy jump3142 = case2268 + 8;
            SymTy tmpval5203 = *(SymTy *) case2268;
            CursorTy tmpcur5204 = case2268 + sizeof(SymTy);
            SymTy x1589 = (SymTy) tmpval5203;
            CursorTy end_x1589 = (CursorTy) tmpcur5204;

            *(TagTyPacked *) loc1865 = 1;

            CursorTy writetag3668 = loc1865 + 1;
            CursorTy writecur3669 = (CursorTy) end_y1590;

            *(SymTy *) writecur3669 = x1589;

            CursorTy writecur3670 = writecur3669 + sizeof(SymTy);
            CursorTy pvrtmp5206 = (CursorTy) writecur3670;
            CursorTy pvrtmp5205 = (CursorTy) loc1865;
            CursorTy taildc3144 = (CursorTy) pvrtmp5205;
            CursorTy end_taildc3144 = (CursorTy) pvrtmp5206;
            CursorTy pvrtmp5208 = (CursorTy) end_taildc3144;
            CursorTy pvrtmp5207 = (CursorTy) taildc3144;
            CursorTy fltPrd4431 = (CursorTy) pvrtmp5207;
            CursorTy fltPrd4432 = (CursorTy) pvrtmp5208;

            return (CursorCursorCursorCursorProd) {end_r1867_3396, jump3142,
                                                   fltPrd4431, fltPrd4432};
            break;
        }

      case 2:
        {
            CursorTy field_cur3672 = (CursorTy) tmpcur5182;
            CursorTy case2277 = (CursorTy) field_cur3672;
            SymTy tmpval5209 = *(SymTy *) case2277;
            CursorTy tmpcur5210 = case2277 + sizeof(SymTy);
            SymTy x1592 = (SymTy) tmpval5209;
            CursorTy end_x1592 = (CursorTy) tmpcur5210;
            CursorTy jump3145 = case2277 + 8;

            *(TagTyPacked *) loc1865 = 2;

            CursorTy writetag3674 = loc1865 + 1;

            *(SymTy *) writetag3674 = x1592;

            CursorTy writecur3675 = writetag3674 + sizeof(SymTy);
            CursorTy pvrtmp5212 = (CursorTy) writecur3675;
            CursorTy pvrtmp5211 = (CursorTy) loc1865;
            CursorTy taildc3146 = (CursorTy) pvrtmp5211;
            CursorTy end_taildc3146 = (CursorTy) pvrtmp5212;
            CursorTy pvrtmp5214 = (CursorTy) end_taildc3146;
            CursorTy pvrtmp5213 = (CursorTy) taildc3146;
            CursorTy fltPrd4433 = (CursorTy) pvrtmp5213;
            CursorTy fltPrd4434 = (CursorTy) pvrtmp5214;

            return (CursorCursorCursorCursorProd) {end_r1867, jump3145,
                                                   fltPrd4433, fltPrd4434};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6606 = *(CursorTy *) tmpcur5182;
            CursorTy tmpaftercur6607 = tmpcur5182 + 8;
            TagTyPacked tagtmp6608 = *(TagTyPacked *) tmpcur6606;
            CursorTy tailtmp6609 = tmpcur6606 + 1;

            tmpval5181 = tagtmp6608;
            tmpcur5182 = tailtmp6609;
            goto switch5215;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6606 = *(CursorTy *) tmpcur5182;
            CursorTy tmpaftercur6607 = tmpcur5182 + 8;
            TagTyPacked tagtmp6608 = *(TagTyPacked *) tmpcur6606;
            CursorTy tailtmp6609 = tmpcur6606 + 1;

            tmpval5181 = tagtmp6608;
            tmpcur5182 = tailtmp6609;
            goto switch5215;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5181");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Formals(CursorTy end_r1869, CursorTy arg1594)
{
    CursorTy loc1868 = (CursorTy) arg1594;
    TagTyPacked tmpval5216 = *(TagTyPacked *) arg1594;
    CursorTy tmpcur5217 = arg1594 + 1;


  switch5226:
    ;
    switch (tmpval5216) {

      case 0:
        {
            CursorTy field_cur3677 = (CursorTy) tmpcur5217;
            CursorTy case2283 = (CursorTy) field_cur3677;
            CursorTy x1595 = (CursorTy) case2283;
            CursorInt64Prod tmp_struct82 =  _traverse_ListSym(end_r1869, x1595);
            CursorTy pvrtmp5218 = tmp_struct82.field0;
            IntTy pvrtmp5219 = tmp_struct82.field1;
            CursorTy endof3148 = (CursorTy) pvrtmp5218;
            IntTy y1596 = (IntTy) pvrtmp5219;
            IntTy fltLitTail3147 = (IntTy) 42;

            return (CursorInt64Prod) {endof3148, fltLitTail3147};
            break;
        }

      case 1:
        {
            CursorTy field_cur3679 = (CursorTy) tmpcur5217;
            CursorTy case2286 = (CursorTy) field_cur3679;
            CursorTy x1597 = (CursorTy) case2286;
            CursorInt64Prod tmp_struct83 =  _traverse_ListSym(end_r1869, x1597);
            CursorTy pvrtmp5220 = tmp_struct83.field0;
            IntTy pvrtmp5221 = tmp_struct83.field1;
            CursorTy endof3151 = (CursorTy) pvrtmp5220;
            IntTy y1599 = (IntTy) pvrtmp5221;
            CursorTy case2287 = (CursorTy) endof3151;
            CursorTy jump3149 = case2287 + 8;
            SymTy tmpval5222 = *(SymTy *) case2287;
            CursorTy tmpcur5223 = case2287 + sizeof(SymTy);
            SymTy x1598 = (SymTy) tmpval5222;
            CursorTy end_x1598 = (CursorTy) tmpcur5223;
            IntTy fltLitTail3150 = (IntTy) 42;

            return (CursorInt64Prod) {jump3149, fltLitTail3150};
            break;
        }

      case 2:
        {
            CursorTy field_cur3682 = (CursorTy) tmpcur5217;
            CursorTy case2290 = (CursorTy) field_cur3682;
            SymTy tmpval5224 = *(SymTy *) case2290;
            CursorTy tmpcur5225 = case2290 + sizeof(SymTy);
            SymTy x1601 = (SymTy) tmpval5224;
            CursorTy end_x1601 = (CursorTy) tmpcur5225;
            CursorTy jump3152 = case2290 + 8;
            IntTy fltLitTail3153 = (IntTy) 42;

            return (CursorInt64Prod) {jump3152, fltLitTail3153};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6610 = *(CursorTy *) tmpcur5217;
            CursorTy tmpaftercur6611 = tmpcur5217 + 8;
            TagTyPacked tagtmp6612 = *(TagTyPacked *) tmpcur6610;
            CursorTy tailtmp6613 = tmpcur6610 + 1;

            tmpval5216 = tagtmp6612;
            tmpcur5217 = tailtmp6613;
            goto switch5226;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6610 = *(CursorTy *) tmpcur5217;
            CursorTy tmpaftercur6611 = tmpcur5217 + 8;
            TagTyPacked tagtmp6612 = *(TagTyPacked *) tmpcur6610;
            CursorTy tailtmp6613 = tmpcur6610 + 1;

            tmpval5216 = tagtmp6612;
            tmpcur5217 = tailtmp6613;
            goto switch5226;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5216");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r1872, CursorTy end_r1873,
                                         CursorTy loc1871, CursorTy arg1603)
{
    CursorTy loc1870 = (CursorTy) arg1603;

    if (loc1871 + 18 > end_r1873) {
        ChunkTy new_chunk84 = alloc_chunk(end_r1873);
        CursorTy chunk_start85 = new_chunk84.start_ptr;
        CursorTy chunk_end86 = new_chunk84.end_ptr;

        end_r1873 = chunk_end86;
        *(TagTyPacked *) loc1871 = 255;

        CursorTy redir = loc1871 + 1;

        *(CursorTy *) redir = chunk_start85;
        loc1871 = chunk_start85;
    }

    TagTyPacked tmpval5227 = *(TagTyPacked *) arg1603;
    CursorTy tmpcur5228 = arg1603 + 1;


  switch5235:
    ;
    switch (tmpval5227) {

      case 0:
        {
            CursorTy field_cur3684 = (CursorTy) tmpcur5228;
            CursorTy case2293 = (CursorTy) field_cur3684;
            IntTy tmpval5229 = *(IntTy *) case2293;
            CursorTy tmpcur5230 = case2293 + sizeof(IntTy);
            IntTy x1604 = (IntTy) tmpval5229;
            CursorTy end_x1604 = (CursorTy) tmpcur5230;
            CursorTy jump3154 = case2293 + 8;

            *(TagTyPacked *) loc1871 = 0;

            CursorTy writetag3686 = loc1871 + 1;

            *(IntTy *) writetag3686 = x1604;

            CursorTy writecur3687 = writetag3686 + sizeof(IntTy);
            CursorTy pvrtmp5232 = (CursorTy) writecur3687;
            CursorTy pvrtmp5231 = (CursorTy) loc1871;
            CursorTy taildc3155 = (CursorTy) pvrtmp5231;
            CursorTy end_taildc3155 = (CursorTy) pvrtmp5232;
            CursorTy pvrtmp5234 = (CursorTy) end_taildc3155;
            CursorTy pvrtmp5233 = (CursorTy) taildc3155;
            CursorTy fltPrd4435 = (CursorTy) pvrtmp5233;
            CursorTy fltPrd4436 = (CursorTy) pvrtmp5234;

            return (CursorCursorCursorCursorProd) {end_r1873, jump3154,
                                                   fltPrd4435, fltPrd4436};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6614 = *(CursorTy *) tmpcur5228;
            CursorTy tmpaftercur6615 = tmpcur5228 + 8;
            TagTyPacked tagtmp6616 = *(TagTyPacked *) tmpcur6614;
            CursorTy tailtmp6617 = tmpcur6614 + 1;

            tmpval5227 = tagtmp6616;
            tmpcur5228 = tailtmp6617;
            goto switch5235;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6614 = *(CursorTy *) tmpcur5228;
            CursorTy tmpaftercur6615 = tmpcur5228 + 8;
            TagTyPacked tagtmp6616 = *(TagTyPacked *) tmpcur6614;
            CursorTy tailtmp6617 = tmpcur6614 + 1;

            tmpval5227 = tagtmp6616;
            tmpcur5228 = tailtmp6617;
            goto switch5235;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5227");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Datum(CursorTy end_r1875, CursorTy arg1606)
{
    CursorTy loc1874 = (CursorTy) arg1606;
    TagTyPacked tmpval5236 = *(TagTyPacked *) arg1606;
    CursorTy tmpcur5237 = arg1606 + 1;


  switch5240:
    ;
    switch (tmpval5236) {

      case 0:
        {
            CursorTy field_cur3689 = (CursorTy) tmpcur5237;
            CursorTy case2299 = (CursorTy) field_cur3689;
            IntTy tmpval5238 = *(IntTy *) case2299;
            CursorTy tmpcur5239 = case2299 + sizeof(IntTy);
            IntTy x1607 = (IntTy) tmpval5238;
            CursorTy end_x1607 = (CursorTy) tmpcur5239;
            CursorTy jump3156 = case2299 + 8;
            IntTy fltLitTail3157 = (IntTy) 42;

            return (CursorInt64Prod) {jump3156, fltLitTail3157};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6618 = *(CursorTy *) tmpcur5237;
            CursorTy tmpaftercur6619 = tmpcur5237 + 8;
            TagTyPacked tagtmp6620 = *(TagTyPacked *) tmpcur6618;
            CursorTy tailtmp6621 = tmpcur6618 + 1;

            tmpval5236 = tagtmp6620;
            tmpcur5237 = tailtmp6621;
            goto switch5240;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6618 = *(CursorTy *) tmpcur5237;
            CursorTy tmpaftercur6619 = tmpcur5237 + 8;
            TagTyPacked tagtmp6620 = *(TagTyPacked *) tmpcur6618;
            CursorTy tailtmp6621 = tmpcur6618 + 1;

            tmpval5236 = tagtmp6620;
            tmpcur5237 = tailtmp6621;
            goto switch5240;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5236");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r1878,
                                              CursorTy end_r1879,
                                              CursorTy loc1877,
                                              CursorTy arg1609)
{
    CursorTy loc1876 = (CursorTy) arg1609;

    if (loc1877 + 18 > end_r1879) {
        ChunkTy new_chunk90 = alloc_chunk(end_r1879);
        CursorTy chunk_start91 = new_chunk90.start_ptr;
        CursorTy chunk_end92 = new_chunk90.end_ptr;

        end_r1879 = chunk_end92;
        *(TagTyPacked *) loc1877 = 255;

        CursorTy redir = loc1877 + 1;

        *(CursorTy *) redir = chunk_start91;
        loc1877 = chunk_start91;
    }

    TagTyPacked tmpval5241 = *(TagTyPacked *) arg1609;
    CursorTy tmpcur5242 = arg1609 + 1;


  switch5275:
    ;
    switch (tmpval5241) {

      case 0:
        {
            CursorTy field_cur3691 = (CursorTy) tmpcur5242;
            CursorTy case2302 = (CursorTy) field_cur3691;
            CursorTy x1610 = (CursorTy) case2302;
            CursorTy loc2314 = loc1877 + 1;
            CursorCursorCursorCursorProd tmp_struct87 =
                                          _copy_Formals(end_r1878, end_r1879, loc2314, x1610);
            CursorTy pvrtmp5243 = tmp_struct87.field0;
            CursorTy pvrtmp5244 = tmp_struct87.field1;
            CursorTy pvrtmp5245 = tmp_struct87.field2;
            CursorTy pvrtmp5246 = tmp_struct87.field3;
            CursorTy fltPrd4437 = (CursorTy) pvrtmp5245;
            CursorTy fltPrd4438 = (CursorTy) pvrtmp5246;
            CursorTy pvrtmp5248 = (CursorTy) fltPrd4438;
            CursorTy pvrtmp5247 = (CursorTy) fltPrd4437;
            CursorTy y1613 = (CursorTy) pvrtmp5247;
            CursorTy fltPrd4439 = (CursorTy) pvrtmp5245;
            CursorTy fltPrd4440 = (CursorTy) pvrtmp5246;
            CursorTy pvrtmp5250 = (CursorTy) fltPrd4440;
            CursorTy pvrtmp5249 = (CursorTy) fltPrd4439;
            CursorTy end_y1613 = (CursorTy) pvrtmp5250;
            CursorTy end_r1879_3397 = (CursorTy) pvrtmp5243;
            CursorTy endof3158 = (CursorTy) pvrtmp5244;
            CursorTy case2303 = (CursorTy) endof3158;
            CursorTy x1611 = (CursorTy) case2303;
            CursorTy loc2315 = (CursorTy) end_y1613;
            CursorCursorCursorCursorProd tmp_struct88 =
                                          _copy_ListExpr(end_r1878, end_r1879_3397, loc2315, x1611);
            CursorTy pvrtmp5251 = tmp_struct88.field0;
            CursorTy pvrtmp5252 = tmp_struct88.field1;
            CursorTy pvrtmp5253 = tmp_struct88.field2;
            CursorTy pvrtmp5254 = tmp_struct88.field3;
            CursorTy fltPrd4441 = (CursorTy) pvrtmp5253;
            CursorTy fltPrd4442 = (CursorTy) pvrtmp5254;
            CursorTy pvrtmp5256 = (CursorTy) fltPrd4442;
            CursorTy pvrtmp5255 = (CursorTy) fltPrd4441;
            CursorTy y1614 = (CursorTy) pvrtmp5255;
            CursorTy fltPrd4443 = (CursorTy) pvrtmp5253;
            CursorTy fltPrd4444 = (CursorTy) pvrtmp5254;
            CursorTy pvrtmp5258 = (CursorTy) fltPrd4444;
            CursorTy pvrtmp5257 = (CursorTy) fltPrd4443;
            CursorTy end_y1614 = (CursorTy) pvrtmp5258;
            CursorTy end_r1879_3397_3398 = (CursorTy) pvrtmp5251;
            CursorTy endof3159 = (CursorTy) pvrtmp5252;
            CursorTy case2304 = (CursorTy) endof3159;
            CursorTy x1612 = (CursorTy) case2304;
            CursorTy loc2316 = (CursorTy) end_y1614;
            CursorCursorCursorCursorProd tmp_struct89 =
                                          _copy_LAMBDACASE(end_r1878, end_r1879_3397_3398, loc2316, x1612);
            CursorTy pvrtmp5259 = tmp_struct89.field0;
            CursorTy pvrtmp5260 = tmp_struct89.field1;
            CursorTy pvrtmp5261 = tmp_struct89.field2;
            CursorTy pvrtmp5262 = tmp_struct89.field3;
            CursorTy fltPrd4445 = (CursorTy) pvrtmp5261;
            CursorTy fltPrd4446 = (CursorTy) pvrtmp5262;
            CursorTy pvrtmp5264 = (CursorTy) fltPrd4446;
            CursorTy pvrtmp5263 = (CursorTy) fltPrd4445;
            CursorTy y1615 = (CursorTy) pvrtmp5263;
            CursorTy fltPrd4447 = (CursorTy) pvrtmp5261;
            CursorTy fltPrd4448 = (CursorTy) pvrtmp5262;
            CursorTy pvrtmp5266 = (CursorTy) fltPrd4448;
            CursorTy pvrtmp5265 = (CursorTy) fltPrd4447;
            CursorTy end_y1615 = (CursorTy) pvrtmp5266;
            CursorTy end_r1879_3397_3398_3399 = (CursorTy) pvrtmp5259;
            CursorTy endof3160 = (CursorTy) pvrtmp5260;

            *(TagTyPacked *) loc1877 = 0;

            CursorTy writetag3695 = loc1877 + 1;
            CursorTy writecur3696 = (CursorTy) end_y1613;
            CursorTy writecur3697 = (CursorTy) end_y1614;
            CursorTy writecur3698 = (CursorTy) end_y1615;
            CursorTy pvrtmp5268 = (CursorTy) writecur3698;
            CursorTy pvrtmp5267 = (CursorTy) loc1877;
            CursorTy taildc3161 = (CursorTy) pvrtmp5267;
            CursorTy end_taildc3161 = (CursorTy) pvrtmp5268;
            CursorTy pvrtmp5270 = (CursorTy) end_taildc3161;
            CursorTy pvrtmp5269 = (CursorTy) taildc3161;
            CursorTy fltPrd4449 = (CursorTy) pvrtmp5269;
            CursorTy fltPrd4450 = (CursorTy) pvrtmp5270;

            return (CursorCursorCursorCursorProd) {end_r1879_3397_3398_3399,
                                                   endof3160, fltPrd4449,
                                                   fltPrd4450};
            break;
        }

      case 1:
        {
            CursorTy field_cur3700 = (CursorTy) tmpcur5242;
            CursorTy jump3162 = loc1876 + 1;

            *(TagTyPacked *) loc1877 = 1;

            CursorTy writetag3701 = loc1877 + 1;
            CursorTy pvrtmp5272 = (CursorTy) writetag3701;
            CursorTy pvrtmp5271 = (CursorTy) loc1877;
            CursorTy taildc3163 = (CursorTy) pvrtmp5271;
            CursorTy end_taildc3163 = (CursorTy) pvrtmp5272;
            CursorTy pvrtmp5274 = (CursorTy) end_taildc3163;
            CursorTy pvrtmp5273 = (CursorTy) taildc3163;
            CursorTy fltPrd4451 = (CursorTy) pvrtmp5273;
            CursorTy fltPrd4452 = (CursorTy) pvrtmp5274;

            return (CursorCursorCursorCursorProd) {end_r1879, jump3162,
                                                   fltPrd4451, fltPrd4452};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6622 = *(CursorTy *) tmpcur5242;
            CursorTy tmpaftercur6623 = tmpcur5242 + 8;
            TagTyPacked tagtmp6624 = *(TagTyPacked *) tmpcur6622;
            CursorTy tailtmp6625 = tmpcur6622 + 1;

            tmpval5241 = tagtmp6624;
            tmpcur5242 = tailtmp6625;
            goto switch5275;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6622 = *(CursorTy *) tmpcur5242;
            CursorTy tmpaftercur6623 = tmpcur5242 + 8;
            TagTyPacked tagtmp6624 = *(TagTyPacked *) tmpcur6622;
            CursorTy tailtmp6625 = tmpcur6622 + 1;

            tmpval5241 = tagtmp6624;
            tmpcur5242 = tailtmp6625;
            goto switch5275;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5241");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_LAMBDACASE(CursorTy end_r1881, CursorTy arg1616)
{
    CursorTy loc1880 = (CursorTy) arg1616;
    TagTyPacked tmpval5276 = *(TagTyPacked *) arg1616;
    CursorTy tmpcur5277 = arg1616 + 1;


  switch5284:
    ;
    switch (tmpval5276) {

      case 0:
        {
            CursorTy field_cur3703 = (CursorTy) tmpcur5277;
            CursorTy case2323 = (CursorTy) field_cur3703;
            CursorTy x1617 = (CursorTy) case2323;
            CursorInt64Prod tmp_struct93 =  _traverse_Formals(end_r1881, x1617);
            CursorTy pvrtmp5278 = tmp_struct93.field0;
            IntTy pvrtmp5279 = tmp_struct93.field1;
            CursorTy endof3164 = (CursorTy) pvrtmp5278;
            IntTy y1620 = (IntTy) pvrtmp5279;
            CursorTy case2324 = (CursorTy) endof3164;
            CursorTy x1618 = (CursorTy) case2324;
            CursorInt64Prod tmp_struct94 =
                             _traverse_ListExpr(end_r1881, x1618);
            CursorTy pvrtmp5280 = tmp_struct94.field0;
            IntTy pvrtmp5281 = tmp_struct94.field1;
            CursorTy endof3165 = (CursorTy) pvrtmp5280;
            IntTy y1621 = (IntTy) pvrtmp5281;
            CursorTy case2325 = (CursorTy) endof3165;
            CursorTy x1619 = (CursorTy) case2325;
            CursorInt64Prod tmp_struct95 =
                             _traverse_LAMBDACASE(end_r1881, x1619);
            CursorTy pvrtmp5282 = tmp_struct95.field0;
            IntTy pvrtmp5283 = tmp_struct95.field1;
            CursorTy endof3167 = (CursorTy) pvrtmp5282;
            IntTy y1622 = (IntTy) pvrtmp5283;
            IntTy fltLitTail3166 = (IntTy) 42;

            return (CursorInt64Prod) {endof3167, fltLitTail3166};
            break;
        }

      case 1:
        {
            CursorTy field_cur3707 = (CursorTy) tmpcur5277;
            CursorTy jump3168 = loc1880 + 1;
            IntTy fltLitTail3169 = (IntTy) 42;

            return (CursorInt64Prod) {jump3168, fltLitTail3169};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6626 = *(CursorTy *) tmpcur5277;
            CursorTy tmpaftercur6627 = tmpcur5277 + 8;
            TagTyPacked tagtmp6628 = *(TagTyPacked *) tmpcur6626;
            CursorTy tailtmp6629 = tmpcur6626 + 1;

            tmpval5276 = tagtmp6628;
            tmpcur5277 = tailtmp6629;
            goto switch5284;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6626 = *(CursorTy *) tmpcur5277;
            CursorTy tmpaftercur6627 = tmpcur5277 + 8;
            TagTyPacked tagtmp6628 = *(TagTyPacked *) tmpcur6626;
            CursorTy tailtmp6629 = tmpcur6626 + 1;

            tmpval5276 = tagtmp6628;
            tmpcur5277 = tailtmp6629;
            goto switch5284;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5276");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r1884,
                                          CursorTy end_r1885, CursorTy loc1883,
                                          CursorTy arg1623)
{
    CursorTy loc1882 = (CursorTy) arg1623;

    if (loc1883 + 18 > end_r1885) {
        ChunkTy new_chunk99 = alloc_chunk(end_r1885);
        CursorTy chunk_start100 = new_chunk99.start_ptr;
        CursorTy chunk_end101 = new_chunk99.end_ptr;

        end_r1885 = chunk_end101;
        *(TagTyPacked *) loc1883 = 255;

        CursorTy redir = loc1883 + 1;

        *(CursorTy *) redir = chunk_start100;
        loc1883 = chunk_start100;
    }

    TagTyPacked tmpval5285 = *(TagTyPacked *) arg1623;
    CursorTy tmpcur5286 = arg1623 + 1;


  switch5319:
    ;
    switch (tmpval5285) {

      case 0:
        {
            CursorTy field_cur3708 = (CursorTy) tmpcur5286;
            CursorTy case2334 = (CursorTy) field_cur3708;
            CursorTy x1624 = (CursorTy) case2334;
            CursorTy loc2346 = loc1883 + 1;
            CursorCursorCursorCursorProd tmp_struct96 =
                                          _copy_ListSym(end_r1884, end_r1885, loc2346, x1624);
            CursorTy pvrtmp5287 = tmp_struct96.field0;
            CursorTy pvrtmp5288 = tmp_struct96.field1;
            CursorTy pvrtmp5289 = tmp_struct96.field2;
            CursorTy pvrtmp5290 = tmp_struct96.field3;
            CursorTy fltPrd4453 = (CursorTy) pvrtmp5289;
            CursorTy fltPrd4454 = (CursorTy) pvrtmp5290;
            CursorTy pvrtmp5292 = (CursorTy) fltPrd4454;
            CursorTy pvrtmp5291 = (CursorTy) fltPrd4453;
            CursorTy y1627 = (CursorTy) pvrtmp5291;
            CursorTy fltPrd4455 = (CursorTy) pvrtmp5289;
            CursorTy fltPrd4456 = (CursorTy) pvrtmp5290;
            CursorTy pvrtmp5294 = (CursorTy) fltPrd4456;
            CursorTy pvrtmp5293 = (CursorTy) fltPrd4455;
            CursorTy end_y1627 = (CursorTy) pvrtmp5294;
            CursorTy end_r1885_3400 = (CursorTy) pvrtmp5287;
            CursorTy endof3170 = (CursorTy) pvrtmp5288;
            CursorTy case2335 = (CursorTy) endof3170;
            CursorTy x1625 = (CursorTy) case2335;
            CursorTy loc2347 = (CursorTy) end_y1627;
            CursorCursorCursorCursorProd tmp_struct97 =
                                          _copy_Expr(end_r1884, end_r1885_3400, loc2347, x1625);
            CursorTy pvrtmp5295 = tmp_struct97.field0;
            CursorTy pvrtmp5296 = tmp_struct97.field1;
            CursorTy pvrtmp5297 = tmp_struct97.field2;
            CursorTy pvrtmp5298 = tmp_struct97.field3;
            CursorTy fltPrd4457 = (CursorTy) pvrtmp5297;
            CursorTy fltPrd4458 = (CursorTy) pvrtmp5298;
            CursorTy pvrtmp5300 = (CursorTy) fltPrd4458;
            CursorTy pvrtmp5299 = (CursorTy) fltPrd4457;
            CursorTy y1628 = (CursorTy) pvrtmp5299;
            CursorTy fltPrd4459 = (CursorTy) pvrtmp5297;
            CursorTy fltPrd4460 = (CursorTy) pvrtmp5298;
            CursorTy pvrtmp5302 = (CursorTy) fltPrd4460;
            CursorTy pvrtmp5301 = (CursorTy) fltPrd4459;
            CursorTy end_y1628 = (CursorTy) pvrtmp5302;
            CursorTy end_r1885_3400_3401 = (CursorTy) pvrtmp5295;
            CursorTy endof3171 = (CursorTy) pvrtmp5296;
            CursorTy case2336 = (CursorTy) endof3171;
            CursorTy x1626 = (CursorTy) case2336;
            CursorTy loc2348 = (CursorTy) end_y1628;
            CursorCursorCursorCursorProd tmp_struct98 =
                                          _copy_LVBIND(end_r1884, end_r1885_3400_3401, loc2348, x1626);
            CursorTy pvrtmp5303 = tmp_struct98.field0;
            CursorTy pvrtmp5304 = tmp_struct98.field1;
            CursorTy pvrtmp5305 = tmp_struct98.field2;
            CursorTy pvrtmp5306 = tmp_struct98.field3;
            CursorTy fltPrd4461 = (CursorTy) pvrtmp5305;
            CursorTy fltPrd4462 = (CursorTy) pvrtmp5306;
            CursorTy pvrtmp5308 = (CursorTy) fltPrd4462;
            CursorTy pvrtmp5307 = (CursorTy) fltPrd4461;
            CursorTy y1629 = (CursorTy) pvrtmp5307;
            CursorTy fltPrd4463 = (CursorTy) pvrtmp5305;
            CursorTy fltPrd4464 = (CursorTy) pvrtmp5306;
            CursorTy pvrtmp5310 = (CursorTy) fltPrd4464;
            CursorTy pvrtmp5309 = (CursorTy) fltPrd4463;
            CursorTy end_y1629 = (CursorTy) pvrtmp5310;
            CursorTy end_r1885_3400_3401_3402 = (CursorTy) pvrtmp5303;
            CursorTy endof3172 = (CursorTy) pvrtmp5304;

            *(TagTyPacked *) loc1883 = 0;

            CursorTy writetag3712 = loc1883 + 1;
            CursorTy writecur3713 = (CursorTy) end_y1627;
            CursorTy writecur3714 = (CursorTy) end_y1628;
            CursorTy writecur3715 = (CursorTy) end_y1629;
            CursorTy pvrtmp5312 = (CursorTy) writecur3715;
            CursorTy pvrtmp5311 = (CursorTy) loc1883;
            CursorTy taildc3173 = (CursorTy) pvrtmp5311;
            CursorTy end_taildc3173 = (CursorTy) pvrtmp5312;
            CursorTy pvrtmp5314 = (CursorTy) end_taildc3173;
            CursorTy pvrtmp5313 = (CursorTy) taildc3173;
            CursorTy fltPrd4465 = (CursorTy) pvrtmp5313;
            CursorTy fltPrd4466 = (CursorTy) pvrtmp5314;

            return (CursorCursorCursorCursorProd) {end_r1885_3400_3401_3402,
                                                   endof3172, fltPrd4465,
                                                   fltPrd4466};
            break;
        }

      case 1:
        {
            CursorTy field_cur3717 = (CursorTy) tmpcur5286;
            CursorTy jump3174 = loc1882 + 1;

            *(TagTyPacked *) loc1883 = 1;

            CursorTy writetag3718 = loc1883 + 1;
            CursorTy pvrtmp5316 = (CursorTy) writetag3718;
            CursorTy pvrtmp5315 = (CursorTy) loc1883;
            CursorTy taildc3175 = (CursorTy) pvrtmp5315;
            CursorTy end_taildc3175 = (CursorTy) pvrtmp5316;
            CursorTy pvrtmp5318 = (CursorTy) end_taildc3175;
            CursorTy pvrtmp5317 = (CursorTy) taildc3175;
            CursorTy fltPrd4467 = (CursorTy) pvrtmp5317;
            CursorTy fltPrd4468 = (CursorTy) pvrtmp5318;

            return (CursorCursorCursorCursorProd) {end_r1885, jump3174,
                                                   fltPrd4467, fltPrd4468};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6630 = *(CursorTy *) tmpcur5286;
            CursorTy tmpaftercur6631 = tmpcur5286 + 8;
            TagTyPacked tagtmp6632 = *(TagTyPacked *) tmpcur6630;
            CursorTy tailtmp6633 = tmpcur6630 + 1;

            tmpval5285 = tagtmp6632;
            tmpcur5286 = tailtmp6633;
            goto switch5319;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6630 = *(CursorTy *) tmpcur5286;
            CursorTy tmpaftercur6631 = tmpcur5286 + 8;
            TagTyPacked tagtmp6632 = *(TagTyPacked *) tmpcur6630;
            CursorTy tailtmp6633 = tmpcur6630 + 1;

            tmpval5285 = tagtmp6632;
            tmpcur5286 = tailtmp6633;
            goto switch5319;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5285");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_LVBIND(CursorTy end_r1887, CursorTy arg1630)
{
    CursorTy loc1886 = (CursorTy) arg1630;
    TagTyPacked tmpval5320 = *(TagTyPacked *) arg1630;
    CursorTy tmpcur5321 = arg1630 + 1;


  switch5328:
    ;
    switch (tmpval5320) {

      case 0:
        {
            CursorTy field_cur3720 = (CursorTy) tmpcur5321;
            CursorTy case2355 = (CursorTy) field_cur3720;
            CursorTy x1631 = (CursorTy) case2355;
            CursorInt64Prod tmp_struct102 =
                             _traverse_ListSym(end_r1887, x1631);
            CursorTy pvrtmp5322 = tmp_struct102.field0;
            IntTy pvrtmp5323 = tmp_struct102.field1;
            CursorTy endof3176 = (CursorTy) pvrtmp5322;
            IntTy y1634 = (IntTy) pvrtmp5323;
            CursorTy case2356 = (CursorTy) endof3176;
            CursorTy x1632 = (CursorTy) case2356;
            CursorInt64Prod tmp_struct103 =  _traverse_Expr(end_r1887, x1632);
            CursorTy pvrtmp5324 = tmp_struct103.field0;
            IntTy pvrtmp5325 = tmp_struct103.field1;
            CursorTy endof3177 = (CursorTy) pvrtmp5324;
            IntTy y1635 = (IntTy) pvrtmp5325;
            CursorTy case2357 = (CursorTy) endof3177;
            CursorTy x1633 = (CursorTy) case2357;
            CursorInt64Prod tmp_struct104 =  _traverse_LVBIND(end_r1887, x1633);
            CursorTy pvrtmp5326 = tmp_struct104.field0;
            IntTy pvrtmp5327 = tmp_struct104.field1;
            CursorTy endof3179 = (CursorTy) pvrtmp5326;
            IntTy y1636 = (IntTy) pvrtmp5327;
            IntTy fltLitTail3178 = (IntTy) 42;

            return (CursorInt64Prod) {endof3179, fltLitTail3178};
            break;
        }

      case 1:
        {
            CursorTy field_cur3724 = (CursorTy) tmpcur5321;
            CursorTy jump3180 = loc1886 + 1;
            IntTy fltLitTail3181 = (IntTy) 42;

            return (CursorInt64Prod) {jump3180, fltLitTail3181};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6634 = *(CursorTy *) tmpcur5321;
            CursorTy tmpaftercur6635 = tmpcur5321 + 8;
            TagTyPacked tagtmp6636 = *(TagTyPacked *) tmpcur6634;
            CursorTy tailtmp6637 = tmpcur6634 + 1;

            tmpval5320 = tagtmp6636;
            tmpcur5321 = tailtmp6637;
            goto switch5328;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6634 = *(CursorTy *) tmpcur5321;
            CursorTy tmpaftercur6635 = tmpcur5321 + 8;
            TagTyPacked tagtmp6636 = *(TagTyPacked *) tmpcur6634;
            CursorTy tailtmp6637 = tmpcur6634 + 1;

            tmpval5320 = tagtmp6636;
            tmpcur5321 = tailtmp6637;
            goto switch5328;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5320");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r1890, CursorTy end_r1891,
                                        CursorTy loc1889, CursorTy arg1637)
{
    CursorTy loc1888 = (CursorTy) arg1637;

    if (loc1889 + 18 > end_r1891) {
        ChunkTy new_chunk127 = alloc_chunk(end_r1891);
        CursorTy chunk_start128 = new_chunk127.start_ptr;
        CursorTy chunk_end129 = new_chunk127.end_ptr;

        end_r1891 = chunk_end129;
        *(TagTyPacked *) loc1889 = 255;

        CursorTy redir = loc1889 + 1;

        *(CursorTy *) redir = chunk_start128;
        loc1889 = chunk_start128;
    }

    CursorTy loc2453 = loc1889 + 1;
    CursorTy loc2454 = loc2453 + 8;
    TagTyPacked tmpval5329 = *(TagTyPacked *) arg1637;
    CursorTy tmpcur5330 = arg1637 + 1;


  switch5589:
    ;
    switch (tmpval5329) {

      case 0:
        {
            CursorTy field_cur3725 = (CursorTy) tmpcur5330;
            CursorTy case2366 = (CursorTy) field_cur3725;
            SymTy tmpval5331 = *(SymTy *) case2366;
            CursorTy tmpcur5332 = case2366 + sizeof(SymTy);
            SymTy x1638 = (SymTy) tmpval5331;
            CursorTy end_x1638 = (CursorTy) tmpcur5332;
            CursorTy jump3182 = case2366 + 8;

            *(TagTyPacked *) loc1889 = 0;

            CursorTy writetag3727 = loc1889 + 1;

            *(SymTy *) writetag3727 = x1638;

            CursorTy writecur3728 = writetag3727 + sizeof(SymTy);
            CursorTy pvrtmp5334 = (CursorTy) writecur3728;
            CursorTy pvrtmp5333 = (CursorTy) loc1889;
            CursorTy taildc3183 = (CursorTy) pvrtmp5333;
            CursorTy end_taildc3183 = (CursorTy) pvrtmp5334;
            CursorTy pvrtmp5336 = (CursorTy) end_taildc3183;
            CursorTy pvrtmp5335 = (CursorTy) taildc3183;
            CursorTy fltPrd4469 = (CursorTy) pvrtmp5335;
            CursorTy fltPrd4470 = (CursorTy) pvrtmp5336;

            return (CursorCursorCursorCursorProd) {end_r1891, jump3182,
                                                   fltPrd4469, fltPrd4470};
            break;
        }

      case 1:
        {
            CursorTy field_cur3730 = (CursorTy) tmpcur5330;
            CursorTy case2370 = (CursorTy) field_cur3730;
            CursorTy x1640 = (CursorTy) case2370;
            CursorTy loc2378 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct105 =
                                          _copy_Formals(end_r1890, end_r1891, loc2378, x1640);
            CursorTy pvrtmp5337 = tmp_struct105.field0;
            CursorTy pvrtmp5338 = tmp_struct105.field1;
            CursorTy pvrtmp5339 = tmp_struct105.field2;
            CursorTy pvrtmp5340 = tmp_struct105.field3;
            CursorTy fltPrd4471 = (CursorTy) pvrtmp5339;
            CursorTy fltPrd4472 = (CursorTy) pvrtmp5340;
            CursorTy pvrtmp5342 = (CursorTy) fltPrd4472;
            CursorTy pvrtmp5341 = (CursorTy) fltPrd4471;
            CursorTy y1642 = (CursorTy) pvrtmp5341;
            CursorTy fltPrd4473 = (CursorTy) pvrtmp5339;
            CursorTy fltPrd4474 = (CursorTy) pvrtmp5340;
            CursorTy pvrtmp5344 = (CursorTy) fltPrd4474;
            CursorTy pvrtmp5343 = (CursorTy) fltPrd4473;
            CursorTy end_y1642 = (CursorTy) pvrtmp5344;
            CursorTy end_r1891_3403 = (CursorTy) pvrtmp5337;
            CursorTy endof3184 = (CursorTy) pvrtmp5338;
            CursorTy case2371 = (CursorTy) endof3184;
            CursorTy x1641 = (CursorTy) case2371;
            CursorTy loc2379 = (CursorTy) end_y1642;
            CursorCursorCursorCursorProd tmp_struct106 =
                                          _copy_ListExpr(end_r1890, end_r1891_3403, loc2379, x1641);
            CursorTy pvrtmp5345 = tmp_struct106.field0;
            CursorTy pvrtmp5346 = tmp_struct106.field1;
            CursorTy pvrtmp5347 = tmp_struct106.field2;
            CursorTy pvrtmp5348 = tmp_struct106.field3;
            CursorTy fltPrd4475 = (CursorTy) pvrtmp5347;
            CursorTy fltPrd4476 = (CursorTy) pvrtmp5348;
            CursorTy pvrtmp5350 = (CursorTy) fltPrd4476;
            CursorTy pvrtmp5349 = (CursorTy) fltPrd4475;
            CursorTy y1643 = (CursorTy) pvrtmp5349;
            CursorTy fltPrd4477 = (CursorTy) pvrtmp5347;
            CursorTy fltPrd4478 = (CursorTy) pvrtmp5348;
            CursorTy pvrtmp5352 = (CursorTy) fltPrd4478;
            CursorTy pvrtmp5351 = (CursorTy) fltPrd4477;
            CursorTy end_y1643 = (CursorTy) pvrtmp5352;
            CursorTy end_r1891_3403_3404 = (CursorTy) pvrtmp5345;
            CursorTy endof3185 = (CursorTy) pvrtmp5346;

            *(TagTyPacked *) loc1889 = 1;

            CursorTy writetag3733 = loc1889 + 1;
            CursorTy writecur3734 = (CursorTy) end_y1642;
            CursorTy writecur3735 = (CursorTy) end_y1643;
            CursorTy pvrtmp5354 = (CursorTy) writecur3735;
            CursorTy pvrtmp5353 = (CursorTy) loc1889;
            CursorTy taildc3186 = (CursorTy) pvrtmp5353;
            CursorTy end_taildc3186 = (CursorTy) pvrtmp5354;
            CursorTy pvrtmp5356 = (CursorTy) end_taildc3186;
            CursorTy pvrtmp5355 = (CursorTy) taildc3186;
            CursorTy fltPrd4479 = (CursorTy) pvrtmp5355;
            CursorTy fltPrd4480 = (CursorTy) pvrtmp5356;

            return (CursorCursorCursorCursorProd) {end_r1891_3403_3404,
                                                   endof3185, fltPrd4479,
                                                   fltPrd4480};
            break;
        }

      case 2:
        {
            CursorTy field_cur3737 = (CursorTy) tmpcur5330;
            CursorTy case2382 = (CursorTy) field_cur3737;
            CursorTy x1644 = (CursorTy) case2382;
            CursorTy loc2386 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct107 =
                                          _copy_LAMBDACASE(end_r1890, end_r1891, loc2386, x1644);
            CursorTy pvrtmp5357 = tmp_struct107.field0;
            CursorTy pvrtmp5358 = tmp_struct107.field1;
            CursorTy pvrtmp5359 = tmp_struct107.field2;
            CursorTy pvrtmp5360 = tmp_struct107.field3;
            CursorTy fltPrd4481 = (CursorTy) pvrtmp5359;
            CursorTy fltPrd4482 = (CursorTy) pvrtmp5360;
            CursorTy pvrtmp5362 = (CursorTy) fltPrd4482;
            CursorTy pvrtmp5361 = (CursorTy) fltPrd4481;
            CursorTy y1645 = (CursorTy) pvrtmp5361;
            CursorTy fltPrd4483 = (CursorTy) pvrtmp5359;
            CursorTy fltPrd4484 = (CursorTy) pvrtmp5360;
            CursorTy pvrtmp5364 = (CursorTy) fltPrd4484;
            CursorTy pvrtmp5363 = (CursorTy) fltPrd4483;
            CursorTy end_y1645 = (CursorTy) pvrtmp5364;
            CursorTy end_r1891_3405 = (CursorTy) pvrtmp5357;
            CursorTy endof3187 = (CursorTy) pvrtmp5358;

            *(TagTyPacked *) loc1889 = 2;

            CursorTy writetag3739 = loc1889 + 1;
            CursorTy writecur3740 = (CursorTy) end_y1645;
            CursorTy pvrtmp5366 = (CursorTy) writecur3740;
            CursorTy pvrtmp5365 = (CursorTy) loc1889;
            CursorTy taildc3188 = (CursorTy) pvrtmp5365;
            CursorTy end_taildc3188 = (CursorTy) pvrtmp5366;
            CursorTy pvrtmp5368 = (CursorTy) end_taildc3188;
            CursorTy pvrtmp5367 = (CursorTy) taildc3188;
            CursorTy fltPrd4485 = (CursorTy) pvrtmp5367;
            CursorTy fltPrd4486 = (CursorTy) pvrtmp5368;

            return (CursorCursorCursorCursorProd) {end_r1891_3405, endof3187,
                                                   fltPrd4485, fltPrd4486};
            break;
        }

      case 3:
        {
            CursorTy field_cur3742 = (CursorTy) tmpcur5330;
            CursorTy case2388 = (CursorTy) field_cur3742;
            CursorTy x1646 = (CursorTy) case2388;
            CursorTy loc2400 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct108 =
                                          _copy_Expr(end_r1890, end_r1891, loc2400, x1646);
            CursorTy pvrtmp5369 = tmp_struct108.field0;
            CursorTy pvrtmp5370 = tmp_struct108.field1;
            CursorTy pvrtmp5371 = tmp_struct108.field2;
            CursorTy pvrtmp5372 = tmp_struct108.field3;
            CursorTy fltPrd4487 = (CursorTy) pvrtmp5371;
            CursorTy fltPrd4488 = (CursorTy) pvrtmp5372;
            CursorTy pvrtmp5374 = (CursorTy) fltPrd4488;
            CursorTy pvrtmp5373 = (CursorTy) fltPrd4487;
            CursorTy y1649 = (CursorTy) pvrtmp5373;
            CursorTy fltPrd4489 = (CursorTy) pvrtmp5371;
            CursorTy fltPrd4490 = (CursorTy) pvrtmp5372;
            CursorTy pvrtmp5376 = (CursorTy) fltPrd4490;
            CursorTy pvrtmp5375 = (CursorTy) fltPrd4489;
            CursorTy end_y1649 = (CursorTy) pvrtmp5376;
            CursorTy end_r1891_3406 = (CursorTy) pvrtmp5369;
            CursorTy endof3189 = (CursorTy) pvrtmp5370;
            CursorTy case2389 = (CursorTy) endof3189;
            CursorTy x1647 = (CursorTy) case2389;
            CursorTy loc2401 = (CursorTy) end_y1649;
            CursorCursorCursorCursorProd tmp_struct109 =
                                          _copy_Expr(end_r1890, end_r1891_3406, loc2401, x1647);
            CursorTy pvrtmp5377 = tmp_struct109.field0;
            CursorTy pvrtmp5378 = tmp_struct109.field1;
            CursorTy pvrtmp5379 = tmp_struct109.field2;
            CursorTy pvrtmp5380 = tmp_struct109.field3;
            CursorTy fltPrd4491 = (CursorTy) pvrtmp5379;
            CursorTy fltPrd4492 = (CursorTy) pvrtmp5380;
            CursorTy pvrtmp5382 = (CursorTy) fltPrd4492;
            CursorTy pvrtmp5381 = (CursorTy) fltPrd4491;
            CursorTy y1650 = (CursorTy) pvrtmp5381;
            CursorTy fltPrd4493 = (CursorTy) pvrtmp5379;
            CursorTy fltPrd4494 = (CursorTy) pvrtmp5380;
            CursorTy pvrtmp5384 = (CursorTy) fltPrd4494;
            CursorTy pvrtmp5383 = (CursorTy) fltPrd4493;
            CursorTy end_y1650 = (CursorTy) pvrtmp5384;
            CursorTy end_r1891_3406_3407 = (CursorTy) pvrtmp5377;
            CursorTy endof3190 = (CursorTy) pvrtmp5378;
            CursorTy case2390 = (CursorTy) endof3190;
            CursorTy x1648 = (CursorTy) case2390;
            CursorTy loc2402 = (CursorTy) end_y1650;
            CursorCursorCursorCursorProd tmp_struct110 =
                                          _copy_Expr(end_r1890, end_r1891_3406_3407, loc2402, x1648);
            CursorTy pvrtmp5385 = tmp_struct110.field0;
            CursorTy pvrtmp5386 = tmp_struct110.field1;
            CursorTy pvrtmp5387 = tmp_struct110.field2;
            CursorTy pvrtmp5388 = tmp_struct110.field3;
            CursorTy fltPrd4495 = (CursorTy) pvrtmp5387;
            CursorTy fltPrd4496 = (CursorTy) pvrtmp5388;
            CursorTy pvrtmp5390 = (CursorTy) fltPrd4496;
            CursorTy pvrtmp5389 = (CursorTy) fltPrd4495;
            CursorTy y1651 = (CursorTy) pvrtmp5389;
            CursorTy fltPrd4497 = (CursorTy) pvrtmp5387;
            CursorTy fltPrd4498 = (CursorTy) pvrtmp5388;
            CursorTy pvrtmp5392 = (CursorTy) fltPrd4498;
            CursorTy pvrtmp5391 = (CursorTy) fltPrd4497;
            CursorTy end_y1651 = (CursorTy) pvrtmp5392;
            CursorTy end_r1891_3406_3407_3408 = (CursorTy) pvrtmp5385;
            CursorTy endof3191 = (CursorTy) pvrtmp5386;

            *(TagTyPacked *) loc1889 = 3;

            CursorTy writetag3746 = loc1889 + 1;
            CursorTy writecur3747 = (CursorTy) end_y1649;
            CursorTy writecur3748 = (CursorTy) end_y1650;
            CursorTy writecur3749 = (CursorTy) end_y1651;
            CursorTy pvrtmp5394 = (CursorTy) writecur3749;
            CursorTy pvrtmp5393 = (CursorTy) loc1889;
            CursorTy taildc3192 = (CursorTy) pvrtmp5393;
            CursorTy end_taildc3192 = (CursorTy) pvrtmp5394;
            CursorTy pvrtmp5396 = (CursorTy) end_taildc3192;
            CursorTy pvrtmp5395 = (CursorTy) taildc3192;
            CursorTy fltPrd4499 = (CursorTy) pvrtmp5395;
            CursorTy fltPrd4500 = (CursorTy) pvrtmp5396;

            return (CursorCursorCursorCursorProd) {end_r1891_3406_3407_3408,
                                                   endof3191, fltPrd4499,
                                                   fltPrd4500};
            break;
        }

      case 4:
        {
            CursorTy field_cur3751 = (CursorTy) tmpcur5330;
            CursorTy case2406 = (CursorTy) field_cur3751;
            CursorTy x1652 = (CursorTy) case2406;
            CursorTy loc2410 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct111 =
                                          _copy_ListExpr(end_r1890, end_r1891, loc2410, x1652);
            CursorTy pvrtmp5397 = tmp_struct111.field0;
            CursorTy pvrtmp5398 = tmp_struct111.field1;
            CursorTy pvrtmp5399 = tmp_struct111.field2;
            CursorTy pvrtmp5400 = tmp_struct111.field3;
            CursorTy fltPrd4501 = (CursorTy) pvrtmp5399;
            CursorTy fltPrd4502 = (CursorTy) pvrtmp5400;
            CursorTy pvrtmp5402 = (CursorTy) fltPrd4502;
            CursorTy pvrtmp5401 = (CursorTy) fltPrd4501;
            CursorTy y1653 = (CursorTy) pvrtmp5401;
            CursorTy fltPrd4503 = (CursorTy) pvrtmp5399;
            CursorTy fltPrd4504 = (CursorTy) pvrtmp5400;
            CursorTy pvrtmp5404 = (CursorTy) fltPrd4504;
            CursorTy pvrtmp5403 = (CursorTy) fltPrd4503;
            CursorTy end_y1653 = (CursorTy) pvrtmp5404;
            CursorTy end_r1891_3409 = (CursorTy) pvrtmp5397;
            CursorTy endof3193 = (CursorTy) pvrtmp5398;

            *(TagTyPacked *) loc1889 = 4;

            CursorTy writetag3753 = loc1889 + 1;
            CursorTy writecur3754 = (CursorTy) end_y1653;
            CursorTy pvrtmp5406 = (CursorTy) writecur3754;
            CursorTy pvrtmp5405 = (CursorTy) loc1889;
            CursorTy taildc3194 = (CursorTy) pvrtmp5405;
            CursorTy end_taildc3194 = (CursorTy) pvrtmp5406;
            CursorTy pvrtmp5408 = (CursorTy) end_taildc3194;
            CursorTy pvrtmp5407 = (CursorTy) taildc3194;
            CursorTy fltPrd4505 = (CursorTy) pvrtmp5407;
            CursorTy fltPrd4506 = (CursorTy) pvrtmp5408;

            return (CursorCursorCursorCursorProd) {end_r1891_3409, endof3193,
                                                   fltPrd4505, fltPrd4506};
            break;
        }

      case 5:
        {
            CursorTy field_cur3756 = (CursorTy) tmpcur5330;
            CursorTy case2412 = (CursorTy) field_cur3756;
            CursorTy x1654 = (CursorTy) case2412;
            CursorTy loc2420 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct112 =
                                          _copy_Expr(end_r1890, end_r1891, loc2420, x1654);
            CursorTy pvrtmp5409 = tmp_struct112.field0;
            CursorTy pvrtmp5410 = tmp_struct112.field1;
            CursorTy pvrtmp5411 = tmp_struct112.field2;
            CursorTy pvrtmp5412 = tmp_struct112.field3;
            CursorTy fltPrd4507 = (CursorTy) pvrtmp5411;
            CursorTy fltPrd4508 = (CursorTy) pvrtmp5412;
            CursorTy pvrtmp5414 = (CursorTy) fltPrd4508;
            CursorTy pvrtmp5413 = (CursorTy) fltPrd4507;
            CursorTy y1656 = (CursorTy) pvrtmp5413;
            CursorTy fltPrd4509 = (CursorTy) pvrtmp5411;
            CursorTy fltPrd4510 = (CursorTy) pvrtmp5412;
            CursorTy pvrtmp5416 = (CursorTy) fltPrd4510;
            CursorTy pvrtmp5415 = (CursorTy) fltPrd4509;
            CursorTy end_y1656 = (CursorTy) pvrtmp5416;
            CursorTy end_r1891_3410 = (CursorTy) pvrtmp5409;
            CursorTy endof3195 = (CursorTy) pvrtmp5410;
            CursorTy case2413 = (CursorTy) endof3195;
            CursorTy x1655 = (CursorTy) case2413;
            CursorTy loc2421 = (CursorTy) end_y1656;
            CursorCursorCursorCursorProd tmp_struct113 =
                                          _copy_ListExpr(end_r1890, end_r1891_3410, loc2421, x1655);
            CursorTy pvrtmp5417 = tmp_struct113.field0;
            CursorTy pvrtmp5418 = tmp_struct113.field1;
            CursorTy pvrtmp5419 = tmp_struct113.field2;
            CursorTy pvrtmp5420 = tmp_struct113.field3;
            CursorTy fltPrd4511 = (CursorTy) pvrtmp5419;
            CursorTy fltPrd4512 = (CursorTy) pvrtmp5420;
            CursorTy pvrtmp5422 = (CursorTy) fltPrd4512;
            CursorTy pvrtmp5421 = (CursorTy) fltPrd4511;
            CursorTy y1657 = (CursorTy) pvrtmp5421;
            CursorTy fltPrd4513 = (CursorTy) pvrtmp5419;
            CursorTy fltPrd4514 = (CursorTy) pvrtmp5420;
            CursorTy pvrtmp5424 = (CursorTy) fltPrd4514;
            CursorTy pvrtmp5423 = (CursorTy) fltPrd4513;
            CursorTy end_y1657 = (CursorTy) pvrtmp5424;
            CursorTy end_r1891_3410_3411 = (CursorTy) pvrtmp5417;
            CursorTy endof3196 = (CursorTy) pvrtmp5418;

            *(TagTyPacked *) loc1889 = 5;

            CursorTy writetag3759 = loc1889 + 1;
            CursorTy writecur3760 = (CursorTy) end_y1656;
            CursorTy writecur3761 = (CursorTy) end_y1657;
            CursorTy pvrtmp5426 = (CursorTy) writecur3761;
            CursorTy pvrtmp5425 = (CursorTy) loc1889;
            CursorTy taildc3197 = (CursorTy) pvrtmp5425;
            CursorTy end_taildc3197 = (CursorTy) pvrtmp5426;
            CursorTy pvrtmp5428 = (CursorTy) end_taildc3197;
            CursorTy pvrtmp5427 = (CursorTy) taildc3197;
            CursorTy fltPrd4515 = (CursorTy) pvrtmp5427;
            CursorTy fltPrd4516 = (CursorTy) pvrtmp5428;

            return (CursorCursorCursorCursorProd) {end_r1891_3410_3411,
                                                   endof3196, fltPrd4515,
                                                   fltPrd4516};
            break;
        }

      case 6:
        {
            CursorTy field_cur3763 = (CursorTy) tmpcur5330;
            CursorTy case2424 = (CursorTy) field_cur3763;
            CursorTy x1658 = (CursorTy) case2424;
            CursorTy loc2432 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct114 =
                                          _copy_LVBIND(end_r1890, end_r1891, loc2432, x1658);
            CursorTy pvrtmp5429 = tmp_struct114.field0;
            CursorTy pvrtmp5430 = tmp_struct114.field1;
            CursorTy pvrtmp5431 = tmp_struct114.field2;
            CursorTy pvrtmp5432 = tmp_struct114.field3;
            CursorTy fltPrd4517 = (CursorTy) pvrtmp5431;
            CursorTy fltPrd4518 = (CursorTy) pvrtmp5432;
            CursorTy pvrtmp5434 = (CursorTy) fltPrd4518;
            CursorTy pvrtmp5433 = (CursorTy) fltPrd4517;
            CursorTy y1660 = (CursorTy) pvrtmp5433;
            CursorTy fltPrd4519 = (CursorTy) pvrtmp5431;
            CursorTy fltPrd4520 = (CursorTy) pvrtmp5432;
            CursorTy pvrtmp5436 = (CursorTy) fltPrd4520;
            CursorTy pvrtmp5435 = (CursorTy) fltPrd4519;
            CursorTy end_y1660 = (CursorTy) pvrtmp5436;
            CursorTy end_r1891_3412 = (CursorTy) pvrtmp5429;
            CursorTy endof3198 = (CursorTy) pvrtmp5430;
            CursorTy case2425 = (CursorTy) endof3198;
            CursorTy x1659 = (CursorTy) case2425;
            CursorTy loc2433 = (CursorTy) end_y1660;
            CursorCursorCursorCursorProd tmp_struct115 =
                                          _copy_ListExpr(end_r1890, end_r1891_3412, loc2433, x1659);
            CursorTy pvrtmp5437 = tmp_struct115.field0;
            CursorTy pvrtmp5438 = tmp_struct115.field1;
            CursorTy pvrtmp5439 = tmp_struct115.field2;
            CursorTy pvrtmp5440 = tmp_struct115.field3;
            CursorTy fltPrd4521 = (CursorTy) pvrtmp5439;
            CursorTy fltPrd4522 = (CursorTy) pvrtmp5440;
            CursorTy pvrtmp5442 = (CursorTy) fltPrd4522;
            CursorTy pvrtmp5441 = (CursorTy) fltPrd4521;
            CursorTy y1661 = (CursorTy) pvrtmp5441;
            CursorTy fltPrd4523 = (CursorTy) pvrtmp5439;
            CursorTy fltPrd4524 = (CursorTy) pvrtmp5440;
            CursorTy pvrtmp5444 = (CursorTy) fltPrd4524;
            CursorTy pvrtmp5443 = (CursorTy) fltPrd4523;
            CursorTy end_y1661 = (CursorTy) pvrtmp5444;
            CursorTy end_r1891_3412_3413 = (CursorTy) pvrtmp5437;
            CursorTy endof3199 = (CursorTy) pvrtmp5438;

            *(TagTyPacked *) loc1889 = 6;

            CursorTy writetag3766 = loc1889 + 1;
            CursorTy writecur3767 = (CursorTy) end_y1660;
            CursorTy writecur3768 = (CursorTy) end_y1661;
            CursorTy pvrtmp5446 = (CursorTy) writecur3768;
            CursorTy pvrtmp5445 = (CursorTy) loc1889;
            CursorTy taildc3200 = (CursorTy) pvrtmp5445;
            CursorTy end_taildc3200 = (CursorTy) pvrtmp5446;
            CursorTy pvrtmp5448 = (CursorTy) end_taildc3200;
            CursorTy pvrtmp5447 = (CursorTy) taildc3200;
            CursorTy fltPrd4525 = (CursorTy) pvrtmp5447;
            CursorTy fltPrd4526 = (CursorTy) pvrtmp5448;

            return (CursorCursorCursorCursorProd) {end_r1891_3412_3413,
                                                   endof3199, fltPrd4525,
                                                   fltPrd4526};
            break;
        }

      case 7:
        {
            CursorTy field_cur3770 = (CursorTy) tmpcur5330;
            CursorTy case2436 = (CursorTy) field_cur3770;
            CursorTy x1662 = (CursorTy) case2436;
            CursorTy loc2444 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct116 =
                                          _copy_LVBIND(end_r1890, end_r1891, loc2444, x1662);
            CursorTy pvrtmp5449 = tmp_struct116.field0;
            CursorTy pvrtmp5450 = tmp_struct116.field1;
            CursorTy pvrtmp5451 = tmp_struct116.field2;
            CursorTy pvrtmp5452 = tmp_struct116.field3;
            CursorTy fltPrd4527 = (CursorTy) pvrtmp5451;
            CursorTy fltPrd4528 = (CursorTy) pvrtmp5452;
            CursorTy pvrtmp5454 = (CursorTy) fltPrd4528;
            CursorTy pvrtmp5453 = (CursorTy) fltPrd4527;
            CursorTy y1664 = (CursorTy) pvrtmp5453;
            CursorTy fltPrd4529 = (CursorTy) pvrtmp5451;
            CursorTy fltPrd4530 = (CursorTy) pvrtmp5452;
            CursorTy pvrtmp5456 = (CursorTy) fltPrd4530;
            CursorTy pvrtmp5455 = (CursorTy) fltPrd4529;
            CursorTy end_y1664 = (CursorTy) pvrtmp5456;
            CursorTy end_r1891_3414 = (CursorTy) pvrtmp5449;
            CursorTy endof3201 = (CursorTy) pvrtmp5450;
            CursorTy case2437 = (CursorTy) endof3201;
            CursorTy x1663 = (CursorTy) case2437;
            CursorTy loc2445 = (CursorTy) end_y1664;
            CursorCursorCursorCursorProd tmp_struct117 =
                                          _copy_ListExpr(end_r1890, end_r1891_3414, loc2445, x1663);
            CursorTy pvrtmp5457 = tmp_struct117.field0;
            CursorTy pvrtmp5458 = tmp_struct117.field1;
            CursorTy pvrtmp5459 = tmp_struct117.field2;
            CursorTy pvrtmp5460 = tmp_struct117.field3;
            CursorTy fltPrd4531 = (CursorTy) pvrtmp5459;
            CursorTy fltPrd4532 = (CursorTy) pvrtmp5460;
            CursorTy pvrtmp5462 = (CursorTy) fltPrd4532;
            CursorTy pvrtmp5461 = (CursorTy) fltPrd4531;
            CursorTy y1665 = (CursorTy) pvrtmp5461;
            CursorTy fltPrd4533 = (CursorTy) pvrtmp5459;
            CursorTy fltPrd4534 = (CursorTy) pvrtmp5460;
            CursorTy pvrtmp5464 = (CursorTy) fltPrd4534;
            CursorTy pvrtmp5463 = (CursorTy) fltPrd4533;
            CursorTy end_y1665 = (CursorTy) pvrtmp5464;
            CursorTy end_r1891_3414_3415 = (CursorTy) pvrtmp5457;
            CursorTy endof3202 = (CursorTy) pvrtmp5458;

            *(TagTyPacked *) loc1889 = 7;

            CursorTy writetag3773 = loc1889 + 1;
            CursorTy writecur3774 = (CursorTy) end_y1664;
            CursorTy writecur3775 = (CursorTy) end_y1665;
            CursorTy pvrtmp5466 = (CursorTy) writecur3775;
            CursorTy pvrtmp5465 = (CursorTy) loc1889;
            CursorTy taildc3203 = (CursorTy) pvrtmp5465;
            CursorTy end_taildc3203 = (CursorTy) pvrtmp5466;
            CursorTy pvrtmp5468 = (CursorTy) end_taildc3203;
            CursorTy pvrtmp5467 = (CursorTy) taildc3203;
            CursorTy fltPrd4535 = (CursorTy) pvrtmp5467;
            CursorTy fltPrd4536 = (CursorTy) pvrtmp5468;

            return (CursorCursorCursorCursorProd) {end_r1891_3414_3415,
                                                   endof3202, fltPrd4535,
                                                   fltPrd4536};
            break;
        }

      case 8:
        {
            CursorTy field_cur3777 = (CursorTy) tmpcur5330;
            CursorTy case2448 = (CursorTy) field_cur3777;
            SymTy tmpval5469 = *(SymTy *) case2448;
            CursorTy tmpcur5470 = case2448 + sizeof(SymTy);
            SymTy x1666 = (SymTy) tmpval5469;
            CursorTy end_x1666 = (CursorTy) tmpcur5470;
            CursorTy case2449 = (CursorTy) end_x1666;
            CursorTy x1667 = (CursorTy) case2449;
            CursorTy jump3204 = case2448 + 8;
            CursorCursorCursorCursorProd tmp_struct118 =
                                          _copy_Expr(end_r1890, end_r1891, loc2454, x1667);
            CursorTy pvrtmp5471 = tmp_struct118.field0;
            CursorTy pvrtmp5472 = tmp_struct118.field1;
            CursorTy pvrtmp5473 = tmp_struct118.field2;
            CursorTy pvrtmp5474 = tmp_struct118.field3;
            CursorTy fltPrd4537 = (CursorTy) pvrtmp5473;
            CursorTy fltPrd4538 = (CursorTy) pvrtmp5474;
            CursorTy pvrtmp5476 = (CursorTy) fltPrd4538;
            CursorTy pvrtmp5475 = (CursorTy) fltPrd4537;
            CursorTy y1669 = (CursorTy) pvrtmp5475;
            CursorTy fltPrd4539 = (CursorTy) pvrtmp5473;
            CursorTy fltPrd4540 = (CursorTy) pvrtmp5474;
            CursorTy pvrtmp5478 = (CursorTy) fltPrd4540;
            CursorTy pvrtmp5477 = (CursorTy) fltPrd4539;
            CursorTy end_y1669 = (CursorTy) pvrtmp5478;
            CursorTy end_r1891_3416 = (CursorTy) pvrtmp5471;
            CursorTy endof3205 = (CursorTy) pvrtmp5472;

            *(TagTyPacked *) loc1889 = 8;

            CursorTy writetag3780 = loc1889 + 1;

            *(SymTy *) writetag3780 = x1666;

            CursorTy writecur3781 = writetag3780 + sizeof(SymTy);
            CursorTy writecur3782 = (CursorTy) end_y1669;
            CursorTy pvrtmp5480 = (CursorTy) writecur3782;
            CursorTy pvrtmp5479 = (CursorTy) loc1889;
            CursorTy taildc3206 = (CursorTy) pvrtmp5479;
            CursorTy end_taildc3206 = (CursorTy) pvrtmp5480;
            CursorTy pvrtmp5482 = (CursorTy) end_taildc3206;
            CursorTy pvrtmp5481 = (CursorTy) taildc3206;
            CursorTy fltPrd4541 = (CursorTy) pvrtmp5481;
            CursorTy fltPrd4542 = (CursorTy) pvrtmp5482;

            return (CursorCursorCursorCursorProd) {end_r1891_3416, endof3205,
                                                   fltPrd4541, fltPrd4542};
            break;
        }

      case 9:
        {
            CursorTy field_cur3784 = (CursorTy) tmpcur5330;
            CursorTy case2458 = (CursorTy) field_cur3784;
            CursorTy x1670 = (CursorTy) case2458;
            CursorTy loc2462 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct119 =
                                          _copy_Datum(end_r1890, end_r1891, loc2462, x1670);
            CursorTy pvrtmp5483 = tmp_struct119.field0;
            CursorTy pvrtmp5484 = tmp_struct119.field1;
            CursorTy pvrtmp5485 = tmp_struct119.field2;
            CursorTy pvrtmp5486 = tmp_struct119.field3;
            CursorTy fltPrd4543 = (CursorTy) pvrtmp5485;
            CursorTy fltPrd4544 = (CursorTy) pvrtmp5486;
            CursorTy pvrtmp5488 = (CursorTy) fltPrd4544;
            CursorTy pvrtmp5487 = (CursorTy) fltPrd4543;
            CursorTy y1671 = (CursorTy) pvrtmp5487;
            CursorTy fltPrd4545 = (CursorTy) pvrtmp5485;
            CursorTy fltPrd4546 = (CursorTy) pvrtmp5486;
            CursorTy pvrtmp5490 = (CursorTy) fltPrd4546;
            CursorTy pvrtmp5489 = (CursorTy) fltPrd4545;
            CursorTy end_y1671 = (CursorTy) pvrtmp5490;
            CursorTy end_r1891_3417 = (CursorTy) pvrtmp5483;
            CursorTy endof3207 = (CursorTy) pvrtmp5484;

            *(TagTyPacked *) loc1889 = 9;

            CursorTy writetag3786 = loc1889 + 1;
            CursorTy writecur3787 = (CursorTy) end_y1671;
            CursorTy pvrtmp5492 = (CursorTy) writecur3787;
            CursorTy pvrtmp5491 = (CursorTy) loc1889;
            CursorTy taildc3208 = (CursorTy) pvrtmp5491;
            CursorTy end_taildc3208 = (CursorTy) pvrtmp5492;
            CursorTy pvrtmp5494 = (CursorTy) end_taildc3208;
            CursorTy pvrtmp5493 = (CursorTy) taildc3208;
            CursorTy fltPrd4547 = (CursorTy) pvrtmp5493;
            CursorTy fltPrd4548 = (CursorTy) pvrtmp5494;

            return (CursorCursorCursorCursorProd) {end_r1891_3417, endof3207,
                                                   fltPrd4547, fltPrd4548};
            break;
        }

      case 10:
        {
            CursorTy field_cur3789 = (CursorTy) tmpcur5330;
            CursorTy case2464 = (CursorTy) field_cur3789;
            CursorTy x1672 = (CursorTy) case2464;
            CursorTy loc2468 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct120 =
                                          _copy_Datum(end_r1890, end_r1891, loc2468, x1672);
            CursorTy pvrtmp5495 = tmp_struct120.field0;
            CursorTy pvrtmp5496 = tmp_struct120.field1;
            CursorTy pvrtmp5497 = tmp_struct120.field2;
            CursorTy pvrtmp5498 = tmp_struct120.field3;
            CursorTy fltPrd4549 = (CursorTy) pvrtmp5497;
            CursorTy fltPrd4550 = (CursorTy) pvrtmp5498;
            CursorTy pvrtmp5500 = (CursorTy) fltPrd4550;
            CursorTy pvrtmp5499 = (CursorTy) fltPrd4549;
            CursorTy y1673 = (CursorTy) pvrtmp5499;
            CursorTy fltPrd4551 = (CursorTy) pvrtmp5497;
            CursorTy fltPrd4552 = (CursorTy) pvrtmp5498;
            CursorTy pvrtmp5502 = (CursorTy) fltPrd4552;
            CursorTy pvrtmp5501 = (CursorTy) fltPrd4551;
            CursorTy end_y1673 = (CursorTy) pvrtmp5502;
            CursorTy end_r1891_3418 = (CursorTy) pvrtmp5495;
            CursorTy endof3209 = (CursorTy) pvrtmp5496;

            *(TagTyPacked *) loc1889 = 10;

            CursorTy writetag3791 = loc1889 + 1;
            CursorTy writecur3792 = (CursorTy) end_y1673;
            CursorTy pvrtmp5504 = (CursorTy) writecur3792;
            CursorTy pvrtmp5503 = (CursorTy) loc1889;
            CursorTy taildc3210 = (CursorTy) pvrtmp5503;
            CursorTy end_taildc3210 = (CursorTy) pvrtmp5504;
            CursorTy pvrtmp5506 = (CursorTy) end_taildc3210;
            CursorTy pvrtmp5505 = (CursorTy) taildc3210;
            CursorTy fltPrd4553 = (CursorTy) pvrtmp5505;
            CursorTy fltPrd4554 = (CursorTy) pvrtmp5506;

            return (CursorCursorCursorCursorProd) {end_r1891_3418, endof3209,
                                                   fltPrd4553, fltPrd4554};
            break;
        }

      case 11:
        {
            CursorTy field_cur3794 = (CursorTy) tmpcur5330;
            CursorTy case2470 = (CursorTy) field_cur3794;
            CursorTy x1674 = (CursorTy) case2470;
            CursorTy loc2474 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct121 =
                                          _copy_Datum(end_r1890, end_r1891, loc2474, x1674);
            CursorTy pvrtmp5507 = tmp_struct121.field0;
            CursorTy pvrtmp5508 = tmp_struct121.field1;
            CursorTy pvrtmp5509 = tmp_struct121.field2;
            CursorTy pvrtmp5510 = tmp_struct121.field3;
            CursorTy fltPrd4555 = (CursorTy) pvrtmp5509;
            CursorTy fltPrd4556 = (CursorTy) pvrtmp5510;
            CursorTy pvrtmp5512 = (CursorTy) fltPrd4556;
            CursorTy pvrtmp5511 = (CursorTy) fltPrd4555;
            CursorTy y1675 = (CursorTy) pvrtmp5511;
            CursorTy fltPrd4557 = (CursorTy) pvrtmp5509;
            CursorTy fltPrd4558 = (CursorTy) pvrtmp5510;
            CursorTy pvrtmp5514 = (CursorTy) fltPrd4558;
            CursorTy pvrtmp5513 = (CursorTy) fltPrd4557;
            CursorTy end_y1675 = (CursorTy) pvrtmp5514;
            CursorTy end_r1891_3419 = (CursorTy) pvrtmp5507;
            CursorTy endof3211 = (CursorTy) pvrtmp5508;

            *(TagTyPacked *) loc1889 = 11;

            CursorTy writetag3796 = loc1889 + 1;
            CursorTy writecur3797 = (CursorTy) end_y1675;
            CursorTy pvrtmp5516 = (CursorTy) writecur3797;
            CursorTy pvrtmp5515 = (CursorTy) loc1889;
            CursorTy taildc3212 = (CursorTy) pvrtmp5515;
            CursorTy end_taildc3212 = (CursorTy) pvrtmp5516;
            CursorTy pvrtmp5518 = (CursorTy) end_taildc3212;
            CursorTy pvrtmp5517 = (CursorTy) taildc3212;
            CursorTy fltPrd4559 = (CursorTy) pvrtmp5517;
            CursorTy fltPrd4560 = (CursorTy) pvrtmp5518;

            return (CursorCursorCursorCursorProd) {end_r1891_3419, endof3211,
                                                   fltPrd4559, fltPrd4560};
            break;
        }

      case 12:
        {
            CursorTy field_cur3799 = (CursorTy) tmpcur5330;
            CursorTy case2476 = (CursorTy) field_cur3799;
            CursorTy x1676 = (CursorTy) case2476;
            CursorTy loc2488 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct122 =
                                          _copy_Expr(end_r1890, end_r1891, loc2488, x1676);
            CursorTy pvrtmp5519 = tmp_struct122.field0;
            CursorTy pvrtmp5520 = tmp_struct122.field1;
            CursorTy pvrtmp5521 = tmp_struct122.field2;
            CursorTy pvrtmp5522 = tmp_struct122.field3;
            CursorTy fltPrd4561 = (CursorTy) pvrtmp5521;
            CursorTy fltPrd4562 = (CursorTy) pvrtmp5522;
            CursorTy pvrtmp5524 = (CursorTy) fltPrd4562;
            CursorTy pvrtmp5523 = (CursorTy) fltPrd4561;
            CursorTy y1679 = (CursorTy) pvrtmp5523;
            CursorTy fltPrd4563 = (CursorTy) pvrtmp5521;
            CursorTy fltPrd4564 = (CursorTy) pvrtmp5522;
            CursorTy pvrtmp5526 = (CursorTy) fltPrd4564;
            CursorTy pvrtmp5525 = (CursorTy) fltPrd4563;
            CursorTy end_y1679 = (CursorTy) pvrtmp5526;
            CursorTy end_r1891_3420 = (CursorTy) pvrtmp5519;
            CursorTy endof3213 = (CursorTy) pvrtmp5520;
            CursorTy case2477 = (CursorTy) endof3213;
            CursorTy x1677 = (CursorTy) case2477;
            CursorTy loc2489 = (CursorTy) end_y1679;
            CursorCursorCursorCursorProd tmp_struct123 =
                                          _copy_Expr(end_r1890, end_r1891_3420, loc2489, x1677);
            CursorTy pvrtmp5527 = tmp_struct123.field0;
            CursorTy pvrtmp5528 = tmp_struct123.field1;
            CursorTy pvrtmp5529 = tmp_struct123.field2;
            CursorTy pvrtmp5530 = tmp_struct123.field3;
            CursorTy fltPrd4565 = (CursorTy) pvrtmp5529;
            CursorTy fltPrd4566 = (CursorTy) pvrtmp5530;
            CursorTy pvrtmp5532 = (CursorTy) fltPrd4566;
            CursorTy pvrtmp5531 = (CursorTy) fltPrd4565;
            CursorTy y1680 = (CursorTy) pvrtmp5531;
            CursorTy fltPrd4567 = (CursorTy) pvrtmp5529;
            CursorTy fltPrd4568 = (CursorTy) pvrtmp5530;
            CursorTy pvrtmp5534 = (CursorTy) fltPrd4568;
            CursorTy pvrtmp5533 = (CursorTy) fltPrd4567;
            CursorTy end_y1680 = (CursorTy) pvrtmp5534;
            CursorTy end_r1891_3420_3421 = (CursorTy) pvrtmp5527;
            CursorTy endof3214 = (CursorTy) pvrtmp5528;
            CursorTy case2478 = (CursorTy) endof3214;
            CursorTy x1678 = (CursorTy) case2478;
            CursorTy loc2490 = (CursorTy) end_y1680;
            CursorCursorCursorCursorProd tmp_struct124 =
                                          _copy_Expr(end_r1890, end_r1891_3420_3421, loc2490, x1678);
            CursorTy pvrtmp5535 = tmp_struct124.field0;
            CursorTy pvrtmp5536 = tmp_struct124.field1;
            CursorTy pvrtmp5537 = tmp_struct124.field2;
            CursorTy pvrtmp5538 = tmp_struct124.field3;
            CursorTy fltPrd4569 = (CursorTy) pvrtmp5537;
            CursorTy fltPrd4570 = (CursorTy) pvrtmp5538;
            CursorTy pvrtmp5540 = (CursorTy) fltPrd4570;
            CursorTy pvrtmp5539 = (CursorTy) fltPrd4569;
            CursorTy y1681 = (CursorTy) pvrtmp5539;
            CursorTy fltPrd4571 = (CursorTy) pvrtmp5537;
            CursorTy fltPrd4572 = (CursorTy) pvrtmp5538;
            CursorTy pvrtmp5542 = (CursorTy) fltPrd4572;
            CursorTy pvrtmp5541 = (CursorTy) fltPrd4571;
            CursorTy end_y1681 = (CursorTy) pvrtmp5542;
            CursorTy end_r1891_3420_3421_3422 = (CursorTy) pvrtmp5535;
            CursorTy endof3215 = (CursorTy) pvrtmp5536;

            *(TagTyPacked *) loc1889 = 12;

            CursorTy writetag3803 = loc1889 + 1;
            CursorTy writecur3804 = (CursorTy) end_y1679;
            CursorTy writecur3805 = (CursorTy) end_y1680;
            CursorTy writecur3806 = (CursorTy) end_y1681;
            CursorTy pvrtmp5544 = (CursorTy) writecur3806;
            CursorTy pvrtmp5543 = (CursorTy) loc1889;
            CursorTy taildc3216 = (CursorTy) pvrtmp5543;
            CursorTy end_taildc3216 = (CursorTy) pvrtmp5544;
            CursorTy pvrtmp5546 = (CursorTy) end_taildc3216;
            CursorTy pvrtmp5545 = (CursorTy) taildc3216;
            CursorTy fltPrd4573 = (CursorTy) pvrtmp5545;
            CursorTy fltPrd4574 = (CursorTy) pvrtmp5546;

            return (CursorCursorCursorCursorProd) {end_r1891_3420_3421_3422,
                                                   endof3215, fltPrd4573,
                                                   fltPrd4574};
            break;
        }

      case 13:
        {
            CursorTy field_cur3808 = (CursorTy) tmpcur5330;
            CursorTy case2494 = (CursorTy) field_cur3808;
            CursorTy x1682 = (CursorTy) case2494;
            CursorTy loc2502 = loc1889 + 1;
            CursorCursorCursorCursorProd tmp_struct125 =
                                          _copy_Expr(end_r1890, end_r1891, loc2502, x1682);
            CursorTy pvrtmp5547 = tmp_struct125.field0;
            CursorTy pvrtmp5548 = tmp_struct125.field1;
            CursorTy pvrtmp5549 = tmp_struct125.field2;
            CursorTy pvrtmp5550 = tmp_struct125.field3;
            CursorTy fltPrd4575 = (CursorTy) pvrtmp5549;
            CursorTy fltPrd4576 = (CursorTy) pvrtmp5550;
            CursorTy pvrtmp5552 = (CursorTy) fltPrd4576;
            CursorTy pvrtmp5551 = (CursorTy) fltPrd4575;
            CursorTy y1684 = (CursorTy) pvrtmp5551;
            CursorTy fltPrd4577 = (CursorTy) pvrtmp5549;
            CursorTy fltPrd4578 = (CursorTy) pvrtmp5550;
            CursorTy pvrtmp5554 = (CursorTy) fltPrd4578;
            CursorTy pvrtmp5553 = (CursorTy) fltPrd4577;
            CursorTy end_y1684 = (CursorTy) pvrtmp5554;
            CursorTy end_r1891_3423 = (CursorTy) pvrtmp5547;
            CursorTy endof3217 = (CursorTy) pvrtmp5548;
            CursorTy case2495 = (CursorTy) endof3217;
            CursorTy x1683 = (CursorTy) case2495;
            CursorTy loc2503 = (CursorTy) end_y1684;
            CursorCursorCursorCursorProd tmp_struct126 =
                                          _copy_ListExpr(end_r1890, end_r1891_3423, loc2503, x1683);
            CursorTy pvrtmp5555 = tmp_struct126.field0;
            CursorTy pvrtmp5556 = tmp_struct126.field1;
            CursorTy pvrtmp5557 = tmp_struct126.field2;
            CursorTy pvrtmp5558 = tmp_struct126.field3;
            CursorTy fltPrd4579 = (CursorTy) pvrtmp5557;
            CursorTy fltPrd4580 = (CursorTy) pvrtmp5558;
            CursorTy pvrtmp5560 = (CursorTy) fltPrd4580;
            CursorTy pvrtmp5559 = (CursorTy) fltPrd4579;
            CursorTy y1685 = (CursorTy) pvrtmp5559;
            CursorTy fltPrd4581 = (CursorTy) pvrtmp5557;
            CursorTy fltPrd4582 = (CursorTy) pvrtmp5558;
            CursorTy pvrtmp5562 = (CursorTy) fltPrd4582;
            CursorTy pvrtmp5561 = (CursorTy) fltPrd4581;
            CursorTy end_y1685 = (CursorTy) pvrtmp5562;
            CursorTy end_r1891_3423_3424 = (CursorTy) pvrtmp5555;
            CursorTy endof3218 = (CursorTy) pvrtmp5556;

            *(TagTyPacked *) loc1889 = 13;

            CursorTy writetag3811 = loc1889 + 1;
            CursorTy writecur3812 = (CursorTy) end_y1684;
            CursorTy writecur3813 = (CursorTy) end_y1685;
            CursorTy pvrtmp5564 = (CursorTy) writecur3813;
            CursorTy pvrtmp5563 = (CursorTy) loc1889;
            CursorTy taildc3219 = (CursorTy) pvrtmp5563;
            CursorTy end_taildc3219 = (CursorTy) pvrtmp5564;
            CursorTy pvrtmp5566 = (CursorTy) end_taildc3219;
            CursorTy pvrtmp5565 = (CursorTy) taildc3219;
            CursorTy fltPrd4583 = (CursorTy) pvrtmp5565;
            CursorTy fltPrd4584 = (CursorTy) pvrtmp5566;

            return (CursorCursorCursorCursorProd) {end_r1891_3423_3424,
                                                   endof3218, fltPrd4583,
                                                   fltPrd4584};
            break;
        }

      case 14:
        {
            CursorTy field_cur3815 = (CursorTy) tmpcur5330;
            CursorTy case2506 = (CursorTy) field_cur3815;
            SymTy tmpval5567 = *(SymTy *) case2506;
            CursorTy tmpcur5568 = case2506 + sizeof(SymTy);
            SymTy x1686 = (SymTy) tmpval5567;
            CursorTy end_x1686 = (CursorTy) tmpcur5568;
            CursorTy jump3220 = case2506 + 8;

            *(TagTyPacked *) loc1889 = 14;

            CursorTy writetag3817 = loc1889 + 1;

            *(SymTy *) writetag3817 = x1686;

            CursorTy writecur3818 = writetag3817 + sizeof(SymTy);
            CursorTy pvrtmp5570 = (CursorTy) writecur3818;
            CursorTy pvrtmp5569 = (CursorTy) loc1889;
            CursorTy taildc3221 = (CursorTy) pvrtmp5569;
            CursorTy end_taildc3221 = (CursorTy) pvrtmp5570;
            CursorTy pvrtmp5572 = (CursorTy) end_taildc3221;
            CursorTy pvrtmp5571 = (CursorTy) taildc3221;
            CursorTy fltPrd4585 = (CursorTy) pvrtmp5571;
            CursorTy fltPrd4586 = (CursorTy) pvrtmp5572;

            return (CursorCursorCursorCursorProd) {end_r1891, jump3220,
                                                   fltPrd4585, fltPrd4586};
            break;
        }

      case 15:
        {
            CursorTy field_cur3820 = (CursorTy) tmpcur5330;
            CursorTy case2510 = (CursorTy) field_cur3820;
            SymTy tmpval5573 = *(SymTy *) case2510;
            CursorTy tmpcur5574 = case2510 + sizeof(SymTy);
            SymTy x1688 = (SymTy) tmpval5573;
            CursorTy end_x1688 = (CursorTy) tmpcur5574;
            CursorTy jump3222 = case2510 + 8;

            *(TagTyPacked *) loc1889 = 15;

            CursorTy writetag3822 = loc1889 + 1;

            *(SymTy *) writetag3822 = x1688;

            CursorTy writecur3823 = writetag3822 + sizeof(SymTy);
            CursorTy pvrtmp5576 = (CursorTy) writecur3823;
            CursorTy pvrtmp5575 = (CursorTy) loc1889;
            CursorTy taildc3223 = (CursorTy) pvrtmp5575;
            CursorTy end_taildc3223 = (CursorTy) pvrtmp5576;
            CursorTy pvrtmp5578 = (CursorTy) end_taildc3223;
            CursorTy pvrtmp5577 = (CursorTy) taildc3223;
            CursorTy fltPrd4587 = (CursorTy) pvrtmp5577;
            CursorTy fltPrd4588 = (CursorTy) pvrtmp5578;

            return (CursorCursorCursorCursorProd) {end_r1891, jump3222,
                                                   fltPrd4587, fltPrd4588};
            break;
        }

      case 16:
        {
            CursorTy field_cur3825 = (CursorTy) tmpcur5330;
            CursorTy case2514 = (CursorTy) field_cur3825;
            SymTy tmpval5579 = *(SymTy *) case2514;
            CursorTy tmpcur5580 = case2514 + sizeof(SymTy);
            SymTy x1690 = (SymTy) tmpval5579;
            CursorTy end_x1690 = (CursorTy) tmpcur5580;
            CursorTy jump3224 = case2514 + 8;

            *(TagTyPacked *) loc1889 = 16;

            CursorTy writetag3827 = loc1889 + 1;

            *(SymTy *) writetag3827 = x1690;

            CursorTy writecur3828 = writetag3827 + sizeof(SymTy);
            CursorTy pvrtmp5582 = (CursorTy) writecur3828;
            CursorTy pvrtmp5581 = (CursorTy) loc1889;
            CursorTy taildc3225 = (CursorTy) pvrtmp5581;
            CursorTy end_taildc3225 = (CursorTy) pvrtmp5582;
            CursorTy pvrtmp5584 = (CursorTy) end_taildc3225;
            CursorTy pvrtmp5583 = (CursorTy) taildc3225;
            CursorTy fltPrd4589 = (CursorTy) pvrtmp5583;
            CursorTy fltPrd4590 = (CursorTy) pvrtmp5584;

            return (CursorCursorCursorCursorProd) {end_r1891, jump3224,
                                                   fltPrd4589, fltPrd4590};
            break;
        }

      case 17:
        {
            CursorTy field_cur3830 = (CursorTy) tmpcur5330;
            CursorTy jump3226 = loc1888 + 1;

            *(TagTyPacked *) loc1889 = 17;

            CursorTy writetag3831 = loc1889 + 1;
            CursorTy pvrtmp5586 = (CursorTy) writetag3831;
            CursorTy pvrtmp5585 = (CursorTy) loc1889;
            CursorTy taildc3227 = (CursorTy) pvrtmp5585;
            CursorTy end_taildc3227 = (CursorTy) pvrtmp5586;
            CursorTy pvrtmp5588 = (CursorTy) end_taildc3227;
            CursorTy pvrtmp5587 = (CursorTy) taildc3227;
            CursorTy fltPrd4591 = (CursorTy) pvrtmp5587;
            CursorTy fltPrd4592 = (CursorTy) pvrtmp5588;

            return (CursorCursorCursorCursorProd) {end_r1891, jump3226,
                                                   fltPrd4591, fltPrd4592};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6638 = *(CursorTy *) tmpcur5330;
            CursorTy tmpaftercur6639 = tmpcur5330 + 8;
            TagTyPacked tagtmp6640 = *(TagTyPacked *) tmpcur6638;
            CursorTy tailtmp6641 = tmpcur6638 + 1;

            tmpval5329 = tagtmp6640;
            tmpcur5330 = tailtmp6641;
            goto switch5589;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6638 = *(CursorTy *) tmpcur5330;
            CursorTy tmpaftercur6639 = tmpcur5330 + 8;
            TagTyPacked tagtmp6640 = *(TagTyPacked *) tmpcur6638;
            CursorTy tailtmp6641 = tmpcur6638 + 1;

            tmpval5329 = tagtmp6640;
            tmpcur5330 = tailtmp6641;
            goto switch5589;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5329");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Expr(CursorTy end_r1893, CursorTy arg1692)
{
    CursorTy loc1892 = (CursorTy) arg1692;
    TagTyPacked tmpval5590 = *(TagTyPacked *) arg1692;
    CursorTy tmpcur5591 = arg1692 + 1;


  switch5646:
    ;
    switch (tmpval5590) {

      case 0:
        {
            CursorTy field_cur3833 = (CursorTy) tmpcur5591;
            CursorTy case2521 = (CursorTy) field_cur3833;
            SymTy tmpval5592 = *(SymTy *) case2521;
            CursorTy tmpcur5593 = case2521 + sizeof(SymTy);
            SymTy x1693 = (SymTy) tmpval5592;
            CursorTy end_x1693 = (CursorTy) tmpcur5593;
            CursorTy jump3228 = case2521 + 8;
            IntTy fltLitTail3229 = (IntTy) 42;

            return (CursorInt64Prod) {jump3228, fltLitTail3229};
            break;
        }

      case 1:
        {
            CursorTy field_cur3835 = (CursorTy) tmpcur5591;
            CursorTy case2522 = (CursorTy) field_cur3835;
            CursorTy x1695 = (CursorTy) case2522;
            CursorInt64Prod tmp_struct130 =
                             _traverse_Formals(end_r1893, x1695);
            CursorTy pvrtmp5594 = tmp_struct130.field0;
            IntTy pvrtmp5595 = tmp_struct130.field1;
            CursorTy endof3230 = (CursorTy) pvrtmp5594;
            IntTy y1697 = (IntTy) pvrtmp5595;
            CursorTy case2523 = (CursorTy) endof3230;
            CursorTy x1696 = (CursorTy) case2523;
            CursorInt64Prod tmp_struct131 =
                             _traverse_ListExpr(end_r1893, x1696);
            CursorTy pvrtmp5596 = tmp_struct131.field0;
            IntTy pvrtmp5597 = tmp_struct131.field1;
            CursorTy endof3232 = (CursorTy) pvrtmp5596;
            IntTy y1698 = (IntTy) pvrtmp5597;
            IntTy fltLitTail3231 = (IntTy) 42;

            return (CursorInt64Prod) {endof3232, fltLitTail3231};
            break;
        }

      case 2:
        {
            CursorTy field_cur3838 = (CursorTy) tmpcur5591;
            CursorTy case2528 = (CursorTy) field_cur3838;
            CursorTy x1699 = (CursorTy) case2528;
            CursorInt64Prod tmp_struct132 =
                             _traverse_LAMBDACASE(end_r1893, x1699);
            CursorTy pvrtmp5598 = tmp_struct132.field0;
            IntTy pvrtmp5599 = tmp_struct132.field1;
            CursorTy endof3234 = (CursorTy) pvrtmp5598;
            IntTy y1700 = (IntTy) pvrtmp5599;
            IntTy fltLitTail3233 = (IntTy) 42;

            return (CursorInt64Prod) {endof3234, fltLitTail3233};
            break;
        }

      case 3:
        {
            CursorTy field_cur3840 = (CursorTy) tmpcur5591;
            CursorTy case2531 = (CursorTy) field_cur3840;
            CursorTy x1701 = (CursorTy) case2531;
            CursorInt64Prod tmp_struct133 =  _traverse_Expr(end_r1893, x1701);
            CursorTy pvrtmp5600 = tmp_struct133.field0;
            IntTy pvrtmp5601 = tmp_struct133.field1;
            CursorTy endof3235 = (CursorTy) pvrtmp5600;
            IntTy y1704 = (IntTy) pvrtmp5601;
            CursorTy case2532 = (CursorTy) endof3235;
            CursorTy x1702 = (CursorTy) case2532;
            CursorInt64Prod tmp_struct134 =  _traverse_Expr(end_r1893, x1702);
            CursorTy pvrtmp5602 = tmp_struct134.field0;
            IntTy pvrtmp5603 = tmp_struct134.field1;
            CursorTy endof3236 = (CursorTy) pvrtmp5602;
            IntTy y1705 = (IntTy) pvrtmp5603;
            CursorTy case2533 = (CursorTy) endof3236;
            CursorTy x1703 = (CursorTy) case2533;
            CursorInt64Prod tmp_struct135 =  _traverse_Expr(end_r1893, x1703);
            CursorTy pvrtmp5604 = tmp_struct135.field0;
            IntTy pvrtmp5605 = tmp_struct135.field1;
            CursorTy endof3238 = (CursorTy) pvrtmp5604;
            IntTy y1706 = (IntTy) pvrtmp5605;
            IntTy fltLitTail3237 = (IntTy) 42;

            return (CursorInt64Prod) {endof3238, fltLitTail3237};
            break;
        }

      case 4:
        {
            CursorTy field_cur3844 = (CursorTy) tmpcur5591;
            CursorTy case2540 = (CursorTy) field_cur3844;
            CursorTy x1707 = (CursorTy) case2540;
            CursorInt64Prod tmp_struct136 =
                             _traverse_ListExpr(end_r1893, x1707);
            CursorTy pvrtmp5606 = tmp_struct136.field0;
            IntTy pvrtmp5607 = tmp_struct136.field1;
            CursorTy endof3240 = (CursorTy) pvrtmp5606;
            IntTy y1708 = (IntTy) pvrtmp5607;
            IntTy fltLitTail3239 = (IntTy) 42;

            return (CursorInt64Prod) {endof3240, fltLitTail3239};
            break;
        }

      case 5:
        {
            CursorTy field_cur3846 = (CursorTy) tmpcur5591;
            CursorTy case2543 = (CursorTy) field_cur3846;
            CursorTy x1709 = (CursorTy) case2543;
            CursorInt64Prod tmp_struct137 =  _traverse_Expr(end_r1893, x1709);
            CursorTy pvrtmp5608 = tmp_struct137.field0;
            IntTy pvrtmp5609 = tmp_struct137.field1;
            CursorTy endof3241 = (CursorTy) pvrtmp5608;
            IntTy y1711 = (IntTy) pvrtmp5609;
            CursorTy case2544 = (CursorTy) endof3241;
            CursorTy x1710 = (CursorTy) case2544;
            CursorInt64Prod tmp_struct138 =
                             _traverse_ListExpr(end_r1893, x1710);
            CursorTy pvrtmp5610 = tmp_struct138.field0;
            IntTy pvrtmp5611 = tmp_struct138.field1;
            CursorTy endof3243 = (CursorTy) pvrtmp5610;
            IntTy y1712 = (IntTy) pvrtmp5611;
            IntTy fltLitTail3242 = (IntTy) 42;

            return (CursorInt64Prod) {endof3243, fltLitTail3242};
            break;
        }

      case 6:
        {
            CursorTy field_cur3849 = (CursorTy) tmpcur5591;
            CursorTy case2549 = (CursorTy) field_cur3849;
            CursorTy x1713 = (CursorTy) case2549;
            CursorInt64Prod tmp_struct139 =  _traverse_LVBIND(end_r1893, x1713);
            CursorTy pvrtmp5612 = tmp_struct139.field0;
            IntTy pvrtmp5613 = tmp_struct139.field1;
            CursorTy endof3244 = (CursorTy) pvrtmp5612;
            IntTy y1715 = (IntTy) pvrtmp5613;
            CursorTy case2550 = (CursorTy) endof3244;
            CursorTy x1714 = (CursorTy) case2550;
            CursorInt64Prod tmp_struct140 =
                             _traverse_ListExpr(end_r1893, x1714);
            CursorTy pvrtmp5614 = tmp_struct140.field0;
            IntTy pvrtmp5615 = tmp_struct140.field1;
            CursorTy endof3246 = (CursorTy) pvrtmp5614;
            IntTy y1716 = (IntTy) pvrtmp5615;
            IntTy fltLitTail3245 = (IntTy) 42;

            return (CursorInt64Prod) {endof3246, fltLitTail3245};
            break;
        }

      case 7:
        {
            CursorTy field_cur3852 = (CursorTy) tmpcur5591;
            CursorTy case2555 = (CursorTy) field_cur3852;
            CursorTy x1717 = (CursorTy) case2555;
            CursorInt64Prod tmp_struct141 =  _traverse_LVBIND(end_r1893, x1717);
            CursorTy pvrtmp5616 = tmp_struct141.field0;
            IntTy pvrtmp5617 = tmp_struct141.field1;
            CursorTy endof3247 = (CursorTy) pvrtmp5616;
            IntTy y1719 = (IntTy) pvrtmp5617;
            CursorTy case2556 = (CursorTy) endof3247;
            CursorTy x1718 = (CursorTy) case2556;
            CursorInt64Prod tmp_struct142 =
                             _traverse_ListExpr(end_r1893, x1718);
            CursorTy pvrtmp5618 = tmp_struct142.field0;
            IntTy pvrtmp5619 = tmp_struct142.field1;
            CursorTy endof3249 = (CursorTy) pvrtmp5618;
            IntTy y1720 = (IntTy) pvrtmp5619;
            IntTy fltLitTail3248 = (IntTy) 42;

            return (CursorInt64Prod) {endof3249, fltLitTail3248};
            break;
        }

      case 8:
        {
            CursorTy field_cur3855 = (CursorTy) tmpcur5591;
            CursorTy case2561 = (CursorTy) field_cur3855;
            SymTy tmpval5620 = *(SymTy *) case2561;
            CursorTy tmpcur5621 = case2561 + sizeof(SymTy);
            SymTy x1721 = (SymTy) tmpval5620;
            CursorTy end_x1721 = (CursorTy) tmpcur5621;
            CursorTy case2562 = (CursorTy) end_x1721;
            CursorTy x1722 = (CursorTy) case2562;
            CursorTy jump3250 = case2561 + 8;
            CursorInt64Prod tmp_struct143 =  _traverse_Expr(end_r1893, x1722);
            CursorTy pvrtmp5622 = tmp_struct143.field0;
            IntTy pvrtmp5623 = tmp_struct143.field1;
            CursorTy endof3252 = (CursorTy) pvrtmp5622;
            IntTy y1724 = (IntTy) pvrtmp5623;
            IntTy fltLitTail3251 = (IntTy) 42;

            return (CursorInt64Prod) {endof3252, fltLitTail3251};
            break;
        }

      case 9:
        {
            CursorTy field_cur3858 = (CursorTy) tmpcur5591;
            CursorTy case2565 = (CursorTy) field_cur3858;
            CursorTy x1725 = (CursorTy) case2565;
            CursorInt64Prod tmp_struct144 =  _traverse_Datum(end_r1893, x1725);
            CursorTy pvrtmp5624 = tmp_struct144.field0;
            IntTy pvrtmp5625 = tmp_struct144.field1;
            CursorTy endof3254 = (CursorTy) pvrtmp5624;
            IntTy y1726 = (IntTy) pvrtmp5625;
            IntTy fltLitTail3253 = (IntTy) 42;

            return (CursorInt64Prod) {endof3254, fltLitTail3253};
            break;
        }

      case 10:
        {
            CursorTy field_cur3860 = (CursorTy) tmpcur5591;
            CursorTy case2568 = (CursorTy) field_cur3860;
            CursorTy x1727 = (CursorTy) case2568;
            CursorInt64Prod tmp_struct145 =  _traverse_Datum(end_r1893, x1727);
            CursorTy pvrtmp5626 = tmp_struct145.field0;
            IntTy pvrtmp5627 = tmp_struct145.field1;
            CursorTy endof3256 = (CursorTy) pvrtmp5626;
            IntTy y1728 = (IntTy) pvrtmp5627;
            IntTy fltLitTail3255 = (IntTy) 42;

            return (CursorInt64Prod) {endof3256, fltLitTail3255};
            break;
        }

      case 11:
        {
            CursorTy field_cur3862 = (CursorTy) tmpcur5591;
            CursorTy case2571 = (CursorTy) field_cur3862;
            CursorTy x1729 = (CursorTy) case2571;
            CursorInt64Prod tmp_struct146 =  _traverse_Datum(end_r1893, x1729);
            CursorTy pvrtmp5628 = tmp_struct146.field0;
            IntTy pvrtmp5629 = tmp_struct146.field1;
            CursorTy endof3258 = (CursorTy) pvrtmp5628;
            IntTy y1730 = (IntTy) pvrtmp5629;
            IntTy fltLitTail3257 = (IntTy) 42;

            return (CursorInt64Prod) {endof3258, fltLitTail3257};
            break;
        }

      case 12:
        {
            CursorTy field_cur3864 = (CursorTy) tmpcur5591;
            CursorTy case2574 = (CursorTy) field_cur3864;
            CursorTy x1731 = (CursorTy) case2574;
            CursorInt64Prod tmp_struct147 =  _traverse_Expr(end_r1893, x1731);
            CursorTy pvrtmp5630 = tmp_struct147.field0;
            IntTy pvrtmp5631 = tmp_struct147.field1;
            CursorTy endof3259 = (CursorTy) pvrtmp5630;
            IntTy y1734 = (IntTy) pvrtmp5631;
            CursorTy case2575 = (CursorTy) endof3259;
            CursorTy x1732 = (CursorTy) case2575;
            CursorInt64Prod tmp_struct148 =  _traverse_Expr(end_r1893, x1732);
            CursorTy pvrtmp5632 = tmp_struct148.field0;
            IntTy pvrtmp5633 = tmp_struct148.field1;
            CursorTy endof3260 = (CursorTy) pvrtmp5632;
            IntTy y1735 = (IntTy) pvrtmp5633;
            CursorTy case2576 = (CursorTy) endof3260;
            CursorTy x1733 = (CursorTy) case2576;
            CursorInt64Prod tmp_struct149 =  _traverse_Expr(end_r1893, x1733);
            CursorTy pvrtmp5634 = tmp_struct149.field0;
            IntTy pvrtmp5635 = tmp_struct149.field1;
            CursorTy endof3262 = (CursorTy) pvrtmp5634;
            IntTy y1736 = (IntTy) pvrtmp5635;
            IntTy fltLitTail3261 = (IntTy) 42;

            return (CursorInt64Prod) {endof3262, fltLitTail3261};
            break;
        }

      case 13:
        {
            CursorTy field_cur3868 = (CursorTy) tmpcur5591;
            CursorTy case2583 = (CursorTy) field_cur3868;
            CursorTy x1737 = (CursorTy) case2583;
            CursorInt64Prod tmp_struct150 =  _traverse_Expr(end_r1893, x1737);
            CursorTy pvrtmp5636 = tmp_struct150.field0;
            IntTy pvrtmp5637 = tmp_struct150.field1;
            CursorTy endof3263 = (CursorTy) pvrtmp5636;
            IntTy y1739 = (IntTy) pvrtmp5637;
            CursorTy case2584 = (CursorTy) endof3263;
            CursorTy x1738 = (CursorTy) case2584;
            CursorInt64Prod tmp_struct151 =
                             _traverse_ListExpr(end_r1893, x1738);
            CursorTy pvrtmp5638 = tmp_struct151.field0;
            IntTy pvrtmp5639 = tmp_struct151.field1;
            CursorTy endof3265 = (CursorTy) pvrtmp5638;
            IntTy y1740 = (IntTy) pvrtmp5639;
            IntTy fltLitTail3264 = (IntTy) 42;

            return (CursorInt64Prod) {endof3265, fltLitTail3264};
            break;
        }

      case 14:
        {
            CursorTy field_cur3871 = (CursorTy) tmpcur5591;
            CursorTy case2589 = (CursorTy) field_cur3871;
            SymTy tmpval5640 = *(SymTy *) case2589;
            CursorTy tmpcur5641 = case2589 + sizeof(SymTy);
            SymTy x1741 = (SymTy) tmpval5640;
            CursorTy end_x1741 = (CursorTy) tmpcur5641;
            CursorTy jump3266 = case2589 + 8;
            IntTy fltLitTail3267 = (IntTy) 42;

            return (CursorInt64Prod) {jump3266, fltLitTail3267};
            break;
        }

      case 15:
        {
            CursorTy field_cur3873 = (CursorTy) tmpcur5591;
            CursorTy case2590 = (CursorTy) field_cur3873;
            SymTy tmpval5642 = *(SymTy *) case2590;
            CursorTy tmpcur5643 = case2590 + sizeof(SymTy);
            SymTy x1743 = (SymTy) tmpval5642;
            CursorTy end_x1743 = (CursorTy) tmpcur5643;
            CursorTy jump3268 = case2590 + 8;
            IntTy fltLitTail3269 = (IntTy) 42;

            return (CursorInt64Prod) {jump3268, fltLitTail3269};
            break;
        }

      case 16:
        {
            CursorTy field_cur3875 = (CursorTy) tmpcur5591;
            CursorTy case2591 = (CursorTy) field_cur3875;
            SymTy tmpval5644 = *(SymTy *) case2591;
            CursorTy tmpcur5645 = case2591 + sizeof(SymTy);
            SymTy x1745 = (SymTy) tmpval5644;
            CursorTy end_x1745 = (CursorTy) tmpcur5645;
            CursorTy jump3270 = case2591 + 8;
            IntTy fltLitTail3271 = (IntTy) 42;

            return (CursorInt64Prod) {jump3270, fltLitTail3271};
            break;
        }

      case 17:
        {
            CursorTy field_cur3877 = (CursorTy) tmpcur5591;
            CursorTy jump3272 = loc1892 + 1;
            IntTy fltLitTail3273 = (IntTy) 42;

            return (CursorInt64Prod) {jump3272, fltLitTail3273};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6642 = *(CursorTy *) tmpcur5591;
            CursorTy tmpaftercur6643 = tmpcur5591 + 8;
            TagTyPacked tagtmp6644 = *(TagTyPacked *) tmpcur6642;
            CursorTy tailtmp6645 = tmpcur6642 + 1;

            tmpval5590 = tagtmp6644;
            tmpcur5591 = tailtmp6645;
            goto switch5646;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6642 = *(CursorTy *) tmpcur5591;
            CursorTy tmpaftercur6643 = tmpcur5591 + 8;
            TagTyPacked tagtmp6644 = *(TagTyPacked *) tmpcur6642;
            CursorTy tailtmp6645 = tmpcur6642 + 1;

            tmpval5590 = tagtmp6644;
            tmpcur5591 = tailtmp6645;
            goto switch5646;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5590");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r1896,
                                          CursorTy end_r1897, CursorTy loc1895,
                                          CursorTy arg1747)
{
    CursorTy loc1894 = (CursorTy) arg1747;

    if (loc1895 + 18 > end_r1897) {
        ChunkTy new_chunk158 = alloc_chunk(end_r1897);
        CursorTy chunk_start159 = new_chunk158.start_ptr;
        CursorTy chunk_end160 = new_chunk158.end_ptr;

        end_r1897 = chunk_end160;
        *(TagTyPacked *) loc1895 = 255;

        CursorTy redir = loc1895 + 1;

        *(CursorTy *) redir = chunk_start159;
        loc1895 = chunk_start159;
    }

    TagTyPacked tmpval5647 = *(TagTyPacked *) arg1747;
    CursorTy tmpcur5648 = arg1747 + 1;


  switch5713:
    ;
    switch (tmpval5647) {

      case 0:
        {
            CursorTy field_cur3878 = (CursorTy) tmpcur5648;
            CursorTy case2594 = (CursorTy) field_cur3878;
            CursorTy x1748 = (CursorTy) case2594;
            CursorTy loc2602 = loc1895 + 1;
            CursorCursorCursorCursorProd tmp_struct152 =
                                          _copy_ListSym(end_r1896, end_r1897, loc2602, x1748);
            CursorTy pvrtmp5649 = tmp_struct152.field0;
            CursorTy pvrtmp5650 = tmp_struct152.field1;
            CursorTy pvrtmp5651 = tmp_struct152.field2;
            CursorTy pvrtmp5652 = tmp_struct152.field3;
            CursorTy fltPrd4593 = (CursorTy) pvrtmp5651;
            CursorTy fltPrd4594 = (CursorTy) pvrtmp5652;
            CursorTy pvrtmp5654 = (CursorTy) fltPrd4594;
            CursorTy pvrtmp5653 = (CursorTy) fltPrd4593;
            CursorTy y1750 = (CursorTy) pvrtmp5653;
            CursorTy fltPrd4595 = (CursorTy) pvrtmp5651;
            CursorTy fltPrd4596 = (CursorTy) pvrtmp5652;
            CursorTy pvrtmp5656 = (CursorTy) fltPrd4596;
            CursorTy pvrtmp5655 = (CursorTy) fltPrd4595;
            CursorTy end_y1750 = (CursorTy) pvrtmp5656;
            CursorTy end_r1897_3425 = (CursorTy) pvrtmp5649;
            CursorTy endof3274 = (CursorTy) pvrtmp5650;
            CursorTy case2595 = (CursorTy) endof3274;
            CursorTy x1749 = (CursorTy) case2595;
            CursorTy loc2603 = (CursorTy) end_y1750;
            CursorCursorCursorCursorProd tmp_struct153 =
                                          _copy_Expr(end_r1896, end_r1897_3425, loc2603, x1749);
            CursorTy pvrtmp5657 = tmp_struct153.field0;
            CursorTy pvrtmp5658 = tmp_struct153.field1;
            CursorTy pvrtmp5659 = tmp_struct153.field2;
            CursorTy pvrtmp5660 = tmp_struct153.field3;
            CursorTy fltPrd4597 = (CursorTy) pvrtmp5659;
            CursorTy fltPrd4598 = (CursorTy) pvrtmp5660;
            CursorTy pvrtmp5662 = (CursorTy) fltPrd4598;
            CursorTy pvrtmp5661 = (CursorTy) fltPrd4597;
            CursorTy y1751 = (CursorTy) pvrtmp5661;
            CursorTy fltPrd4599 = (CursorTy) pvrtmp5659;
            CursorTy fltPrd4600 = (CursorTy) pvrtmp5660;
            CursorTy pvrtmp5664 = (CursorTy) fltPrd4600;
            CursorTy pvrtmp5663 = (CursorTy) fltPrd4599;
            CursorTy end_y1751 = (CursorTy) pvrtmp5664;
            CursorTy end_r1897_3425_3426 = (CursorTy) pvrtmp5657;
            CursorTy endof3275 = (CursorTy) pvrtmp5658;

            *(TagTyPacked *) loc1895 = 0;

            CursorTy writetag3881 = loc1895 + 1;
            CursorTy writecur3882 = (CursorTy) end_y1750;
            CursorTy writecur3883 = (CursorTy) end_y1751;
            CursorTy pvrtmp5666 = (CursorTy) writecur3883;
            CursorTy pvrtmp5665 = (CursorTy) loc1895;
            CursorTy taildc3276 = (CursorTy) pvrtmp5665;
            CursorTy end_taildc3276 = (CursorTy) pvrtmp5666;
            CursorTy pvrtmp5668 = (CursorTy) end_taildc3276;
            CursorTy pvrtmp5667 = (CursorTy) taildc3276;
            CursorTy fltPrd4601 = (CursorTy) pvrtmp5667;
            CursorTy fltPrd4602 = (CursorTy) pvrtmp5668;

            return (CursorCursorCursorCursorProd) {end_r1897_3425_3426,
                                                   endof3275, fltPrd4601,
                                                   fltPrd4602};
            break;
        }

      case 1:
        {
            CursorTy field_cur3885 = (CursorTy) tmpcur5648;
            CursorTy case2606 = (CursorTy) field_cur3885;
            CursorTy x1752 = (CursorTy) case2606;
            CursorTy loc2614 = loc1895 + 1;
            CursorCursorCursorCursorProd tmp_struct154 =
                                          _copy_ListSym(end_r1896, end_r1897, loc2614, x1752);
            CursorTy pvrtmp5669 = tmp_struct154.field0;
            CursorTy pvrtmp5670 = tmp_struct154.field1;
            CursorTy pvrtmp5671 = tmp_struct154.field2;
            CursorTy pvrtmp5672 = tmp_struct154.field3;
            CursorTy fltPrd4603 = (CursorTy) pvrtmp5671;
            CursorTy fltPrd4604 = (CursorTy) pvrtmp5672;
            CursorTy pvrtmp5674 = (CursorTy) fltPrd4604;
            CursorTy pvrtmp5673 = (CursorTy) fltPrd4603;
            CursorTy y1754 = (CursorTy) pvrtmp5673;
            CursorTy fltPrd4605 = (CursorTy) pvrtmp5671;
            CursorTy fltPrd4606 = (CursorTy) pvrtmp5672;
            CursorTy pvrtmp5676 = (CursorTy) fltPrd4606;
            CursorTy pvrtmp5675 = (CursorTy) fltPrd4605;
            CursorTy end_y1754 = (CursorTy) pvrtmp5676;
            CursorTy end_r1897_3427 = (CursorTy) pvrtmp5669;
            CursorTy endof3277 = (CursorTy) pvrtmp5670;
            CursorTy case2607 = (CursorTy) endof3277;
            CursorTy x1753 = (CursorTy) case2607;
            CursorTy loc2615 = (CursorTy) end_y1754;
            CursorCursorCursorCursorProd tmp_struct155 =
                                          _copy_Expr(end_r1896, end_r1897_3427, loc2615, x1753);
            CursorTy pvrtmp5677 = tmp_struct155.field0;
            CursorTy pvrtmp5678 = tmp_struct155.field1;
            CursorTy pvrtmp5679 = tmp_struct155.field2;
            CursorTy pvrtmp5680 = tmp_struct155.field3;
            CursorTy fltPrd4607 = (CursorTy) pvrtmp5679;
            CursorTy fltPrd4608 = (CursorTy) pvrtmp5680;
            CursorTy pvrtmp5682 = (CursorTy) fltPrd4608;
            CursorTy pvrtmp5681 = (CursorTy) fltPrd4607;
            CursorTy y1755 = (CursorTy) pvrtmp5681;
            CursorTy fltPrd4609 = (CursorTy) pvrtmp5679;
            CursorTy fltPrd4610 = (CursorTy) pvrtmp5680;
            CursorTy pvrtmp5684 = (CursorTy) fltPrd4610;
            CursorTy pvrtmp5683 = (CursorTy) fltPrd4609;
            CursorTy end_y1755 = (CursorTy) pvrtmp5684;
            CursorTy end_r1897_3427_3428 = (CursorTy) pvrtmp5677;
            CursorTy endof3278 = (CursorTy) pvrtmp5678;

            *(TagTyPacked *) loc1895 = 1;

            CursorTy writetag3888 = loc1895 + 1;
            CursorTy writecur3889 = (CursorTy) end_y1754;
            CursorTy writecur3890 = (CursorTy) end_y1755;
            CursorTy pvrtmp5686 = (CursorTy) writecur3890;
            CursorTy pvrtmp5685 = (CursorTy) loc1895;
            CursorTy taildc3279 = (CursorTy) pvrtmp5685;
            CursorTy end_taildc3279 = (CursorTy) pvrtmp5686;
            CursorTy pvrtmp5688 = (CursorTy) end_taildc3279;
            CursorTy pvrtmp5687 = (CursorTy) taildc3279;
            CursorTy fltPrd4611 = (CursorTy) pvrtmp5687;
            CursorTy fltPrd4612 = (CursorTy) pvrtmp5688;

            return (CursorCursorCursorCursorProd) {end_r1897_3427_3428,
                                                   endof3278, fltPrd4611,
                                                   fltPrd4612};
            break;
        }

      case 2:
        {
            CursorTy field_cur3892 = (CursorTy) tmpcur5648;
            CursorTy case2618 = (CursorTy) field_cur3892;
            CursorTy x1756 = (CursorTy) case2618;
            CursorTy loc2622 = loc1895 + 1;
            CursorCursorCursorCursorProd tmp_struct156 =
                                          _copy_ListToplvl(end_r1896, end_r1897, loc2622, x1756);
            CursorTy pvrtmp5689 = tmp_struct156.field0;
            CursorTy pvrtmp5690 = tmp_struct156.field1;
            CursorTy pvrtmp5691 = tmp_struct156.field2;
            CursorTy pvrtmp5692 = tmp_struct156.field3;
            CursorTy fltPrd4613 = (CursorTy) pvrtmp5691;
            CursorTy fltPrd4614 = (CursorTy) pvrtmp5692;
            CursorTy pvrtmp5694 = (CursorTy) fltPrd4614;
            CursorTy pvrtmp5693 = (CursorTy) fltPrd4613;
            CursorTy y1757 = (CursorTy) pvrtmp5693;
            CursorTy fltPrd4615 = (CursorTy) pvrtmp5691;
            CursorTy fltPrd4616 = (CursorTy) pvrtmp5692;
            CursorTy pvrtmp5696 = (CursorTy) fltPrd4616;
            CursorTy pvrtmp5695 = (CursorTy) fltPrd4615;
            CursorTy end_y1757 = (CursorTy) pvrtmp5696;
            CursorTy end_r1897_3429 = (CursorTy) pvrtmp5689;
            CursorTy endof3280 = (CursorTy) pvrtmp5690;

            *(TagTyPacked *) loc1895 = 2;

            CursorTy writetag3894 = loc1895 + 1;
            CursorTy writecur3895 = (CursorTy) end_y1757;
            CursorTy pvrtmp5698 = (CursorTy) writecur3895;
            CursorTy pvrtmp5697 = (CursorTy) loc1895;
            CursorTy taildc3281 = (CursorTy) pvrtmp5697;
            CursorTy end_taildc3281 = (CursorTy) pvrtmp5698;
            CursorTy pvrtmp5700 = (CursorTy) end_taildc3281;
            CursorTy pvrtmp5699 = (CursorTy) taildc3281;
            CursorTy fltPrd4617 = (CursorTy) pvrtmp5699;
            CursorTy fltPrd4618 = (CursorTy) pvrtmp5700;

            return (CursorCursorCursorCursorProd) {end_r1897_3429, endof3280,
                                                   fltPrd4617, fltPrd4618};
            break;
        }

      case 3:
        {
            CursorTy field_cur3897 = (CursorTy) tmpcur5648;
            CursorTy case2624 = (CursorTy) field_cur3897;
            CursorTy x1758 = (CursorTy) case2624;
            CursorTy loc2628 = loc1895 + 1;
            CursorCursorCursorCursorProd tmp_struct157 =
                                          _copy_Expr(end_r1896, end_r1897, loc2628, x1758);
            CursorTy pvrtmp5701 = tmp_struct157.field0;
            CursorTy pvrtmp5702 = tmp_struct157.field1;
            CursorTy pvrtmp5703 = tmp_struct157.field2;
            CursorTy pvrtmp5704 = tmp_struct157.field3;
            CursorTy fltPrd4619 = (CursorTy) pvrtmp5703;
            CursorTy fltPrd4620 = (CursorTy) pvrtmp5704;
            CursorTy pvrtmp5706 = (CursorTy) fltPrd4620;
            CursorTy pvrtmp5705 = (CursorTy) fltPrd4619;
            CursorTy y1759 = (CursorTy) pvrtmp5705;
            CursorTy fltPrd4621 = (CursorTy) pvrtmp5703;
            CursorTy fltPrd4622 = (CursorTy) pvrtmp5704;
            CursorTy pvrtmp5708 = (CursorTy) fltPrd4622;
            CursorTy pvrtmp5707 = (CursorTy) fltPrd4621;
            CursorTy end_y1759 = (CursorTy) pvrtmp5708;
            CursorTy end_r1897_3430 = (CursorTy) pvrtmp5701;
            CursorTy endof3282 = (CursorTy) pvrtmp5702;

            *(TagTyPacked *) loc1895 = 3;

            CursorTy writetag3899 = loc1895 + 1;
            CursorTy writecur3900 = (CursorTy) end_y1759;
            CursorTy pvrtmp5710 = (CursorTy) writecur3900;
            CursorTy pvrtmp5709 = (CursorTy) loc1895;
            CursorTy taildc3283 = (CursorTy) pvrtmp5709;
            CursorTy end_taildc3283 = (CursorTy) pvrtmp5710;
            CursorTy pvrtmp5712 = (CursorTy) end_taildc3283;
            CursorTy pvrtmp5711 = (CursorTy) taildc3283;
            CursorTy fltPrd4623 = (CursorTy) pvrtmp5711;
            CursorTy fltPrd4624 = (CursorTy) pvrtmp5712;

            return (CursorCursorCursorCursorProd) {end_r1897_3430, endof3282,
                                                   fltPrd4623, fltPrd4624};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6646 = *(CursorTy *) tmpcur5648;
            CursorTy tmpaftercur6647 = tmpcur5648 + 8;
            TagTyPacked tagtmp6648 = *(TagTyPacked *) tmpcur6646;
            CursorTy tailtmp6649 = tmpcur6646 + 1;

            tmpval5647 = tagtmp6648;
            tmpcur5648 = tailtmp6649;
            goto switch5713;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6646 = *(CursorTy *) tmpcur5648;
            CursorTy tmpaftercur6647 = tmpcur5648 + 8;
            TagTyPacked tagtmp6648 = *(TagTyPacked *) tmpcur6646;
            CursorTy tailtmp6649 = tmpcur6646 + 1;

            tmpval5647 = tagtmp6648;
            tmpcur5648 = tailtmp6649;
            goto switch5713;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5647");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Toplvl(CursorTy end_r1899, CursorTy arg1760)
{
    CursorTy loc1898 = (CursorTy) arg1760;
    TagTyPacked tmpval5714 = *(TagTyPacked *) arg1760;
    CursorTy tmpcur5715 = arg1760 + 1;


  switch5728:
    ;
    switch (tmpval5714) {

      case 0:
        {
            CursorTy field_cur3902 = (CursorTy) tmpcur5715;
            CursorTy case2632 = (CursorTy) field_cur3902;
            CursorTy x1761 = (CursorTy) case2632;
            CursorInt64Prod tmp_struct161 =
                             _traverse_ListSym(end_r1899, x1761);
            CursorTy pvrtmp5716 = tmp_struct161.field0;
            IntTy pvrtmp5717 = tmp_struct161.field1;
            CursorTy endof3284 = (CursorTy) pvrtmp5716;
            IntTy y1763 = (IntTy) pvrtmp5717;
            CursorTy case2633 = (CursorTy) endof3284;
            CursorTy x1762 = (CursorTy) case2633;
            CursorInt64Prod tmp_struct162 =  _traverse_Expr(end_r1899, x1762);
            CursorTy pvrtmp5718 = tmp_struct162.field0;
            IntTy pvrtmp5719 = tmp_struct162.field1;
            CursorTy endof3286 = (CursorTy) pvrtmp5718;
            IntTy y1764 = (IntTy) pvrtmp5719;
            IntTy fltLitTail3285 = (IntTy) 42;

            return (CursorInt64Prod) {endof3286, fltLitTail3285};
            break;
        }

      case 1:
        {
            CursorTy field_cur3905 = (CursorTy) tmpcur5715;
            CursorTy case2638 = (CursorTy) field_cur3905;
            CursorTy x1765 = (CursorTy) case2638;
            CursorInt64Prod tmp_struct163 =
                             _traverse_ListSym(end_r1899, x1765);
            CursorTy pvrtmp5720 = tmp_struct163.field0;
            IntTy pvrtmp5721 = tmp_struct163.field1;
            CursorTy endof3287 = (CursorTy) pvrtmp5720;
            IntTy y1767 = (IntTy) pvrtmp5721;
            CursorTy case2639 = (CursorTy) endof3287;
            CursorTy x1766 = (CursorTy) case2639;
            CursorInt64Prod tmp_struct164 =  _traverse_Expr(end_r1899, x1766);
            CursorTy pvrtmp5722 = tmp_struct164.field0;
            IntTy pvrtmp5723 = tmp_struct164.field1;
            CursorTy endof3289 = (CursorTy) pvrtmp5722;
            IntTy y1768 = (IntTy) pvrtmp5723;
            IntTy fltLitTail3288 = (IntTy) 42;

            return (CursorInt64Prod) {endof3289, fltLitTail3288};
            break;
        }

      case 2:
        {
            CursorTy field_cur3908 = (CursorTy) tmpcur5715;
            CursorTy case2644 = (CursorTy) field_cur3908;
            CursorTy x1769 = (CursorTy) case2644;
            CursorInt64Prod tmp_struct165 =
                             _traverse_ListToplvl(end_r1899, x1769);
            CursorTy pvrtmp5724 = tmp_struct165.field0;
            IntTy pvrtmp5725 = tmp_struct165.field1;
            CursorTy endof3291 = (CursorTy) pvrtmp5724;
            IntTy y1770 = (IntTy) pvrtmp5725;
            IntTy fltLitTail3290 = (IntTy) 42;

            return (CursorInt64Prod) {endof3291, fltLitTail3290};
            break;
        }

      case 3:
        {
            CursorTy field_cur3910 = (CursorTy) tmpcur5715;
            CursorTy case2647 = (CursorTy) field_cur3910;
            CursorTy x1771 = (CursorTy) case2647;
            CursorInt64Prod tmp_struct166 =  _traverse_Expr(end_r1899, x1771);
            CursorTy pvrtmp5726 = tmp_struct166.field0;
            IntTy pvrtmp5727 = tmp_struct166.field1;
            CursorTy endof3293 = (CursorTy) pvrtmp5726;
            IntTy y1772 = (IntTy) pvrtmp5727;
            IntTy fltLitTail3292 = (IntTy) 42;

            return (CursorInt64Prod) {endof3293, fltLitTail3292};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6650 = *(CursorTy *) tmpcur5715;
            CursorTy tmpaftercur6651 = tmpcur5715 + 8;
            TagTyPacked tagtmp6652 = *(TagTyPacked *) tmpcur6650;
            CursorTy tailtmp6653 = tmpcur6650 + 1;

            tmpval5714 = tagtmp6652;
            tmpcur5715 = tailtmp6653;
            goto switch5728;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6650 = *(CursorTy *) tmpcur5715;
            CursorTy tmpaftercur6651 = tmpcur5715 + 8;
            TagTyPacked tagtmp6652 = *(TagTyPacked *) tmpcur6650;
            CursorTy tailtmp6653 = tmpcur6650 + 1;

            tmpval5714 = tagtmp6652;
            tmpcur5715 = tailtmp6653;
            goto switch5728;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5714");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListSym(CursorTy end_r1902,
                                                               CursorTy end_r1903,
                                                               CursorTy loc1901,
                                                               CursorTy arg1414)
{
    CursorTy loc1900 = (CursorTy) arg1414;

    if (loc1901 + 18 > end_r1903) {
        ChunkTy new_chunk168 = alloc_chunk(end_r1903);
        CursorTy chunk_start169 = new_chunk168.start_ptr;
        CursorTy chunk_end170 = new_chunk168.end_ptr;

        end_r1903 = chunk_end170;
        *(TagTyPacked *) loc1901 = 255;

        CursorTy redir = loc1901 + 1;

        *(CursorTy *) redir = chunk_start169;
        loc1901 = chunk_start169;
    }

    CursorTy loc2657 = loc1901 + 1;
    CursorTy loc2658 = loc2657 + 8;
    TagTyPacked tmpval5729 = *(TagTyPacked *) arg1414;
    CursorTy tmpcur5730 = arg1414 + 1;


  switch5749:
    ;
    switch (tmpval5729) {

      case 0:
        {
            CursorTy field_cur3912 = (CursorTy) tmpcur5730;
            CursorTy case2652 = (CursorTy) field_cur3912;
            SymTy tmpval5731 = *(SymTy *) case2652;
            CursorTy tmpcur5732 = case2652 + sizeof(SymTy);
            SymTy x1415 = (SymTy) tmpval5731;
            CursorTy end_x1415 = (CursorTy) tmpcur5732;
            CursorTy case2653 = (CursorTy) end_x1415;
            CursorTy x1416 = (CursorTy) case2653;
            CursorTy jump3294 = case2652 + 8;
            CursorCursorCursorCursorProd tmp_struct167 =
                                          _add_size_and_rel_offsets_ListSym(end_r1902, end_r1903, loc2658, x1416);
            CursorTy pvrtmp5733 = tmp_struct167.field0;
            CursorTy pvrtmp5734 = tmp_struct167.field1;
            CursorTy pvrtmp5735 = tmp_struct167.field2;
            CursorTy pvrtmp5736 = tmp_struct167.field3;
            CursorTy fltPrd4625 = (CursorTy) pvrtmp5735;
            CursorTy fltPrd4626 = (CursorTy) pvrtmp5736;
            CursorTy pvrtmp5738 = (CursorTy) fltPrd4626;
            CursorTy pvrtmp5737 = (CursorTy) fltPrd4625;
            CursorTy y1418 = (CursorTy) pvrtmp5737;
            CursorTy fltPrd4627 = (CursorTy) pvrtmp5735;
            CursorTy fltPrd4628 = (CursorTy) pvrtmp5736;
            CursorTy pvrtmp5740 = (CursorTy) fltPrd4628;
            CursorTy pvrtmp5739 = (CursorTy) fltPrd4627;
            CursorTy end_y1418 = (CursorTy) pvrtmp5740;
            CursorTy end_r1903_3431 = (CursorTy) pvrtmp5733;
            CursorTy endof3295 = (CursorTy) pvrtmp5734;

            *(TagTyPacked *) loc1901 = 0;

            CursorTy writetag3915 = loc1901 + 1;

            *(SymTy *) writetag3915 = x1415;

            CursorTy writecur3916 = writetag3915 + sizeof(SymTy);
            CursorTy writecur3917 = (CursorTy) end_y1418;
            CursorTy pvrtmp5742 = (CursorTy) writecur3917;
            CursorTy pvrtmp5741 = (CursorTy) loc1901;
            CursorTy taildc3296 = (CursorTy) pvrtmp5741;
            CursorTy end_taildc3296 = (CursorTy) pvrtmp5742;
            CursorTy pvrtmp5744 = (CursorTy) end_taildc3296;
            CursorTy pvrtmp5743 = (CursorTy) taildc3296;
            CursorTy fltPrd4629 = (CursorTy) pvrtmp5743;
            CursorTy fltPrd4630 = (CursorTy) pvrtmp5744;

            return (CursorCursorCursorCursorProd) {end_r1903_3431, endof3295,
                                                   fltPrd4629, fltPrd4630};
            break;
        }

      case 1:
        {
            CursorTy field_cur3919 = (CursorTy) tmpcur5730;
            CursorTy jump3297 = loc1900 + 1;

            *(TagTyPacked *) loc1901 = 1;

            CursorTy writetag3920 = loc1901 + 1;
            CursorTy pvrtmp5746 = (CursorTy) writetag3920;
            CursorTy pvrtmp5745 = (CursorTy) loc1901;
            CursorTy taildc3298 = (CursorTy) pvrtmp5745;
            CursorTy end_taildc3298 = (CursorTy) pvrtmp5746;
            CursorTy pvrtmp5748 = (CursorTy) end_taildc3298;
            CursorTy pvrtmp5747 = (CursorTy) taildc3298;
            CursorTy fltPrd4631 = (CursorTy) pvrtmp5747;
            CursorTy fltPrd4632 = (CursorTy) pvrtmp5748;

            return (CursorCursorCursorCursorProd) {end_r1903, jump3297,
                                                   fltPrd4631, fltPrd4632};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6654 = *(CursorTy *) tmpcur5730;
            CursorTy tmpaftercur6655 = tmpcur5730 + 8;
            TagTyPacked tagtmp6656 = *(TagTyPacked *) tmpcur6654;
            CursorTy tailtmp6657 = tmpcur6654 + 1;

            tmpval5729 = tagtmp6656;
            tmpcur5730 = tailtmp6657;
            goto switch5749;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6654 = *(CursorTy *) tmpcur5730;
            CursorTy tmpaftercur6655 = tmpcur5730 + 8;
            TagTyPacked tagtmp6656 = *(TagTyPacked *) tmpcur6654;
            CursorTy tailtmp6657 = tmpcur6654 + 1;

            tmpval5729 = tagtmp6656;
            tmpcur5730 = tailtmp6657;
            goto switch5749;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5729");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListExpr(CursorTy end_r1906,
                                                                CursorTy end_r1907,
                                                                CursorTy loc1905,
                                                                CursorTy arg1419)
{
    CursorTy loc1904 = (CursorTy) arg1419;

    if (loc1905 + 18 > end_r1907) {
        ChunkTy new_chunk173 = alloc_chunk(end_r1907);
        CursorTy chunk_start174 = new_chunk173.start_ptr;
        CursorTy chunk_end175 = new_chunk173.end_ptr;

        end_r1907 = chunk_end175;
        *(TagTyPacked *) loc1905 = 255;

        CursorTy redir = loc1905 + 1;

        *(CursorTy *) redir = chunk_start174;
        loc1905 = chunk_start174;
    }

    TagTyPacked tmpval5750 = *(TagTyPacked *) arg1419;
    CursorTy tmpcur5751 = arg1419 + 1;


  switch5776:
    ;
    switch (tmpval5750) {

      case 0:
        {
            CursorTy field_cur3922 = (CursorTy) tmpcur5751;
            CursorTy case2665 = (CursorTy) field_cur3922;
            CursorTy x1420 = (CursorTy) case2665;
            CursorTy loc2673 = loc1905 + 1;
            CursorCursorCursorCursorProd tmp_struct171 =
                                          _add_size_and_rel_offsets_Expr(end_r1906, end_r1907, loc2673, x1420);
            CursorTy pvrtmp5752 = tmp_struct171.field0;
            CursorTy pvrtmp5753 = tmp_struct171.field1;
            CursorTy pvrtmp5754 = tmp_struct171.field2;
            CursorTy pvrtmp5755 = tmp_struct171.field3;
            CursorTy fltPrd4633 = (CursorTy) pvrtmp5754;
            CursorTy fltPrd4634 = (CursorTy) pvrtmp5755;
            CursorTy pvrtmp5757 = (CursorTy) fltPrd4634;
            CursorTy pvrtmp5756 = (CursorTy) fltPrd4633;
            CursorTy y1422 = (CursorTy) pvrtmp5756;
            CursorTy fltPrd4635 = (CursorTy) pvrtmp5754;
            CursorTy fltPrd4636 = (CursorTy) pvrtmp5755;
            CursorTy pvrtmp5759 = (CursorTy) fltPrd4636;
            CursorTy pvrtmp5758 = (CursorTy) fltPrd4635;
            CursorTy end_y1422 = (CursorTy) pvrtmp5759;
            CursorTy end_r1907_3432 = (CursorTy) pvrtmp5752;
            CursorTy endof3299 = (CursorTy) pvrtmp5753;
            CursorTy case2666 = (CursorTy) endof3299;
            CursorTy x1421 = (CursorTy) case2666;
            CursorTy loc2674 = (CursorTy) end_y1422;
            CursorCursorCursorCursorProd tmp_struct172 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1906, end_r1907_3432, loc2674, x1421);
            CursorTy pvrtmp5760 = tmp_struct172.field0;
            CursorTy pvrtmp5761 = tmp_struct172.field1;
            CursorTy pvrtmp5762 = tmp_struct172.field2;
            CursorTy pvrtmp5763 = tmp_struct172.field3;
            CursorTy fltPrd4637 = (CursorTy) pvrtmp5762;
            CursorTy fltPrd4638 = (CursorTy) pvrtmp5763;
            CursorTy pvrtmp5765 = (CursorTy) fltPrd4638;
            CursorTy pvrtmp5764 = (CursorTy) fltPrd4637;
            CursorTy y1423 = (CursorTy) pvrtmp5764;
            CursorTy fltPrd4639 = (CursorTy) pvrtmp5762;
            CursorTy fltPrd4640 = (CursorTy) pvrtmp5763;
            CursorTy pvrtmp5767 = (CursorTy) fltPrd4640;
            CursorTy pvrtmp5766 = (CursorTy) fltPrd4639;
            CursorTy end_y1423 = (CursorTy) pvrtmp5767;
            CursorTy end_r1907_3432_3433 = (CursorTy) pvrtmp5760;
            CursorTy endof3300 = (CursorTy) pvrtmp5761;

            *(TagTyPacked *) loc1905 = 0;

            CursorTy writetag3925 = loc1905 + 1;
            CursorTy writecur3926 = (CursorTy) end_y1422;
            CursorTy writecur3927 = (CursorTy) end_y1423;
            CursorTy pvrtmp5769 = (CursorTy) writecur3927;
            CursorTy pvrtmp5768 = (CursorTy) loc1905;
            CursorTy taildc3301 = (CursorTy) pvrtmp5768;
            CursorTy end_taildc3301 = (CursorTy) pvrtmp5769;
            CursorTy pvrtmp5771 = (CursorTy) end_taildc3301;
            CursorTy pvrtmp5770 = (CursorTy) taildc3301;
            CursorTy fltPrd4641 = (CursorTy) pvrtmp5770;
            CursorTy fltPrd4642 = (CursorTy) pvrtmp5771;

            return (CursorCursorCursorCursorProd) {end_r1907_3432_3433,
                                                   endof3300, fltPrd4641,
                                                   fltPrd4642};
            break;
        }

      case 1:
        {
            CursorTy field_cur3929 = (CursorTy) tmpcur5751;
            CursorTy jump3302 = loc1904 + 1;

            *(TagTyPacked *) loc1905 = 1;

            CursorTy writetag3930 = loc1905 + 1;
            CursorTy pvrtmp5773 = (CursorTy) writetag3930;
            CursorTy pvrtmp5772 = (CursorTy) loc1905;
            CursorTy taildc3303 = (CursorTy) pvrtmp5772;
            CursorTy end_taildc3303 = (CursorTy) pvrtmp5773;
            CursorTy pvrtmp5775 = (CursorTy) end_taildc3303;
            CursorTy pvrtmp5774 = (CursorTy) taildc3303;
            CursorTy fltPrd4643 = (CursorTy) pvrtmp5774;
            CursorTy fltPrd4644 = (CursorTy) pvrtmp5775;

            return (CursorCursorCursorCursorProd) {end_r1907, jump3302,
                                                   fltPrd4643, fltPrd4644};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6658 = *(CursorTy *) tmpcur5751;
            CursorTy tmpaftercur6659 = tmpcur5751 + 8;
            TagTyPacked tagtmp6660 = *(TagTyPacked *) tmpcur6658;
            CursorTy tailtmp6661 = tmpcur6658 + 1;

            tmpval5750 = tagtmp6660;
            tmpcur5751 = tailtmp6661;
            goto switch5776;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6658 = *(CursorTy *) tmpcur5751;
            CursorTy tmpaftercur6659 = tmpcur5751 + 8;
            TagTyPacked tagtmp6660 = *(TagTyPacked *) tmpcur6658;
            CursorTy tailtmp6661 = tmpcur6658 + 1;

            tmpval5750 = tagtmp6660;
            tmpcur5751 = tailtmp6661;
            goto switch5776;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5750");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListToplvl(CursorTy end_r1910,
                                                                  CursorTy end_r1911,
                                                                  CursorTy loc1909,
                                                                  CursorTy arg1424)
{
    CursorTy loc1908 = (CursorTy) arg1424;

    if (loc1909 + 26 > end_r1911) {
        ChunkTy new_chunk178 = alloc_chunk(end_r1911);
        CursorTy chunk_start179 = new_chunk178.start_ptr;
        CursorTy chunk_end180 = new_chunk178.end_ptr;

        end_r1911 = chunk_end180;
        *(TagTyPacked *) loc1909 = 255;

        CursorTy redir = loc1909 + 1;

        *(CursorTy *) redir = chunk_start179;
        loc1909 = chunk_start179;
    }

    CursorTy loc2688 = loc1909 + 1;
    CursorTy loc2689 = loc2688 + 8;
    CursorTy loc2690 = loc2689 + 8;
    TagTyPacked tmpval5777 = *(TagTyPacked *) arg1424;
    CursorTy tmpcur5778 = arg1424 + 1;


  switch5803:
    ;
    switch (tmpval5777) {

      case 0:
        {
            CursorTy field_cur3932 = (CursorTy) tmpcur5778;
            CursorTy case2680 = (CursorTy) field_cur3932;
            CursorTy x1425 = (CursorTy) case2680;
            CursorCursorCursorCursorProd tmp_struct176 =
                                          _add_size_and_rel_offsets_Toplvl(end_r1910, end_r1911, loc2690, x1425);
            CursorTy pvrtmp5779 = tmp_struct176.field0;
            CursorTy pvrtmp5780 = tmp_struct176.field1;
            CursorTy pvrtmp5781 = tmp_struct176.field2;
            CursorTy pvrtmp5782 = tmp_struct176.field3;
            CursorTy fltPrd4645 = (CursorTy) pvrtmp5781;
            CursorTy fltPrd4646 = (CursorTy) pvrtmp5782;
            CursorTy pvrtmp5784 = (CursorTy) fltPrd4646;
            CursorTy pvrtmp5783 = (CursorTy) fltPrd4645;
            CursorTy y1427 = (CursorTy) pvrtmp5783;
            CursorTy fltPrd4647 = (CursorTy) pvrtmp5781;
            CursorTy fltPrd4648 = (CursorTy) pvrtmp5782;
            CursorTy pvrtmp5786 = (CursorTy) fltPrd4648;
            CursorTy pvrtmp5785 = (CursorTy) fltPrd4647;
            CursorTy end_y1427 = (CursorTy) pvrtmp5786;
            CursorTy end_r1911_3434 = (CursorTy) pvrtmp5779;
            CursorTy endof3304 = (CursorTy) pvrtmp5780;
            CursorTy case2681 = (CursorTy) endof3304;
            CursorTy x1426 = (CursorTy) case2681;
            CursorTy loc2691 = (CursorTy) end_y1427;
            CursorCursorCursorCursorProd tmp_struct177 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r1910, end_r1911_3434, loc2691, x1426);
            CursorTy pvrtmp5787 = tmp_struct177.field0;
            CursorTy pvrtmp5788 = tmp_struct177.field1;
            CursorTy pvrtmp5789 = tmp_struct177.field2;
            CursorTy pvrtmp5790 = tmp_struct177.field3;
            CursorTy fltPrd4649 = (CursorTy) pvrtmp5789;
            CursorTy fltPrd4650 = (CursorTy) pvrtmp5790;
            CursorTy pvrtmp5792 = (CursorTy) fltPrd4650;
            CursorTy pvrtmp5791 = (CursorTy) fltPrd4649;
            CursorTy y1428 = (CursorTy) pvrtmp5791;
            CursorTy fltPrd4651 = (CursorTy) pvrtmp5789;
            CursorTy fltPrd4652 = (CursorTy) pvrtmp5790;
            CursorTy pvrtmp5794 = (CursorTy) fltPrd4652;
            CursorTy pvrtmp5793 = (CursorTy) fltPrd4651;
            CursorTy end_y1428 = (CursorTy) pvrtmp5794;
            CursorTy end_r1911_3434_3435 = (CursorTy) pvrtmp5787;
            CursorTy endof3305 = (CursorTy) pvrtmp5788;
            IntTy sizeof_y1427_1429 = end_y1427 - y1427;
            IntTy sizeof_y1428_1430 = end_y1428 - y1428;
            IntTy fltPrm1773 = sizeof_y1427_1429 + 0;
            IntTy offset_1431 = 0 + fltPrm1773;
            IntTy fltPrm1774 = sizeof_y1427_1429 + sizeof_y1428_1430;
            IntTy size_dcon1432 = 9 + fltPrm1774;

            *(TagTyPacked *) loc1909 = 153;

            CursorTy writetag3935 = loc1909 + 1;

            *(IntTy *) writetag3935 = size_dcon1432;

            CursorTy writecur3936 = writetag3935 + sizeof(IntTy);

            *(IntTy *) writecur3936 = offset_1431;

            CursorTy writecur3937 = writecur3936 + sizeof(IntTy);
            CursorTy writecur3938 = (CursorTy) end_y1427;
            CursorTy writecur3939 = (CursorTy) end_y1428;
            CursorTy pvrtmp5796 = (CursorTy) writecur3939;
            CursorTy pvrtmp5795 = (CursorTy) loc1909;
            CursorTy taildc3306 = (CursorTy) pvrtmp5795;
            CursorTy end_taildc3306 = (CursorTy) pvrtmp5796;
            CursorTy pvrtmp5798 = (CursorTy) end_taildc3306;
            CursorTy pvrtmp5797 = (CursorTy) taildc3306;
            CursorTy fltPrd4653 = (CursorTy) pvrtmp5797;
            CursorTy fltPrd4654 = (CursorTy) pvrtmp5798;

            return (CursorCursorCursorCursorProd) {end_r1911_3434_3435,
                                                   endof3305, fltPrd4653,
                                                   fltPrd4654};
            break;
        }

      case 1:
        {
            CursorTy field_cur3941 = (CursorTy) tmpcur5778;
            CursorTy jump3307 = loc1908 + 1;

            *(TagTyPacked *) loc1909 = 1;

            CursorTy writetag3942 = loc1909 + 1;
            CursorTy pvrtmp5800 = (CursorTy) writetag3942;
            CursorTy pvrtmp5799 = (CursorTy) loc1909;
            CursorTy taildc3308 = (CursorTy) pvrtmp5799;
            CursorTy end_taildc3308 = (CursorTy) pvrtmp5800;
            CursorTy pvrtmp5802 = (CursorTy) end_taildc3308;
            CursorTy pvrtmp5801 = (CursorTy) taildc3308;
            CursorTy fltPrd4655 = (CursorTy) pvrtmp5801;
            CursorTy fltPrd4656 = (CursorTy) pvrtmp5802;

            return (CursorCursorCursorCursorProd) {end_r1911, jump3307,
                                                   fltPrd4655, fltPrd4656};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6662 = *(CursorTy *) tmpcur5778;
            CursorTy tmpaftercur6663 = tmpcur5778 + 8;
            TagTyPacked tagtmp6664 = *(TagTyPacked *) tmpcur6662;
            CursorTy tailtmp6665 = tmpcur6662 + 1;

            tmpval5777 = tagtmp6664;
            tmpcur5778 = tailtmp6665;
            goto switch5803;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6662 = *(CursorTy *) tmpcur5778;
            CursorTy tmpaftercur6663 = tmpcur5778 + 8;
            TagTyPacked tagtmp6664 = *(TagTyPacked *) tmpcur6662;
            CursorTy tailtmp6665 = tmpcur6662 + 1;

            tmpval5777 = tagtmp6664;
            tmpcur5778 = tailtmp6665;
            goto switch5803;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5777");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Formals(CursorTy end_r1914,
                                                               CursorTy end_r1915,
                                                               CursorTy loc1913,
                                                               CursorTy arg1433)
{
    CursorTy loc1912 = (CursorTy) arg1433;

    if (loc1913 + 18 > end_r1915) {
        ChunkTy new_chunk183 = alloc_chunk(end_r1915);
        CursorTy chunk_start184 = new_chunk183.start_ptr;
        CursorTy chunk_end185 = new_chunk183.end_ptr;

        end_r1915 = chunk_end185;
        *(TagTyPacked *) loc1913 = 255;

        CursorTy redir = loc1913 + 1;

        *(CursorTy *) redir = chunk_start184;
        loc1913 = chunk_start184;
    }

    TagTyPacked tmpval5804 = *(TagTyPacked *) arg1433;
    CursorTy tmpcur5805 = arg1433 + 1;


  switch5838:
    ;
    switch (tmpval5804) {

      case 0:
        {
            CursorTy field_cur3944 = (CursorTy) tmpcur5805;
            CursorTy case2701 = (CursorTy) field_cur3944;
            CursorTy x1434 = (CursorTy) case2701;
            CursorTy loc2705 = loc1913 + 1;
            CursorCursorCursorCursorProd tmp_struct181 =
                                          _add_size_and_rel_offsets_ListSym(end_r1914, end_r1915, loc2705, x1434);
            CursorTy pvrtmp5806 = tmp_struct181.field0;
            CursorTy pvrtmp5807 = tmp_struct181.field1;
            CursorTy pvrtmp5808 = tmp_struct181.field2;
            CursorTy pvrtmp5809 = tmp_struct181.field3;
            CursorTy fltPrd4657 = (CursorTy) pvrtmp5808;
            CursorTy fltPrd4658 = (CursorTy) pvrtmp5809;
            CursorTy pvrtmp5811 = (CursorTy) fltPrd4658;
            CursorTy pvrtmp5810 = (CursorTy) fltPrd4657;
            CursorTy y1435 = (CursorTy) pvrtmp5810;
            CursorTy fltPrd4659 = (CursorTy) pvrtmp5808;
            CursorTy fltPrd4660 = (CursorTy) pvrtmp5809;
            CursorTy pvrtmp5813 = (CursorTy) fltPrd4660;
            CursorTy pvrtmp5812 = (CursorTy) fltPrd4659;
            CursorTy end_y1435 = (CursorTy) pvrtmp5813;
            CursorTy end_r1915_3436 = (CursorTy) pvrtmp5806;
            CursorTy endof3309 = (CursorTy) pvrtmp5807;

            *(TagTyPacked *) loc1913 = 0;

            CursorTy writetag3946 = loc1913 + 1;
            CursorTy writecur3947 = (CursorTy) end_y1435;
            CursorTy pvrtmp5815 = (CursorTy) writecur3947;
            CursorTy pvrtmp5814 = (CursorTy) loc1913;
            CursorTy taildc3310 = (CursorTy) pvrtmp5814;
            CursorTy end_taildc3310 = (CursorTy) pvrtmp5815;
            CursorTy pvrtmp5817 = (CursorTy) end_taildc3310;
            CursorTy pvrtmp5816 = (CursorTy) taildc3310;
            CursorTy fltPrd4661 = (CursorTy) pvrtmp5816;
            CursorTy fltPrd4662 = (CursorTy) pvrtmp5817;

            return (CursorCursorCursorCursorProd) {end_r1915_3436, endof3309,
                                                   fltPrd4661, fltPrd4662};
            break;
        }

      case 1:
        {
            CursorTy field_cur3949 = (CursorTy) tmpcur5805;
            CursorTy case2707 = (CursorTy) field_cur3949;
            CursorTy x1436 = (CursorTy) case2707;
            CursorTy loc2712 = loc1913 + 1;
            CursorCursorCursorCursorProd tmp_struct182 =
                                          _add_size_and_rel_offsets_ListSym(end_r1914, end_r1915, loc2712, x1436);
            CursorTy pvrtmp5818 = tmp_struct182.field0;
            CursorTy pvrtmp5819 = tmp_struct182.field1;
            CursorTy pvrtmp5820 = tmp_struct182.field2;
            CursorTy pvrtmp5821 = tmp_struct182.field3;
            CursorTy fltPrd4663 = (CursorTy) pvrtmp5820;
            CursorTy fltPrd4664 = (CursorTy) pvrtmp5821;
            CursorTy pvrtmp5823 = (CursorTy) fltPrd4664;
            CursorTy pvrtmp5822 = (CursorTy) fltPrd4663;
            CursorTy y1438 = (CursorTy) pvrtmp5822;
            CursorTy fltPrd4665 = (CursorTy) pvrtmp5820;
            CursorTy fltPrd4666 = (CursorTy) pvrtmp5821;
            CursorTy pvrtmp5825 = (CursorTy) fltPrd4666;
            CursorTy pvrtmp5824 = (CursorTy) fltPrd4665;
            CursorTy end_y1438 = (CursorTy) pvrtmp5825;
            CursorTy end_r1915_3437 = (CursorTy) pvrtmp5818;
            CursorTy endof3312 = (CursorTy) pvrtmp5819;
            CursorTy case2708 = (CursorTy) endof3312;
            CursorTy jump3311 = case2708 + 8;
            SymTy tmpval5826 = *(SymTy *) case2708;
            CursorTy tmpcur5827 = case2708 + sizeof(SymTy);
            SymTy x1437 = (SymTy) tmpval5826;
            CursorTy end_x1437 = (CursorTy) tmpcur5827;

            *(TagTyPacked *) loc1913 = 1;

            CursorTy writetag3952 = loc1913 + 1;
            CursorTy writecur3953 = (CursorTy) end_y1438;

            *(SymTy *) writecur3953 = x1437;

            CursorTy writecur3954 = writecur3953 + sizeof(SymTy);
            CursorTy pvrtmp5829 = (CursorTy) writecur3954;
            CursorTy pvrtmp5828 = (CursorTy) loc1913;
            CursorTy taildc3313 = (CursorTy) pvrtmp5828;
            CursorTy end_taildc3313 = (CursorTy) pvrtmp5829;
            CursorTy pvrtmp5831 = (CursorTy) end_taildc3313;
            CursorTy pvrtmp5830 = (CursorTy) taildc3313;
            CursorTy fltPrd4667 = (CursorTy) pvrtmp5830;
            CursorTy fltPrd4668 = (CursorTy) pvrtmp5831;

            return (CursorCursorCursorCursorProd) {end_r1915_3437, jump3311,
                                                   fltPrd4667, fltPrd4668};
            break;
        }

      case 2:
        {
            CursorTy field_cur3956 = (CursorTy) tmpcur5805;
            CursorTy case2717 = (CursorTy) field_cur3956;
            SymTy tmpval5832 = *(SymTy *) case2717;
            CursorTy tmpcur5833 = case2717 + sizeof(SymTy);
            SymTy x1440 = (SymTy) tmpval5832;
            CursorTy end_x1440 = (CursorTy) tmpcur5833;
            CursorTy jump3314 = case2717 + 8;

            *(TagTyPacked *) loc1913 = 2;

            CursorTy writetag3958 = loc1913 + 1;

            *(SymTy *) writetag3958 = x1440;

            CursorTy writecur3959 = writetag3958 + sizeof(SymTy);
            CursorTy pvrtmp5835 = (CursorTy) writecur3959;
            CursorTy pvrtmp5834 = (CursorTy) loc1913;
            CursorTy taildc3315 = (CursorTy) pvrtmp5834;
            CursorTy end_taildc3315 = (CursorTy) pvrtmp5835;
            CursorTy pvrtmp5837 = (CursorTy) end_taildc3315;
            CursorTy pvrtmp5836 = (CursorTy) taildc3315;
            CursorTy fltPrd4669 = (CursorTy) pvrtmp5836;
            CursorTy fltPrd4670 = (CursorTy) pvrtmp5837;

            return (CursorCursorCursorCursorProd) {end_r1915, jump3314,
                                                   fltPrd4669, fltPrd4670};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6666 = *(CursorTy *) tmpcur5805;
            CursorTy tmpaftercur6667 = tmpcur5805 + 8;
            TagTyPacked tagtmp6668 = *(TagTyPacked *) tmpcur6666;
            CursorTy tailtmp6669 = tmpcur6666 + 1;

            tmpval5804 = tagtmp6668;
            tmpcur5805 = tailtmp6669;
            goto switch5838;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6666 = *(CursorTy *) tmpcur5805;
            CursorTy tmpaftercur6667 = tmpcur5805 + 8;
            TagTyPacked tagtmp6668 = *(TagTyPacked *) tmpcur6666;
            CursorTy tailtmp6669 = tmpcur6666 + 1;

            tmpval5804 = tagtmp6668;
            tmpcur5805 = tailtmp6669;
            goto switch5838;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5804");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Datum(CursorTy end_r1918,
                                                             CursorTy end_r1919,
                                                             CursorTy loc1917,
                                                             CursorTy arg1442)
{
    CursorTy loc1916 = (CursorTy) arg1442;

    if (loc1917 + 18 > end_r1919) {
        ChunkTy new_chunk186 = alloc_chunk(end_r1919);
        CursorTy chunk_start187 = new_chunk186.start_ptr;
        CursorTy chunk_end188 = new_chunk186.end_ptr;

        end_r1919 = chunk_end188;
        *(TagTyPacked *) loc1917 = 255;

        CursorTy redir = loc1917 + 1;

        *(CursorTy *) redir = chunk_start187;
        loc1917 = chunk_start187;
    }

    TagTyPacked tmpval5839 = *(TagTyPacked *) arg1442;
    CursorTy tmpcur5840 = arg1442 + 1;


  switch5847:
    ;
    switch (tmpval5839) {

      case 0:
        {
            CursorTy field_cur3961 = (CursorTy) tmpcur5840;
            CursorTy case2723 = (CursorTy) field_cur3961;
            IntTy tmpval5841 = *(IntTy *) case2723;
            CursorTy tmpcur5842 = case2723 + sizeof(IntTy);
            IntTy x1443 = (IntTy) tmpval5841;
            CursorTy end_x1443 = (CursorTy) tmpcur5842;
            CursorTy jump3316 = case2723 + 8;

            *(TagTyPacked *) loc1917 = 0;

            CursorTy writetag3963 = loc1917 + 1;

            *(IntTy *) writetag3963 = x1443;

            CursorTy writecur3964 = writetag3963 + sizeof(IntTy);
            CursorTy pvrtmp5844 = (CursorTy) writecur3964;
            CursorTy pvrtmp5843 = (CursorTy) loc1917;
            CursorTy taildc3317 = (CursorTy) pvrtmp5843;
            CursorTy end_taildc3317 = (CursorTy) pvrtmp5844;
            CursorTy pvrtmp5846 = (CursorTy) end_taildc3317;
            CursorTy pvrtmp5845 = (CursorTy) taildc3317;
            CursorTy fltPrd4671 = (CursorTy) pvrtmp5845;
            CursorTy fltPrd4672 = (CursorTy) pvrtmp5846;

            return (CursorCursorCursorCursorProd) {end_r1919, jump3316,
                                                   fltPrd4671, fltPrd4672};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6670 = *(CursorTy *) tmpcur5840;
            CursorTy tmpaftercur6671 = tmpcur5840 + 8;
            TagTyPacked tagtmp6672 = *(TagTyPacked *) tmpcur6670;
            CursorTy tailtmp6673 = tmpcur6670 + 1;

            tmpval5839 = tagtmp6672;
            tmpcur5840 = tailtmp6673;
            goto switch5847;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6670 = *(CursorTy *) tmpcur5840;
            CursorTy tmpaftercur6671 = tmpcur5840 + 8;
            TagTyPacked tagtmp6672 = *(TagTyPacked *) tmpcur6670;
            CursorTy tailtmp6673 = tmpcur6670 + 1;

            tmpval5839 = tagtmp6672;
            tmpcur5840 = tailtmp6673;
            goto switch5847;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5839");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LAMBDACASE(CursorTy end_r1922,
                                                                  CursorTy end_r1923,
                                                                  CursorTy loc1921,
                                                                  CursorTy arg1445)
{
    CursorTy loc1920 = (CursorTy) arg1445;

    if (loc1921 + 18 > end_r1923) {
        ChunkTy new_chunk192 = alloc_chunk(end_r1923);
        CursorTy chunk_start193 = new_chunk192.start_ptr;
        CursorTy chunk_end194 = new_chunk192.end_ptr;

        end_r1923 = chunk_end194;
        *(TagTyPacked *) loc1921 = 255;

        CursorTy redir = loc1921 + 1;

        *(CursorTy *) redir = chunk_start193;
        loc1921 = chunk_start193;
    }

    TagTyPacked tmpval5848 = *(TagTyPacked *) arg1445;
    CursorTy tmpcur5849 = arg1445 + 1;


  switch5882:
    ;
    switch (tmpval5848) {

      case 0:
        {
            CursorTy field_cur3966 = (CursorTy) tmpcur5849;
            CursorTy case2729 = (CursorTy) field_cur3966;
            CursorTy x1446 = (CursorTy) case2729;
            CursorTy loc2741 = loc1921 + 1;
            CursorCursorCursorCursorProd tmp_struct189 =
                                          _add_size_and_rel_offsets_Formals(end_r1922, end_r1923, loc2741, x1446);
            CursorTy pvrtmp5850 = tmp_struct189.field0;
            CursorTy pvrtmp5851 = tmp_struct189.field1;
            CursorTy pvrtmp5852 = tmp_struct189.field2;
            CursorTy pvrtmp5853 = tmp_struct189.field3;
            CursorTy fltPrd4673 = (CursorTy) pvrtmp5852;
            CursorTy fltPrd4674 = (CursorTy) pvrtmp5853;
            CursorTy pvrtmp5855 = (CursorTy) fltPrd4674;
            CursorTy pvrtmp5854 = (CursorTy) fltPrd4673;
            CursorTy y1449 = (CursorTy) pvrtmp5854;
            CursorTy fltPrd4675 = (CursorTy) pvrtmp5852;
            CursorTy fltPrd4676 = (CursorTy) pvrtmp5853;
            CursorTy pvrtmp5857 = (CursorTy) fltPrd4676;
            CursorTy pvrtmp5856 = (CursorTy) fltPrd4675;
            CursorTy end_y1449 = (CursorTy) pvrtmp5857;
            CursorTy end_r1923_3438 = (CursorTy) pvrtmp5850;
            CursorTy endof3318 = (CursorTy) pvrtmp5851;
            CursorTy case2730 = (CursorTy) endof3318;
            CursorTy x1447 = (CursorTy) case2730;
            CursorTy loc2742 = (CursorTy) end_y1449;
            CursorCursorCursorCursorProd tmp_struct190 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1922, end_r1923_3438, loc2742, x1447);
            CursorTy pvrtmp5858 = tmp_struct190.field0;
            CursorTy pvrtmp5859 = tmp_struct190.field1;
            CursorTy pvrtmp5860 = tmp_struct190.field2;
            CursorTy pvrtmp5861 = tmp_struct190.field3;
            CursorTy fltPrd4677 = (CursorTy) pvrtmp5860;
            CursorTy fltPrd4678 = (CursorTy) pvrtmp5861;
            CursorTy pvrtmp5863 = (CursorTy) fltPrd4678;
            CursorTy pvrtmp5862 = (CursorTy) fltPrd4677;
            CursorTy y1450 = (CursorTy) pvrtmp5862;
            CursorTy fltPrd4679 = (CursorTy) pvrtmp5860;
            CursorTy fltPrd4680 = (CursorTy) pvrtmp5861;
            CursorTy pvrtmp5865 = (CursorTy) fltPrd4680;
            CursorTy pvrtmp5864 = (CursorTy) fltPrd4679;
            CursorTy end_y1450 = (CursorTy) pvrtmp5865;
            CursorTy end_r1923_3438_3439 = (CursorTy) pvrtmp5858;
            CursorTy endof3319 = (CursorTy) pvrtmp5859;
            CursorTy case2731 = (CursorTy) endof3319;
            CursorTy x1448 = (CursorTy) case2731;
            CursorTy loc2743 = (CursorTy) end_y1450;
            CursorCursorCursorCursorProd tmp_struct191 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r1922, end_r1923_3438_3439, loc2743, x1448);
            CursorTy pvrtmp5866 = tmp_struct191.field0;
            CursorTy pvrtmp5867 = tmp_struct191.field1;
            CursorTy pvrtmp5868 = tmp_struct191.field2;
            CursorTy pvrtmp5869 = tmp_struct191.field3;
            CursorTy fltPrd4681 = (CursorTy) pvrtmp5868;
            CursorTy fltPrd4682 = (CursorTy) pvrtmp5869;
            CursorTy pvrtmp5871 = (CursorTy) fltPrd4682;
            CursorTy pvrtmp5870 = (CursorTy) fltPrd4681;
            CursorTy y1451 = (CursorTy) pvrtmp5870;
            CursorTy fltPrd4683 = (CursorTy) pvrtmp5868;
            CursorTy fltPrd4684 = (CursorTy) pvrtmp5869;
            CursorTy pvrtmp5873 = (CursorTy) fltPrd4684;
            CursorTy pvrtmp5872 = (CursorTy) fltPrd4683;
            CursorTy end_y1451 = (CursorTy) pvrtmp5873;
            CursorTy end_r1923_3438_3439_3440 = (CursorTy) pvrtmp5866;
            CursorTy endof3320 = (CursorTy) pvrtmp5867;

            *(TagTyPacked *) loc1921 = 0;

            CursorTy writetag3970 = loc1921 + 1;
            CursorTy writecur3971 = (CursorTy) end_y1449;
            CursorTy writecur3972 = (CursorTy) end_y1450;
            CursorTy writecur3973 = (CursorTy) end_y1451;
            CursorTy pvrtmp5875 = (CursorTy) writecur3973;
            CursorTy pvrtmp5874 = (CursorTy) loc1921;
            CursorTy taildc3321 = (CursorTy) pvrtmp5874;
            CursorTy end_taildc3321 = (CursorTy) pvrtmp5875;
            CursorTy pvrtmp5877 = (CursorTy) end_taildc3321;
            CursorTy pvrtmp5876 = (CursorTy) taildc3321;
            CursorTy fltPrd4685 = (CursorTy) pvrtmp5876;
            CursorTy fltPrd4686 = (CursorTy) pvrtmp5877;

            return (CursorCursorCursorCursorProd) {end_r1923_3438_3439_3440,
                                                   endof3320, fltPrd4685,
                                                   fltPrd4686};
            break;
        }

      case 1:
        {
            CursorTy field_cur3975 = (CursorTy) tmpcur5849;
            CursorTy jump3322 = loc1920 + 1;

            *(TagTyPacked *) loc1921 = 1;

            CursorTy writetag3976 = loc1921 + 1;
            CursorTy pvrtmp5879 = (CursorTy) writetag3976;
            CursorTy pvrtmp5878 = (CursorTy) loc1921;
            CursorTy taildc3323 = (CursorTy) pvrtmp5878;
            CursorTy end_taildc3323 = (CursorTy) pvrtmp5879;
            CursorTy pvrtmp5881 = (CursorTy) end_taildc3323;
            CursorTy pvrtmp5880 = (CursorTy) taildc3323;
            CursorTy fltPrd4687 = (CursorTy) pvrtmp5880;
            CursorTy fltPrd4688 = (CursorTy) pvrtmp5881;

            return (CursorCursorCursorCursorProd) {end_r1923, jump3322,
                                                   fltPrd4687, fltPrd4688};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6674 = *(CursorTy *) tmpcur5849;
            CursorTy tmpaftercur6675 = tmpcur5849 + 8;
            TagTyPacked tagtmp6676 = *(TagTyPacked *) tmpcur6674;
            CursorTy tailtmp6677 = tmpcur6674 + 1;

            tmpval5848 = tagtmp6676;
            tmpcur5849 = tailtmp6677;
            goto switch5882;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6674 = *(CursorTy *) tmpcur5849;
            CursorTy tmpaftercur6675 = tmpcur5849 + 8;
            TagTyPacked tagtmp6676 = *(TagTyPacked *) tmpcur6674;
            CursorTy tailtmp6677 = tmpcur6674 + 1;

            tmpval5848 = tagtmp6676;
            tmpcur5849 = tailtmp6677;
            goto switch5882;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5848");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LVBIND(CursorTy end_r1926,
                                                              CursorTy end_r1927,
                                                              CursorTy loc1925,
                                                              CursorTy arg1452)
{
    CursorTy loc1924 = (CursorTy) arg1452;

    if (loc1925 + 18 > end_r1927) {
        ChunkTy new_chunk198 = alloc_chunk(end_r1927);
        CursorTy chunk_start199 = new_chunk198.start_ptr;
        CursorTy chunk_end200 = new_chunk198.end_ptr;

        end_r1927 = chunk_end200;
        *(TagTyPacked *) loc1925 = 255;

        CursorTy redir = loc1925 + 1;

        *(CursorTy *) redir = chunk_start199;
        loc1925 = chunk_start199;
    }

    TagTyPacked tmpval5883 = *(TagTyPacked *) arg1452;
    CursorTy tmpcur5884 = arg1452 + 1;


  switch5917:
    ;
    switch (tmpval5883) {

      case 0:
        {
            CursorTy field_cur3978 = (CursorTy) tmpcur5884;
            CursorTy case2750 = (CursorTy) field_cur3978;
            CursorTy x1453 = (CursorTy) case2750;
            CursorTy loc2762 = loc1925 + 1;
            CursorCursorCursorCursorProd tmp_struct195 =
                                          _add_size_and_rel_offsets_ListSym(end_r1926, end_r1927, loc2762, x1453);
            CursorTy pvrtmp5885 = tmp_struct195.field0;
            CursorTy pvrtmp5886 = tmp_struct195.field1;
            CursorTy pvrtmp5887 = tmp_struct195.field2;
            CursorTy pvrtmp5888 = tmp_struct195.field3;
            CursorTy fltPrd4689 = (CursorTy) pvrtmp5887;
            CursorTy fltPrd4690 = (CursorTy) pvrtmp5888;
            CursorTy pvrtmp5890 = (CursorTy) fltPrd4690;
            CursorTy pvrtmp5889 = (CursorTy) fltPrd4689;
            CursorTy y1456 = (CursorTy) pvrtmp5889;
            CursorTy fltPrd4691 = (CursorTy) pvrtmp5887;
            CursorTy fltPrd4692 = (CursorTy) pvrtmp5888;
            CursorTy pvrtmp5892 = (CursorTy) fltPrd4692;
            CursorTy pvrtmp5891 = (CursorTy) fltPrd4691;
            CursorTy end_y1456 = (CursorTy) pvrtmp5892;
            CursorTy end_r1927_3441 = (CursorTy) pvrtmp5885;
            CursorTy endof3324 = (CursorTy) pvrtmp5886;
            CursorTy case2751 = (CursorTy) endof3324;
            CursorTy x1454 = (CursorTy) case2751;
            CursorTy loc2763 = (CursorTy) end_y1456;
            CursorCursorCursorCursorProd tmp_struct196 =
                                          _add_size_and_rel_offsets_Expr(end_r1926, end_r1927_3441, loc2763, x1454);
            CursorTy pvrtmp5893 = tmp_struct196.field0;
            CursorTy pvrtmp5894 = tmp_struct196.field1;
            CursorTy pvrtmp5895 = tmp_struct196.field2;
            CursorTy pvrtmp5896 = tmp_struct196.field3;
            CursorTy fltPrd4693 = (CursorTy) pvrtmp5895;
            CursorTy fltPrd4694 = (CursorTy) pvrtmp5896;
            CursorTy pvrtmp5898 = (CursorTy) fltPrd4694;
            CursorTy pvrtmp5897 = (CursorTy) fltPrd4693;
            CursorTy y1457 = (CursorTy) pvrtmp5897;
            CursorTy fltPrd4695 = (CursorTy) pvrtmp5895;
            CursorTy fltPrd4696 = (CursorTy) pvrtmp5896;
            CursorTy pvrtmp5900 = (CursorTy) fltPrd4696;
            CursorTy pvrtmp5899 = (CursorTy) fltPrd4695;
            CursorTy end_y1457 = (CursorTy) pvrtmp5900;
            CursorTy end_r1927_3441_3442 = (CursorTy) pvrtmp5893;
            CursorTy endof3325 = (CursorTy) pvrtmp5894;
            CursorTy case2752 = (CursorTy) endof3325;
            CursorTy x1455 = (CursorTy) case2752;
            CursorTy loc2764 = (CursorTy) end_y1457;
            CursorCursorCursorCursorProd tmp_struct197 =
                                          _add_size_and_rel_offsets_LVBIND(end_r1926, end_r1927_3441_3442, loc2764, x1455);
            CursorTy pvrtmp5901 = tmp_struct197.field0;
            CursorTy pvrtmp5902 = tmp_struct197.field1;
            CursorTy pvrtmp5903 = tmp_struct197.field2;
            CursorTy pvrtmp5904 = tmp_struct197.field3;
            CursorTy fltPrd4697 = (CursorTy) pvrtmp5903;
            CursorTy fltPrd4698 = (CursorTy) pvrtmp5904;
            CursorTy pvrtmp5906 = (CursorTy) fltPrd4698;
            CursorTy pvrtmp5905 = (CursorTy) fltPrd4697;
            CursorTy y1458 = (CursorTy) pvrtmp5905;
            CursorTy fltPrd4699 = (CursorTy) pvrtmp5903;
            CursorTy fltPrd4700 = (CursorTy) pvrtmp5904;
            CursorTy pvrtmp5908 = (CursorTy) fltPrd4700;
            CursorTy pvrtmp5907 = (CursorTy) fltPrd4699;
            CursorTy end_y1458 = (CursorTy) pvrtmp5908;
            CursorTy end_r1927_3441_3442_3443 = (CursorTy) pvrtmp5901;
            CursorTy endof3326 = (CursorTy) pvrtmp5902;

            *(TagTyPacked *) loc1925 = 0;

            CursorTy writetag3982 = loc1925 + 1;
            CursorTy writecur3983 = (CursorTy) end_y1456;
            CursorTy writecur3984 = (CursorTy) end_y1457;
            CursorTy writecur3985 = (CursorTy) end_y1458;
            CursorTy pvrtmp5910 = (CursorTy) writecur3985;
            CursorTy pvrtmp5909 = (CursorTy) loc1925;
            CursorTy taildc3327 = (CursorTy) pvrtmp5909;
            CursorTy end_taildc3327 = (CursorTy) pvrtmp5910;
            CursorTy pvrtmp5912 = (CursorTy) end_taildc3327;
            CursorTy pvrtmp5911 = (CursorTy) taildc3327;
            CursorTy fltPrd4701 = (CursorTy) pvrtmp5911;
            CursorTy fltPrd4702 = (CursorTy) pvrtmp5912;

            return (CursorCursorCursorCursorProd) {end_r1927_3441_3442_3443,
                                                   endof3326, fltPrd4701,
                                                   fltPrd4702};
            break;
        }

      case 1:
        {
            CursorTy field_cur3987 = (CursorTy) tmpcur5884;
            CursorTy jump3328 = loc1924 + 1;

            *(TagTyPacked *) loc1925 = 1;

            CursorTy writetag3988 = loc1925 + 1;
            CursorTy pvrtmp5914 = (CursorTy) writetag3988;
            CursorTy pvrtmp5913 = (CursorTy) loc1925;
            CursorTy taildc3329 = (CursorTy) pvrtmp5913;
            CursorTy end_taildc3329 = (CursorTy) pvrtmp5914;
            CursorTy pvrtmp5916 = (CursorTy) end_taildc3329;
            CursorTy pvrtmp5915 = (CursorTy) taildc3329;
            CursorTy fltPrd4703 = (CursorTy) pvrtmp5915;
            CursorTy fltPrd4704 = (CursorTy) pvrtmp5916;

            return (CursorCursorCursorCursorProd) {end_r1927, jump3328,
                                                   fltPrd4703, fltPrd4704};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6678 = *(CursorTy *) tmpcur5884;
            CursorTy tmpaftercur6679 = tmpcur5884 + 8;
            TagTyPacked tagtmp6680 = *(TagTyPacked *) tmpcur6678;
            CursorTy tailtmp6681 = tmpcur6678 + 1;

            tmpval5883 = tagtmp6680;
            tmpcur5884 = tailtmp6681;
            goto switch5917;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6678 = *(CursorTy *) tmpcur5884;
            CursorTy tmpaftercur6679 = tmpcur5884 + 8;
            TagTyPacked tagtmp6680 = *(TagTyPacked *) tmpcur6678;
            CursorTy tailtmp6681 = tmpcur6678 + 1;

            tmpval5883 = tagtmp6680;
            tmpcur5884 = tailtmp6681;
            goto switch5917;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5883");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Expr(CursorTy end_r1930,
                                                            CursorTy end_r1931,
                                                            CursorTy loc1929,
                                                            CursorTy arg1459)
{
    CursorTy loc1928 = (CursorTy) arg1459;

    if (loc1929 + 18 > end_r1931) {
        ChunkTy new_chunk223 = alloc_chunk(end_r1931);
        CursorTy chunk_start224 = new_chunk223.start_ptr;
        CursorTy chunk_end225 = new_chunk223.end_ptr;

        end_r1931 = chunk_end225;
        *(TagTyPacked *) loc1929 = 255;

        CursorTy redir = loc1929 + 1;

        *(CursorTy *) redir = chunk_start224;
        loc1929 = chunk_start224;
    }

    CursorTy loc2858 = loc1929 + 1;
    CursorTy loc2859 = loc2858 + 8;
    TagTyPacked tmpval5918 = *(TagTyPacked *) arg1459;
    CursorTy tmpcur5919 = arg1459 + 1;


  switch6178:
    ;
    switch (tmpval5918) {

      case 0:
        {
            CursorTy field_cur3990 = (CursorTy) tmpcur5919;
            CursorTy case2771 = (CursorTy) field_cur3990;
            SymTy tmpval5920 = *(SymTy *) case2771;
            CursorTy tmpcur5921 = case2771 + sizeof(SymTy);
            SymTy x1460 = (SymTy) tmpval5920;
            CursorTy end_x1460 = (CursorTy) tmpcur5921;
            CursorTy jump3330 = case2771 + 8;

            *(TagTyPacked *) loc1929 = 0;

            CursorTy writetag3992 = loc1929 + 1;

            *(SymTy *) writetag3992 = x1460;

            CursorTy writecur3993 = writetag3992 + sizeof(SymTy);
            CursorTy pvrtmp5923 = (CursorTy) writecur3993;
            CursorTy pvrtmp5922 = (CursorTy) loc1929;
            CursorTy taildc3331 = (CursorTy) pvrtmp5922;
            CursorTy end_taildc3331 = (CursorTy) pvrtmp5923;
            CursorTy pvrtmp5925 = (CursorTy) end_taildc3331;
            CursorTy pvrtmp5924 = (CursorTy) taildc3331;
            CursorTy fltPrd4705 = (CursorTy) pvrtmp5924;
            CursorTy fltPrd4706 = (CursorTy) pvrtmp5925;

            return (CursorCursorCursorCursorProd) {end_r1931, jump3330,
                                                   fltPrd4705, fltPrd4706};
            break;
        }

      case 1:
        {
            CursorTy field_cur3995 = (CursorTy) tmpcur5919;
            CursorTy case2775 = (CursorTy) field_cur3995;
            CursorTy x1462 = (CursorTy) case2775;
            CursorTy loc2783 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct201 =
                                          _add_size_and_rel_offsets_Formals(end_r1930, end_r1931, loc2783, x1462);
            CursorTy pvrtmp5926 = tmp_struct201.field0;
            CursorTy pvrtmp5927 = tmp_struct201.field1;
            CursorTy pvrtmp5928 = tmp_struct201.field2;
            CursorTy pvrtmp5929 = tmp_struct201.field3;
            CursorTy fltPrd4707 = (CursorTy) pvrtmp5928;
            CursorTy fltPrd4708 = (CursorTy) pvrtmp5929;
            CursorTy pvrtmp5931 = (CursorTy) fltPrd4708;
            CursorTy pvrtmp5930 = (CursorTy) fltPrd4707;
            CursorTy y1464 = (CursorTy) pvrtmp5930;
            CursorTy fltPrd4709 = (CursorTy) pvrtmp5928;
            CursorTy fltPrd4710 = (CursorTy) pvrtmp5929;
            CursorTy pvrtmp5933 = (CursorTy) fltPrd4710;
            CursorTy pvrtmp5932 = (CursorTy) fltPrd4709;
            CursorTy end_y1464 = (CursorTy) pvrtmp5933;
            CursorTy end_r1931_3444 = (CursorTy) pvrtmp5926;
            CursorTy endof3332 = (CursorTy) pvrtmp5927;
            CursorTy case2776 = (CursorTy) endof3332;
            CursorTy x1463 = (CursorTy) case2776;
            CursorTy loc2784 = (CursorTy) end_y1464;
            CursorCursorCursorCursorProd tmp_struct202 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1930, end_r1931_3444, loc2784, x1463);
            CursorTy pvrtmp5934 = tmp_struct202.field0;
            CursorTy pvrtmp5935 = tmp_struct202.field1;
            CursorTy pvrtmp5936 = tmp_struct202.field2;
            CursorTy pvrtmp5937 = tmp_struct202.field3;
            CursorTy fltPrd4711 = (CursorTy) pvrtmp5936;
            CursorTy fltPrd4712 = (CursorTy) pvrtmp5937;
            CursorTy pvrtmp5939 = (CursorTy) fltPrd4712;
            CursorTy pvrtmp5938 = (CursorTy) fltPrd4711;
            CursorTy y1465 = (CursorTy) pvrtmp5938;
            CursorTy fltPrd4713 = (CursorTy) pvrtmp5936;
            CursorTy fltPrd4714 = (CursorTy) pvrtmp5937;
            CursorTy pvrtmp5941 = (CursorTy) fltPrd4714;
            CursorTy pvrtmp5940 = (CursorTy) fltPrd4713;
            CursorTy end_y1465 = (CursorTy) pvrtmp5941;
            CursorTy end_r1931_3444_3445 = (CursorTy) pvrtmp5934;
            CursorTy endof3333 = (CursorTy) pvrtmp5935;

            *(TagTyPacked *) loc1929 = 1;

            CursorTy writetag3998 = loc1929 + 1;
            CursorTy writecur3999 = (CursorTy) end_y1464;
            CursorTy writecur4000 = (CursorTy) end_y1465;
            CursorTy pvrtmp5943 = (CursorTy) writecur4000;
            CursorTy pvrtmp5942 = (CursorTy) loc1929;
            CursorTy taildc3334 = (CursorTy) pvrtmp5942;
            CursorTy end_taildc3334 = (CursorTy) pvrtmp5943;
            CursorTy pvrtmp5945 = (CursorTy) end_taildc3334;
            CursorTy pvrtmp5944 = (CursorTy) taildc3334;
            CursorTy fltPrd4715 = (CursorTy) pvrtmp5944;
            CursorTy fltPrd4716 = (CursorTy) pvrtmp5945;

            return (CursorCursorCursorCursorProd) {end_r1931_3444_3445,
                                                   endof3333, fltPrd4715,
                                                   fltPrd4716};
            break;
        }

      case 2:
        {
            CursorTy field_cur4002 = (CursorTy) tmpcur5919;
            CursorTy case2787 = (CursorTy) field_cur4002;
            CursorTy x1466 = (CursorTy) case2787;
            CursorTy loc2791 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct203 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r1930, end_r1931, loc2791, x1466);
            CursorTy pvrtmp5946 = tmp_struct203.field0;
            CursorTy pvrtmp5947 = tmp_struct203.field1;
            CursorTy pvrtmp5948 = tmp_struct203.field2;
            CursorTy pvrtmp5949 = tmp_struct203.field3;
            CursorTy fltPrd4717 = (CursorTy) pvrtmp5948;
            CursorTy fltPrd4718 = (CursorTy) pvrtmp5949;
            CursorTy pvrtmp5951 = (CursorTy) fltPrd4718;
            CursorTy pvrtmp5950 = (CursorTy) fltPrd4717;
            CursorTy y1467 = (CursorTy) pvrtmp5950;
            CursorTy fltPrd4719 = (CursorTy) pvrtmp5948;
            CursorTy fltPrd4720 = (CursorTy) pvrtmp5949;
            CursorTy pvrtmp5953 = (CursorTy) fltPrd4720;
            CursorTy pvrtmp5952 = (CursorTy) fltPrd4719;
            CursorTy end_y1467 = (CursorTy) pvrtmp5953;
            CursorTy end_r1931_3446 = (CursorTy) pvrtmp5946;
            CursorTy endof3335 = (CursorTy) pvrtmp5947;

            *(TagTyPacked *) loc1929 = 2;

            CursorTy writetag4004 = loc1929 + 1;
            CursorTy writecur4005 = (CursorTy) end_y1467;
            CursorTy pvrtmp5955 = (CursorTy) writecur4005;
            CursorTy pvrtmp5954 = (CursorTy) loc1929;
            CursorTy taildc3336 = (CursorTy) pvrtmp5954;
            CursorTy end_taildc3336 = (CursorTy) pvrtmp5955;
            CursorTy pvrtmp5957 = (CursorTy) end_taildc3336;
            CursorTy pvrtmp5956 = (CursorTy) taildc3336;
            CursorTy fltPrd4721 = (CursorTy) pvrtmp5956;
            CursorTy fltPrd4722 = (CursorTy) pvrtmp5957;

            return (CursorCursorCursorCursorProd) {end_r1931_3446, endof3335,
                                                   fltPrd4721, fltPrd4722};
            break;
        }

      case 3:
        {
            CursorTy field_cur4007 = (CursorTy) tmpcur5919;
            CursorTy case2793 = (CursorTy) field_cur4007;
            CursorTy x1468 = (CursorTy) case2793;
            CursorTy loc2805 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct204 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931, loc2805, x1468);
            CursorTy pvrtmp5958 = tmp_struct204.field0;
            CursorTy pvrtmp5959 = tmp_struct204.field1;
            CursorTy pvrtmp5960 = tmp_struct204.field2;
            CursorTy pvrtmp5961 = tmp_struct204.field3;
            CursorTy fltPrd4723 = (CursorTy) pvrtmp5960;
            CursorTy fltPrd4724 = (CursorTy) pvrtmp5961;
            CursorTy pvrtmp5963 = (CursorTy) fltPrd4724;
            CursorTy pvrtmp5962 = (CursorTy) fltPrd4723;
            CursorTy y1471 = (CursorTy) pvrtmp5962;
            CursorTy fltPrd4725 = (CursorTy) pvrtmp5960;
            CursorTy fltPrd4726 = (CursorTy) pvrtmp5961;
            CursorTy pvrtmp5965 = (CursorTy) fltPrd4726;
            CursorTy pvrtmp5964 = (CursorTy) fltPrd4725;
            CursorTy end_y1471 = (CursorTy) pvrtmp5965;
            CursorTy end_r1931_3447 = (CursorTy) pvrtmp5958;
            CursorTy endof3337 = (CursorTy) pvrtmp5959;
            CursorTy case2794 = (CursorTy) endof3337;
            CursorTy x1469 = (CursorTy) case2794;
            CursorTy loc2806 = (CursorTy) end_y1471;
            CursorCursorCursorCursorProd tmp_struct205 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931_3447, loc2806, x1469);
            CursorTy pvrtmp5966 = tmp_struct205.field0;
            CursorTy pvrtmp5967 = tmp_struct205.field1;
            CursorTy pvrtmp5968 = tmp_struct205.field2;
            CursorTy pvrtmp5969 = tmp_struct205.field3;
            CursorTy fltPrd4727 = (CursorTy) pvrtmp5968;
            CursorTy fltPrd4728 = (CursorTy) pvrtmp5969;
            CursorTy pvrtmp5971 = (CursorTy) fltPrd4728;
            CursorTy pvrtmp5970 = (CursorTy) fltPrd4727;
            CursorTy y1472 = (CursorTy) pvrtmp5970;
            CursorTy fltPrd4729 = (CursorTy) pvrtmp5968;
            CursorTy fltPrd4730 = (CursorTy) pvrtmp5969;
            CursorTy pvrtmp5973 = (CursorTy) fltPrd4730;
            CursorTy pvrtmp5972 = (CursorTy) fltPrd4729;
            CursorTy end_y1472 = (CursorTy) pvrtmp5973;
            CursorTy end_r1931_3447_3448 = (CursorTy) pvrtmp5966;
            CursorTy endof3338 = (CursorTy) pvrtmp5967;
            CursorTy case2795 = (CursorTy) endof3338;
            CursorTy x1470 = (CursorTy) case2795;
            CursorTy loc2807 = (CursorTy) end_y1472;
            CursorCursorCursorCursorProd tmp_struct206 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931_3447_3448, loc2807, x1470);
            CursorTy pvrtmp5974 = tmp_struct206.field0;
            CursorTy pvrtmp5975 = tmp_struct206.field1;
            CursorTy pvrtmp5976 = tmp_struct206.field2;
            CursorTy pvrtmp5977 = tmp_struct206.field3;
            CursorTy fltPrd4731 = (CursorTy) pvrtmp5976;
            CursorTy fltPrd4732 = (CursorTy) pvrtmp5977;
            CursorTy pvrtmp5979 = (CursorTy) fltPrd4732;
            CursorTy pvrtmp5978 = (CursorTy) fltPrd4731;
            CursorTy y1473 = (CursorTy) pvrtmp5978;
            CursorTy fltPrd4733 = (CursorTy) pvrtmp5976;
            CursorTy fltPrd4734 = (CursorTy) pvrtmp5977;
            CursorTy pvrtmp5981 = (CursorTy) fltPrd4734;
            CursorTy pvrtmp5980 = (CursorTy) fltPrd4733;
            CursorTy end_y1473 = (CursorTy) pvrtmp5981;
            CursorTy end_r1931_3447_3448_3449 = (CursorTy) pvrtmp5974;
            CursorTy endof3339 = (CursorTy) pvrtmp5975;

            *(TagTyPacked *) loc1929 = 3;

            CursorTy writetag4011 = loc1929 + 1;
            CursorTy writecur4012 = (CursorTy) end_y1471;
            CursorTy writecur4013 = (CursorTy) end_y1472;
            CursorTy writecur4014 = (CursorTy) end_y1473;
            CursorTy pvrtmp5983 = (CursorTy) writecur4014;
            CursorTy pvrtmp5982 = (CursorTy) loc1929;
            CursorTy taildc3340 = (CursorTy) pvrtmp5982;
            CursorTy end_taildc3340 = (CursorTy) pvrtmp5983;
            CursorTy pvrtmp5985 = (CursorTy) end_taildc3340;
            CursorTy pvrtmp5984 = (CursorTy) taildc3340;
            CursorTy fltPrd4735 = (CursorTy) pvrtmp5984;
            CursorTy fltPrd4736 = (CursorTy) pvrtmp5985;

            return (CursorCursorCursorCursorProd) {end_r1931_3447_3448_3449,
                                                   endof3339, fltPrd4735,
                                                   fltPrd4736};
            break;
        }

      case 4:
        {
            CursorTy field_cur4016 = (CursorTy) tmpcur5919;
            CursorTy case2811 = (CursorTy) field_cur4016;
            CursorTy x1474 = (CursorTy) case2811;
            CursorTy loc2815 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct207 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1930, end_r1931, loc2815, x1474);
            CursorTy pvrtmp5986 = tmp_struct207.field0;
            CursorTy pvrtmp5987 = tmp_struct207.field1;
            CursorTy pvrtmp5988 = tmp_struct207.field2;
            CursorTy pvrtmp5989 = tmp_struct207.field3;
            CursorTy fltPrd4737 = (CursorTy) pvrtmp5988;
            CursorTy fltPrd4738 = (CursorTy) pvrtmp5989;
            CursorTy pvrtmp5991 = (CursorTy) fltPrd4738;
            CursorTy pvrtmp5990 = (CursorTy) fltPrd4737;
            CursorTy y1475 = (CursorTy) pvrtmp5990;
            CursorTy fltPrd4739 = (CursorTy) pvrtmp5988;
            CursorTy fltPrd4740 = (CursorTy) pvrtmp5989;
            CursorTy pvrtmp5993 = (CursorTy) fltPrd4740;
            CursorTy pvrtmp5992 = (CursorTy) fltPrd4739;
            CursorTy end_y1475 = (CursorTy) pvrtmp5993;
            CursorTy end_r1931_3450 = (CursorTy) pvrtmp5986;
            CursorTy endof3341 = (CursorTy) pvrtmp5987;

            *(TagTyPacked *) loc1929 = 4;

            CursorTy writetag4018 = loc1929 + 1;
            CursorTy writecur4019 = (CursorTy) end_y1475;
            CursorTy pvrtmp5995 = (CursorTy) writecur4019;
            CursorTy pvrtmp5994 = (CursorTy) loc1929;
            CursorTy taildc3342 = (CursorTy) pvrtmp5994;
            CursorTy end_taildc3342 = (CursorTy) pvrtmp5995;
            CursorTy pvrtmp5997 = (CursorTy) end_taildc3342;
            CursorTy pvrtmp5996 = (CursorTy) taildc3342;
            CursorTy fltPrd4741 = (CursorTy) pvrtmp5996;
            CursorTy fltPrd4742 = (CursorTy) pvrtmp5997;

            return (CursorCursorCursorCursorProd) {end_r1931_3450, endof3341,
                                                   fltPrd4741, fltPrd4742};
            break;
        }

      case 5:
        {
            CursorTy field_cur4021 = (CursorTy) tmpcur5919;
            CursorTy case2817 = (CursorTy) field_cur4021;
            CursorTy x1476 = (CursorTy) case2817;
            CursorTy loc2825 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct208 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931, loc2825, x1476);
            CursorTy pvrtmp5998 = tmp_struct208.field0;
            CursorTy pvrtmp5999 = tmp_struct208.field1;
            CursorTy pvrtmp6000 = tmp_struct208.field2;
            CursorTy pvrtmp6001 = tmp_struct208.field3;
            CursorTy fltPrd4743 = (CursorTy) pvrtmp6000;
            CursorTy fltPrd4744 = (CursorTy) pvrtmp6001;
            CursorTy pvrtmp6003 = (CursorTy) fltPrd4744;
            CursorTy pvrtmp6002 = (CursorTy) fltPrd4743;
            CursorTy y1478 = (CursorTy) pvrtmp6002;
            CursorTy fltPrd4745 = (CursorTy) pvrtmp6000;
            CursorTy fltPrd4746 = (CursorTy) pvrtmp6001;
            CursorTy pvrtmp6005 = (CursorTy) fltPrd4746;
            CursorTy pvrtmp6004 = (CursorTy) fltPrd4745;
            CursorTy end_y1478 = (CursorTy) pvrtmp6005;
            CursorTy end_r1931_3451 = (CursorTy) pvrtmp5998;
            CursorTy endof3343 = (CursorTy) pvrtmp5999;
            CursorTy case2818 = (CursorTy) endof3343;
            CursorTy x1477 = (CursorTy) case2818;
            CursorTy loc2826 = (CursorTy) end_y1478;
            CursorCursorCursorCursorProd tmp_struct209 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1930, end_r1931_3451, loc2826, x1477);
            CursorTy pvrtmp6006 = tmp_struct209.field0;
            CursorTy pvrtmp6007 = tmp_struct209.field1;
            CursorTy pvrtmp6008 = tmp_struct209.field2;
            CursorTy pvrtmp6009 = tmp_struct209.field3;
            CursorTy fltPrd4747 = (CursorTy) pvrtmp6008;
            CursorTy fltPrd4748 = (CursorTy) pvrtmp6009;
            CursorTy pvrtmp6011 = (CursorTy) fltPrd4748;
            CursorTy pvrtmp6010 = (CursorTy) fltPrd4747;
            CursorTy y1479 = (CursorTy) pvrtmp6010;
            CursorTy fltPrd4749 = (CursorTy) pvrtmp6008;
            CursorTy fltPrd4750 = (CursorTy) pvrtmp6009;
            CursorTy pvrtmp6013 = (CursorTy) fltPrd4750;
            CursorTy pvrtmp6012 = (CursorTy) fltPrd4749;
            CursorTy end_y1479 = (CursorTy) pvrtmp6013;
            CursorTy end_r1931_3451_3452 = (CursorTy) pvrtmp6006;
            CursorTy endof3344 = (CursorTy) pvrtmp6007;

            *(TagTyPacked *) loc1929 = 5;

            CursorTy writetag4024 = loc1929 + 1;
            CursorTy writecur4025 = (CursorTy) end_y1478;
            CursorTy writecur4026 = (CursorTy) end_y1479;
            CursorTy pvrtmp6015 = (CursorTy) writecur4026;
            CursorTy pvrtmp6014 = (CursorTy) loc1929;
            CursorTy taildc3345 = (CursorTy) pvrtmp6014;
            CursorTy end_taildc3345 = (CursorTy) pvrtmp6015;
            CursorTy pvrtmp6017 = (CursorTy) end_taildc3345;
            CursorTy pvrtmp6016 = (CursorTy) taildc3345;
            CursorTy fltPrd4751 = (CursorTy) pvrtmp6016;
            CursorTy fltPrd4752 = (CursorTy) pvrtmp6017;

            return (CursorCursorCursorCursorProd) {end_r1931_3451_3452,
                                                   endof3344, fltPrd4751,
                                                   fltPrd4752};
            break;
        }

      case 6:
        {
            CursorTy field_cur4028 = (CursorTy) tmpcur5919;
            CursorTy case2829 = (CursorTy) field_cur4028;
            CursorTy x1480 = (CursorTy) case2829;
            CursorTy loc2837 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct210 =
                                          _add_size_and_rel_offsets_LVBIND(end_r1930, end_r1931, loc2837, x1480);
            CursorTy pvrtmp6018 = tmp_struct210.field0;
            CursorTy pvrtmp6019 = tmp_struct210.field1;
            CursorTy pvrtmp6020 = tmp_struct210.field2;
            CursorTy pvrtmp6021 = tmp_struct210.field3;
            CursorTy fltPrd4753 = (CursorTy) pvrtmp6020;
            CursorTy fltPrd4754 = (CursorTy) pvrtmp6021;
            CursorTy pvrtmp6023 = (CursorTy) fltPrd4754;
            CursorTy pvrtmp6022 = (CursorTy) fltPrd4753;
            CursorTy y1482 = (CursorTy) pvrtmp6022;
            CursorTy fltPrd4755 = (CursorTy) pvrtmp6020;
            CursorTy fltPrd4756 = (CursorTy) pvrtmp6021;
            CursorTy pvrtmp6025 = (CursorTy) fltPrd4756;
            CursorTy pvrtmp6024 = (CursorTy) fltPrd4755;
            CursorTy end_y1482 = (CursorTy) pvrtmp6025;
            CursorTy end_r1931_3453 = (CursorTy) pvrtmp6018;
            CursorTy endof3346 = (CursorTy) pvrtmp6019;
            CursorTy case2830 = (CursorTy) endof3346;
            CursorTy x1481 = (CursorTy) case2830;
            CursorTy loc2838 = (CursorTy) end_y1482;
            CursorCursorCursorCursorProd tmp_struct211 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1930, end_r1931_3453, loc2838, x1481);
            CursorTy pvrtmp6026 = tmp_struct211.field0;
            CursorTy pvrtmp6027 = tmp_struct211.field1;
            CursorTy pvrtmp6028 = tmp_struct211.field2;
            CursorTy pvrtmp6029 = tmp_struct211.field3;
            CursorTy fltPrd4757 = (CursorTy) pvrtmp6028;
            CursorTy fltPrd4758 = (CursorTy) pvrtmp6029;
            CursorTy pvrtmp6031 = (CursorTy) fltPrd4758;
            CursorTy pvrtmp6030 = (CursorTy) fltPrd4757;
            CursorTy y1483 = (CursorTy) pvrtmp6030;
            CursorTy fltPrd4759 = (CursorTy) pvrtmp6028;
            CursorTy fltPrd4760 = (CursorTy) pvrtmp6029;
            CursorTy pvrtmp6033 = (CursorTy) fltPrd4760;
            CursorTy pvrtmp6032 = (CursorTy) fltPrd4759;
            CursorTy end_y1483 = (CursorTy) pvrtmp6033;
            CursorTy end_r1931_3453_3454 = (CursorTy) pvrtmp6026;
            CursorTy endof3347 = (CursorTy) pvrtmp6027;

            *(TagTyPacked *) loc1929 = 6;

            CursorTy writetag4031 = loc1929 + 1;
            CursorTy writecur4032 = (CursorTy) end_y1482;
            CursorTy writecur4033 = (CursorTy) end_y1483;
            CursorTy pvrtmp6035 = (CursorTy) writecur4033;
            CursorTy pvrtmp6034 = (CursorTy) loc1929;
            CursorTy taildc3348 = (CursorTy) pvrtmp6034;
            CursorTy end_taildc3348 = (CursorTy) pvrtmp6035;
            CursorTy pvrtmp6037 = (CursorTy) end_taildc3348;
            CursorTy pvrtmp6036 = (CursorTy) taildc3348;
            CursorTy fltPrd4761 = (CursorTy) pvrtmp6036;
            CursorTy fltPrd4762 = (CursorTy) pvrtmp6037;

            return (CursorCursorCursorCursorProd) {end_r1931_3453_3454,
                                                   endof3347, fltPrd4761,
                                                   fltPrd4762};
            break;
        }

      case 7:
        {
            CursorTy field_cur4035 = (CursorTy) tmpcur5919;
            CursorTy case2841 = (CursorTy) field_cur4035;
            CursorTy x1484 = (CursorTy) case2841;
            CursorTy loc2849 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct212 =
                                          _add_size_and_rel_offsets_LVBIND(end_r1930, end_r1931, loc2849, x1484);
            CursorTy pvrtmp6038 = tmp_struct212.field0;
            CursorTy pvrtmp6039 = tmp_struct212.field1;
            CursorTy pvrtmp6040 = tmp_struct212.field2;
            CursorTy pvrtmp6041 = tmp_struct212.field3;
            CursorTy fltPrd4763 = (CursorTy) pvrtmp6040;
            CursorTy fltPrd4764 = (CursorTy) pvrtmp6041;
            CursorTy pvrtmp6043 = (CursorTy) fltPrd4764;
            CursorTy pvrtmp6042 = (CursorTy) fltPrd4763;
            CursorTy y1486 = (CursorTy) pvrtmp6042;
            CursorTy fltPrd4765 = (CursorTy) pvrtmp6040;
            CursorTy fltPrd4766 = (CursorTy) pvrtmp6041;
            CursorTy pvrtmp6045 = (CursorTy) fltPrd4766;
            CursorTy pvrtmp6044 = (CursorTy) fltPrd4765;
            CursorTy end_y1486 = (CursorTy) pvrtmp6045;
            CursorTy end_r1931_3455 = (CursorTy) pvrtmp6038;
            CursorTy endof3349 = (CursorTy) pvrtmp6039;
            CursorTy case2842 = (CursorTy) endof3349;
            CursorTy x1485 = (CursorTy) case2842;
            CursorTy loc2850 = (CursorTy) end_y1486;
            CursorCursorCursorCursorProd tmp_struct213 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1930, end_r1931_3455, loc2850, x1485);
            CursorTy pvrtmp6046 = tmp_struct213.field0;
            CursorTy pvrtmp6047 = tmp_struct213.field1;
            CursorTy pvrtmp6048 = tmp_struct213.field2;
            CursorTy pvrtmp6049 = tmp_struct213.field3;
            CursorTy fltPrd4767 = (CursorTy) pvrtmp6048;
            CursorTy fltPrd4768 = (CursorTy) pvrtmp6049;
            CursorTy pvrtmp6051 = (CursorTy) fltPrd4768;
            CursorTy pvrtmp6050 = (CursorTy) fltPrd4767;
            CursorTy y1487 = (CursorTy) pvrtmp6050;
            CursorTy fltPrd4769 = (CursorTy) pvrtmp6048;
            CursorTy fltPrd4770 = (CursorTy) pvrtmp6049;
            CursorTy pvrtmp6053 = (CursorTy) fltPrd4770;
            CursorTy pvrtmp6052 = (CursorTy) fltPrd4769;
            CursorTy end_y1487 = (CursorTy) pvrtmp6053;
            CursorTy end_r1931_3455_3456 = (CursorTy) pvrtmp6046;
            CursorTy endof3350 = (CursorTy) pvrtmp6047;

            *(TagTyPacked *) loc1929 = 7;

            CursorTy writetag4038 = loc1929 + 1;
            CursorTy writecur4039 = (CursorTy) end_y1486;
            CursorTy writecur4040 = (CursorTy) end_y1487;
            CursorTy pvrtmp6055 = (CursorTy) writecur4040;
            CursorTy pvrtmp6054 = (CursorTy) loc1929;
            CursorTy taildc3351 = (CursorTy) pvrtmp6054;
            CursorTy end_taildc3351 = (CursorTy) pvrtmp6055;
            CursorTy pvrtmp6057 = (CursorTy) end_taildc3351;
            CursorTy pvrtmp6056 = (CursorTy) taildc3351;
            CursorTy fltPrd4771 = (CursorTy) pvrtmp6056;
            CursorTy fltPrd4772 = (CursorTy) pvrtmp6057;

            return (CursorCursorCursorCursorProd) {end_r1931_3455_3456,
                                                   endof3350, fltPrd4771,
                                                   fltPrd4772};
            break;
        }

      case 8:
        {
            CursorTy field_cur4042 = (CursorTy) tmpcur5919;
            CursorTy case2853 = (CursorTy) field_cur4042;
            SymTy tmpval6058 = *(SymTy *) case2853;
            CursorTy tmpcur6059 = case2853 + sizeof(SymTy);
            SymTy x1488 = (SymTy) tmpval6058;
            CursorTy end_x1488 = (CursorTy) tmpcur6059;
            CursorTy case2854 = (CursorTy) end_x1488;
            CursorTy x1489 = (CursorTy) case2854;
            CursorTy jump3352 = case2853 + 8;
            CursorCursorCursorCursorProd tmp_struct214 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931, loc2859, x1489);
            CursorTy pvrtmp6060 = tmp_struct214.field0;
            CursorTy pvrtmp6061 = tmp_struct214.field1;
            CursorTy pvrtmp6062 = tmp_struct214.field2;
            CursorTy pvrtmp6063 = tmp_struct214.field3;
            CursorTy fltPrd4773 = (CursorTy) pvrtmp6062;
            CursorTy fltPrd4774 = (CursorTy) pvrtmp6063;
            CursorTy pvrtmp6065 = (CursorTy) fltPrd4774;
            CursorTy pvrtmp6064 = (CursorTy) fltPrd4773;
            CursorTy y1491 = (CursorTy) pvrtmp6064;
            CursorTy fltPrd4775 = (CursorTy) pvrtmp6062;
            CursorTy fltPrd4776 = (CursorTy) pvrtmp6063;
            CursorTy pvrtmp6067 = (CursorTy) fltPrd4776;
            CursorTy pvrtmp6066 = (CursorTy) fltPrd4775;
            CursorTy end_y1491 = (CursorTy) pvrtmp6067;
            CursorTy end_r1931_3457 = (CursorTy) pvrtmp6060;
            CursorTy endof3353 = (CursorTy) pvrtmp6061;

            *(TagTyPacked *) loc1929 = 8;

            CursorTy writetag4045 = loc1929 + 1;

            *(SymTy *) writetag4045 = x1488;

            CursorTy writecur4046 = writetag4045 + sizeof(SymTy);
            CursorTy writecur4047 = (CursorTy) end_y1491;
            CursorTy pvrtmp6069 = (CursorTy) writecur4047;
            CursorTy pvrtmp6068 = (CursorTy) loc1929;
            CursorTy taildc3354 = (CursorTy) pvrtmp6068;
            CursorTy end_taildc3354 = (CursorTy) pvrtmp6069;
            CursorTy pvrtmp6071 = (CursorTy) end_taildc3354;
            CursorTy pvrtmp6070 = (CursorTy) taildc3354;
            CursorTy fltPrd4777 = (CursorTy) pvrtmp6070;
            CursorTy fltPrd4778 = (CursorTy) pvrtmp6071;

            return (CursorCursorCursorCursorProd) {end_r1931_3457, endof3353,
                                                   fltPrd4777, fltPrd4778};
            break;
        }

      case 9:
        {
            CursorTy field_cur4049 = (CursorTy) tmpcur5919;
            CursorTy case2863 = (CursorTy) field_cur4049;
            CursorTy x1492 = (CursorTy) case2863;
            CursorTy loc2867 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct215 =
                                          _add_size_and_rel_offsets_Datum(end_r1930, end_r1931, loc2867, x1492);
            CursorTy pvrtmp6072 = tmp_struct215.field0;
            CursorTy pvrtmp6073 = tmp_struct215.field1;
            CursorTy pvrtmp6074 = tmp_struct215.field2;
            CursorTy pvrtmp6075 = tmp_struct215.field3;
            CursorTy fltPrd4779 = (CursorTy) pvrtmp6074;
            CursorTy fltPrd4780 = (CursorTy) pvrtmp6075;
            CursorTy pvrtmp6077 = (CursorTy) fltPrd4780;
            CursorTy pvrtmp6076 = (CursorTy) fltPrd4779;
            CursorTy y1493 = (CursorTy) pvrtmp6076;
            CursorTy fltPrd4781 = (CursorTy) pvrtmp6074;
            CursorTy fltPrd4782 = (CursorTy) pvrtmp6075;
            CursorTy pvrtmp6079 = (CursorTy) fltPrd4782;
            CursorTy pvrtmp6078 = (CursorTy) fltPrd4781;
            CursorTy end_y1493 = (CursorTy) pvrtmp6079;
            CursorTy end_r1931_3458 = (CursorTy) pvrtmp6072;
            CursorTy endof3355 = (CursorTy) pvrtmp6073;

            *(TagTyPacked *) loc1929 = 9;

            CursorTy writetag4051 = loc1929 + 1;
            CursorTy writecur4052 = (CursorTy) end_y1493;
            CursorTy pvrtmp6081 = (CursorTy) writecur4052;
            CursorTy pvrtmp6080 = (CursorTy) loc1929;
            CursorTy taildc3356 = (CursorTy) pvrtmp6080;
            CursorTy end_taildc3356 = (CursorTy) pvrtmp6081;
            CursorTy pvrtmp6083 = (CursorTy) end_taildc3356;
            CursorTy pvrtmp6082 = (CursorTy) taildc3356;
            CursorTy fltPrd4783 = (CursorTy) pvrtmp6082;
            CursorTy fltPrd4784 = (CursorTy) pvrtmp6083;

            return (CursorCursorCursorCursorProd) {end_r1931_3458, endof3355,
                                                   fltPrd4783, fltPrd4784};
            break;
        }

      case 10:
        {
            CursorTy field_cur4054 = (CursorTy) tmpcur5919;
            CursorTy case2869 = (CursorTy) field_cur4054;
            CursorTy x1494 = (CursorTy) case2869;
            CursorTy loc2873 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct216 =
                                          _add_size_and_rel_offsets_Datum(end_r1930, end_r1931, loc2873, x1494);
            CursorTy pvrtmp6084 = tmp_struct216.field0;
            CursorTy pvrtmp6085 = tmp_struct216.field1;
            CursorTy pvrtmp6086 = tmp_struct216.field2;
            CursorTy pvrtmp6087 = tmp_struct216.field3;
            CursorTy fltPrd4785 = (CursorTy) pvrtmp6086;
            CursorTy fltPrd4786 = (CursorTy) pvrtmp6087;
            CursorTy pvrtmp6089 = (CursorTy) fltPrd4786;
            CursorTy pvrtmp6088 = (CursorTy) fltPrd4785;
            CursorTy y1495 = (CursorTy) pvrtmp6088;
            CursorTy fltPrd4787 = (CursorTy) pvrtmp6086;
            CursorTy fltPrd4788 = (CursorTy) pvrtmp6087;
            CursorTy pvrtmp6091 = (CursorTy) fltPrd4788;
            CursorTy pvrtmp6090 = (CursorTy) fltPrd4787;
            CursorTy end_y1495 = (CursorTy) pvrtmp6091;
            CursorTy end_r1931_3459 = (CursorTy) pvrtmp6084;
            CursorTy endof3357 = (CursorTy) pvrtmp6085;

            *(TagTyPacked *) loc1929 = 10;

            CursorTy writetag4056 = loc1929 + 1;
            CursorTy writecur4057 = (CursorTy) end_y1495;
            CursorTy pvrtmp6093 = (CursorTy) writecur4057;
            CursorTy pvrtmp6092 = (CursorTy) loc1929;
            CursorTy taildc3358 = (CursorTy) pvrtmp6092;
            CursorTy end_taildc3358 = (CursorTy) pvrtmp6093;
            CursorTy pvrtmp6095 = (CursorTy) end_taildc3358;
            CursorTy pvrtmp6094 = (CursorTy) taildc3358;
            CursorTy fltPrd4789 = (CursorTy) pvrtmp6094;
            CursorTy fltPrd4790 = (CursorTy) pvrtmp6095;

            return (CursorCursorCursorCursorProd) {end_r1931_3459, endof3357,
                                                   fltPrd4789, fltPrd4790};
            break;
        }

      case 11:
        {
            CursorTy field_cur4059 = (CursorTy) tmpcur5919;
            CursorTy case2875 = (CursorTy) field_cur4059;
            CursorTy x1496 = (CursorTy) case2875;
            CursorTy loc2879 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct217 =
                                          _add_size_and_rel_offsets_Datum(end_r1930, end_r1931, loc2879, x1496);
            CursorTy pvrtmp6096 = tmp_struct217.field0;
            CursorTy pvrtmp6097 = tmp_struct217.field1;
            CursorTy pvrtmp6098 = tmp_struct217.field2;
            CursorTy pvrtmp6099 = tmp_struct217.field3;
            CursorTy fltPrd4791 = (CursorTy) pvrtmp6098;
            CursorTy fltPrd4792 = (CursorTy) pvrtmp6099;
            CursorTy pvrtmp6101 = (CursorTy) fltPrd4792;
            CursorTy pvrtmp6100 = (CursorTy) fltPrd4791;
            CursorTy y1497 = (CursorTy) pvrtmp6100;
            CursorTy fltPrd4793 = (CursorTy) pvrtmp6098;
            CursorTy fltPrd4794 = (CursorTy) pvrtmp6099;
            CursorTy pvrtmp6103 = (CursorTy) fltPrd4794;
            CursorTy pvrtmp6102 = (CursorTy) fltPrd4793;
            CursorTy end_y1497 = (CursorTy) pvrtmp6103;
            CursorTy end_r1931_3460 = (CursorTy) pvrtmp6096;
            CursorTy endof3359 = (CursorTy) pvrtmp6097;

            *(TagTyPacked *) loc1929 = 11;

            CursorTy writetag4061 = loc1929 + 1;
            CursorTy writecur4062 = (CursorTy) end_y1497;
            CursorTy pvrtmp6105 = (CursorTy) writecur4062;
            CursorTy pvrtmp6104 = (CursorTy) loc1929;
            CursorTy taildc3360 = (CursorTy) pvrtmp6104;
            CursorTy end_taildc3360 = (CursorTy) pvrtmp6105;
            CursorTy pvrtmp6107 = (CursorTy) end_taildc3360;
            CursorTy pvrtmp6106 = (CursorTy) taildc3360;
            CursorTy fltPrd4795 = (CursorTy) pvrtmp6106;
            CursorTy fltPrd4796 = (CursorTy) pvrtmp6107;

            return (CursorCursorCursorCursorProd) {end_r1931_3460, endof3359,
                                                   fltPrd4795, fltPrd4796};
            break;
        }

      case 12:
        {
            CursorTy field_cur4064 = (CursorTy) tmpcur5919;
            CursorTy case2881 = (CursorTy) field_cur4064;
            CursorTy x1498 = (CursorTy) case2881;
            CursorTy loc2893 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct218 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931, loc2893, x1498);
            CursorTy pvrtmp6108 = tmp_struct218.field0;
            CursorTy pvrtmp6109 = tmp_struct218.field1;
            CursorTy pvrtmp6110 = tmp_struct218.field2;
            CursorTy pvrtmp6111 = tmp_struct218.field3;
            CursorTy fltPrd4797 = (CursorTy) pvrtmp6110;
            CursorTy fltPrd4798 = (CursorTy) pvrtmp6111;
            CursorTy pvrtmp6113 = (CursorTy) fltPrd4798;
            CursorTy pvrtmp6112 = (CursorTy) fltPrd4797;
            CursorTy y1501 = (CursorTy) pvrtmp6112;
            CursorTy fltPrd4799 = (CursorTy) pvrtmp6110;
            CursorTy fltPrd4800 = (CursorTy) pvrtmp6111;
            CursorTy pvrtmp6115 = (CursorTy) fltPrd4800;
            CursorTy pvrtmp6114 = (CursorTy) fltPrd4799;
            CursorTy end_y1501 = (CursorTy) pvrtmp6115;
            CursorTy end_r1931_3461 = (CursorTy) pvrtmp6108;
            CursorTy endof3361 = (CursorTy) pvrtmp6109;
            CursorTy case2882 = (CursorTy) endof3361;
            CursorTy x1499 = (CursorTy) case2882;
            CursorTy loc2894 = (CursorTy) end_y1501;
            CursorCursorCursorCursorProd tmp_struct219 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931_3461, loc2894, x1499);
            CursorTy pvrtmp6116 = tmp_struct219.field0;
            CursorTy pvrtmp6117 = tmp_struct219.field1;
            CursorTy pvrtmp6118 = tmp_struct219.field2;
            CursorTy pvrtmp6119 = tmp_struct219.field3;
            CursorTy fltPrd4801 = (CursorTy) pvrtmp6118;
            CursorTy fltPrd4802 = (CursorTy) pvrtmp6119;
            CursorTy pvrtmp6121 = (CursorTy) fltPrd4802;
            CursorTy pvrtmp6120 = (CursorTy) fltPrd4801;
            CursorTy y1502 = (CursorTy) pvrtmp6120;
            CursorTy fltPrd4803 = (CursorTy) pvrtmp6118;
            CursorTy fltPrd4804 = (CursorTy) pvrtmp6119;
            CursorTy pvrtmp6123 = (CursorTy) fltPrd4804;
            CursorTy pvrtmp6122 = (CursorTy) fltPrd4803;
            CursorTy end_y1502 = (CursorTy) pvrtmp6123;
            CursorTy end_r1931_3461_3462 = (CursorTy) pvrtmp6116;
            CursorTy endof3362 = (CursorTy) pvrtmp6117;
            CursorTy case2883 = (CursorTy) endof3362;
            CursorTy x1500 = (CursorTy) case2883;
            CursorTy loc2895 = (CursorTy) end_y1502;
            CursorCursorCursorCursorProd tmp_struct220 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931_3461_3462, loc2895, x1500);
            CursorTy pvrtmp6124 = tmp_struct220.field0;
            CursorTy pvrtmp6125 = tmp_struct220.field1;
            CursorTy pvrtmp6126 = tmp_struct220.field2;
            CursorTy pvrtmp6127 = tmp_struct220.field3;
            CursorTy fltPrd4805 = (CursorTy) pvrtmp6126;
            CursorTy fltPrd4806 = (CursorTy) pvrtmp6127;
            CursorTy pvrtmp6129 = (CursorTy) fltPrd4806;
            CursorTy pvrtmp6128 = (CursorTy) fltPrd4805;
            CursorTy y1503 = (CursorTy) pvrtmp6128;
            CursorTy fltPrd4807 = (CursorTy) pvrtmp6126;
            CursorTy fltPrd4808 = (CursorTy) pvrtmp6127;
            CursorTy pvrtmp6131 = (CursorTy) fltPrd4808;
            CursorTy pvrtmp6130 = (CursorTy) fltPrd4807;
            CursorTy end_y1503 = (CursorTy) pvrtmp6131;
            CursorTy end_r1931_3461_3462_3463 = (CursorTy) pvrtmp6124;
            CursorTy endof3363 = (CursorTy) pvrtmp6125;

            *(TagTyPacked *) loc1929 = 12;

            CursorTy writetag4068 = loc1929 + 1;
            CursorTy writecur4069 = (CursorTy) end_y1501;
            CursorTy writecur4070 = (CursorTy) end_y1502;
            CursorTy writecur4071 = (CursorTy) end_y1503;
            CursorTy pvrtmp6133 = (CursorTy) writecur4071;
            CursorTy pvrtmp6132 = (CursorTy) loc1929;
            CursorTy taildc3364 = (CursorTy) pvrtmp6132;
            CursorTy end_taildc3364 = (CursorTy) pvrtmp6133;
            CursorTy pvrtmp6135 = (CursorTy) end_taildc3364;
            CursorTy pvrtmp6134 = (CursorTy) taildc3364;
            CursorTy fltPrd4809 = (CursorTy) pvrtmp6134;
            CursorTy fltPrd4810 = (CursorTy) pvrtmp6135;

            return (CursorCursorCursorCursorProd) {end_r1931_3461_3462_3463,
                                                   endof3363, fltPrd4809,
                                                   fltPrd4810};
            break;
        }

      case 13:
        {
            CursorTy field_cur4073 = (CursorTy) tmpcur5919;
            CursorTy case2899 = (CursorTy) field_cur4073;
            CursorTy x1504 = (CursorTy) case2899;
            CursorTy loc2907 = loc1929 + 1;
            CursorCursorCursorCursorProd tmp_struct221 =
                                          _add_size_and_rel_offsets_Expr(end_r1930, end_r1931, loc2907, x1504);
            CursorTy pvrtmp6136 = tmp_struct221.field0;
            CursorTy pvrtmp6137 = tmp_struct221.field1;
            CursorTy pvrtmp6138 = tmp_struct221.field2;
            CursorTy pvrtmp6139 = tmp_struct221.field3;
            CursorTy fltPrd4811 = (CursorTy) pvrtmp6138;
            CursorTy fltPrd4812 = (CursorTy) pvrtmp6139;
            CursorTy pvrtmp6141 = (CursorTy) fltPrd4812;
            CursorTy pvrtmp6140 = (CursorTy) fltPrd4811;
            CursorTy y1506 = (CursorTy) pvrtmp6140;
            CursorTy fltPrd4813 = (CursorTy) pvrtmp6138;
            CursorTy fltPrd4814 = (CursorTy) pvrtmp6139;
            CursorTy pvrtmp6143 = (CursorTy) fltPrd4814;
            CursorTy pvrtmp6142 = (CursorTy) fltPrd4813;
            CursorTy end_y1506 = (CursorTy) pvrtmp6143;
            CursorTy end_r1931_3464 = (CursorTy) pvrtmp6136;
            CursorTy endof3365 = (CursorTy) pvrtmp6137;
            CursorTy case2900 = (CursorTy) endof3365;
            CursorTy x1505 = (CursorTy) case2900;
            CursorTy loc2908 = (CursorTy) end_y1506;
            CursorCursorCursorCursorProd tmp_struct222 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1930, end_r1931_3464, loc2908, x1505);
            CursorTy pvrtmp6144 = tmp_struct222.field0;
            CursorTy pvrtmp6145 = tmp_struct222.field1;
            CursorTy pvrtmp6146 = tmp_struct222.field2;
            CursorTy pvrtmp6147 = tmp_struct222.field3;
            CursorTy fltPrd4815 = (CursorTy) pvrtmp6146;
            CursorTy fltPrd4816 = (CursorTy) pvrtmp6147;
            CursorTy pvrtmp6149 = (CursorTy) fltPrd4816;
            CursorTy pvrtmp6148 = (CursorTy) fltPrd4815;
            CursorTy y1507 = (CursorTy) pvrtmp6148;
            CursorTy fltPrd4817 = (CursorTy) pvrtmp6146;
            CursorTy fltPrd4818 = (CursorTy) pvrtmp6147;
            CursorTy pvrtmp6151 = (CursorTy) fltPrd4818;
            CursorTy pvrtmp6150 = (CursorTy) fltPrd4817;
            CursorTy end_y1507 = (CursorTy) pvrtmp6151;
            CursorTy end_r1931_3464_3465 = (CursorTy) pvrtmp6144;
            CursorTy endof3366 = (CursorTy) pvrtmp6145;

            *(TagTyPacked *) loc1929 = 13;

            CursorTy writetag4076 = loc1929 + 1;
            CursorTy writecur4077 = (CursorTy) end_y1506;
            CursorTy writecur4078 = (CursorTy) end_y1507;
            CursorTy pvrtmp6153 = (CursorTy) writecur4078;
            CursorTy pvrtmp6152 = (CursorTy) loc1929;
            CursorTy taildc3367 = (CursorTy) pvrtmp6152;
            CursorTy end_taildc3367 = (CursorTy) pvrtmp6153;
            CursorTy pvrtmp6155 = (CursorTy) end_taildc3367;
            CursorTy pvrtmp6154 = (CursorTy) taildc3367;
            CursorTy fltPrd4819 = (CursorTy) pvrtmp6154;
            CursorTy fltPrd4820 = (CursorTy) pvrtmp6155;

            return (CursorCursorCursorCursorProd) {end_r1931_3464_3465,
                                                   endof3366, fltPrd4819,
                                                   fltPrd4820};
            break;
        }

      case 14:
        {
            CursorTy field_cur4080 = (CursorTy) tmpcur5919;
            CursorTy case2911 = (CursorTy) field_cur4080;
            SymTy tmpval6156 = *(SymTy *) case2911;
            CursorTy tmpcur6157 = case2911 + sizeof(SymTy);
            SymTy x1508 = (SymTy) tmpval6156;
            CursorTy end_x1508 = (CursorTy) tmpcur6157;
            CursorTy jump3368 = case2911 + 8;

            *(TagTyPacked *) loc1929 = 14;

            CursorTy writetag4082 = loc1929 + 1;

            *(SymTy *) writetag4082 = x1508;

            CursorTy writecur4083 = writetag4082 + sizeof(SymTy);
            CursorTy pvrtmp6159 = (CursorTy) writecur4083;
            CursorTy pvrtmp6158 = (CursorTy) loc1929;
            CursorTy taildc3369 = (CursorTy) pvrtmp6158;
            CursorTy end_taildc3369 = (CursorTy) pvrtmp6159;
            CursorTy pvrtmp6161 = (CursorTy) end_taildc3369;
            CursorTy pvrtmp6160 = (CursorTy) taildc3369;
            CursorTy fltPrd4821 = (CursorTy) pvrtmp6160;
            CursorTy fltPrd4822 = (CursorTy) pvrtmp6161;

            return (CursorCursorCursorCursorProd) {end_r1931, jump3368,
                                                   fltPrd4821, fltPrd4822};
            break;
        }

      case 15:
        {
            CursorTy field_cur4085 = (CursorTy) tmpcur5919;
            CursorTy case2915 = (CursorTy) field_cur4085;
            SymTy tmpval6162 = *(SymTy *) case2915;
            CursorTy tmpcur6163 = case2915 + sizeof(SymTy);
            SymTy x1510 = (SymTy) tmpval6162;
            CursorTy end_x1510 = (CursorTy) tmpcur6163;
            CursorTy jump3370 = case2915 + 8;

            *(TagTyPacked *) loc1929 = 15;

            CursorTy writetag4087 = loc1929 + 1;

            *(SymTy *) writetag4087 = x1510;

            CursorTy writecur4088 = writetag4087 + sizeof(SymTy);
            CursorTy pvrtmp6165 = (CursorTy) writecur4088;
            CursorTy pvrtmp6164 = (CursorTy) loc1929;
            CursorTy taildc3371 = (CursorTy) pvrtmp6164;
            CursorTy end_taildc3371 = (CursorTy) pvrtmp6165;
            CursorTy pvrtmp6167 = (CursorTy) end_taildc3371;
            CursorTy pvrtmp6166 = (CursorTy) taildc3371;
            CursorTy fltPrd4823 = (CursorTy) pvrtmp6166;
            CursorTy fltPrd4824 = (CursorTy) pvrtmp6167;

            return (CursorCursorCursorCursorProd) {end_r1931, jump3370,
                                                   fltPrd4823, fltPrd4824};
            break;
        }

      case 16:
        {
            CursorTy field_cur4090 = (CursorTy) tmpcur5919;
            CursorTy case2919 = (CursorTy) field_cur4090;
            SymTy tmpval6168 = *(SymTy *) case2919;
            CursorTy tmpcur6169 = case2919 + sizeof(SymTy);
            SymTy x1512 = (SymTy) tmpval6168;
            CursorTy end_x1512 = (CursorTy) tmpcur6169;
            CursorTy jump3372 = case2919 + 8;

            *(TagTyPacked *) loc1929 = 16;

            CursorTy writetag4092 = loc1929 + 1;

            *(SymTy *) writetag4092 = x1512;

            CursorTy writecur4093 = writetag4092 + sizeof(SymTy);
            CursorTy pvrtmp6171 = (CursorTy) writecur4093;
            CursorTy pvrtmp6170 = (CursorTy) loc1929;
            CursorTy taildc3373 = (CursorTy) pvrtmp6170;
            CursorTy end_taildc3373 = (CursorTy) pvrtmp6171;
            CursorTy pvrtmp6173 = (CursorTy) end_taildc3373;
            CursorTy pvrtmp6172 = (CursorTy) taildc3373;
            CursorTy fltPrd4825 = (CursorTy) pvrtmp6172;
            CursorTy fltPrd4826 = (CursorTy) pvrtmp6173;

            return (CursorCursorCursorCursorProd) {end_r1931, jump3372,
                                                   fltPrd4825, fltPrd4826};
            break;
        }

      case 17:
        {
            CursorTy field_cur4095 = (CursorTy) tmpcur5919;
            CursorTy jump3374 = loc1928 + 1;

            *(TagTyPacked *) loc1929 = 17;

            CursorTy writetag4096 = loc1929 + 1;
            CursorTy pvrtmp6175 = (CursorTy) writetag4096;
            CursorTy pvrtmp6174 = (CursorTy) loc1929;
            CursorTy taildc3375 = (CursorTy) pvrtmp6174;
            CursorTy end_taildc3375 = (CursorTy) pvrtmp6175;
            CursorTy pvrtmp6177 = (CursorTy) end_taildc3375;
            CursorTy pvrtmp6176 = (CursorTy) taildc3375;
            CursorTy fltPrd4827 = (CursorTy) pvrtmp6176;
            CursorTy fltPrd4828 = (CursorTy) pvrtmp6177;

            return (CursorCursorCursorCursorProd) {end_r1931, jump3374,
                                                   fltPrd4827, fltPrd4828};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6682 = *(CursorTy *) tmpcur5919;
            CursorTy tmpaftercur6683 = tmpcur5919 + 8;
            TagTyPacked tagtmp6684 = *(TagTyPacked *) tmpcur6682;
            CursorTy tailtmp6685 = tmpcur6682 + 1;

            tmpval5918 = tagtmp6684;
            tmpcur5919 = tailtmp6685;
            goto switch6178;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6682 = *(CursorTy *) tmpcur5919;
            CursorTy tmpaftercur6683 = tmpcur5919 + 8;
            TagTyPacked tagtmp6684 = *(TagTyPacked *) tmpcur6682;
            CursorTy tailtmp6685 = tmpcur6682 + 1;

            tmpval5918 = tagtmp6684;
            tmpcur5919 = tailtmp6685;
            goto switch6178;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5918");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Toplvl(CursorTy end_r1934,
                                                              CursorTy end_r1935,
                                                              CursorTy loc1933,
                                                              CursorTy arg1514)
{
    CursorTy loc1932 = (CursorTy) arg1514;

    if (loc1933 + 18 > end_r1935) {
        ChunkTy new_chunk232 = alloc_chunk(end_r1935);
        CursorTy chunk_start233 = new_chunk232.start_ptr;
        CursorTy chunk_end234 = new_chunk232.end_ptr;

        end_r1935 = chunk_end234;
        *(TagTyPacked *) loc1933 = 255;

        CursorTy redir = loc1933 + 1;

        *(CursorTy *) redir = chunk_start233;
        loc1933 = chunk_start233;
    }

    TagTyPacked tmpval6179 = *(TagTyPacked *) arg1514;
    CursorTy tmpcur6180 = arg1514 + 1;


  switch6245:
    ;
    switch (tmpval6179) {

      case 0:
        {
            CursorTy field_cur4098 = (CursorTy) tmpcur6180;
            CursorTy case2926 = (CursorTy) field_cur4098;
            CursorTy x1515 = (CursorTy) case2926;
            CursorTy loc2934 = loc1933 + 1;
            CursorCursorCursorCursorProd tmp_struct226 =
                                          _add_size_and_rel_offsets_ListSym(end_r1934, end_r1935, loc2934, x1515);
            CursorTy pvrtmp6181 = tmp_struct226.field0;
            CursorTy pvrtmp6182 = tmp_struct226.field1;
            CursorTy pvrtmp6183 = tmp_struct226.field2;
            CursorTy pvrtmp6184 = tmp_struct226.field3;
            CursorTy fltPrd4829 = (CursorTy) pvrtmp6183;
            CursorTy fltPrd4830 = (CursorTy) pvrtmp6184;
            CursorTy pvrtmp6186 = (CursorTy) fltPrd4830;
            CursorTy pvrtmp6185 = (CursorTy) fltPrd4829;
            CursorTy y1517 = (CursorTy) pvrtmp6185;
            CursorTy fltPrd4831 = (CursorTy) pvrtmp6183;
            CursorTy fltPrd4832 = (CursorTy) pvrtmp6184;
            CursorTy pvrtmp6188 = (CursorTy) fltPrd4832;
            CursorTy pvrtmp6187 = (CursorTy) fltPrd4831;
            CursorTy end_y1517 = (CursorTy) pvrtmp6188;
            CursorTy end_r1935_3466 = (CursorTy) pvrtmp6181;
            CursorTy endof3376 = (CursorTy) pvrtmp6182;
            CursorTy case2927 = (CursorTy) endof3376;
            CursorTy x1516 = (CursorTy) case2927;
            CursorTy loc2935 = (CursorTy) end_y1517;
            CursorCursorCursorCursorProd tmp_struct227 =
                                          _add_size_and_rel_offsets_Expr(end_r1934, end_r1935_3466, loc2935, x1516);
            CursorTy pvrtmp6189 = tmp_struct227.field0;
            CursorTy pvrtmp6190 = tmp_struct227.field1;
            CursorTy pvrtmp6191 = tmp_struct227.field2;
            CursorTy pvrtmp6192 = tmp_struct227.field3;
            CursorTy fltPrd4833 = (CursorTy) pvrtmp6191;
            CursorTy fltPrd4834 = (CursorTy) pvrtmp6192;
            CursorTy pvrtmp6194 = (CursorTy) fltPrd4834;
            CursorTy pvrtmp6193 = (CursorTy) fltPrd4833;
            CursorTy y1518 = (CursorTy) pvrtmp6193;
            CursorTy fltPrd4835 = (CursorTy) pvrtmp6191;
            CursorTy fltPrd4836 = (CursorTy) pvrtmp6192;
            CursorTy pvrtmp6196 = (CursorTy) fltPrd4836;
            CursorTy pvrtmp6195 = (CursorTy) fltPrd4835;
            CursorTy end_y1518 = (CursorTy) pvrtmp6196;
            CursorTy end_r1935_3466_3467 = (CursorTy) pvrtmp6189;
            CursorTy endof3377 = (CursorTy) pvrtmp6190;

            *(TagTyPacked *) loc1933 = 0;

            CursorTy writetag4101 = loc1933 + 1;
            CursorTy writecur4102 = (CursorTy) end_y1517;
            CursorTy writecur4103 = (CursorTy) end_y1518;
            CursorTy pvrtmp6198 = (CursorTy) writecur4103;
            CursorTy pvrtmp6197 = (CursorTy) loc1933;
            CursorTy taildc3378 = (CursorTy) pvrtmp6197;
            CursorTy end_taildc3378 = (CursorTy) pvrtmp6198;
            CursorTy pvrtmp6200 = (CursorTy) end_taildc3378;
            CursorTy pvrtmp6199 = (CursorTy) taildc3378;
            CursorTy fltPrd4837 = (CursorTy) pvrtmp6199;
            CursorTy fltPrd4838 = (CursorTy) pvrtmp6200;

            return (CursorCursorCursorCursorProd) {end_r1935_3466_3467,
                                                   endof3377, fltPrd4837,
                                                   fltPrd4838};
            break;
        }

      case 1:
        {
            CursorTy field_cur4105 = (CursorTy) tmpcur6180;
            CursorTy case2938 = (CursorTy) field_cur4105;
            CursorTy x1519 = (CursorTy) case2938;
            CursorTy loc2946 = loc1933 + 1;
            CursorCursorCursorCursorProd tmp_struct228 =
                                          _add_size_and_rel_offsets_ListSym(end_r1934, end_r1935, loc2946, x1519);
            CursorTy pvrtmp6201 = tmp_struct228.field0;
            CursorTy pvrtmp6202 = tmp_struct228.field1;
            CursorTy pvrtmp6203 = tmp_struct228.field2;
            CursorTy pvrtmp6204 = tmp_struct228.field3;
            CursorTy fltPrd4839 = (CursorTy) pvrtmp6203;
            CursorTy fltPrd4840 = (CursorTy) pvrtmp6204;
            CursorTy pvrtmp6206 = (CursorTy) fltPrd4840;
            CursorTy pvrtmp6205 = (CursorTy) fltPrd4839;
            CursorTy y1521 = (CursorTy) pvrtmp6205;
            CursorTy fltPrd4841 = (CursorTy) pvrtmp6203;
            CursorTy fltPrd4842 = (CursorTy) pvrtmp6204;
            CursorTy pvrtmp6208 = (CursorTy) fltPrd4842;
            CursorTy pvrtmp6207 = (CursorTy) fltPrd4841;
            CursorTy end_y1521 = (CursorTy) pvrtmp6208;
            CursorTy end_r1935_3468 = (CursorTy) pvrtmp6201;
            CursorTy endof3379 = (CursorTy) pvrtmp6202;
            CursorTy case2939 = (CursorTy) endof3379;
            CursorTy x1520 = (CursorTy) case2939;
            CursorTy loc2947 = (CursorTy) end_y1521;
            CursorCursorCursorCursorProd tmp_struct229 =
                                          _add_size_and_rel_offsets_Expr(end_r1934, end_r1935_3468, loc2947, x1520);
            CursorTy pvrtmp6209 = tmp_struct229.field0;
            CursorTy pvrtmp6210 = tmp_struct229.field1;
            CursorTy pvrtmp6211 = tmp_struct229.field2;
            CursorTy pvrtmp6212 = tmp_struct229.field3;
            CursorTy fltPrd4843 = (CursorTy) pvrtmp6211;
            CursorTy fltPrd4844 = (CursorTy) pvrtmp6212;
            CursorTy pvrtmp6214 = (CursorTy) fltPrd4844;
            CursorTy pvrtmp6213 = (CursorTy) fltPrd4843;
            CursorTy y1522 = (CursorTy) pvrtmp6213;
            CursorTy fltPrd4845 = (CursorTy) pvrtmp6211;
            CursorTy fltPrd4846 = (CursorTy) pvrtmp6212;
            CursorTy pvrtmp6216 = (CursorTy) fltPrd4846;
            CursorTy pvrtmp6215 = (CursorTy) fltPrd4845;
            CursorTy end_y1522 = (CursorTy) pvrtmp6216;
            CursorTy end_r1935_3468_3469 = (CursorTy) pvrtmp6209;
            CursorTy endof3380 = (CursorTy) pvrtmp6210;

            *(TagTyPacked *) loc1933 = 1;

            CursorTy writetag4108 = loc1933 + 1;
            CursorTy writecur4109 = (CursorTy) end_y1521;
            CursorTy writecur4110 = (CursorTy) end_y1522;
            CursorTy pvrtmp6218 = (CursorTy) writecur4110;
            CursorTy pvrtmp6217 = (CursorTy) loc1933;
            CursorTy taildc3381 = (CursorTy) pvrtmp6217;
            CursorTy end_taildc3381 = (CursorTy) pvrtmp6218;
            CursorTy pvrtmp6220 = (CursorTy) end_taildc3381;
            CursorTy pvrtmp6219 = (CursorTy) taildc3381;
            CursorTy fltPrd4847 = (CursorTy) pvrtmp6219;
            CursorTy fltPrd4848 = (CursorTy) pvrtmp6220;

            return (CursorCursorCursorCursorProd) {end_r1935_3468_3469,
                                                   endof3380, fltPrd4847,
                                                   fltPrd4848};
            break;
        }

      case 2:
        {
            CursorTy field_cur4112 = (CursorTy) tmpcur6180;
            CursorTy case2950 = (CursorTy) field_cur4112;
            CursorTy x1523 = (CursorTy) case2950;
            CursorTy loc2954 = loc1933 + 1;
            CursorCursorCursorCursorProd tmp_struct230 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r1934, end_r1935, loc2954, x1523);
            CursorTy pvrtmp6221 = tmp_struct230.field0;
            CursorTy pvrtmp6222 = tmp_struct230.field1;
            CursorTy pvrtmp6223 = tmp_struct230.field2;
            CursorTy pvrtmp6224 = tmp_struct230.field3;
            CursorTy fltPrd4849 = (CursorTy) pvrtmp6223;
            CursorTy fltPrd4850 = (CursorTy) pvrtmp6224;
            CursorTy pvrtmp6226 = (CursorTy) fltPrd4850;
            CursorTy pvrtmp6225 = (CursorTy) fltPrd4849;
            CursorTy y1524 = (CursorTy) pvrtmp6225;
            CursorTy fltPrd4851 = (CursorTy) pvrtmp6223;
            CursorTy fltPrd4852 = (CursorTy) pvrtmp6224;
            CursorTy pvrtmp6228 = (CursorTy) fltPrd4852;
            CursorTy pvrtmp6227 = (CursorTy) fltPrd4851;
            CursorTy end_y1524 = (CursorTy) pvrtmp6228;
            CursorTy end_r1935_3470 = (CursorTy) pvrtmp6221;
            CursorTy endof3382 = (CursorTy) pvrtmp6222;

            *(TagTyPacked *) loc1933 = 2;

            CursorTy writetag4114 = loc1933 + 1;
            CursorTy writecur4115 = (CursorTy) end_y1524;
            CursorTy pvrtmp6230 = (CursorTy) writecur4115;
            CursorTy pvrtmp6229 = (CursorTy) loc1933;
            CursorTy taildc3383 = (CursorTy) pvrtmp6229;
            CursorTy end_taildc3383 = (CursorTy) pvrtmp6230;
            CursorTy pvrtmp6232 = (CursorTy) end_taildc3383;
            CursorTy pvrtmp6231 = (CursorTy) taildc3383;
            CursorTy fltPrd4853 = (CursorTy) pvrtmp6231;
            CursorTy fltPrd4854 = (CursorTy) pvrtmp6232;

            return (CursorCursorCursorCursorProd) {end_r1935_3470, endof3382,
                                                   fltPrd4853, fltPrd4854};
            break;
        }

      case 3:
        {
            CursorTy field_cur4117 = (CursorTy) tmpcur6180;
            CursorTy case2956 = (CursorTy) field_cur4117;
            CursorTy x1525 = (CursorTy) case2956;
            CursorTy loc2960 = loc1933 + 1;
            CursorCursorCursorCursorProd tmp_struct231 =
                                          _add_size_and_rel_offsets_Expr(end_r1934, end_r1935, loc2960, x1525);
            CursorTy pvrtmp6233 = tmp_struct231.field0;
            CursorTy pvrtmp6234 = tmp_struct231.field1;
            CursorTy pvrtmp6235 = tmp_struct231.field2;
            CursorTy pvrtmp6236 = tmp_struct231.field3;
            CursorTy fltPrd4855 = (CursorTy) pvrtmp6235;
            CursorTy fltPrd4856 = (CursorTy) pvrtmp6236;
            CursorTy pvrtmp6238 = (CursorTy) fltPrd4856;
            CursorTy pvrtmp6237 = (CursorTy) fltPrd4855;
            CursorTy y1526 = (CursorTy) pvrtmp6237;
            CursorTy fltPrd4857 = (CursorTy) pvrtmp6235;
            CursorTy fltPrd4858 = (CursorTy) pvrtmp6236;
            CursorTy pvrtmp6240 = (CursorTy) fltPrd4858;
            CursorTy pvrtmp6239 = (CursorTy) fltPrd4857;
            CursorTy end_y1526 = (CursorTy) pvrtmp6240;
            CursorTy end_r1935_3471 = (CursorTy) pvrtmp6233;
            CursorTy endof3384 = (CursorTy) pvrtmp6234;

            *(TagTyPacked *) loc1933 = 3;

            CursorTy writetag4119 = loc1933 + 1;
            CursorTy writecur4120 = (CursorTy) end_y1526;
            CursorTy pvrtmp6242 = (CursorTy) writecur4120;
            CursorTy pvrtmp6241 = (CursorTy) loc1933;
            CursorTy taildc3385 = (CursorTy) pvrtmp6241;
            CursorTy end_taildc3385 = (CursorTy) pvrtmp6242;
            CursorTy pvrtmp6244 = (CursorTy) end_taildc3385;
            CursorTy pvrtmp6243 = (CursorTy) taildc3385;
            CursorTy fltPrd4859 = (CursorTy) pvrtmp6243;
            CursorTy fltPrd4860 = (CursorTy) pvrtmp6244;

            return (CursorCursorCursorCursorProd) {end_r1935_3471, endof3384,
                                                   fltPrd4859, fltPrd4860};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6686 = *(CursorTy *) tmpcur6180;
            CursorTy tmpaftercur6687 = tmpcur6180 + 8;
            TagTyPacked tagtmp6688 = *(TagTyPacked *) tmpcur6686;
            CursorTy tailtmp6689 = tmpcur6686 + 1;

            tmpval6179 = tagtmp6688;
            tmpcur6180 = tailtmp6689;
            goto switch6245;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6686 = *(CursorTy *) tmpcur6180;
            CursorTy tmpaftercur6687 = tmpcur6180 + 8;
            TagTyPacked tagtmp6688 = *(TagTyPacked *) tmpcur6686;
            CursorTy tailtmp6689 = tmpcur6686 + 1;

            tmpval6179 = tagtmp6688;
            tmpcur6180 = tailtmp6689;
            goto switch6245;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6179");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_ListSym(CursorTy p6246)
{
    TagTyPacked tag6247 = *(TagTyPacked *) p6246;
    CursorTy tail6248 = p6246 + 1;


  switch6255:
    ;
    switch (tag6247) {

      case 0:
        {
            SymTy val6249 = *(SymTy *) tail6248;
            CursorTy tail6250 = tail6248 + sizeof(SymTy);
            PtrCursorProd tmp_struct235 =  _unpack_ListSym(tail6250);
            PtrTy ptr6251 = tmp_struct235.field0;
            CursorTy tail6252 = tmp_struct235.field1;
            PtrTy ptr6253 = ALLOC(sizeof(TagSymCursorProd));

            ((TagSymCursorProd *) ptr6253)->field0 = tag6247;
            ((TagSymCursorProd *) ptr6253)->field1 = val6249;
            ((TagSymCursorProd *) ptr6253)->field2 = ptr6251;
            return (PtrCursorProd) {ptr6253, tail6252};
            break;
        }

      case 1:
        {
            PtrTy ptr6254 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr6254)->field0 = tag6247;
            return (PtrCursorProd) {ptr6254, tail6248};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6690 = *(CursorTy *) tail6248;
            CursorTy tmpaftercur6691 = tail6248 + 8;
            TagTyPacked tagtmp6692 = *(TagTyPacked *) tmpcur6690;
            CursorTy tailtmp6693 = tmpcur6690 + 1;

            tag6247 = tagtmp6692;
            tail6248 = tailtmp6693;
            goto switch6255;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6690 = *(CursorTy *) tail6248;
            CursorTy tmpaftercur6691 = tail6248 + 8;
            TagTyPacked tagtmp6692 = *(TagTyPacked *) tmpcur6690;
            CursorTy tailtmp6693 = tmpcur6690 + 1;

            tag6247 = tagtmp6692;
            tail6248 = tailtmp6693;
            goto switch6255;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6255");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_ListExpr(CursorTy p6256)
{
    TagTyPacked tag6257 = *(TagTyPacked *) p6256;
    CursorTy tail6258 = p6256 + 1;


  switch6265:
    ;
    switch (tag6257) {

      case 0:
        {
            PtrCursorProd tmp_struct236 =  _unpack_Expr(tail6258);
            PtrTy ptr6259 = tmp_struct236.field0;
            CursorTy tail6260 = tmp_struct236.field1;
            PtrCursorProd tmp_struct237 =  _unpack_ListExpr(tail6260);
            PtrTy ptr6261 = tmp_struct237.field0;
            CursorTy tail6262 = tmp_struct237.field1;
            PtrTy ptr6263 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6263)->field0 = tag6257;
            ((TagCursorCursorProd *) ptr6263)->field1 = ptr6259;
            ((TagCursorCursorProd *) ptr6263)->field2 = ptr6261;
            return (PtrCursorProd) {ptr6263, tail6262};
            break;
        }

      case 1:
        {
            PtrTy ptr6264 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr6264)->field0 = tag6257;
            return (PtrCursorProd) {ptr6264, tail6258};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6694 = *(CursorTy *) tail6258;
            CursorTy tmpaftercur6695 = tail6258 + 8;
            TagTyPacked tagtmp6696 = *(TagTyPacked *) tmpcur6694;
            CursorTy tailtmp6697 = tmpcur6694 + 1;

            tag6257 = tagtmp6696;
            tail6258 = tailtmp6697;
            goto switch6265;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6694 = *(CursorTy *) tail6258;
            CursorTy tmpaftercur6695 = tail6258 + 8;
            TagTyPacked tagtmp6696 = *(TagTyPacked *) tmpcur6694;
            CursorTy tailtmp6697 = tmpcur6694 + 1;

            tag6257 = tagtmp6696;
            tail6258 = tailtmp6697;
            goto switch6265;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6265");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_ListToplvl(CursorTy p6266)
{
    TagTyPacked tag6267 = *(TagTyPacked *) p6266;
    CursorTy tail6268 = p6266 + 1;


  switch6291:
    ;
    switch (tag6267) {

      case 0:
        {
            PtrCursorProd tmp_struct238 =  _unpack_Toplvl(tail6268);
            PtrTy ptr6269 = tmp_struct238.field0;
            CursorTy tail6270 = tmp_struct238.field1;
            PtrCursorProd tmp_struct239 =  _unpack_ListToplvl(tail6270);
            PtrTy ptr6271 = tmp_struct239.field0;
            CursorTy tail6272 = tmp_struct239.field1;
            PtrTy ptr6273 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6273)->field0 = tag6267;
            ((TagCursorCursorProd *) ptr6273)->field1 = ptr6269;
            ((TagCursorCursorProd *) ptr6273)->field2 = ptr6271;
            return (PtrCursorProd) {ptr6273, tail6272};
            break;
        }

      case 1:
        {
            PtrTy ptr6274 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr6274)->field0 = tag6267;
            return (PtrCursorProd) {ptr6274, tail6268};
            break;
        }

      case 2:
        {
            CursorTy next6275 = *(CursorTy *) tail6268;
            CursorTy afternext6276 = tail6268 + 8;
            PtrCursorProd tmp_struct240 =  _unpack_Toplvl(afternext6276);
            PtrTy ptr6277 = tmp_struct240.field0;
            CursorTy tail6278 = tmp_struct240.field1;
            PtrCursorProd tmp_struct241 =  _unpack_ListToplvl(tail6278);
            PtrTy ptr6279 = tmp_struct241.field0;
            CursorTy tail6280 = tmp_struct241.field1;
            PtrTy ptr6281 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr6281)->field0 = tag6267;
            ((TagCursorCursorCursorProd *) ptr6281)->field1 = next6275;
            ((TagCursorCursorCursorProd *) ptr6281)->field2 = ptr6277;
            ((TagCursorCursorCursorProd *) ptr6281)->field3 = ptr6279;
            return (PtrCursorProd) {ptr6281, tail6280};
            break;
        }

      case 3:
        {
            IntTy val6282 = *(IntTy *) tail6268;
            CursorTy tail6283 = tail6268 + sizeof(IntTy);
            IntTy val6284 = *(IntTy *) tail6283;
            CursorTy tail6285 = tail6283 + sizeof(IntTy);
            PtrCursorProd tmp_struct242 =  _unpack_Toplvl(tail6285);
            PtrTy ptr6286 = tmp_struct242.field0;
            CursorTy tail6287 = tmp_struct242.field1;
            PtrCursorProd tmp_struct243 =  _unpack_ListToplvl(tail6287);
            PtrTy ptr6288 = tmp_struct243.field0;
            CursorTy tail6289 = tmp_struct243.field1;
            PtrTy ptr6290 = ALLOC(sizeof(TagInt64Int64CursorCursorProd));

            ((TagInt64Int64CursorCursorProd *) ptr6290)->field0 = tag6267;
            ((TagInt64Int64CursorCursorProd *) ptr6290)->field1 = val6282;
            ((TagInt64Int64CursorCursorProd *) ptr6290)->field2 = val6284;
            ((TagInt64Int64CursorCursorProd *) ptr6290)->field3 = ptr6286;
            ((TagInt64Int64CursorCursorProd *) ptr6290)->field4 = ptr6288;
            return (PtrCursorProd) {ptr6290, tail6289};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6698 = *(CursorTy *) tail6268;
            CursorTy tmpaftercur6699 = tail6268 + 8;
            TagTyPacked tagtmp6700 = *(TagTyPacked *) tmpcur6698;
            CursorTy tailtmp6701 = tmpcur6698 + 1;

            tag6267 = tagtmp6700;
            tail6268 = tailtmp6701;
            goto switch6291;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6698 = *(CursorTy *) tail6268;
            CursorTy tmpaftercur6699 = tail6268 + 8;
            TagTyPacked tagtmp6700 = *(TagTyPacked *) tmpcur6698;
            CursorTy tailtmp6701 = tmpcur6698 + 1;

            tag6267 = tagtmp6700;
            tail6268 = tailtmp6701;
            goto switch6291;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6291");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Formals(CursorTy p6292)
{
    TagTyPacked tag6293 = *(TagTyPacked *) p6292;
    CursorTy tail6294 = p6292 + 1;


  switch6306:
    ;
    switch (tag6293) {

      case 0:
        {
            PtrCursorProd tmp_struct244 =  _unpack_ListSym(tail6294);
            PtrTy ptr6295 = tmp_struct244.field0;
            CursorTy tail6296 = tmp_struct244.field1;
            PtrTy ptr6297 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6297)->field0 = tag6293;
            ((TagCursorProd *) ptr6297)->field1 = ptr6295;
            return (PtrCursorProd) {ptr6297, tail6296};
            break;
        }

      case 1:
        {
            PtrCursorProd tmp_struct245 =  _unpack_ListSym(tail6294);
            PtrTy ptr6298 = tmp_struct245.field0;
            CursorTy tail6299 = tmp_struct245.field1;
            SymTy val6300 = *(SymTy *) tail6299;
            CursorTy tail6301 = tail6299 + sizeof(SymTy);
            PtrTy ptr6302 = ALLOC(sizeof(TagCursorSymProd));

            ((TagCursorSymProd *) ptr6302)->field0 = tag6293;
            ((TagCursorSymProd *) ptr6302)->field1 = ptr6298;
            ((TagCursorSymProd *) ptr6302)->field2 = val6300;
            return (PtrCursorProd) {ptr6302, tail6301};
            break;
        }

      case 2:
        {
            SymTy val6303 = *(SymTy *) tail6294;
            CursorTy tail6304 = tail6294 + sizeof(SymTy);
            PtrTy ptr6305 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr6305)->field0 = tag6293;
            ((TagSymProd *) ptr6305)->field1 = val6303;
            return (PtrCursorProd) {ptr6305, tail6304};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6702 = *(CursorTy *) tail6294;
            CursorTy tmpaftercur6703 = tail6294 + 8;
            TagTyPacked tagtmp6704 = *(TagTyPacked *) tmpcur6702;
            CursorTy tailtmp6705 = tmpcur6702 + 1;

            tag6293 = tagtmp6704;
            tail6294 = tailtmp6705;
            goto switch6306;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6702 = *(CursorTy *) tail6294;
            CursorTy tmpaftercur6703 = tail6294 + 8;
            TagTyPacked tagtmp6704 = *(TagTyPacked *) tmpcur6702;
            CursorTy tailtmp6705 = tmpcur6702 + 1;

            tag6293 = tagtmp6704;
            tail6294 = tailtmp6705;
            goto switch6306;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6306");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Datum(CursorTy p6307)
{
    TagTyPacked tag6308 = *(TagTyPacked *) p6307;
    CursorTy tail6309 = p6307 + 1;


  switch6313:
    ;
    switch (tag6308) {

      case 0:
        {
            IntTy val6310 = *(IntTy *) tail6309;
            CursorTy tail6311 = tail6309 + sizeof(IntTy);
            PtrTy ptr6312 = ALLOC(sizeof(TagInt64Prod));

            ((TagInt64Prod *) ptr6312)->field0 = tag6308;
            ((TagInt64Prod *) ptr6312)->field1 = val6310;
            return (PtrCursorProd) {ptr6312, tail6311};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6706 = *(CursorTy *) tail6309;
            CursorTy tmpaftercur6707 = tail6309 + 8;
            TagTyPacked tagtmp6708 = *(TagTyPacked *) tmpcur6706;
            CursorTy tailtmp6709 = tmpcur6706 + 1;

            tag6308 = tagtmp6708;
            tail6309 = tailtmp6709;
            goto switch6313;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6706 = *(CursorTy *) tail6309;
            CursorTy tmpaftercur6707 = tail6309 + 8;
            TagTyPacked tagtmp6708 = *(TagTyPacked *) tmpcur6706;
            CursorTy tailtmp6709 = tmpcur6706 + 1;

            tag6308 = tagtmp6708;
            tail6309 = tailtmp6709;
            goto switch6313;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6313");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_LAMBDACASE(CursorTy p6314)
{
    TagTyPacked tag6315 = *(TagTyPacked *) p6314;
    CursorTy tail6316 = p6314 + 1;


  switch6325:
    ;
    switch (tag6315) {

      case 0:
        {
            PtrCursorProd tmp_struct246 =  _unpack_Formals(tail6316);
            PtrTy ptr6317 = tmp_struct246.field0;
            CursorTy tail6318 = tmp_struct246.field1;
            PtrCursorProd tmp_struct247 =  _unpack_ListExpr(tail6318);
            PtrTy ptr6319 = tmp_struct247.field0;
            CursorTy tail6320 = tmp_struct247.field1;
            PtrCursorProd tmp_struct248 =  _unpack_LAMBDACASE(tail6320);
            PtrTy ptr6321 = tmp_struct248.field0;
            CursorTy tail6322 = tmp_struct248.field1;
            PtrTy ptr6323 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr6323)->field0 = tag6315;
            ((TagCursorCursorCursorProd *) ptr6323)->field1 = ptr6317;
            ((TagCursorCursorCursorProd *) ptr6323)->field2 = ptr6319;
            ((TagCursorCursorCursorProd *) ptr6323)->field3 = ptr6321;
            return (PtrCursorProd) {ptr6323, tail6322};
            break;
        }

      case 1:
        {
            PtrTy ptr6324 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr6324)->field0 = tag6315;
            return (PtrCursorProd) {ptr6324, tail6316};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6710 = *(CursorTy *) tail6316;
            CursorTy tmpaftercur6711 = tail6316 + 8;
            TagTyPacked tagtmp6712 = *(TagTyPacked *) tmpcur6710;
            CursorTy tailtmp6713 = tmpcur6710 + 1;

            tag6315 = tagtmp6712;
            tail6316 = tailtmp6713;
            goto switch6325;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6710 = *(CursorTy *) tail6316;
            CursorTy tmpaftercur6711 = tail6316 + 8;
            TagTyPacked tagtmp6712 = *(TagTyPacked *) tmpcur6710;
            CursorTy tailtmp6713 = tmpcur6710 + 1;

            tag6315 = tagtmp6712;
            tail6316 = tailtmp6713;
            goto switch6325;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6325");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_LVBIND(CursorTy p6326)
{
    TagTyPacked tag6327 = *(TagTyPacked *) p6326;
    CursorTy tail6328 = p6326 + 1;


  switch6337:
    ;
    switch (tag6327) {

      case 0:
        {
            PtrCursorProd tmp_struct249 =  _unpack_ListSym(tail6328);
            PtrTy ptr6329 = tmp_struct249.field0;
            CursorTy tail6330 = tmp_struct249.field1;
            PtrCursorProd tmp_struct250 =  _unpack_Expr(tail6330);
            PtrTy ptr6331 = tmp_struct250.field0;
            CursorTy tail6332 = tmp_struct250.field1;
            PtrCursorProd tmp_struct251 =  _unpack_LVBIND(tail6332);
            PtrTy ptr6333 = tmp_struct251.field0;
            CursorTy tail6334 = tmp_struct251.field1;
            PtrTy ptr6335 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr6335)->field0 = tag6327;
            ((TagCursorCursorCursorProd *) ptr6335)->field1 = ptr6329;
            ((TagCursorCursorCursorProd *) ptr6335)->field2 = ptr6331;
            ((TagCursorCursorCursorProd *) ptr6335)->field3 = ptr6333;
            return (PtrCursorProd) {ptr6335, tail6334};
            break;
        }

      case 1:
        {
            PtrTy ptr6336 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr6336)->field0 = tag6327;
            return (PtrCursorProd) {ptr6336, tail6328};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6714 = *(CursorTy *) tail6328;
            CursorTy tmpaftercur6715 = tail6328 + 8;
            TagTyPacked tagtmp6716 = *(TagTyPacked *) tmpcur6714;
            CursorTy tailtmp6717 = tmpcur6714 + 1;

            tag6327 = tagtmp6716;
            tail6328 = tailtmp6717;
            goto switch6337;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6714 = *(CursorTy *) tail6328;
            CursorTy tmpaftercur6715 = tail6328 + 8;
            TagTyPacked tagtmp6716 = *(TagTyPacked *) tmpcur6714;
            CursorTy tailtmp6717 = tmpcur6714 + 1;

            tag6327 = tagtmp6716;
            tail6328 = tailtmp6717;
            goto switch6337;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6337");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Expr(CursorTy p6338)
{
    TagTyPacked tag6339 = *(TagTyPacked *) p6338;
    CursorTy tail6340 = p6338 + 1;


  switch6413:
    ;
    switch (tag6339) {

      case 0:
        {
            SymTy val6341 = *(SymTy *) tail6340;
            CursorTy tail6342 = tail6340 + sizeof(SymTy);
            PtrTy ptr6343 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr6343)->field0 = tag6339;
            ((TagSymProd *) ptr6343)->field1 = val6341;
            return (PtrCursorProd) {ptr6343, tail6342};
            break;
        }

      case 1:
        {
            PtrCursorProd tmp_struct252 =  _unpack_Formals(tail6340);
            PtrTy ptr6344 = tmp_struct252.field0;
            CursorTy tail6345 = tmp_struct252.field1;
            PtrCursorProd tmp_struct253 =  _unpack_ListExpr(tail6345);
            PtrTy ptr6346 = tmp_struct253.field0;
            CursorTy tail6347 = tmp_struct253.field1;
            PtrTy ptr6348 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6348)->field0 = tag6339;
            ((TagCursorCursorProd *) ptr6348)->field1 = ptr6344;
            ((TagCursorCursorProd *) ptr6348)->field2 = ptr6346;
            return (PtrCursorProd) {ptr6348, tail6347};
            break;
        }

      case 2:
        {
            PtrCursorProd tmp_struct254 =  _unpack_LAMBDACASE(tail6340);
            PtrTy ptr6349 = tmp_struct254.field0;
            CursorTy tail6350 = tmp_struct254.field1;
            PtrTy ptr6351 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6351)->field0 = tag6339;
            ((TagCursorProd *) ptr6351)->field1 = ptr6349;
            return (PtrCursorProd) {ptr6351, tail6350};
            break;
        }

      case 3:
        {
            PtrCursorProd tmp_struct255 =  _unpack_Expr(tail6340);
            PtrTy ptr6352 = tmp_struct255.field0;
            CursorTy tail6353 = tmp_struct255.field1;
            PtrCursorProd tmp_struct256 =  _unpack_Expr(tail6353);
            PtrTy ptr6354 = tmp_struct256.field0;
            CursorTy tail6355 = tmp_struct256.field1;
            PtrCursorProd tmp_struct257 =  _unpack_Expr(tail6355);
            PtrTy ptr6356 = tmp_struct257.field0;
            CursorTy tail6357 = tmp_struct257.field1;
            PtrTy ptr6358 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr6358)->field0 = tag6339;
            ((TagCursorCursorCursorProd *) ptr6358)->field1 = ptr6352;
            ((TagCursorCursorCursorProd *) ptr6358)->field2 = ptr6354;
            ((TagCursorCursorCursorProd *) ptr6358)->field3 = ptr6356;
            return (PtrCursorProd) {ptr6358, tail6357};
            break;
        }

      case 4:
        {
            PtrCursorProd tmp_struct258 =  _unpack_ListExpr(tail6340);
            PtrTy ptr6359 = tmp_struct258.field0;
            CursorTy tail6360 = tmp_struct258.field1;
            PtrTy ptr6361 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6361)->field0 = tag6339;
            ((TagCursorProd *) ptr6361)->field1 = ptr6359;
            return (PtrCursorProd) {ptr6361, tail6360};
            break;
        }

      case 5:
        {
            PtrCursorProd tmp_struct259 =  _unpack_Expr(tail6340);
            PtrTy ptr6362 = tmp_struct259.field0;
            CursorTy tail6363 = tmp_struct259.field1;
            PtrCursorProd tmp_struct260 =  _unpack_ListExpr(tail6363);
            PtrTy ptr6364 = tmp_struct260.field0;
            CursorTy tail6365 = tmp_struct260.field1;
            PtrTy ptr6366 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6366)->field0 = tag6339;
            ((TagCursorCursorProd *) ptr6366)->field1 = ptr6362;
            ((TagCursorCursorProd *) ptr6366)->field2 = ptr6364;
            return (PtrCursorProd) {ptr6366, tail6365};
            break;
        }

      case 6:
        {
            PtrCursorProd tmp_struct261 =  _unpack_LVBIND(tail6340);
            PtrTy ptr6367 = tmp_struct261.field0;
            CursorTy tail6368 = tmp_struct261.field1;
            PtrCursorProd tmp_struct262 =  _unpack_ListExpr(tail6368);
            PtrTy ptr6369 = tmp_struct262.field0;
            CursorTy tail6370 = tmp_struct262.field1;
            PtrTy ptr6371 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6371)->field0 = tag6339;
            ((TagCursorCursorProd *) ptr6371)->field1 = ptr6367;
            ((TagCursorCursorProd *) ptr6371)->field2 = ptr6369;
            return (PtrCursorProd) {ptr6371, tail6370};
            break;
        }

      case 7:
        {
            PtrCursorProd tmp_struct263 =  _unpack_LVBIND(tail6340);
            PtrTy ptr6372 = tmp_struct263.field0;
            CursorTy tail6373 = tmp_struct263.field1;
            PtrCursorProd tmp_struct264 =  _unpack_ListExpr(tail6373);
            PtrTy ptr6374 = tmp_struct264.field0;
            CursorTy tail6375 = tmp_struct264.field1;
            PtrTy ptr6376 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6376)->field0 = tag6339;
            ((TagCursorCursorProd *) ptr6376)->field1 = ptr6372;
            ((TagCursorCursorProd *) ptr6376)->field2 = ptr6374;
            return (PtrCursorProd) {ptr6376, tail6375};
            break;
        }

      case 8:
        {
            SymTy val6377 = *(SymTy *) tail6340;
            CursorTy tail6378 = tail6340 + sizeof(SymTy);
            PtrCursorProd tmp_struct265 =  _unpack_Expr(tail6378);
            PtrTy ptr6379 = tmp_struct265.field0;
            CursorTy tail6380 = tmp_struct265.field1;
            PtrTy ptr6381 = ALLOC(sizeof(TagSymCursorProd));

            ((TagSymCursorProd *) ptr6381)->field0 = tag6339;
            ((TagSymCursorProd *) ptr6381)->field1 = val6377;
            ((TagSymCursorProd *) ptr6381)->field2 = ptr6379;
            return (PtrCursorProd) {ptr6381, tail6380};
            break;
        }

      case 9:
        {
            PtrCursorProd tmp_struct266 =  _unpack_Datum(tail6340);
            PtrTy ptr6382 = tmp_struct266.field0;
            CursorTy tail6383 = tmp_struct266.field1;
            PtrTy ptr6384 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6384)->field0 = tag6339;
            ((TagCursorProd *) ptr6384)->field1 = ptr6382;
            return (PtrCursorProd) {ptr6384, tail6383};
            break;
        }

      case 10:
        {
            PtrCursorProd tmp_struct267 =  _unpack_Datum(tail6340);
            PtrTy ptr6385 = tmp_struct267.field0;
            CursorTy tail6386 = tmp_struct267.field1;
            PtrTy ptr6387 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6387)->field0 = tag6339;
            ((TagCursorProd *) ptr6387)->field1 = ptr6385;
            return (PtrCursorProd) {ptr6387, tail6386};
            break;
        }

      case 11:
        {
            PtrCursorProd tmp_struct268 =  _unpack_Datum(tail6340);
            PtrTy ptr6388 = tmp_struct268.field0;
            CursorTy tail6389 = tmp_struct268.field1;
            PtrTy ptr6390 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6390)->field0 = tag6339;
            ((TagCursorProd *) ptr6390)->field1 = ptr6388;
            return (PtrCursorProd) {ptr6390, tail6389};
            break;
        }

      case 12:
        {
            PtrCursorProd tmp_struct269 =  _unpack_Expr(tail6340);
            PtrTy ptr6391 = tmp_struct269.field0;
            CursorTy tail6392 = tmp_struct269.field1;
            PtrCursorProd tmp_struct270 =  _unpack_Expr(tail6392);
            PtrTy ptr6393 = tmp_struct270.field0;
            CursorTy tail6394 = tmp_struct270.field1;
            PtrCursorProd tmp_struct271 =  _unpack_Expr(tail6394);
            PtrTy ptr6395 = tmp_struct271.field0;
            CursorTy tail6396 = tmp_struct271.field1;
            PtrTy ptr6397 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr6397)->field0 = tag6339;
            ((TagCursorCursorCursorProd *) ptr6397)->field1 = ptr6391;
            ((TagCursorCursorCursorProd *) ptr6397)->field2 = ptr6393;
            ((TagCursorCursorCursorProd *) ptr6397)->field3 = ptr6395;
            return (PtrCursorProd) {ptr6397, tail6396};
            break;
        }

      case 13:
        {
            PtrCursorProd tmp_struct272 =  _unpack_Expr(tail6340);
            PtrTy ptr6398 = tmp_struct272.field0;
            CursorTy tail6399 = tmp_struct272.field1;
            PtrCursorProd tmp_struct273 =  _unpack_ListExpr(tail6399);
            PtrTy ptr6400 = tmp_struct273.field0;
            CursorTy tail6401 = tmp_struct273.field1;
            PtrTy ptr6402 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6402)->field0 = tag6339;
            ((TagCursorCursorProd *) ptr6402)->field1 = ptr6398;
            ((TagCursorCursorProd *) ptr6402)->field2 = ptr6400;
            return (PtrCursorProd) {ptr6402, tail6401};
            break;
        }

      case 14:
        {
            SymTy val6403 = *(SymTy *) tail6340;
            CursorTy tail6404 = tail6340 + sizeof(SymTy);
            PtrTy ptr6405 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr6405)->field0 = tag6339;
            ((TagSymProd *) ptr6405)->field1 = val6403;
            return (PtrCursorProd) {ptr6405, tail6404};
            break;
        }

      case 15:
        {
            SymTy val6406 = *(SymTy *) tail6340;
            CursorTy tail6407 = tail6340 + sizeof(SymTy);
            PtrTy ptr6408 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr6408)->field0 = tag6339;
            ((TagSymProd *) ptr6408)->field1 = val6406;
            return (PtrCursorProd) {ptr6408, tail6407};
            break;
        }

      case 16:
        {
            SymTy val6409 = *(SymTy *) tail6340;
            CursorTy tail6410 = tail6340 + sizeof(SymTy);
            PtrTy ptr6411 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr6411)->field0 = tag6339;
            ((TagSymProd *) ptr6411)->field1 = val6409;
            return (PtrCursorProd) {ptr6411, tail6410};
            break;
        }

      case 17:
        {
            PtrTy ptr6412 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr6412)->field0 = tag6339;
            return (PtrCursorProd) {ptr6412, tail6340};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6718 = *(CursorTy *) tail6340;
            CursorTy tmpaftercur6719 = tail6340 + 8;
            TagTyPacked tagtmp6720 = *(TagTyPacked *) tmpcur6718;
            CursorTy tailtmp6721 = tmpcur6718 + 1;

            tag6339 = tagtmp6720;
            tail6340 = tailtmp6721;
            goto switch6413;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6718 = *(CursorTy *) tail6340;
            CursorTy tmpaftercur6719 = tail6340 + 8;
            TagTyPacked tagtmp6720 = *(TagTyPacked *) tmpcur6718;
            CursorTy tailtmp6721 = tmpcur6718 + 1;

            tag6339 = tagtmp6720;
            tail6340 = tailtmp6721;
            goto switch6413;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6413");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Toplvl(CursorTy p6414)
{
    TagTyPacked tag6415 = *(TagTyPacked *) p6414;
    CursorTy tail6416 = p6414 + 1;


  switch6433:
    ;
    switch (tag6415) {

      case 0:
        {
            PtrCursorProd tmp_struct274 =  _unpack_ListSym(tail6416);
            PtrTy ptr6417 = tmp_struct274.field0;
            CursorTy tail6418 = tmp_struct274.field1;
            PtrCursorProd tmp_struct275 =  _unpack_Expr(tail6418);
            PtrTy ptr6419 = tmp_struct275.field0;
            CursorTy tail6420 = tmp_struct275.field1;
            PtrTy ptr6421 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6421)->field0 = tag6415;
            ((TagCursorCursorProd *) ptr6421)->field1 = ptr6417;
            ((TagCursorCursorProd *) ptr6421)->field2 = ptr6419;
            return (PtrCursorProd) {ptr6421, tail6420};
            break;
        }

      case 1:
        {
            PtrCursorProd tmp_struct276 =  _unpack_ListSym(tail6416);
            PtrTy ptr6422 = tmp_struct276.field0;
            CursorTy tail6423 = tmp_struct276.field1;
            PtrCursorProd tmp_struct277 =  _unpack_Expr(tail6423);
            PtrTy ptr6424 = tmp_struct277.field0;
            CursorTy tail6425 = tmp_struct277.field1;
            PtrTy ptr6426 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr6426)->field0 = tag6415;
            ((TagCursorCursorProd *) ptr6426)->field1 = ptr6422;
            ((TagCursorCursorProd *) ptr6426)->field2 = ptr6424;
            return (PtrCursorProd) {ptr6426, tail6425};
            break;
        }

      case 2:
        {
            PtrCursorProd tmp_struct278 =  _unpack_ListToplvl(tail6416);
            PtrTy ptr6427 = tmp_struct278.field0;
            CursorTy tail6428 = tmp_struct278.field1;
            PtrTy ptr6429 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6429)->field0 = tag6415;
            ((TagCursorProd *) ptr6429)->field1 = ptr6427;
            return (PtrCursorProd) {ptr6429, tail6428};
            break;
        }

      case 3:
        {
            PtrCursorProd tmp_struct279 =  _unpack_Expr(tail6416);
            PtrTy ptr6430 = tmp_struct279.field0;
            CursorTy tail6431 = tmp_struct279.field1;
            PtrTy ptr6432 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr6432)->field0 = tag6415;
            ((TagCursorProd *) ptr6432)->field1 = ptr6430;
            return (PtrCursorProd) {ptr6432, tail6431};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6722 = *(CursorTy *) tail6416;
            CursorTy tmpaftercur6723 = tail6416 + 8;
            TagTyPacked tagtmp6724 = *(TagTyPacked *) tmpcur6722;
            CursorTy tailtmp6725 = tmpcur6722 + 1;

            tag6415 = tagtmp6724;
            tail6416 = tailtmp6725;
            goto switch6433;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6722 = *(CursorTy *) tail6416;
            CursorTy tmpaftercur6723 = tail6416 + 8;
            TagTyPacked tagtmp6724 = *(TagTyPacked *) tmpcur6722;
            CursorTy tailtmp6725 = tmpcur6722 + 1;

            tag6415 = tagtmp6724;
            tail6416 = tailtmp6725;
            goto switch6433;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6433");
            exit(1);
        }
    }
}
CursorTy _print_ListSym(CursorTy p6434)
{
    TagTyPacked tag6435 = *(TagTyPacked *) p6434;
    CursorTy tail6436 = p6434 + 1;


  switch6440:
    ;
    switch (tag6435) {

      case 0:
        {
            fputs("(CONSSYM ", stdout);

            SymTy val6437 = *(SymTy *) tail6436;
            CursorTy tail6438 = tail6436 + sizeof(SymTy);

            print_symbol(val6437);
            fputs(" ", stdout);

            CursorTy tail6439 =  _print_ListSym(tail6438);

            fputs(")", stdout);
            return tail6439;
            break;
        }

      case 1:
        {
            fputs("(NULLSYM ", stdout);
            fputs(")", stdout);
            return tail6436;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6726 = *(CursorTy *) tail6436;
            CursorTy tmpaftercur6727 = tail6436 + 8;
            TagTyPacked tagtmp6728 = *(TagTyPacked *) tmpcur6726;
            CursorTy tailtmp6729 = tmpcur6726 + 1;

            tag6435 = tagtmp6728;
            tail6436 = tailtmp6729;
            goto switch6440;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6726 = *(CursorTy *) tail6436;
            CursorTy tmpaftercur6727 = tail6436 + 8;
            TagTyPacked tagtmp6728 = *(TagTyPacked *) tmpcur6726;
            CursorTy tailtmp6729 = tmpcur6726 + 1;

            tag6435 = tagtmp6728;
            tail6436 = tailtmp6729;
            goto switch6440;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6440");
            exit(1);
        }
    }
}
CursorTy _print_ListExpr(CursorTy p6441)
{
    TagTyPacked tag6442 = *(TagTyPacked *) p6441;
    CursorTy tail6443 = p6441 + 1;


  switch6446:
    ;
    switch (tag6442) {

      case 0:
        {
            fputs("(CONSEXPR ", stdout);

            CursorTy tail6444 =  _print_Expr(tail6443);

            fputs(" ", stdout);

            CursorTy tail6445 =  _print_ListExpr(tail6444);

            fputs(")", stdout);
            return tail6445;
            break;
        }

      case 1:
        {
            fputs("(NULLEXPR ", stdout);
            fputs(")", stdout);
            return tail6443;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6730 = *(CursorTy *) tail6443;
            CursorTy tmpaftercur6731 = tail6443 + 8;
            TagTyPacked tagtmp6732 = *(TagTyPacked *) tmpcur6730;
            CursorTy tailtmp6733 = tmpcur6730 + 1;

            tag6442 = tagtmp6732;
            tail6443 = tailtmp6733;
            goto switch6446;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6730 = *(CursorTy *) tail6443;
            CursorTy tmpaftercur6731 = tail6443 + 8;
            TagTyPacked tagtmp6732 = *(TagTyPacked *) tmpcur6730;
            CursorTy tailtmp6733 = tmpcur6730 + 1;

            tag6442 = tagtmp6732;
            tail6443 = tailtmp6733;
            goto switch6446;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6446");
            exit(1);
        }
    }
}
CursorTy _print_ListToplvl(CursorTy p6447)
{
    TagTyPacked tag6448 = *(TagTyPacked *) p6447;
    CursorTy tail6449 = p6447 + 1;


  switch6461:
    ;
    switch (tag6448) {

      case 0:
        {
            fputs("(CONSTOPLVL ", stdout);

            CursorTy tail6450 =  _print_Toplvl(tail6449);

            fputs(" ", stdout);

            CursorTy tail6451 =  _print_ListToplvl(tail6450);

            fputs(")", stdout);
            return tail6451;
            break;
        }

      case 1:
        {
            fputs("(NULLTOPLVL ", stdout);
            fputs(")", stdout);
            return tail6449;
            break;
        }

      case 2:
        {
            fputs("(CONSTOPLVL^ ", stdout);

            CursorTy tail6452 = tail6449 + 8;
            CursorTy tail6453 =  _print_Toplvl(tail6452);

            fputs(" ", stdout);

            CursorTy tail6454 =  _print_ListToplvl(tail6453);

            fputs(")", stdout);
            return tail6454;
            break;
        }

      case 3:
        {
            fputs("(CONSTOPLVL* ", stdout);

            IntTy val6455 = *(IntTy *) tail6449;
            CursorTy tail6456 = tail6449 + sizeof(IntTy);

            printf("%lld", val6455);
            fputs(" ", stdout);

            IntTy val6457 = *(IntTy *) tail6456;
            CursorTy tail6458 = tail6456 + sizeof(IntTy);

            printf("%lld", val6457);
            fputs(" ", stdout);

            CursorTy tail6459 =  _print_Toplvl(tail6458);

            fputs(" ", stdout);

            CursorTy tail6460 =  _print_ListToplvl(tail6459);

            fputs(")", stdout);
            return tail6460;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6734 = *(CursorTy *) tail6449;
            CursorTy tmpaftercur6735 = tail6449 + 8;
            TagTyPacked tagtmp6736 = *(TagTyPacked *) tmpcur6734;
            CursorTy tailtmp6737 = tmpcur6734 + 1;

            tag6448 = tagtmp6736;
            tail6449 = tailtmp6737;
            goto switch6461;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6734 = *(CursorTy *) tail6449;
            CursorTy tmpaftercur6735 = tail6449 + 8;
            TagTyPacked tagtmp6736 = *(TagTyPacked *) tmpcur6734;
            CursorTy tailtmp6737 = tmpcur6734 + 1;

            tag6448 = tagtmp6736;
            tail6449 = tailtmp6737;
            goto switch6461;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6461");
            exit(1);
        }
    }
}
CursorTy _print_Formals(CursorTy p6462)
{
    TagTyPacked tag6463 = *(TagTyPacked *) p6462;
    CursorTy tail6464 = p6462 + 1;


  switch6471:
    ;
    switch (tag6463) {

      case 0:
        {
            fputs("(F1 ", stdout);

            CursorTy tail6465 =  _print_ListSym(tail6464);

            fputs(")", stdout);
            return tail6465;
            break;
        }

      case 1:
        {
            fputs("(F2 ", stdout);

            CursorTy tail6466 =  _print_ListSym(tail6464);

            fputs(" ", stdout);

            SymTy val6467 = *(SymTy *) tail6466;
            CursorTy tail6468 = tail6466 + sizeof(SymTy);

            print_symbol(val6467);
            fputs(")", stdout);
            return tail6468;
            break;
        }

      case 2:
        {
            fputs("(F3 ", stdout);

            SymTy val6469 = *(SymTy *) tail6464;
            CursorTy tail6470 = tail6464 + sizeof(SymTy);

            print_symbol(val6469);
            fputs(")", stdout);
            return tail6470;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6738 = *(CursorTy *) tail6464;
            CursorTy tmpaftercur6739 = tail6464 + 8;
            TagTyPacked tagtmp6740 = *(TagTyPacked *) tmpcur6738;
            CursorTy tailtmp6741 = tmpcur6738 + 1;

            tag6463 = tagtmp6740;
            tail6464 = tailtmp6741;
            goto switch6471;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6738 = *(CursorTy *) tail6464;
            CursorTy tmpaftercur6739 = tail6464 + 8;
            TagTyPacked tagtmp6740 = *(TagTyPacked *) tmpcur6738;
            CursorTy tailtmp6741 = tmpcur6738 + 1;

            tag6463 = tagtmp6740;
            tail6464 = tailtmp6741;
            goto switch6471;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6471");
            exit(1);
        }
    }
}
CursorTy _print_Datum(CursorTy p6472)
{
    TagTyPacked tag6473 = *(TagTyPacked *) p6472;
    CursorTy tail6474 = p6472 + 1;


  switch6477:
    ;
    switch (tag6473) {

      case 0:
        {
            fputs("(INTLIT ", stdout);

            IntTy val6475 = *(IntTy *) tail6474;
            CursorTy tail6476 = tail6474 + sizeof(IntTy);

            printf("%lld", val6475);
            fputs(")", stdout);
            return tail6476;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6742 = *(CursorTy *) tail6474;
            CursorTy tmpaftercur6743 = tail6474 + 8;
            TagTyPacked tagtmp6744 = *(TagTyPacked *) tmpcur6742;
            CursorTy tailtmp6745 = tmpcur6742 + 1;

            tag6473 = tagtmp6744;
            tail6474 = tailtmp6745;
            goto switch6477;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6742 = *(CursorTy *) tail6474;
            CursorTy tmpaftercur6743 = tail6474 + 8;
            TagTyPacked tagtmp6744 = *(TagTyPacked *) tmpcur6742;
            CursorTy tailtmp6745 = tmpcur6742 + 1;

            tag6473 = tagtmp6744;
            tail6474 = tailtmp6745;
            goto switch6477;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6477");
            exit(1);
        }
    }
}
CursorTy _print_LAMBDACASE(CursorTy p6478)
{
    TagTyPacked tag6479 = *(TagTyPacked *) p6478;
    CursorTy tail6480 = p6478 + 1;


  switch6484:
    ;
    switch (tag6479) {

      case 0:
        {
            fputs("(CONSLAMBDACASE ", stdout);

            CursorTy tail6481 =  _print_Formals(tail6480);

            fputs(" ", stdout);

            CursorTy tail6482 =  _print_ListExpr(tail6481);

            fputs(" ", stdout);

            CursorTy tail6483 =  _print_LAMBDACASE(tail6482);

            fputs(")", stdout);
            return tail6483;
            break;
        }

      case 1:
        {
            fputs("(NULLLAMBDACASE ", stdout);
            fputs(")", stdout);
            return tail6480;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6746 = *(CursorTy *) tail6480;
            CursorTy tmpaftercur6747 = tail6480 + 8;
            TagTyPacked tagtmp6748 = *(TagTyPacked *) tmpcur6746;
            CursorTy tailtmp6749 = tmpcur6746 + 1;

            tag6479 = tagtmp6748;
            tail6480 = tailtmp6749;
            goto switch6484;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6746 = *(CursorTy *) tail6480;
            CursorTy tmpaftercur6747 = tail6480 + 8;
            TagTyPacked tagtmp6748 = *(TagTyPacked *) tmpcur6746;
            CursorTy tailtmp6749 = tmpcur6746 + 1;

            tag6479 = tagtmp6748;
            tail6480 = tailtmp6749;
            goto switch6484;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6484");
            exit(1);
        }
    }
}
CursorTy _print_LVBIND(CursorTy p6485)
{
    TagTyPacked tag6486 = *(TagTyPacked *) p6485;
    CursorTy tail6487 = p6485 + 1;


  switch6491:
    ;
    switch (tag6486) {

      case 0:
        {
            fputs("(CONSLVBIND ", stdout);

            CursorTy tail6488 =  _print_ListSym(tail6487);

            fputs(" ", stdout);

            CursorTy tail6489 =  _print_Expr(tail6488);

            fputs(" ", stdout);

            CursorTy tail6490 =  _print_LVBIND(tail6489);

            fputs(")", stdout);
            return tail6490;
            break;
        }

      case 1:
        {
            fputs("(NULLLVBIND ", stdout);
            fputs(")", stdout);
            return tail6487;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6750 = *(CursorTy *) tail6487;
            CursorTy tmpaftercur6751 = tail6487 + 8;
            TagTyPacked tagtmp6752 = *(TagTyPacked *) tmpcur6750;
            CursorTy tailtmp6753 = tmpcur6750 + 1;

            tag6486 = tagtmp6752;
            tail6487 = tailtmp6753;
            goto switch6491;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6750 = *(CursorTy *) tail6487;
            CursorTy tmpaftercur6751 = tail6487 + 8;
            TagTyPacked tagtmp6752 = *(TagTyPacked *) tmpcur6750;
            CursorTy tailtmp6753 = tmpcur6750 + 1;

            tag6486 = tagtmp6752;
            tail6487 = tailtmp6753;
            goto switch6491;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6491");
            exit(1);
        }
    }
}
CursorTy _print_Expr(CursorTy p6492)
{
    TagTyPacked tag6493 = *(TagTyPacked *) p6492;
    CursorTy tail6494 = p6492 + 1;


  switch6527:
    ;
    switch (tag6493) {

      case 0:
        {
            fputs("(VARREF ", stdout);

            SymTy val6495 = *(SymTy *) tail6494;
            CursorTy tail6496 = tail6494 + sizeof(SymTy);

            print_symbol(val6495);
            fputs(")", stdout);
            return tail6496;
            break;
        }

      case 1:
        {
            fputs("(Lambda ", stdout);

            CursorTy tail6497 =  _print_Formals(tail6494);

            fputs(" ", stdout);

            CursorTy tail6498 =  _print_ListExpr(tail6497);

            fputs(")", stdout);
            return tail6498;
            break;
        }

      case 2:
        {
            fputs("(CaseLambda ", stdout);

            CursorTy tail6499 =  _print_LAMBDACASE(tail6494);

            fputs(")", stdout);
            return tail6499;
            break;
        }

      case 3:
        {
            fputs("(If ", stdout);

            CursorTy tail6500 =  _print_Expr(tail6494);

            fputs(" ", stdout);

            CursorTy tail6501 =  _print_Expr(tail6500);

            fputs(" ", stdout);

            CursorTy tail6502 =  _print_Expr(tail6501);

            fputs(")", stdout);
            return tail6502;
            break;
        }

      case 4:
        {
            fputs("(Begin ", stdout);

            CursorTy tail6503 =  _print_ListExpr(tail6494);

            fputs(")", stdout);
            return tail6503;
            break;
        }

      case 5:
        {
            fputs("(Begin0 ", stdout);

            CursorTy tail6504 =  _print_Expr(tail6494);

            fputs(" ", stdout);

            CursorTy tail6505 =  _print_ListExpr(tail6504);

            fputs(")", stdout);
            return tail6505;
            break;
        }

      case 6:
        {
            fputs("(LetValues ", stdout);

            CursorTy tail6506 =  _print_LVBIND(tail6494);

            fputs(" ", stdout);

            CursorTy tail6507 =  _print_ListExpr(tail6506);

            fputs(")", stdout);
            return tail6507;
            break;
        }

      case 7:
        {
            fputs("(LetrecValues ", stdout);

            CursorTy tail6508 =  _print_LVBIND(tail6494);

            fputs(" ", stdout);

            CursorTy tail6509 =  _print_ListExpr(tail6508);

            fputs(")", stdout);
            return tail6509;
            break;
        }

      case 8:
        {
            fputs("(SetBang ", stdout);

            SymTy val6510 = *(SymTy *) tail6494;
            CursorTy tail6511 = tail6494 + sizeof(SymTy);

            print_symbol(val6510);
            fputs(" ", stdout);

            CursorTy tail6512 =  _print_Expr(tail6511);

            fputs(")", stdout);
            return tail6512;
            break;
        }

      case 9:
        {
            fputs("(Quote ", stdout);

            CursorTy tail6513 =  _print_Datum(tail6494);

            fputs(")", stdout);
            return tail6513;
            break;
        }

      case 10:
        {
            fputs("(QuoteSyntax ", stdout);

            CursorTy tail6514 =  _print_Datum(tail6494);

            fputs(")", stdout);
            return tail6514;
            break;
        }

      case 11:
        {
            fputs("(QuoteSyntaxLocal ", stdout);

            CursorTy tail6515 =  _print_Datum(tail6494);

            fputs(")", stdout);
            return tail6515;
            break;
        }

      case 12:
        {
            fputs("(WithContinuationMark ", stdout);

            CursorTy tail6516 =  _print_Expr(tail6494);

            fputs(" ", stdout);

            CursorTy tail6517 =  _print_Expr(tail6516);

            fputs(" ", stdout);

            CursorTy tail6518 =  _print_Expr(tail6517);

            fputs(")", stdout);
            return tail6518;
            break;
        }

      case 13:
        {
            fputs("(App ", stdout);

            CursorTy tail6519 =  _print_Expr(tail6494);

            fputs(" ", stdout);

            CursorTy tail6520 =  _print_ListExpr(tail6519);

            fputs(")", stdout);
            return tail6520;
            break;
        }

      case 14:
        {
            fputs("(Top ", stdout);

            SymTy val6521 = *(SymTy *) tail6494;
            CursorTy tail6522 = tail6494 + sizeof(SymTy);

            print_symbol(val6521);
            fputs(")", stdout);
            return tail6522;
            break;
        }

      case 15:
        {
            fputs("(VariableReference ", stdout);

            SymTy val6523 = *(SymTy *) tail6494;
            CursorTy tail6524 = tail6494 + sizeof(SymTy);

            print_symbol(val6523);
            fputs(")", stdout);
            return tail6524;
            break;
        }

      case 16:
        {
            fputs("(VariableReferenceTop ", stdout);

            SymTy val6525 = *(SymTy *) tail6494;
            CursorTy tail6526 = tail6494 + sizeof(SymTy);

            print_symbol(val6525);
            fputs(")", stdout);
            return tail6526;
            break;
        }

      case 17:
        {
            fputs("(VariableReferenceNull ", stdout);
            fputs(")", stdout);
            return tail6494;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6754 = *(CursorTy *) tail6494;
            CursorTy tmpaftercur6755 = tail6494 + 8;
            TagTyPacked tagtmp6756 = *(TagTyPacked *) tmpcur6754;
            CursorTy tailtmp6757 = tmpcur6754 + 1;

            tag6493 = tagtmp6756;
            tail6494 = tailtmp6757;
            goto switch6527;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6754 = *(CursorTy *) tail6494;
            CursorTy tmpaftercur6755 = tail6494 + 8;
            TagTyPacked tagtmp6756 = *(TagTyPacked *) tmpcur6754;
            CursorTy tailtmp6757 = tmpcur6754 + 1;

            tag6493 = tagtmp6756;
            tail6494 = tailtmp6757;
            goto switch6527;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6527");
            exit(1);
        }
    }
}
CursorTy _print_Toplvl(CursorTy p6528)
{
    TagTyPacked tag6529 = *(TagTyPacked *) p6528;
    CursorTy tail6530 = p6528 + 1;


  switch6537:
    ;
    switch (tag6529) {

      case 0:
        {
            fputs("(DefineValues ", stdout);

            CursorTy tail6531 =  _print_ListSym(tail6530);

            fputs(" ", stdout);

            CursorTy tail6532 =  _print_Expr(tail6531);

            fputs(")", stdout);
            return tail6532;
            break;
        }

      case 1:
        {
            fputs("(DefineSyntaxes ", stdout);

            CursorTy tail6533 =  _print_ListSym(tail6530);

            fputs(" ", stdout);

            CursorTy tail6534 =  _print_Expr(tail6533);

            fputs(")", stdout);
            return tail6534;
            break;
        }

      case 2:
        {
            fputs("(BeginTop ", stdout);

            CursorTy tail6535 =  _print_ListToplvl(tail6530);

            fputs(")", stdout);
            return tail6535;
            break;
        }

      case 3:
        {
            fputs("(Expression ", stdout);

            CursorTy tail6536 =  _print_Expr(tail6530);

            fputs(")", stdout);
            return tail6536;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur6758 = *(CursorTy *) tail6530;
            CursorTy tmpaftercur6759 = tail6530 + 8;
            TagTyPacked tagtmp6760 = *(TagTyPacked *) tmpcur6758;
            CursorTy tailtmp6761 = tmpcur6758 + 1;

            tag6529 = tagtmp6760;
            tail6530 = tailtmp6761;
            goto switch6537;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur6758 = *(CursorTy *) tail6530;
            CursorTy tmpaftercur6759 = tail6530 + 8;
            TagTyPacked tagtmp6760 = *(TagTyPacked *) tmpcur6758;
            CursorTy tailtmp6761 = tmpcur6758 + 1;

            tag6529 = tagtmp6760;
            tail6530 = tailtmp6761;
            goto switch6537;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch6537");
            exit(1);
        }
    }
}
void __main_expr()
{
    IntTy timed4368;
    UT_array *times282;

    utarray_new(times282, &double_icd);

    struct timespec begin_timed4368;
    struct timespec end_timed4368;


    int fd = open(read_benchfile_param(), O_RDONLY);

    if (fd == -1) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    struct stat st;

    fstat(fd, &st);

    IntTy bnch_size = st.st_size;
    CursorTy ptr = (CursorTy) mmap(0, st.st_size, PROT_READ, MAP_PRIVATE,
                                   fd, 0);

    if (ptr == MAP_FAILED) {
        fprintf(stderr, "mmap failed\n");
        abort();
    }
    {
        int sum = 0;

        for (int i = 0; i < st.st_size; i++)
            sum += ptr[i];
    }

    CursorTy bnch = ptr;
    CursorTy r1936 = (CursorTy) bnch;
    IntTy sizeof_end_r19364861 = bnch_size;
    CursorTy end_r1936 = r1936 + sizeof_end_r19364861;

    CursorInt64Prod i = _traverse_Toplvl(end_r1936, r1936);

    for (long long iters_timed4368 = 0; iters_timed4368 < global_iters_param;
         iters_timed4368++) {
        if (iters_timed4368 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed4368);

        IntTy benchres =  par_countnodes(end_r1936, bnch);

        timed4368 = benchres;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed4368);
        if (iters_timed4368 != global_iters_param - 1)
            restore_alloc_state();

        double batchtime280 = difftimespecs(&begin_timed4368, &end_timed4368);

        utarray_push_back(times282, &batchtime280);
    }
    utarray_sort(times282, compare_doubles);

    double *tmp283 = (double *) utarray_eltptr(times282, global_iters_param / 2);
    double selftimed281 = *tmp283;

    print_timing_array(times282);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("SELFTIMED: %e\n", selftimed281);
    printf("%lld", timed4368);
    fputs("\n", stdout);
    free_symtable();
    return;
}
