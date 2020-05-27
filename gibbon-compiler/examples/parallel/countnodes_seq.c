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
typedef struct TagProd_struct {
            TagTyPacked field0;
        } TagProd;
typedef struct TagInt64Prod_struct {
            TagTyPacked field0;
            IntTy field1;
        } TagInt64Prod;
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
CursorInt64Prod formals(CursorTy end_r599, CursorTy f50);
CursorInt64Prod loopSyms(CursorTy end_r601, CursorTy ls55);
CursorInt64Prod datum(CursorTy end_r603, CursorTy d58);
CursorInt64Prod expr(CursorTy end_r605, CursorTy e60);
CursorInt64Prod top(CursorTy end_r607, CursorTy e88);
CursorInt64Prod loopLVBIND(CursorTy end_r609, CursorTy ls95);
CursorInt64Prod loopLambdaCase(CursorTy end_r611, CursorTy ls99);
CursorInt64Prod loopExpr(CursorTy end_r613, CursorTy ls103);
CursorInt64Prod loopTopLvl(CursorTy end_r615, CursorTy ls106);
CursorInt64Prod countnodes(CursorTy end_r617, CursorTy e0109);
CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r620, CursorTy end_r621,
                                           CursorTy loc619, CursorTy arg339);
CursorInt64Prod _traverse_ListSym(CursorTy end_r623, CursorTy arg344);
CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r626,
                                            CursorTy end_r627, CursorTy loc625,
                                            CursorTy arg349);
CursorInt64Prod _traverse_ListExpr(CursorTy end_r629, CursorTy arg354);
CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r632,
                                              CursorTy end_r633,
                                              CursorTy loc631, CursorTy arg359);
CursorInt64Prod _traverse_ListToplvl(CursorTy end_r635, CursorTy arg364);
CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r638, CursorTy end_r639,
                                           CursorTy loc637, CursorTy arg369);
CursorInt64Prod _traverse_Formals(CursorTy end_r641, CursorTy arg378);
CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r644, CursorTy end_r645,
                                         CursorTy loc643, CursorTy arg387);
CursorInt64Prod _traverse_Datum(CursorTy end_r647, CursorTy arg390);
CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r650,
                                              CursorTy end_r651,
                                              CursorTy loc649, CursorTy arg393);
CursorInt64Prod _traverse_LAMBDACASE(CursorTy end_r653, CursorTy arg400);
CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r656, CursorTy end_r657,
                                          CursorTy loc655, CursorTy arg407);
CursorInt64Prod _traverse_LVBIND(CursorTy end_r659, CursorTy arg414);
CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r662, CursorTy end_r663,
                                        CursorTy loc661, CursorTy arg421);
CursorInt64Prod _traverse_Expr(CursorTy end_r665, CursorTy arg476);
CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r668, CursorTy end_r669,
                                          CursorTy loc667, CursorTy arg531);
CursorInt64Prod _traverse_Toplvl(CursorTy end_r671, CursorTy arg544);
PtrCursorProd _unpack_ListSym(CursorTy p3127);
PtrCursorProd _unpack_ListExpr(CursorTy p3137);
PtrCursorProd _unpack_ListToplvl(CursorTy p3147);
PtrCursorProd _unpack_Formals(CursorTy p3157);
PtrCursorProd _unpack_Datum(CursorTy p3172);
PtrCursorProd _unpack_LAMBDACASE(CursorTy p3179);
PtrCursorProd _unpack_LVBIND(CursorTy p3191);
PtrCursorProd _unpack_Expr(CursorTy p3203);
PtrCursorProd _unpack_Toplvl(CursorTy p3279);
CursorTy _print_ListSym(CursorTy p3299);
CursorTy _print_ListExpr(CursorTy p3306);
CursorTy _print_ListToplvl(CursorTy p3312);
CursorTy _print_Formals(CursorTy p3318);
CursorTy _print_Datum(CursorTy p3328);
CursorTy _print_LAMBDACASE(CursorTy p3334);
CursorTy _print_LVBIND(CursorTy p3341);
CursorTy _print_Expr(CursorTy p3348);
CursorTy _print_Toplvl(CursorTy p3384);
CursorInt64Prod formals(CursorTy end_r599, CursorTy f50)
{
    CursorTy loc598 = (CursorTy) f50;
    TagTyPacked tmpval2354 = *(TagTyPacked *) f50;
    CursorTy tmpcur2355 = f50 + 1;


  switch2364:
    ;
    switch (tmpval2354) {

      case 0:
        {
            CursorTy field_cur1614 = (CursorTy) tmpcur2355;
            CursorTy case679 = (CursorTy) field_cur1614;
            CursorTy ls51 = (CursorTy) case679;
            CursorInt64Prod tmp_struct0 =  loopSyms(end_r599, ls51);
            CursorTy pvrtmp2356 = tmp_struct0.field0;
            IntTy pvrtmp2357 = tmp_struct0.field1;
            CursorTy endof1294 = (CursorTy) pvrtmp2356;
            IntTy fltPrm278 = (IntTy) pvrtmp2357;
            IntTy tailprim1295 = 1 + fltPrm278;

            return (CursorInt64Prod) {endof1294, tailprim1295};
            break;
        }

      case 1:
        {
            CursorTy field_cur1616 = (CursorTy) tmpcur2355;
            CursorTy case682 = (CursorTy) field_cur1616;
            CursorTy ls52 = (CursorTy) case682;
            CursorInt64Prod tmp_struct1 =  loopSyms(end_r599, ls52);
            CursorTy pvrtmp2358 = tmp_struct1.field0;
            IntTy pvrtmp2359 = tmp_struct1.field1;
            CursorTy endof1297 = (CursorTy) pvrtmp2358;
            IntTy fltPrm280 = (IntTy) pvrtmp2359;
            CursorTy case683 = (CursorTy) endof1297;
            CursorTy jump1296 = case683 + 8;
            SymTy tmpval2360 = *(SymTy *) case683;
            CursorTy tmpcur2361 = case683 + sizeof(SymTy);
            SymTy s53 = (SymTy) tmpval2360;
            CursorTy end_s53 = (CursorTy) tmpcur2361;
            IntTy fltPrm279 = fltPrm280 + 0;
            IntTy tailprim1298 = 1 + fltPrm279;

            return (CursorInt64Prod) {jump1296, tailprim1298};
            break;
        }

      case 2:
        {
            CursorTy field_cur1619 = (CursorTy) tmpcur2355;
            CursorTy case686 = (CursorTy) field_cur1619;
            SymTy tmpval2362 = *(SymTy *) case686;
            CursorTy tmpcur2363 = case686 + sizeof(SymTy);
            SymTy s54 = (SymTy) tmpval2362;
            CursorTy end_s54 = (CursorTy) tmpcur2363;
            CursorTy jump1299 = case686 + 8;
            IntTy tailprim1300 = 1 + 0;

            return (CursorInt64Prod) {jump1299, tailprim1300};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3394 = *(CursorTy *) tmpcur2355;
            CursorTy tmpaftercur3395 = tmpcur2355 + 8;
            TagTyPacked tagtmp3396 = *(TagTyPacked *) tmpcur3394;
            CursorTy tailtmp3397 = tmpcur3394 + 1;

            tmpval2354 = tagtmp3396;
            tmpcur2355 = tailtmp3397;
            goto switch2364;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3394 = *(CursorTy *) tmpcur2355;
            CursorTy tmpaftercur3395 = tmpcur2355 + 8;
            TagTyPacked tagtmp3396 = *(TagTyPacked *) tmpcur3394;
            CursorTy tailtmp3397 = tmpcur3394 + 1;

            tmpval2354 = tagtmp3396;
            tmpcur2355 = tailtmp3397;
            goto switch2364;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2354");
            exit(1);
        }
    }
}
CursorInt64Prod loopSyms(CursorTy end_r601, CursorTy ls55)
{
    CursorTy loc600 = (CursorTy) ls55;
    TagTyPacked tmpval2365 = *(TagTyPacked *) ls55;
    CursorTy tmpcur2366 = ls55 + 1;


  switch2371:
    ;
    switch (tmpval2365) {

      case 0:
        {
            CursorTy field_cur1621 = (CursorTy) tmpcur2366;
            CursorTy case689 = (CursorTy) field_cur1621;
            SymTy tmpval2367 = *(SymTy *) case689;
            CursorTy tmpcur2368 = case689 + sizeof(SymTy);
            SymTy s56 = (SymTy) tmpval2367;
            CursorTy end_s56 = (CursorTy) tmpcur2368;
            CursorTy case690 = (CursorTy) end_s56;
            CursorTy ls57 = (CursorTy) case690;
            CursorTy jump1301 = case689 + 8;
            CursorInt64Prod tmp_struct2 =  loopSyms(end_r601, ls57);
            CursorTy pvrtmp2369 = tmp_struct2.field0;
            IntTy pvrtmp2370 = tmp_struct2.field1;
            CursorTy endof1302 = (CursorTy) pvrtmp2369;
            IntTy fltPrm282 = (IntTy) pvrtmp2370;
            IntTy fltPrm281 = 0 + fltPrm282;
            IntTy tailprim1303 = 1 + fltPrm281;

            return (CursorInt64Prod) {endof1302, tailprim1303};
            break;
        }

      case 1:
        {
            CursorTy field_cur1624 = (CursorTy) tmpcur2366;
            CursorTy jump1304 = loc600 + 1;
            IntTy fltLitTail1305 = (IntTy) 1;

            return (CursorInt64Prod) {jump1304, fltLitTail1305};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3398 = *(CursorTy *) tmpcur2366;
            CursorTy tmpaftercur3399 = tmpcur2366 + 8;
            TagTyPacked tagtmp3400 = *(TagTyPacked *) tmpcur3398;
            CursorTy tailtmp3401 = tmpcur3398 + 1;

            tmpval2365 = tagtmp3400;
            tmpcur2366 = tailtmp3401;
            goto switch2371;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3398 = *(CursorTy *) tmpcur2366;
            CursorTy tmpaftercur3399 = tmpcur2366 + 8;
            TagTyPacked tagtmp3400 = *(TagTyPacked *) tmpcur3398;
            CursorTy tailtmp3401 = tmpcur3398 + 1;

            tmpval2365 = tagtmp3400;
            tmpcur2366 = tailtmp3401;
            goto switch2371;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2365");
            exit(1);
        }
    }
}
CursorInt64Prod datum(CursorTy end_r603, CursorTy d58)
{
    CursorTy loc602 = (CursorTy) d58;
    TagTyPacked tmpval2372 = *(TagTyPacked *) d58;
    CursorTy tmpcur2373 = d58 + 1;


  switch2376:
    ;
    switch (tmpval2372) {

      case 0:
        {
            CursorTy field_cur1625 = (CursorTy) tmpcur2373;
            CursorTy case695 = (CursorTy) field_cur1625;
            IntTy tmpval2374 = *(IntTy *) case695;
            CursorTy tmpcur2375 = case695 + sizeof(IntTy);
            IntTy i59 = (IntTy) tmpval2374;
            CursorTy end_i59 = (CursorTy) tmpcur2375;
            CursorTy jump1306 = case695 + 8;
            IntTy tailprim1307 = 1 + 0;

            return (CursorInt64Prod) {jump1306, tailprim1307};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3402 = *(CursorTy *) tmpcur2373;
            CursorTy tmpaftercur3403 = tmpcur2373 + 8;
            TagTyPacked tagtmp3404 = *(TagTyPacked *) tmpcur3402;
            CursorTy tailtmp3405 = tmpcur3402 + 1;

            tmpval2372 = tagtmp3404;
            tmpcur2373 = tailtmp3405;
            goto switch2376;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3402 = *(CursorTy *) tmpcur2373;
            CursorTy tmpaftercur3403 = tmpcur2373 + 8;
            TagTyPacked tagtmp3404 = *(TagTyPacked *) tmpcur3402;
            CursorTy tailtmp3405 = tmpcur3402 + 1;

            tmpval2372 = tagtmp3404;
            tmpcur2373 = tailtmp3405;
            goto switch2376;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2372");
            exit(1);
        }
    }
}
CursorInt64Prod expr(CursorTy end_r605, CursorTy e60)
{
    CursorTy loc604 = (CursorTy) e60;
    TagTyPacked tmpval2377 = *(TagTyPacked *) e60;
    CursorTy tmpcur2378 = e60 + 1;


  switch2433:
    ;
    switch (tmpval2377) {

      case 0:
        {
            CursorTy field_cur1627 = (CursorTy) tmpcur2378;
            CursorTy case698 = (CursorTy) field_cur1627;
            SymTy tmpval2379 = *(SymTy *) case698;
            CursorTy tmpcur2380 = case698 + sizeof(SymTy);
            SymTy s61 = (SymTy) tmpval2379;
            CursorTy end_s61 = (CursorTy) tmpcur2380;
            CursorTy jump1308 = case698 + 8;
            IntTy tailprim1309 = 1 + 0;

            return (CursorInt64Prod) {jump1308, tailprim1309};
            break;
        }

      case 14:
        {
            CursorTy field_cur1629 = (CursorTy) tmpcur2378;
            CursorTy case699 = (CursorTy) field_cur1629;
            SymTy tmpval2381 = *(SymTy *) case699;
            CursorTy tmpcur2382 = case699 + sizeof(SymTy);
            SymTy s62 = (SymTy) tmpval2381;
            CursorTy end_s62 = (CursorTy) tmpcur2382;
            CursorTy jump1310 = case699 + 8;
            IntTy tailprim1311 = 1 + 0;

            return (CursorInt64Prod) {jump1310, tailprim1311};
            break;
        }

      case 15:
        {
            CursorTy field_cur1631 = (CursorTy) tmpcur2378;
            CursorTy case700 = (CursorTy) field_cur1631;
            SymTy tmpval2383 = *(SymTy *) case700;
            CursorTy tmpcur2384 = case700 + sizeof(SymTy);
            SymTy s63 = (SymTy) tmpval2383;
            CursorTy end_s63 = (CursorTy) tmpcur2384;
            CursorTy jump1312 = case700 + 8;
            IntTy tailprim1313 = 1 + 0;

            return (CursorInt64Prod) {jump1312, tailprim1313};
            break;
        }

      case 16:
        {
            CursorTy field_cur1633 = (CursorTy) tmpcur2378;
            CursorTy case701 = (CursorTy) field_cur1633;
            SymTy tmpval2385 = *(SymTy *) case701;
            CursorTy tmpcur2386 = case701 + sizeof(SymTy);
            SymTy s64 = (SymTy) tmpval2385;
            CursorTy end_s64 = (CursorTy) tmpcur2386;
            CursorTy jump1314 = case701 + 8;
            IntTy tailprim1315 = 1 + 0;

            return (CursorInt64Prod) {jump1314, tailprim1315};
            break;
        }

      case 17:
        {
            CursorTy field_cur1635 = (CursorTy) tmpcur2378;
            CursorTy jump1316 = loc604 + 1;
            IntTy fltLitTail1317 = (IntTy) 1;

            return (CursorInt64Prod) {jump1316, fltLitTail1317};
            break;
        }

      case 9:
        {
            CursorTy field_cur1636 = (CursorTy) tmpcur2378;
            CursorTy case702 = (CursorTy) field_cur1636;
            CursorTy d65 = (CursorTy) case702;
            CursorInt64Prod tmp_struct3 =  datum(end_r605, d65);
            CursorTy pvrtmp2387 = tmp_struct3.field0;
            IntTy pvrtmp2388 = tmp_struct3.field1;
            CursorTy endof1318 = (CursorTy) pvrtmp2387;
            IntTy fltPrm283 = (IntTy) pvrtmp2388;
            IntTy tailprim1319 = 1 + fltPrm283;

            return (CursorInt64Prod) {endof1318, tailprim1319};
            break;
        }

      case 10:
        {
            CursorTy field_cur1638 = (CursorTy) tmpcur2378;
            CursorTy case705 = (CursorTy) field_cur1638;
            CursorTy d66 = (CursorTy) case705;
            CursorInt64Prod tmp_struct4 =  datum(end_r605, d66);
            CursorTy pvrtmp2389 = tmp_struct4.field0;
            IntTy pvrtmp2390 = tmp_struct4.field1;
            CursorTy endof1320 = (CursorTy) pvrtmp2389;
            IntTy fltPrm284 = (IntTy) pvrtmp2390;
            IntTy tailprim1321 = 1 + fltPrm284;

            return (CursorInt64Prod) {endof1320, tailprim1321};
            break;
        }

      case 11:
        {
            CursorTy field_cur1640 = (CursorTy) tmpcur2378;
            CursorTy case708 = (CursorTy) field_cur1640;
            CursorTy d67 = (CursorTy) case708;
            CursorInt64Prod tmp_struct5 =  datum(end_r605, d67);
            CursorTy pvrtmp2391 = tmp_struct5.field0;
            IntTy pvrtmp2392 = tmp_struct5.field1;
            CursorTy endof1322 = (CursorTy) pvrtmp2391;
            IntTy fltPrm285 = (IntTy) pvrtmp2392;
            IntTy tailprim1323 = 1 + fltPrm285;

            return (CursorInt64Prod) {endof1322, tailprim1323};
            break;
        }

      case 1:
        {
            CursorTy field_cur1642 = (CursorTy) tmpcur2378;
            CursorTy case711 = (CursorTy) field_cur1642;
            CursorTy f68 = (CursorTy) case711;
            CursorInt64Prod tmp_struct6 =  formals(end_r605, f68);
            CursorTy pvrtmp2393 = tmp_struct6.field0;
            IntTy pvrtmp2394 = tmp_struct6.field1;
            CursorTy endof1324 = (CursorTy) pvrtmp2393;
            IntTy fltPrm287 = (IntTy) pvrtmp2394;
            CursorTy case712 = (CursorTy) endof1324;
            CursorTy lse69 = (CursorTy) case712;
            CursorInt64Prod tmp_struct7 =  loopExpr(end_r605, lse69);
            CursorTy pvrtmp2395 = tmp_struct7.field0;
            IntTy pvrtmp2396 = tmp_struct7.field1;
            CursorTy endof1325 = (CursorTy) pvrtmp2395;
            IntTy fltPrm288 = (IntTy) pvrtmp2396;
            IntTy fltPrm286 = fltPrm287 + fltPrm288;
            IntTy tailprim1326 = 1 + fltPrm286;

            return (CursorInt64Prod) {endof1325, tailprim1326};
            break;
        }

      case 2:
        {
            CursorTy field_cur1645 = (CursorTy) tmpcur2378;
            CursorTy case717 = (CursorTy) field_cur1645;
            CursorTy cases70 = (CursorTy) case717;
            CursorInt64Prod tmp_struct8 =  loopLambdaCase(end_r605, cases70);
            CursorTy pvrtmp2397 = tmp_struct8.field0;
            IntTy pvrtmp2398 = tmp_struct8.field1;
            CursorTy endof1327 = (CursorTy) pvrtmp2397;
            IntTy fltPrm289 = (IntTy) pvrtmp2398;
            IntTy tailprim1328 = 1 + fltPrm289;

            return (CursorInt64Prod) {endof1327, tailprim1328};
            break;
        }

      case 6:
        {
            CursorTy field_cur1647 = (CursorTy) tmpcur2378;
            CursorTy case720 = (CursorTy) field_cur1647;
            CursorTy binds71 = (CursorTy) case720;
            CursorInt64Prod tmp_struct9 =  loopLVBIND(end_r605, binds71);
            CursorTy pvrtmp2399 = tmp_struct9.field0;
            IntTy pvrtmp2400 = tmp_struct9.field1;
            CursorTy endof1329 = (CursorTy) pvrtmp2399;
            IntTy fltPrm291 = (IntTy) pvrtmp2400;
            CursorTy case721 = (CursorTy) endof1329;
            CursorTy body72 = (CursorTy) case721;
            CursorInt64Prod tmp_struct10 =  loopExpr(end_r605, body72);
            CursorTy pvrtmp2401 = tmp_struct10.field0;
            IntTy pvrtmp2402 = tmp_struct10.field1;
            CursorTy endof1330 = (CursorTy) pvrtmp2401;
            IntTy fltPrm292 = (IntTy) pvrtmp2402;
            IntTy fltPrm290 = fltPrm291 + fltPrm292;
            IntTy tailprim1331 = 1 + fltPrm290;

            return (CursorInt64Prod) {endof1330, tailprim1331};
            break;
        }

      case 7:
        {
            CursorTy field_cur1650 = (CursorTy) tmpcur2378;
            CursorTy case726 = (CursorTy) field_cur1650;
            CursorTy binds73 = (CursorTy) case726;
            CursorInt64Prod tmp_struct11 =  loopLVBIND(end_r605, binds73);
            CursorTy pvrtmp2403 = tmp_struct11.field0;
            IntTy pvrtmp2404 = tmp_struct11.field1;
            CursorTy endof1332 = (CursorTy) pvrtmp2403;
            IntTy fltPrm294 = (IntTy) pvrtmp2404;
            CursorTy case727 = (CursorTy) endof1332;
            CursorTy body74 = (CursorTy) case727;
            CursorInt64Prod tmp_struct12 =  loopExpr(end_r605, body74);
            CursorTy pvrtmp2405 = tmp_struct12.field0;
            IntTy pvrtmp2406 = tmp_struct12.field1;
            CursorTy endof1333 = (CursorTy) pvrtmp2405;
            IntTy fltPrm295 = (IntTy) pvrtmp2406;
            IntTy fltPrm293 = fltPrm294 + fltPrm295;
            IntTy tailprim1334 = 1 + fltPrm293;

            return (CursorInt64Prod) {endof1333, tailprim1334};
            break;
        }

      case 3:
        {
            CursorTy field_cur1653 = (CursorTy) tmpcur2378;
            CursorTy case732 = (CursorTy) field_cur1653;
            CursorTy cond75 = (CursorTy) case732;
            CursorInt64Prod tmp_struct13 =  expr(end_r605, cond75);
            CursorTy pvrtmp2407 = tmp_struct13.field0;
            IntTy pvrtmp2408 = tmp_struct13.field1;
            CursorTy endof1335 = (CursorTy) pvrtmp2407;
            IntTy fltPrm297 = (IntTy) pvrtmp2408;
            CursorTy case733 = (CursorTy) endof1335;
            CursorTy then76 = (CursorTy) case733;
            CursorInt64Prod tmp_struct14 =  expr(end_r605, then76);
            CursorTy pvrtmp2409 = tmp_struct14.field0;
            IntTy pvrtmp2410 = tmp_struct14.field1;
            CursorTy endof1336 = (CursorTy) pvrtmp2409;
            IntTy fltPrm299 = (IntTy) pvrtmp2410;
            CursorTy case734 = (CursorTy) endof1336;
            CursorTy else77 = (CursorTy) case734;
            CursorInt64Prod tmp_struct15 =  expr(end_r605, else77);
            CursorTy pvrtmp2411 = tmp_struct15.field0;
            IntTy pvrtmp2412 = tmp_struct15.field1;
            CursorTy endof1337 = (CursorTy) pvrtmp2411;
            IntTy fltPrm300 = (IntTy) pvrtmp2412;
            IntTy fltPrm298 = fltPrm299 + fltPrm300;
            IntTy fltPrm296 = fltPrm297 + fltPrm298;
            IntTy tailprim1338 = 1 + fltPrm296;

            return (CursorInt64Prod) {endof1337, tailprim1338};
            break;
        }

      case 4:
        {
            CursorTy field_cur1657 = (CursorTy) tmpcur2378;
            CursorTy case741 = (CursorTy) field_cur1657;
            CursorTy exprs78 = (CursorTy) case741;
            CursorInt64Prod tmp_struct16 =  loopExpr(end_r605, exprs78);
            CursorTy pvrtmp2413 = tmp_struct16.field0;
            IntTy pvrtmp2414 = tmp_struct16.field1;
            CursorTy endof1339 = (CursorTy) pvrtmp2413;
            IntTy fltPrm301 = (IntTy) pvrtmp2414;
            IntTy tailprim1340 = 1 + fltPrm301;

            return (CursorInt64Prod) {endof1339, tailprim1340};
            break;
        }

      case 5:
        {
            CursorTy field_cur1659 = (CursorTy) tmpcur2378;
            CursorTy case744 = (CursorTy) field_cur1659;
            CursorTy e179 = (CursorTy) case744;
            CursorInt64Prod tmp_struct17 =  expr(end_r605, e179);
            CursorTy pvrtmp2415 = tmp_struct17.field0;
            IntTy pvrtmp2416 = tmp_struct17.field1;
            CursorTy endof1341 = (CursorTy) pvrtmp2415;
            IntTy fltPrm303 = (IntTy) pvrtmp2416;
            CursorTy case745 = (CursorTy) endof1341;
            CursorTy exprs80 = (CursorTy) case745;
            CursorInt64Prod tmp_struct18 =  loopExpr(end_r605, exprs80);
            CursorTy pvrtmp2417 = tmp_struct18.field0;
            IntTy pvrtmp2418 = tmp_struct18.field1;
            CursorTy endof1342 = (CursorTy) pvrtmp2417;
            IntTy fltPrm304 = (IntTy) pvrtmp2418;
            IntTy fltPrm302 = fltPrm303 + fltPrm304;
            IntTy tailprim1343 = 1 + fltPrm302;

            return (CursorInt64Prod) {endof1342, tailprim1343};
            break;
        }

      case 13:
        {
            CursorTy field_cur1662 = (CursorTy) tmpcur2378;
            CursorTy case750 = (CursorTy) field_cur1662;
            CursorTy e181 = (CursorTy) case750;
            CursorInt64Prod tmp_struct19 =  expr(end_r605, e181);
            CursorTy pvrtmp2419 = tmp_struct19.field0;
            IntTy pvrtmp2420 = tmp_struct19.field1;
            CursorTy endof1344 = (CursorTy) pvrtmp2419;
            IntTy fltPrm306 = (IntTy) pvrtmp2420;
            CursorTy case751 = (CursorTy) endof1344;
            CursorTy es82 = (CursorTy) case751;
            CursorInt64Prod tmp_struct20 =  loopExpr(end_r605, es82);
            CursorTy pvrtmp2421 = tmp_struct20.field0;
            IntTy pvrtmp2422 = tmp_struct20.field1;
            CursorTy endof1345 = (CursorTy) pvrtmp2421;
            IntTy fltPrm307 = (IntTy) pvrtmp2422;
            IntTy fltPrm305 = fltPrm306 + fltPrm307;
            IntTy tailprim1346 = 1 + fltPrm305;

            return (CursorInt64Prod) {endof1345, tailprim1346};
            break;
        }

      case 8:
        {
            CursorTy field_cur1665 = (CursorTy) tmpcur2378;
            CursorTy case756 = (CursorTy) field_cur1665;
            SymTy tmpval2423 = *(SymTy *) case756;
            CursorTy tmpcur2424 = case756 + sizeof(SymTy);
            SymTy s83 = (SymTy) tmpval2423;
            CursorTy end_s83 = (CursorTy) tmpcur2424;
            CursorTy case757 = (CursorTy) end_s83;
            CursorTy e84 = (CursorTy) case757;
            CursorTy jump1347 = case756 + 8;
            CursorInt64Prod tmp_struct21 =  expr(end_r605, e84);
            CursorTy pvrtmp2425 = tmp_struct21.field0;
            IntTy pvrtmp2426 = tmp_struct21.field1;
            CursorTy endof1348 = (CursorTy) pvrtmp2425;
            IntTy fltPrm309 = (IntTy) pvrtmp2426;
            IntTy fltPrm308 = 0 + fltPrm309;
            IntTy tailprim1349 = 1 + fltPrm308;

            return (CursorInt64Prod) {endof1348, tailprim1349};
            break;
        }

      case 12:
        {
            CursorTy field_cur1668 = (CursorTy) tmpcur2378;
            CursorTy case760 = (CursorTy) field_cur1668;
            CursorTy e185 = (CursorTy) case760;
            CursorInt64Prod tmp_struct22 =  expr(end_r605, e185);
            CursorTy pvrtmp2427 = tmp_struct22.field0;
            IntTy pvrtmp2428 = tmp_struct22.field1;
            CursorTy endof1350 = (CursorTy) pvrtmp2427;
            IntTy fltPrm311 = (IntTy) pvrtmp2428;
            CursorTy case761 = (CursorTy) endof1350;
            CursorTy e286 = (CursorTy) case761;
            CursorInt64Prod tmp_struct23 =  expr(end_r605, e286);
            CursorTy pvrtmp2429 = tmp_struct23.field0;
            IntTy pvrtmp2430 = tmp_struct23.field1;
            CursorTy endof1351 = (CursorTy) pvrtmp2429;
            IntTy fltPrm313 = (IntTy) pvrtmp2430;
            CursorTy case762 = (CursorTy) endof1351;
            CursorTy e387 = (CursorTy) case762;
            CursorInt64Prod tmp_struct24 =  expr(end_r605, e387);
            CursorTy pvrtmp2431 = tmp_struct24.field0;
            IntTy pvrtmp2432 = tmp_struct24.field1;
            CursorTy endof1352 = (CursorTy) pvrtmp2431;
            IntTy fltPrm314 = (IntTy) pvrtmp2432;
            IntTy fltPrm312 = fltPrm313 + fltPrm314;
            IntTy fltPrm310 = fltPrm311 + fltPrm312;
            IntTy tailprim1353 = 1 + fltPrm310;

            return (CursorInt64Prod) {endof1352, tailprim1353};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3406 = *(CursorTy *) tmpcur2378;
            CursorTy tmpaftercur3407 = tmpcur2378 + 8;
            TagTyPacked tagtmp3408 = *(TagTyPacked *) tmpcur3406;
            CursorTy tailtmp3409 = tmpcur3406 + 1;

            tmpval2377 = tagtmp3408;
            tmpcur2378 = tailtmp3409;
            goto switch2433;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3406 = *(CursorTy *) tmpcur2378;
            CursorTy tmpaftercur3407 = tmpcur2378 + 8;
            TagTyPacked tagtmp3408 = *(TagTyPacked *) tmpcur3406;
            CursorTy tailtmp3409 = tmpcur3406 + 1;

            tmpval2377 = tagtmp3408;
            tmpcur2378 = tailtmp3409;
            goto switch2433;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2377");
            exit(1);
        }
    }
}
CursorInt64Prod top(CursorTy end_r607, CursorTy e88)
{
    CursorTy loc606 = (CursorTy) e88;
    TagTyPacked tmpval2434 = *(TagTyPacked *) e88;
    CursorTy tmpcur2435 = e88 + 1;


  switch2448:
    ;
    switch (tmpval2434) {

      case 0:
        {
            CursorTy field_cur1672 = (CursorTy) tmpcur2435;
            CursorTy case771 = (CursorTy) field_cur1672;
            CursorTy ls89 = (CursorTy) case771;
            CursorInt64Prod tmp_struct25 =  loopSyms(end_r607, ls89);
            CursorTy pvrtmp2436 = tmp_struct25.field0;
            IntTy pvrtmp2437 = tmp_struct25.field1;
            CursorTy endof1354 = (CursorTy) pvrtmp2436;
            IntTy fltPrm316 = (IntTy) pvrtmp2437;
            CursorTy case772 = (CursorTy) endof1354;
            CursorTy e90 = (CursorTy) case772;
            CursorInt64Prod tmp_struct26 =  expr(end_r607, e90);
            CursorTy pvrtmp2438 = tmp_struct26.field0;
            IntTy pvrtmp2439 = tmp_struct26.field1;
            CursorTy endof1355 = (CursorTy) pvrtmp2438;
            IntTy fltPrm317 = (IntTy) pvrtmp2439;
            IntTy fltPrm315 = fltPrm316 + fltPrm317;
            IntTy tailprim1356 = 1 + fltPrm315;

            return (CursorInt64Prod) {endof1355, tailprim1356};
            break;
        }

      case 1:
        {
            CursorTy field_cur1675 = (CursorTy) tmpcur2435;
            CursorTy case777 = (CursorTy) field_cur1675;
            CursorTy ls91 = (CursorTy) case777;
            CursorInt64Prod tmp_struct27 =  loopSyms(end_r607, ls91);
            CursorTy pvrtmp2440 = tmp_struct27.field0;
            IntTy pvrtmp2441 = tmp_struct27.field1;
            CursorTy endof1357 = (CursorTy) pvrtmp2440;
            IntTy fltPrm319 = (IntTy) pvrtmp2441;
            CursorTy case778 = (CursorTy) endof1357;
            CursorTy e92 = (CursorTy) case778;
            CursorInt64Prod tmp_struct28 =  expr(end_r607, e92);
            CursorTy pvrtmp2442 = tmp_struct28.field0;
            IntTy pvrtmp2443 = tmp_struct28.field1;
            CursorTy endof1358 = (CursorTy) pvrtmp2442;
            IntTy fltPrm320 = (IntTy) pvrtmp2443;
            IntTy fltPrm318 = fltPrm319 + fltPrm320;
            IntTy tailprim1359 = 1 + fltPrm318;

            return (CursorInt64Prod) {endof1358, tailprim1359};
            break;
        }

      case 2:
        {
            CursorTy field_cur1678 = (CursorTy) tmpcur2435;
            CursorTy case783 = (CursorTy) field_cur1678;
            CursorTy ls93 = (CursorTy) case783;
            CursorInt64Prod tmp_struct29 =  loopTopLvl(end_r607, ls93);
            CursorTy pvrtmp2444 = tmp_struct29.field0;
            IntTy pvrtmp2445 = tmp_struct29.field1;
            CursorTy endof1360 = (CursorTy) pvrtmp2444;
            IntTy fltPrm321 = (IntTy) pvrtmp2445;
            IntTy tailprim1361 = 1 + fltPrm321;

            return (CursorInt64Prod) {endof1360, tailprim1361};
            break;
        }

      case 3:
        {
            CursorTy field_cur1680 = (CursorTy) tmpcur2435;
            CursorTy case786 = (CursorTy) field_cur1680;
            CursorTy e94 = (CursorTy) case786;
            CursorInt64Prod tmp_struct30 =  expr(end_r607, e94);
            CursorTy pvrtmp2446 = tmp_struct30.field0;
            IntTy pvrtmp2447 = tmp_struct30.field1;
            CursorTy endof1362 = (CursorTy) pvrtmp2446;
            IntTy fltPrm322 = (IntTy) pvrtmp2447;
            IntTy tailprim1363 = 1 + fltPrm322;

            return (CursorInt64Prod) {endof1362, tailprim1363};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3410 = *(CursorTy *) tmpcur2435;
            CursorTy tmpaftercur3411 = tmpcur2435 + 8;
            TagTyPacked tagtmp3412 = *(TagTyPacked *) tmpcur3410;
            CursorTy tailtmp3413 = tmpcur3410 + 1;

            tmpval2434 = tagtmp3412;
            tmpcur2435 = tailtmp3413;
            goto switch2448;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3410 = *(CursorTy *) tmpcur2435;
            CursorTy tmpaftercur3411 = tmpcur2435 + 8;
            TagTyPacked tagtmp3412 = *(TagTyPacked *) tmpcur3410;
            CursorTy tailtmp3413 = tmpcur3410 + 1;

            tmpval2434 = tagtmp3412;
            tmpcur2435 = tailtmp3413;
            goto switch2448;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2434");
            exit(1);
        }
    }
}
CursorInt64Prod loopLVBIND(CursorTy end_r609, CursorTy ls95)
{
    CursorTy loc608 = (CursorTy) ls95;
    TagTyPacked tmpval2449 = *(TagTyPacked *) ls95;
    CursorTy tmpcur2450 = ls95 + 1;


  switch2457:
    ;
    switch (tmpval2449) {

      case 0:
        {
            CursorTy field_cur1682 = (CursorTy) tmpcur2450;
            CursorTy case791 = (CursorTy) field_cur1682;
            CursorTy syms96 = (CursorTy) case791;
            CursorInt64Prod tmp_struct31 =  loopSyms(end_r609, syms96);
            CursorTy pvrtmp2451 = tmp_struct31.field0;
            IntTy pvrtmp2452 = tmp_struct31.field1;
            CursorTy endof1364 = (CursorTy) pvrtmp2451;
            IntTy fltPrm324 = (IntTy) pvrtmp2452;
            CursorTy case792 = (CursorTy) endof1364;
            CursorTy e97 = (CursorTy) case792;
            CursorInt64Prod tmp_struct32 =  expr(end_r609, e97);
            CursorTy pvrtmp2453 = tmp_struct32.field0;
            IntTy pvrtmp2454 = tmp_struct32.field1;
            CursorTy endof1365 = (CursorTy) pvrtmp2453;
            IntTy fltPrm326 = (IntTy) pvrtmp2454;
            CursorTy case793 = (CursorTy) endof1365;
            CursorTy ls98 = (CursorTy) case793;
            CursorInt64Prod tmp_struct33 =  loopLVBIND(end_r609, ls98);
            CursorTy pvrtmp2455 = tmp_struct33.field0;
            IntTy pvrtmp2456 = tmp_struct33.field1;
            CursorTy endof1366 = (CursorTy) pvrtmp2455;
            IntTy fltPrm327 = (IntTy) pvrtmp2456;
            IntTy fltPrm325 = fltPrm326 + fltPrm327;
            IntTy fltPrm323 = fltPrm324 + fltPrm325;
            IntTy tailprim1367 = 1 + fltPrm323;

            return (CursorInt64Prod) {endof1366, tailprim1367};
            break;
        }

      case 1:
        {
            CursorTy field_cur1686 = (CursorTy) tmpcur2450;
            CursorTy jump1368 = loc608 + 1;
            IntTy fltLitTail1369 = (IntTy) 1;

            return (CursorInt64Prod) {jump1368, fltLitTail1369};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3414 = *(CursorTy *) tmpcur2450;
            CursorTy tmpaftercur3415 = tmpcur2450 + 8;
            TagTyPacked tagtmp3416 = *(TagTyPacked *) tmpcur3414;
            CursorTy tailtmp3417 = tmpcur3414 + 1;

            tmpval2449 = tagtmp3416;
            tmpcur2450 = tailtmp3417;
            goto switch2457;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3414 = *(CursorTy *) tmpcur2450;
            CursorTy tmpaftercur3415 = tmpcur2450 + 8;
            TagTyPacked tagtmp3416 = *(TagTyPacked *) tmpcur3414;
            CursorTy tailtmp3417 = tmpcur3414 + 1;

            tmpval2449 = tagtmp3416;
            tmpcur2450 = tailtmp3417;
            goto switch2457;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2449");
            exit(1);
        }
    }
}
CursorInt64Prod loopLambdaCase(CursorTy end_r611, CursorTy ls99)
{
    CursorTy loc610 = (CursorTy) ls99;
    TagTyPacked tmpval2458 = *(TagTyPacked *) ls99;
    CursorTy tmpcur2459 = ls99 + 1;


  switch2466:
    ;
    switch (tmpval2458) {

      case 0:
        {
            CursorTy field_cur1687 = (CursorTy) tmpcur2459;
            CursorTy case802 = (CursorTy) field_cur1687;
            CursorTy f100 = (CursorTy) case802;
            CursorInt64Prod tmp_struct34 =  formals(end_r611, f100);
            CursorTy pvrtmp2460 = tmp_struct34.field0;
            IntTy pvrtmp2461 = tmp_struct34.field1;
            CursorTy endof1370 = (CursorTy) pvrtmp2460;
            IntTy fltPrm329 = (IntTy) pvrtmp2461;
            CursorTy case803 = (CursorTy) endof1370;
            CursorTy le101 = (CursorTy) case803;
            CursorInt64Prod tmp_struct35 =  loopExpr(end_r611, le101);
            CursorTy pvrtmp2462 = tmp_struct35.field0;
            IntTy pvrtmp2463 = tmp_struct35.field1;
            CursorTy endof1371 = (CursorTy) pvrtmp2462;
            IntTy fltPrm331 = (IntTy) pvrtmp2463;
            CursorTy case804 = (CursorTy) endof1371;
            CursorTy ls102 = (CursorTy) case804;
            CursorInt64Prod tmp_struct36 =  loopLambdaCase(end_r611, ls102);
            CursorTy pvrtmp2464 = tmp_struct36.field0;
            IntTy pvrtmp2465 = tmp_struct36.field1;
            CursorTy endof1372 = (CursorTy) pvrtmp2464;
            IntTy fltPrm332 = (IntTy) pvrtmp2465;
            IntTy fltPrm330 = fltPrm331 + fltPrm332;
            IntTy fltPrm328 = fltPrm329 + fltPrm330;
            IntTy tailprim1373 = 1 + fltPrm328;

            return (CursorInt64Prod) {endof1372, tailprim1373};
            break;
        }

      case 1:
        {
            CursorTy field_cur1691 = (CursorTy) tmpcur2459;
            CursorTy jump1374 = loc610 + 1;
            IntTy fltLitTail1375 = (IntTy) 1;

            return (CursorInt64Prod) {jump1374, fltLitTail1375};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3418 = *(CursorTy *) tmpcur2459;
            CursorTy tmpaftercur3419 = tmpcur2459 + 8;
            TagTyPacked tagtmp3420 = *(TagTyPacked *) tmpcur3418;
            CursorTy tailtmp3421 = tmpcur3418 + 1;

            tmpval2458 = tagtmp3420;
            tmpcur2459 = tailtmp3421;
            goto switch2466;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3418 = *(CursorTy *) tmpcur2459;
            CursorTy tmpaftercur3419 = tmpcur2459 + 8;
            TagTyPacked tagtmp3420 = *(TagTyPacked *) tmpcur3418;
            CursorTy tailtmp3421 = tmpcur3418 + 1;

            tmpval2458 = tagtmp3420;
            tmpcur2459 = tailtmp3421;
            goto switch2466;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2458");
            exit(1);
        }
    }
}
CursorInt64Prod loopExpr(CursorTy end_r613, CursorTy ls103)
{
    CursorTy loc612 = (CursorTy) ls103;
    TagTyPacked tmpval2467 = *(TagTyPacked *) ls103;
    CursorTy tmpcur2468 = ls103 + 1;


  switch2473:
    ;
    switch (tmpval2467) {

      case 0:
        {
            CursorTy field_cur1692 = (CursorTy) tmpcur2468;
            CursorTy case813 = (CursorTy) field_cur1692;
            CursorTy e104 = (CursorTy) case813;
            CursorInt64Prod tmp_struct37 =  expr(end_r613, e104);
            CursorTy pvrtmp2469 = tmp_struct37.field0;
            IntTy pvrtmp2470 = tmp_struct37.field1;
            CursorTy endof1376 = (CursorTy) pvrtmp2469;
            IntTy fltPrm334 = (IntTy) pvrtmp2470;
            CursorTy case814 = (CursorTy) endof1376;
            CursorTy ls105 = (CursorTy) case814;
            CursorInt64Prod tmp_struct38 =  loopExpr(end_r613, ls105);
            CursorTy pvrtmp2471 = tmp_struct38.field0;
            IntTy pvrtmp2472 = tmp_struct38.field1;
            CursorTy endof1377 = (CursorTy) pvrtmp2471;
            IntTy fltPrm335 = (IntTy) pvrtmp2472;
            IntTy fltPrm333 = fltPrm334 + fltPrm335;
            IntTy tailprim1378 = 1 + fltPrm333;

            return (CursorInt64Prod) {endof1377, tailprim1378};
            break;
        }

      case 1:
        {
            CursorTy field_cur1695 = (CursorTy) tmpcur2468;
            CursorTy jump1379 = loc612 + 1;
            IntTy fltLitTail1380 = (IntTy) 1;

            return (CursorInt64Prod) {jump1379, fltLitTail1380};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3422 = *(CursorTy *) tmpcur2468;
            CursorTy tmpaftercur3423 = tmpcur2468 + 8;
            TagTyPacked tagtmp3424 = *(TagTyPacked *) tmpcur3422;
            CursorTy tailtmp3425 = tmpcur3422 + 1;

            tmpval2467 = tagtmp3424;
            tmpcur2468 = tailtmp3425;
            goto switch2473;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3422 = *(CursorTy *) tmpcur2468;
            CursorTy tmpaftercur3423 = tmpcur2468 + 8;
            TagTyPacked tagtmp3424 = *(TagTyPacked *) tmpcur3422;
            CursorTy tailtmp3425 = tmpcur3422 + 1;

            tmpval2467 = tagtmp3424;
            tmpcur2468 = tailtmp3425;
            goto switch2473;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2467");
            exit(1);
        }
    }
}
CursorInt64Prod loopTopLvl(CursorTy end_r615, CursorTy ls106)
{
    CursorTy loc614 = (CursorTy) ls106;
    TagTyPacked tmpval2474 = *(TagTyPacked *) ls106;
    CursorTy tmpcur2475 = ls106 + 1;


  switch2480:
    ;
    switch (tmpval2474) {

      case 0:
        {
            CursorTy field_cur1696 = (CursorTy) tmpcur2475;
            CursorTy case821 = (CursorTy) field_cur1696;
            CursorTy tl107 = (CursorTy) case821;
            CursorInt64Prod tmp_struct39 =  top(end_r615, tl107);
            CursorTy pvrtmp2476 = tmp_struct39.field0;
            IntTy pvrtmp2477 = tmp_struct39.field1;
            CursorTy endof1381 = (CursorTy) pvrtmp2476;
            IntTy fltPrm337 = (IntTy) pvrtmp2477;
            CursorTy case822 = (CursorTy) endof1381;
            CursorTy ls108 = (CursorTy) case822;
            CursorInt64Prod tmp_struct40 =  loopTopLvl(end_r615, ls108);
            CursorTy pvrtmp2478 = tmp_struct40.field0;
            IntTy pvrtmp2479 = tmp_struct40.field1;
            CursorTy endof1382 = (CursorTy) pvrtmp2478;
            IntTy fltPrm338 = (IntTy) pvrtmp2479;
            IntTy fltPrm336 = fltPrm337 + fltPrm338;
            IntTy tailprim1383 = 1 + fltPrm336;

            return (CursorInt64Prod) {endof1382, tailprim1383};
            break;
        }

      case 1:
        {
            CursorTy field_cur1699 = (CursorTy) tmpcur2475;
            CursorTy jump1384 = loc614 + 1;
            IntTy fltLitTail1385 = (IntTy) 1;

            return (CursorInt64Prod) {jump1384, fltLitTail1385};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3426 = *(CursorTy *) tmpcur2475;
            CursorTy tmpaftercur3427 = tmpcur2475 + 8;
            TagTyPacked tagtmp3428 = *(TagTyPacked *) tmpcur3426;
            CursorTy tailtmp3429 = tmpcur3426 + 1;

            tmpval2474 = tagtmp3428;
            tmpcur2475 = tailtmp3429;
            goto switch2480;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3426 = *(CursorTy *) tmpcur2475;
            CursorTy tmpaftercur3427 = tmpcur2475 + 8;
            TagTyPacked tagtmp3428 = *(TagTyPacked *) tmpcur3426;
            CursorTy tailtmp3429 = tmpcur3426 + 1;

            tmpval2474 = tagtmp3428;
            tmpcur2475 = tailtmp3429;
            goto switch2480;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2474");
            exit(1);
        }
    }
}
CursorInt64Prod countnodes(CursorTy end_r617, CursorTy e0109)
{
    CursorTy loc616 = (CursorTy) e0109;
    CursorInt64Prod tmp_struct41 =  top(end_r617, e0109);
    CursorTy pvrtmp2481 = tmp_struct41.field0;
    IntTy pvrtmp2482 = tmp_struct41.field1;
    CursorTy endof1387 = (CursorTy) pvrtmp2481;
    IntTy tailapp1386 = (IntTy) pvrtmp2482;

    return (CursorInt64Prod) {endof1387, tailapp1386};
}
CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r620, CursorTy end_r621,
                                           CursorTy loc619, CursorTy arg339)
{
    CursorTy loc618 = (CursorTy) arg339;

    if (loc619 + 18 > end_r621) {
        ChunkTy new_chunk43 = alloc_chunk(end_r621);
        CursorTy chunk_start44 = new_chunk43.start_ptr;
        CursorTy chunk_end45 = new_chunk43.end_ptr;

        end_r621 = chunk_end45;
        *(TagTyPacked *) loc619 = 255;

        CursorTy redir = loc619 + 1;

        *(CursorTy *) redir = chunk_start44;
        loc619 = chunk_start44;
    }

    CursorTy loc836 = loc619 + 1;
    CursorTy loc837 = loc836 + 8;
    TagTyPacked tmpval2483 = *(TagTyPacked *) arg339;
    CursorTy tmpcur2484 = arg339 + 1;


  switch2503:
    ;
    switch (tmpval2483) {

      case 0:
        {
            CursorTy field_cur1701 = (CursorTy) tmpcur2484;
            CursorTy case831 = (CursorTy) field_cur1701;
            SymTy tmpval2485 = *(SymTy *) case831;
            CursorTy tmpcur2486 = case831 + sizeof(SymTy);
            SymTy x340 = (SymTy) tmpval2485;
            CursorTy end_x340 = (CursorTy) tmpcur2486;
            CursorTy case832 = (CursorTy) end_x340;
            CursorTy x341 = (CursorTy) case832;
            CursorTy jump1388 = case831 + 8;
            CursorCursorCursorCursorProd tmp_struct42 =
                                          _copy_ListSym(end_r620, end_r621, loc837, x341);
            CursorTy pvrtmp2487 = tmp_struct42.field0;
            CursorTy pvrtmp2488 = tmp_struct42.field1;
            CursorTy pvrtmp2489 = tmp_struct42.field2;
            CursorTy pvrtmp2490 = tmp_struct42.field3;
            CursorTy fltPrd2115 = (CursorTy) pvrtmp2489;
            CursorTy fltPrd2116 = (CursorTy) pvrtmp2490;
            CursorTy pvrtmp2492 = (CursorTy) fltPrd2116;
            CursorTy pvrtmp2491 = (CursorTy) fltPrd2115;
            CursorTy y343 = (CursorTy) pvrtmp2491;
            CursorTy fltPrd2117 = (CursorTy) pvrtmp2489;
            CursorTy fltPrd2118 = (CursorTy) pvrtmp2490;
            CursorTy pvrtmp2494 = (CursorTy) fltPrd2118;
            CursorTy pvrtmp2493 = (CursorTy) fltPrd2117;
            CursorTy end_y343 = (CursorTy) pvrtmp2494;
            CursorTy end_r621_1573 = (CursorTy) pvrtmp2487;
            CursorTy endof1389 = (CursorTy) pvrtmp2488;

            *(TagTyPacked *) loc619 = 0;

            CursorTy writetag1704 = loc619 + 1;

            *(SymTy *) writetag1704 = x340;

            CursorTy writecur1705 = writetag1704 + sizeof(SymTy);
            CursorTy writecur1706 = (CursorTy) end_y343;
            CursorTy pvrtmp2496 = (CursorTy) writecur1706;
            CursorTy pvrtmp2495 = (CursorTy) loc619;
            CursorTy taildc1390 = (CursorTy) pvrtmp2495;
            CursorTy end_taildc1390 = (CursorTy) pvrtmp2496;
            CursorTy pvrtmp2498 = (CursorTy) end_taildc1390;
            CursorTy pvrtmp2497 = (CursorTy) taildc1390;
            CursorTy fltPrd2119 = (CursorTy) pvrtmp2497;
            CursorTy fltPrd2120 = (CursorTy) pvrtmp2498;

            return (CursorCursorCursorCursorProd) {end_r621_1573, endof1389,
                                                   fltPrd2119, fltPrd2120};
            break;
        }

      case 1:
        {
            CursorTy field_cur1708 = (CursorTy) tmpcur2484;
            CursorTy jump1391 = loc618 + 1;

            *(TagTyPacked *) loc619 = 1;

            CursorTy writetag1709 = loc619 + 1;
            CursorTy pvrtmp2500 = (CursorTy) writetag1709;
            CursorTy pvrtmp2499 = (CursorTy) loc619;
            CursorTy taildc1392 = (CursorTy) pvrtmp2499;
            CursorTy end_taildc1392 = (CursorTy) pvrtmp2500;
            CursorTy pvrtmp2502 = (CursorTy) end_taildc1392;
            CursorTy pvrtmp2501 = (CursorTy) taildc1392;
            CursorTy fltPrd2121 = (CursorTy) pvrtmp2501;
            CursorTy fltPrd2122 = (CursorTy) pvrtmp2502;

            return (CursorCursorCursorCursorProd) {end_r621, jump1391,
                                                   fltPrd2121, fltPrd2122};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3430 = *(CursorTy *) tmpcur2484;
            CursorTy tmpaftercur3431 = tmpcur2484 + 8;
            TagTyPacked tagtmp3432 = *(TagTyPacked *) tmpcur3430;
            CursorTy tailtmp3433 = tmpcur3430 + 1;

            tmpval2483 = tagtmp3432;
            tmpcur2484 = tailtmp3433;
            goto switch2503;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3430 = *(CursorTy *) tmpcur2484;
            CursorTy tmpaftercur3431 = tmpcur2484 + 8;
            TagTyPacked tagtmp3432 = *(TagTyPacked *) tmpcur3430;
            CursorTy tailtmp3433 = tmpcur3430 + 1;

            tmpval2483 = tagtmp3432;
            tmpcur2484 = tailtmp3433;
            goto switch2503;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2483");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_ListSym(CursorTy end_r623, CursorTy arg344)
{
    CursorTy loc622 = (CursorTy) arg344;
    TagTyPacked tmpval2504 = *(TagTyPacked *) arg344;
    CursorTy tmpcur2505 = arg344 + 1;


  switch2510:
    ;
    switch (tmpval2504) {

      case 0:
        {
            CursorTy field_cur1711 = (CursorTy) tmpcur2505;
            CursorTy case844 = (CursorTy) field_cur1711;
            SymTy tmpval2506 = *(SymTy *) case844;
            CursorTy tmpcur2507 = case844 + sizeof(SymTy);
            SymTy x345 = (SymTy) tmpval2506;
            CursorTy end_x345 = (CursorTy) tmpcur2507;
            CursorTy case845 = (CursorTy) end_x345;
            CursorTy x346 = (CursorTy) case845;
            CursorTy jump1393 = case844 + 8;
            CursorInt64Prod tmp_struct46 =  _traverse_ListSym(end_r623, x346);
            CursorTy pvrtmp2508 = tmp_struct46.field0;
            IntTy pvrtmp2509 = tmp_struct46.field1;
            CursorTy endof1395 = (CursorTy) pvrtmp2508;
            IntTy y348 = (IntTy) pvrtmp2509;
            IntTy fltLitTail1394 = (IntTy) 42;

            return (CursorInt64Prod) {endof1395, fltLitTail1394};
            break;
        }

      case 1:
        {
            CursorTy field_cur1714 = (CursorTy) tmpcur2505;
            CursorTy jump1396 = loc622 + 1;
            IntTy fltLitTail1397 = (IntTy) 42;

            return (CursorInt64Prod) {jump1396, fltLitTail1397};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3434 = *(CursorTy *) tmpcur2505;
            CursorTy tmpaftercur3435 = tmpcur2505 + 8;
            TagTyPacked tagtmp3436 = *(TagTyPacked *) tmpcur3434;
            CursorTy tailtmp3437 = tmpcur3434 + 1;

            tmpval2504 = tagtmp3436;
            tmpcur2505 = tailtmp3437;
            goto switch2510;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3434 = *(CursorTy *) tmpcur2505;
            CursorTy tmpaftercur3435 = tmpcur2505 + 8;
            TagTyPacked tagtmp3436 = *(TagTyPacked *) tmpcur3434;
            CursorTy tailtmp3437 = tmpcur3434 + 1;

            tmpval2504 = tagtmp3436;
            tmpcur2505 = tailtmp3437;
            goto switch2510;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2504");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r626,
                                            CursorTy end_r627, CursorTy loc625,
                                            CursorTy arg349)
{
    CursorTy loc624 = (CursorTy) arg349;

    if (loc625 + 18 > end_r627) {
        ChunkTy new_chunk49 = alloc_chunk(end_r627);
        CursorTy chunk_start50 = new_chunk49.start_ptr;
        CursorTy chunk_end51 = new_chunk49.end_ptr;

        end_r627 = chunk_end51;
        *(TagTyPacked *) loc625 = 255;

        CursorTy redir = loc625 + 1;

        *(CursorTy *) redir = chunk_start50;
        loc625 = chunk_start50;
    }

    TagTyPacked tmpval2511 = *(TagTyPacked *) arg349;
    CursorTy tmpcur2512 = arg349 + 1;


  switch2537:
    ;
    switch (tmpval2511) {

      case 0:
        {
            CursorTy field_cur1715 = (CursorTy) tmpcur2512;
            CursorTy case850 = (CursorTy) field_cur1715;
            CursorTy x350 = (CursorTy) case850;
            CursorTy loc858 = loc625 + 1;
            CursorCursorCursorCursorProd tmp_struct47 =
                                          _copy_Expr(end_r626, end_r627, loc858, x350);
            CursorTy pvrtmp2513 = tmp_struct47.field0;
            CursorTy pvrtmp2514 = tmp_struct47.field1;
            CursorTy pvrtmp2515 = tmp_struct47.field2;
            CursorTy pvrtmp2516 = tmp_struct47.field3;
            CursorTy fltPrd2123 = (CursorTy) pvrtmp2515;
            CursorTy fltPrd2124 = (CursorTy) pvrtmp2516;
            CursorTy pvrtmp2518 = (CursorTy) fltPrd2124;
            CursorTy pvrtmp2517 = (CursorTy) fltPrd2123;
            CursorTy y352 = (CursorTy) pvrtmp2517;
            CursorTy fltPrd2125 = (CursorTy) pvrtmp2515;
            CursorTy fltPrd2126 = (CursorTy) pvrtmp2516;
            CursorTy pvrtmp2520 = (CursorTy) fltPrd2126;
            CursorTy pvrtmp2519 = (CursorTy) fltPrd2125;
            CursorTy end_y352 = (CursorTy) pvrtmp2520;
            CursorTy end_r627_1574 = (CursorTy) pvrtmp2513;
            CursorTy endof1398 = (CursorTy) pvrtmp2514;
            CursorTy case851 = (CursorTy) endof1398;
            CursorTy x351 = (CursorTy) case851;
            CursorTy loc859 = (CursorTy) end_y352;
            CursorCursorCursorCursorProd tmp_struct48 =
                                          _copy_ListExpr(end_r626, end_r627_1574, loc859, x351);
            CursorTy pvrtmp2521 = tmp_struct48.field0;
            CursorTy pvrtmp2522 = tmp_struct48.field1;
            CursorTy pvrtmp2523 = tmp_struct48.field2;
            CursorTy pvrtmp2524 = tmp_struct48.field3;
            CursorTy fltPrd2127 = (CursorTy) pvrtmp2523;
            CursorTy fltPrd2128 = (CursorTy) pvrtmp2524;
            CursorTy pvrtmp2526 = (CursorTy) fltPrd2128;
            CursorTy pvrtmp2525 = (CursorTy) fltPrd2127;
            CursorTy y353 = (CursorTy) pvrtmp2525;
            CursorTy fltPrd2129 = (CursorTy) pvrtmp2523;
            CursorTy fltPrd2130 = (CursorTy) pvrtmp2524;
            CursorTy pvrtmp2528 = (CursorTy) fltPrd2130;
            CursorTy pvrtmp2527 = (CursorTy) fltPrd2129;
            CursorTy end_y353 = (CursorTy) pvrtmp2528;
            CursorTy end_r627_1574_1575 = (CursorTy) pvrtmp2521;
            CursorTy endof1399 = (CursorTy) pvrtmp2522;

            *(TagTyPacked *) loc625 = 0;

            CursorTy writetag1718 = loc625 + 1;
            CursorTy writecur1719 = (CursorTy) end_y352;
            CursorTy writecur1720 = (CursorTy) end_y353;
            CursorTy pvrtmp2530 = (CursorTy) writecur1720;
            CursorTy pvrtmp2529 = (CursorTy) loc625;
            CursorTy taildc1400 = (CursorTy) pvrtmp2529;
            CursorTy end_taildc1400 = (CursorTy) pvrtmp2530;
            CursorTy pvrtmp2532 = (CursorTy) end_taildc1400;
            CursorTy pvrtmp2531 = (CursorTy) taildc1400;
            CursorTy fltPrd2131 = (CursorTy) pvrtmp2531;
            CursorTy fltPrd2132 = (CursorTy) pvrtmp2532;

            return (CursorCursorCursorCursorProd) {end_r627_1574_1575,
                                                   endof1399, fltPrd2131,
                                                   fltPrd2132};
            break;
        }

      case 1:
        {
            CursorTy field_cur1722 = (CursorTy) tmpcur2512;
            CursorTy jump1401 = loc624 + 1;

            *(TagTyPacked *) loc625 = 1;

            CursorTy writetag1723 = loc625 + 1;
            CursorTy pvrtmp2534 = (CursorTy) writetag1723;
            CursorTy pvrtmp2533 = (CursorTy) loc625;
            CursorTy taildc1402 = (CursorTy) pvrtmp2533;
            CursorTy end_taildc1402 = (CursorTy) pvrtmp2534;
            CursorTy pvrtmp2536 = (CursorTy) end_taildc1402;
            CursorTy pvrtmp2535 = (CursorTy) taildc1402;
            CursorTy fltPrd2133 = (CursorTy) pvrtmp2535;
            CursorTy fltPrd2134 = (CursorTy) pvrtmp2536;

            return (CursorCursorCursorCursorProd) {end_r627, jump1401,
                                                   fltPrd2133, fltPrd2134};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3438 = *(CursorTy *) tmpcur2512;
            CursorTy tmpaftercur3439 = tmpcur2512 + 8;
            TagTyPacked tagtmp3440 = *(TagTyPacked *) tmpcur3438;
            CursorTy tailtmp3441 = tmpcur3438 + 1;

            tmpval2511 = tagtmp3440;
            tmpcur2512 = tailtmp3441;
            goto switch2537;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3438 = *(CursorTy *) tmpcur2512;
            CursorTy tmpaftercur3439 = tmpcur2512 + 8;
            TagTyPacked tagtmp3440 = *(TagTyPacked *) tmpcur3438;
            CursorTy tailtmp3441 = tmpcur3438 + 1;

            tmpval2511 = tagtmp3440;
            tmpcur2512 = tailtmp3441;
            goto switch2537;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2511");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_ListExpr(CursorTy end_r629, CursorTy arg354)
{
    CursorTy loc628 = (CursorTy) arg354;
    TagTyPacked tmpval2538 = *(TagTyPacked *) arg354;
    CursorTy tmpcur2539 = arg354 + 1;


  switch2544:
    ;
    switch (tmpval2538) {

      case 0:
        {
            CursorTy field_cur1725 = (CursorTy) tmpcur2539;
            CursorTy case865 = (CursorTy) field_cur1725;
            CursorTy x355 = (CursorTy) case865;
            CursorInt64Prod tmp_struct52 =  _traverse_Expr(end_r629, x355);
            CursorTy pvrtmp2540 = tmp_struct52.field0;
            IntTy pvrtmp2541 = tmp_struct52.field1;
            CursorTy endof1403 = (CursorTy) pvrtmp2540;
            IntTy y357 = (IntTy) pvrtmp2541;
            CursorTy case866 = (CursorTy) endof1403;
            CursorTy x356 = (CursorTy) case866;
            CursorInt64Prod tmp_struct53 =  _traverse_ListExpr(end_r629, x356);
            CursorTy pvrtmp2542 = tmp_struct53.field0;
            IntTy pvrtmp2543 = tmp_struct53.field1;
            CursorTy endof1405 = (CursorTy) pvrtmp2542;
            IntTy y358 = (IntTy) pvrtmp2543;
            IntTy fltLitTail1404 = (IntTy) 42;

            return (CursorInt64Prod) {endof1405, fltLitTail1404};
            break;
        }

      case 1:
        {
            CursorTy field_cur1728 = (CursorTy) tmpcur2539;
            CursorTy jump1406 = loc628 + 1;
            IntTy fltLitTail1407 = (IntTy) 42;

            return (CursorInt64Prod) {jump1406, fltLitTail1407};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3442 = *(CursorTy *) tmpcur2539;
            CursorTy tmpaftercur3443 = tmpcur2539 + 8;
            TagTyPacked tagtmp3444 = *(TagTyPacked *) tmpcur3442;
            CursorTy tailtmp3445 = tmpcur3442 + 1;

            tmpval2538 = tagtmp3444;
            tmpcur2539 = tailtmp3445;
            goto switch2544;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3442 = *(CursorTy *) tmpcur2539;
            CursorTy tmpaftercur3443 = tmpcur2539 + 8;
            TagTyPacked tagtmp3444 = *(TagTyPacked *) tmpcur3442;
            CursorTy tailtmp3445 = tmpcur3442 + 1;

            tmpval2538 = tagtmp3444;
            tmpcur2539 = tailtmp3445;
            goto switch2544;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2538");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r632,
                                              CursorTy end_r633,
                                              CursorTy loc631, CursorTy arg359)
{
    CursorTy loc630 = (CursorTy) arg359;

    if (loc631 + 18 > end_r633) {
        ChunkTy new_chunk56 = alloc_chunk(end_r633);
        CursorTy chunk_start57 = new_chunk56.start_ptr;
        CursorTy chunk_end58 = new_chunk56.end_ptr;

        end_r633 = chunk_end58;
        *(TagTyPacked *) loc631 = 255;

        CursorTy redir = loc631 + 1;

        *(CursorTy *) redir = chunk_start57;
        loc631 = chunk_start57;
    }

    TagTyPacked tmpval2545 = *(TagTyPacked *) arg359;
    CursorTy tmpcur2546 = arg359 + 1;


  switch2571:
    ;
    switch (tmpval2545) {

      case 0:
        {
            CursorTy field_cur1729 = (CursorTy) tmpcur2546;
            CursorTy case873 = (CursorTy) field_cur1729;
            CursorTy x360 = (CursorTy) case873;
            CursorTy loc881 = loc631 + 1;
            CursorCursorCursorCursorProd tmp_struct54 =
                                          _copy_Toplvl(end_r632, end_r633, loc881, x360);
            CursorTy pvrtmp2547 = tmp_struct54.field0;
            CursorTy pvrtmp2548 = tmp_struct54.field1;
            CursorTy pvrtmp2549 = tmp_struct54.field2;
            CursorTy pvrtmp2550 = tmp_struct54.field3;
            CursorTy fltPrd2135 = (CursorTy) pvrtmp2549;
            CursorTy fltPrd2136 = (CursorTy) pvrtmp2550;
            CursorTy pvrtmp2552 = (CursorTy) fltPrd2136;
            CursorTy pvrtmp2551 = (CursorTy) fltPrd2135;
            CursorTy y362 = (CursorTy) pvrtmp2551;
            CursorTy fltPrd2137 = (CursorTy) pvrtmp2549;
            CursorTy fltPrd2138 = (CursorTy) pvrtmp2550;
            CursorTy pvrtmp2554 = (CursorTy) fltPrd2138;
            CursorTy pvrtmp2553 = (CursorTy) fltPrd2137;
            CursorTy end_y362 = (CursorTy) pvrtmp2554;
            CursorTy end_r633_1576 = (CursorTy) pvrtmp2547;
            CursorTy endof1408 = (CursorTy) pvrtmp2548;
            CursorTy case874 = (CursorTy) endof1408;
            CursorTy x361 = (CursorTy) case874;
            CursorTy loc882 = (CursorTy) end_y362;
            CursorCursorCursorCursorProd tmp_struct55 =
                                          _copy_ListToplvl(end_r632, end_r633_1576, loc882, x361);
            CursorTy pvrtmp2555 = tmp_struct55.field0;
            CursorTy pvrtmp2556 = tmp_struct55.field1;
            CursorTy pvrtmp2557 = tmp_struct55.field2;
            CursorTy pvrtmp2558 = tmp_struct55.field3;
            CursorTy fltPrd2139 = (CursorTy) pvrtmp2557;
            CursorTy fltPrd2140 = (CursorTy) pvrtmp2558;
            CursorTy pvrtmp2560 = (CursorTy) fltPrd2140;
            CursorTy pvrtmp2559 = (CursorTy) fltPrd2139;
            CursorTy y363 = (CursorTy) pvrtmp2559;
            CursorTy fltPrd2141 = (CursorTy) pvrtmp2557;
            CursorTy fltPrd2142 = (CursorTy) pvrtmp2558;
            CursorTy pvrtmp2562 = (CursorTy) fltPrd2142;
            CursorTy pvrtmp2561 = (CursorTy) fltPrd2141;
            CursorTy end_y363 = (CursorTy) pvrtmp2562;
            CursorTy end_r633_1576_1577 = (CursorTy) pvrtmp2555;
            CursorTy endof1409 = (CursorTy) pvrtmp2556;

            *(TagTyPacked *) loc631 = 0;

            CursorTy writetag1732 = loc631 + 1;
            CursorTy writecur1733 = (CursorTy) end_y362;
            CursorTy writecur1734 = (CursorTy) end_y363;
            CursorTy pvrtmp2564 = (CursorTy) writecur1734;
            CursorTy pvrtmp2563 = (CursorTy) loc631;
            CursorTy taildc1410 = (CursorTy) pvrtmp2563;
            CursorTy end_taildc1410 = (CursorTy) pvrtmp2564;
            CursorTy pvrtmp2566 = (CursorTy) end_taildc1410;
            CursorTy pvrtmp2565 = (CursorTy) taildc1410;
            CursorTy fltPrd2143 = (CursorTy) pvrtmp2565;
            CursorTy fltPrd2144 = (CursorTy) pvrtmp2566;

            return (CursorCursorCursorCursorProd) {end_r633_1576_1577,
                                                   endof1409, fltPrd2143,
                                                   fltPrd2144};
            break;
        }

      case 1:
        {
            CursorTy field_cur1736 = (CursorTy) tmpcur2546;
            CursorTy jump1411 = loc630 + 1;

            *(TagTyPacked *) loc631 = 1;

            CursorTy writetag1737 = loc631 + 1;
            CursorTy pvrtmp2568 = (CursorTy) writetag1737;
            CursorTy pvrtmp2567 = (CursorTy) loc631;
            CursorTy taildc1412 = (CursorTy) pvrtmp2567;
            CursorTy end_taildc1412 = (CursorTy) pvrtmp2568;
            CursorTy pvrtmp2570 = (CursorTy) end_taildc1412;
            CursorTy pvrtmp2569 = (CursorTy) taildc1412;
            CursorTy fltPrd2145 = (CursorTy) pvrtmp2569;
            CursorTy fltPrd2146 = (CursorTy) pvrtmp2570;

            return (CursorCursorCursorCursorProd) {end_r633, jump1411,
                                                   fltPrd2145, fltPrd2146};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3446 = *(CursorTy *) tmpcur2546;
            CursorTy tmpaftercur3447 = tmpcur2546 + 8;
            TagTyPacked tagtmp3448 = *(TagTyPacked *) tmpcur3446;
            CursorTy tailtmp3449 = tmpcur3446 + 1;

            tmpval2545 = tagtmp3448;
            tmpcur2546 = tailtmp3449;
            goto switch2571;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3446 = *(CursorTy *) tmpcur2546;
            CursorTy tmpaftercur3447 = tmpcur2546 + 8;
            TagTyPacked tagtmp3448 = *(TagTyPacked *) tmpcur3446;
            CursorTy tailtmp3449 = tmpcur3446 + 1;

            tmpval2545 = tagtmp3448;
            tmpcur2546 = tailtmp3449;
            goto switch2571;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2545");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_ListToplvl(CursorTy end_r635, CursorTy arg364)
{
    CursorTy loc634 = (CursorTy) arg364;
    TagTyPacked tmpval2572 = *(TagTyPacked *) arg364;
    CursorTy tmpcur2573 = arg364 + 1;


  switch2578:
    ;
    switch (tmpval2572) {

      case 0:
        {
            CursorTy field_cur1739 = (CursorTy) tmpcur2573;
            CursorTy case888 = (CursorTy) field_cur1739;
            CursorTy x365 = (CursorTy) case888;
            CursorInt64Prod tmp_struct59 =  _traverse_Toplvl(end_r635, x365);
            CursorTy pvrtmp2574 = tmp_struct59.field0;
            IntTy pvrtmp2575 = tmp_struct59.field1;
            CursorTy endof1413 = (CursorTy) pvrtmp2574;
            IntTy y367 = (IntTy) pvrtmp2575;
            CursorTy case889 = (CursorTy) endof1413;
            CursorTy x366 = (CursorTy) case889;
            CursorInt64Prod tmp_struct60 =
                             _traverse_ListToplvl(end_r635, x366);
            CursorTy pvrtmp2576 = tmp_struct60.field0;
            IntTy pvrtmp2577 = tmp_struct60.field1;
            CursorTy endof1415 = (CursorTy) pvrtmp2576;
            IntTy y368 = (IntTy) pvrtmp2577;
            IntTy fltLitTail1414 = (IntTy) 42;

            return (CursorInt64Prod) {endof1415, fltLitTail1414};
            break;
        }

      case 1:
        {
            CursorTy field_cur1742 = (CursorTy) tmpcur2573;
            CursorTy jump1416 = loc634 + 1;
            IntTy fltLitTail1417 = (IntTy) 42;

            return (CursorInt64Prod) {jump1416, fltLitTail1417};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3450 = *(CursorTy *) tmpcur2573;
            CursorTy tmpaftercur3451 = tmpcur2573 + 8;
            TagTyPacked tagtmp3452 = *(TagTyPacked *) tmpcur3450;
            CursorTy tailtmp3453 = tmpcur3450 + 1;

            tmpval2572 = tagtmp3452;
            tmpcur2573 = tailtmp3453;
            goto switch2578;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3450 = *(CursorTy *) tmpcur2573;
            CursorTy tmpaftercur3451 = tmpcur2573 + 8;
            TagTyPacked tagtmp3452 = *(TagTyPacked *) tmpcur3450;
            CursorTy tailtmp3453 = tmpcur3450 + 1;

            tmpval2572 = tagtmp3452;
            tmpcur2573 = tailtmp3453;
            goto switch2578;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2572");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r638, CursorTy end_r639,
                                           CursorTy loc637, CursorTy arg369)
{
    CursorTy loc636 = (CursorTy) arg369;

    if (loc637 + 18 > end_r639) {
        ChunkTy new_chunk63 = alloc_chunk(end_r639);
        CursorTy chunk_start64 = new_chunk63.start_ptr;
        CursorTy chunk_end65 = new_chunk63.end_ptr;

        end_r639 = chunk_end65;
        *(TagTyPacked *) loc637 = 255;

        CursorTy redir = loc637 + 1;

        *(CursorTy *) redir = chunk_start64;
        loc637 = chunk_start64;
    }

    TagTyPacked tmpval2579 = *(TagTyPacked *) arg369;
    CursorTy tmpcur2580 = arg369 + 1;


  switch2613:
    ;
    switch (tmpval2579) {

      case 0:
        {
            CursorTy field_cur1743 = (CursorTy) tmpcur2580;
            CursorTy case896 = (CursorTy) field_cur1743;
            CursorTy x370 = (CursorTy) case896;
            CursorTy loc900 = loc637 + 1;
            CursorCursorCursorCursorProd tmp_struct61 =
                                          _copy_ListSym(end_r638, end_r639, loc900, x370);
            CursorTy pvrtmp2581 = tmp_struct61.field0;
            CursorTy pvrtmp2582 = tmp_struct61.field1;
            CursorTy pvrtmp2583 = tmp_struct61.field2;
            CursorTy pvrtmp2584 = tmp_struct61.field3;
            CursorTy fltPrd2147 = (CursorTy) pvrtmp2583;
            CursorTy fltPrd2148 = (CursorTy) pvrtmp2584;
            CursorTy pvrtmp2586 = (CursorTy) fltPrd2148;
            CursorTy pvrtmp2585 = (CursorTy) fltPrd2147;
            CursorTy y371 = (CursorTy) pvrtmp2585;
            CursorTy fltPrd2149 = (CursorTy) pvrtmp2583;
            CursorTy fltPrd2150 = (CursorTy) pvrtmp2584;
            CursorTy pvrtmp2588 = (CursorTy) fltPrd2150;
            CursorTy pvrtmp2587 = (CursorTy) fltPrd2149;
            CursorTy end_y371 = (CursorTy) pvrtmp2588;
            CursorTy end_r639_1578 = (CursorTy) pvrtmp2581;
            CursorTy endof1418 = (CursorTy) pvrtmp2582;

            *(TagTyPacked *) loc637 = 0;

            CursorTy writetag1745 = loc637 + 1;
            CursorTy writecur1746 = (CursorTy) end_y371;
            CursorTy pvrtmp2590 = (CursorTy) writecur1746;
            CursorTy pvrtmp2589 = (CursorTy) loc637;
            CursorTy taildc1419 = (CursorTy) pvrtmp2589;
            CursorTy end_taildc1419 = (CursorTy) pvrtmp2590;
            CursorTy pvrtmp2592 = (CursorTy) end_taildc1419;
            CursorTy pvrtmp2591 = (CursorTy) taildc1419;
            CursorTy fltPrd2151 = (CursorTy) pvrtmp2591;
            CursorTy fltPrd2152 = (CursorTy) pvrtmp2592;

            return (CursorCursorCursorCursorProd) {end_r639_1578, endof1418,
                                                   fltPrd2151, fltPrd2152};
            break;
        }

      case 1:
        {
            CursorTy field_cur1748 = (CursorTy) tmpcur2580;
            CursorTy case902 = (CursorTy) field_cur1748;
            CursorTy x372 = (CursorTy) case902;
            CursorTy loc907 = loc637 + 1;
            CursorCursorCursorCursorProd tmp_struct62 =
                                          _copy_ListSym(end_r638, end_r639, loc907, x372);
            CursorTy pvrtmp2593 = tmp_struct62.field0;
            CursorTy pvrtmp2594 = tmp_struct62.field1;
            CursorTy pvrtmp2595 = tmp_struct62.field2;
            CursorTy pvrtmp2596 = tmp_struct62.field3;
            CursorTy fltPrd2153 = (CursorTy) pvrtmp2595;
            CursorTy fltPrd2154 = (CursorTy) pvrtmp2596;
            CursorTy pvrtmp2598 = (CursorTy) fltPrd2154;
            CursorTy pvrtmp2597 = (CursorTy) fltPrd2153;
            CursorTy y374 = (CursorTy) pvrtmp2597;
            CursorTy fltPrd2155 = (CursorTy) pvrtmp2595;
            CursorTy fltPrd2156 = (CursorTy) pvrtmp2596;
            CursorTy pvrtmp2600 = (CursorTy) fltPrd2156;
            CursorTy pvrtmp2599 = (CursorTy) fltPrd2155;
            CursorTy end_y374 = (CursorTy) pvrtmp2600;
            CursorTy end_r639_1579 = (CursorTy) pvrtmp2593;
            CursorTy endof1421 = (CursorTy) pvrtmp2594;
            CursorTy case903 = (CursorTy) endof1421;
            CursorTy jump1420 = case903 + 8;
            SymTy tmpval2601 = *(SymTy *) case903;
            CursorTy tmpcur2602 = case903 + sizeof(SymTy);
            SymTy x373 = (SymTy) tmpval2601;
            CursorTy end_x373 = (CursorTy) tmpcur2602;

            *(TagTyPacked *) loc637 = 1;

            CursorTy writetag1751 = loc637 + 1;
            CursorTy writecur1752 = (CursorTy) end_y374;

            *(SymTy *) writecur1752 = x373;

            CursorTy writecur1753 = writecur1752 + sizeof(SymTy);
            CursorTy pvrtmp2604 = (CursorTy) writecur1753;
            CursorTy pvrtmp2603 = (CursorTy) loc637;
            CursorTy taildc1422 = (CursorTy) pvrtmp2603;
            CursorTy end_taildc1422 = (CursorTy) pvrtmp2604;
            CursorTy pvrtmp2606 = (CursorTy) end_taildc1422;
            CursorTy pvrtmp2605 = (CursorTy) taildc1422;
            CursorTy fltPrd2157 = (CursorTy) pvrtmp2605;
            CursorTy fltPrd2158 = (CursorTy) pvrtmp2606;

            return (CursorCursorCursorCursorProd) {end_r639_1579, jump1420,
                                                   fltPrd2157, fltPrd2158};
            break;
        }

      case 2:
        {
            CursorTy field_cur1755 = (CursorTy) tmpcur2580;
            CursorTy case912 = (CursorTy) field_cur1755;
            SymTy tmpval2607 = *(SymTy *) case912;
            CursorTy tmpcur2608 = case912 + sizeof(SymTy);
            SymTy x376 = (SymTy) tmpval2607;
            CursorTy end_x376 = (CursorTy) tmpcur2608;
            CursorTy jump1423 = case912 + 8;

            *(TagTyPacked *) loc637 = 2;

            CursorTy writetag1757 = loc637 + 1;

            *(SymTy *) writetag1757 = x376;

            CursorTy writecur1758 = writetag1757 + sizeof(SymTy);
            CursorTy pvrtmp2610 = (CursorTy) writecur1758;
            CursorTy pvrtmp2609 = (CursorTy) loc637;
            CursorTy taildc1424 = (CursorTy) pvrtmp2609;
            CursorTy end_taildc1424 = (CursorTy) pvrtmp2610;
            CursorTy pvrtmp2612 = (CursorTy) end_taildc1424;
            CursorTy pvrtmp2611 = (CursorTy) taildc1424;
            CursorTy fltPrd2159 = (CursorTy) pvrtmp2611;
            CursorTy fltPrd2160 = (CursorTy) pvrtmp2612;

            return (CursorCursorCursorCursorProd) {end_r639, jump1423,
                                                   fltPrd2159, fltPrd2160};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3454 = *(CursorTy *) tmpcur2580;
            CursorTy tmpaftercur3455 = tmpcur2580 + 8;
            TagTyPacked tagtmp3456 = *(TagTyPacked *) tmpcur3454;
            CursorTy tailtmp3457 = tmpcur3454 + 1;

            tmpval2579 = tagtmp3456;
            tmpcur2580 = tailtmp3457;
            goto switch2613;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3454 = *(CursorTy *) tmpcur2580;
            CursorTy tmpaftercur3455 = tmpcur2580 + 8;
            TagTyPacked tagtmp3456 = *(TagTyPacked *) tmpcur3454;
            CursorTy tailtmp3457 = tmpcur3454 + 1;

            tmpval2579 = tagtmp3456;
            tmpcur2580 = tailtmp3457;
            goto switch2613;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2579");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Formals(CursorTy end_r641, CursorTy arg378)
{
    CursorTy loc640 = (CursorTy) arg378;
    TagTyPacked tmpval2614 = *(TagTyPacked *) arg378;
    CursorTy tmpcur2615 = arg378 + 1;


  switch2624:
    ;
    switch (tmpval2614) {

      case 0:
        {
            CursorTy field_cur1760 = (CursorTy) tmpcur2615;
            CursorTy case918 = (CursorTy) field_cur1760;
            CursorTy x379 = (CursorTy) case918;
            CursorInt64Prod tmp_struct66 =  _traverse_ListSym(end_r641, x379);
            CursorTy pvrtmp2616 = tmp_struct66.field0;
            IntTy pvrtmp2617 = tmp_struct66.field1;
            CursorTy endof1426 = (CursorTy) pvrtmp2616;
            IntTy y380 = (IntTy) pvrtmp2617;
            IntTy fltLitTail1425 = (IntTy) 42;

            return (CursorInt64Prod) {endof1426, fltLitTail1425};
            break;
        }

      case 1:
        {
            CursorTy field_cur1762 = (CursorTy) tmpcur2615;
            CursorTy case921 = (CursorTy) field_cur1762;
            CursorTy x381 = (CursorTy) case921;
            CursorInt64Prod tmp_struct67 =  _traverse_ListSym(end_r641, x381);
            CursorTy pvrtmp2618 = tmp_struct67.field0;
            IntTy pvrtmp2619 = tmp_struct67.field1;
            CursorTy endof1429 = (CursorTy) pvrtmp2618;
            IntTy y383 = (IntTy) pvrtmp2619;
            CursorTy case922 = (CursorTy) endof1429;
            CursorTy jump1427 = case922 + 8;
            SymTy tmpval2620 = *(SymTy *) case922;
            CursorTy tmpcur2621 = case922 + sizeof(SymTy);
            SymTy x382 = (SymTy) tmpval2620;
            CursorTy end_x382 = (CursorTy) tmpcur2621;
            IntTy fltLitTail1428 = (IntTy) 42;

            return (CursorInt64Prod) {jump1427, fltLitTail1428};
            break;
        }

      case 2:
        {
            CursorTy field_cur1765 = (CursorTy) tmpcur2615;
            CursorTy case925 = (CursorTy) field_cur1765;
            SymTy tmpval2622 = *(SymTy *) case925;
            CursorTy tmpcur2623 = case925 + sizeof(SymTy);
            SymTy x385 = (SymTy) tmpval2622;
            CursorTy end_x385 = (CursorTy) tmpcur2623;
            CursorTy jump1430 = case925 + 8;
            IntTy fltLitTail1431 = (IntTy) 42;

            return (CursorInt64Prod) {jump1430, fltLitTail1431};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3458 = *(CursorTy *) tmpcur2615;
            CursorTy tmpaftercur3459 = tmpcur2615 + 8;
            TagTyPacked tagtmp3460 = *(TagTyPacked *) tmpcur3458;
            CursorTy tailtmp3461 = tmpcur3458 + 1;

            tmpval2614 = tagtmp3460;
            tmpcur2615 = tailtmp3461;
            goto switch2624;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3458 = *(CursorTy *) tmpcur2615;
            CursorTy tmpaftercur3459 = tmpcur2615 + 8;
            TagTyPacked tagtmp3460 = *(TagTyPacked *) tmpcur3458;
            CursorTy tailtmp3461 = tmpcur3458 + 1;

            tmpval2614 = tagtmp3460;
            tmpcur2615 = tailtmp3461;
            goto switch2624;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2614");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r644, CursorTy end_r645,
                                         CursorTy loc643, CursorTy arg387)
{
    CursorTy loc642 = (CursorTy) arg387;

    if (loc643 + 18 > end_r645) {
        ChunkTy new_chunk68 = alloc_chunk(end_r645);
        CursorTy chunk_start69 = new_chunk68.start_ptr;
        CursorTy chunk_end70 = new_chunk68.end_ptr;

        end_r645 = chunk_end70;
        *(TagTyPacked *) loc643 = 255;

        CursorTy redir = loc643 + 1;

        *(CursorTy *) redir = chunk_start69;
        loc643 = chunk_start69;
    }

    TagTyPacked tmpval2625 = *(TagTyPacked *) arg387;
    CursorTy tmpcur2626 = arg387 + 1;


  switch2633:
    ;
    switch (tmpval2625) {

      case 0:
        {
            CursorTy field_cur1767 = (CursorTy) tmpcur2626;
            CursorTy case928 = (CursorTy) field_cur1767;
            IntTy tmpval2627 = *(IntTy *) case928;
            CursorTy tmpcur2628 = case928 + sizeof(IntTy);
            IntTy x388 = (IntTy) tmpval2627;
            CursorTy end_x388 = (CursorTy) tmpcur2628;
            CursorTy jump1432 = case928 + 8;

            *(TagTyPacked *) loc643 = 0;

            CursorTy writetag1769 = loc643 + 1;

            *(IntTy *) writetag1769 = x388;

            CursorTy writecur1770 = writetag1769 + sizeof(IntTy);
            CursorTy pvrtmp2630 = (CursorTy) writecur1770;
            CursorTy pvrtmp2629 = (CursorTy) loc643;
            CursorTy taildc1433 = (CursorTy) pvrtmp2629;
            CursorTy end_taildc1433 = (CursorTy) pvrtmp2630;
            CursorTy pvrtmp2632 = (CursorTy) end_taildc1433;
            CursorTy pvrtmp2631 = (CursorTy) taildc1433;
            CursorTy fltPrd2161 = (CursorTy) pvrtmp2631;
            CursorTy fltPrd2162 = (CursorTy) pvrtmp2632;

            return (CursorCursorCursorCursorProd) {end_r645, jump1432,
                                                   fltPrd2161, fltPrd2162};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3462 = *(CursorTy *) tmpcur2626;
            CursorTy tmpaftercur3463 = tmpcur2626 + 8;
            TagTyPacked tagtmp3464 = *(TagTyPacked *) tmpcur3462;
            CursorTy tailtmp3465 = tmpcur3462 + 1;

            tmpval2625 = tagtmp3464;
            tmpcur2626 = tailtmp3465;
            goto switch2633;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3462 = *(CursorTy *) tmpcur2626;
            CursorTy tmpaftercur3463 = tmpcur2626 + 8;
            TagTyPacked tagtmp3464 = *(TagTyPacked *) tmpcur3462;
            CursorTy tailtmp3465 = tmpcur3462 + 1;

            tmpval2625 = tagtmp3464;
            tmpcur2626 = tailtmp3465;
            goto switch2633;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2625");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Datum(CursorTy end_r647, CursorTy arg390)
{
    CursorTy loc646 = (CursorTy) arg390;
    TagTyPacked tmpval2634 = *(TagTyPacked *) arg390;
    CursorTy tmpcur2635 = arg390 + 1;


  switch2638:
    ;
    switch (tmpval2634) {

      case 0:
        {
            CursorTy field_cur1772 = (CursorTy) tmpcur2635;
            CursorTy case934 = (CursorTy) field_cur1772;
            IntTy tmpval2636 = *(IntTy *) case934;
            CursorTy tmpcur2637 = case934 + sizeof(IntTy);
            IntTy x391 = (IntTy) tmpval2636;
            CursorTy end_x391 = (CursorTy) tmpcur2637;
            CursorTy jump1434 = case934 + 8;
            IntTy fltLitTail1435 = (IntTy) 42;

            return (CursorInt64Prod) {jump1434, fltLitTail1435};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3466 = *(CursorTy *) tmpcur2635;
            CursorTy tmpaftercur3467 = tmpcur2635 + 8;
            TagTyPacked tagtmp3468 = *(TagTyPacked *) tmpcur3466;
            CursorTy tailtmp3469 = tmpcur3466 + 1;

            tmpval2634 = tagtmp3468;
            tmpcur2635 = tailtmp3469;
            goto switch2638;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3466 = *(CursorTy *) tmpcur2635;
            CursorTy tmpaftercur3467 = tmpcur2635 + 8;
            TagTyPacked tagtmp3468 = *(TagTyPacked *) tmpcur3466;
            CursorTy tailtmp3469 = tmpcur3466 + 1;

            tmpval2634 = tagtmp3468;
            tmpcur2635 = tailtmp3469;
            goto switch2638;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2634");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r650,
                                              CursorTy end_r651,
                                              CursorTy loc649, CursorTy arg393)
{
    CursorTy loc648 = (CursorTy) arg393;

    if (loc649 + 18 > end_r651) {
        ChunkTy new_chunk74 = alloc_chunk(end_r651);
        CursorTy chunk_start75 = new_chunk74.start_ptr;
        CursorTy chunk_end76 = new_chunk74.end_ptr;

        end_r651 = chunk_end76;
        *(TagTyPacked *) loc649 = 255;

        CursorTy redir = loc649 + 1;

        *(CursorTy *) redir = chunk_start75;
        loc649 = chunk_start75;
    }

    TagTyPacked tmpval2639 = *(TagTyPacked *) arg393;
    CursorTy tmpcur2640 = arg393 + 1;


  switch2673:
    ;
    switch (tmpval2639) {

      case 0:
        {
            CursorTy field_cur1774 = (CursorTy) tmpcur2640;
            CursorTy case937 = (CursorTy) field_cur1774;
            CursorTy x394 = (CursorTy) case937;
            CursorTy loc949 = loc649 + 1;
            CursorCursorCursorCursorProd tmp_struct71 =
                                          _copy_Formals(end_r650, end_r651, loc949, x394);
            CursorTy pvrtmp2641 = tmp_struct71.field0;
            CursorTy pvrtmp2642 = tmp_struct71.field1;
            CursorTy pvrtmp2643 = tmp_struct71.field2;
            CursorTy pvrtmp2644 = tmp_struct71.field3;
            CursorTy fltPrd2163 = (CursorTy) pvrtmp2643;
            CursorTy fltPrd2164 = (CursorTy) pvrtmp2644;
            CursorTy pvrtmp2646 = (CursorTy) fltPrd2164;
            CursorTy pvrtmp2645 = (CursorTy) fltPrd2163;
            CursorTy y397 = (CursorTy) pvrtmp2645;
            CursorTy fltPrd2165 = (CursorTy) pvrtmp2643;
            CursorTy fltPrd2166 = (CursorTy) pvrtmp2644;
            CursorTy pvrtmp2648 = (CursorTy) fltPrd2166;
            CursorTy pvrtmp2647 = (CursorTy) fltPrd2165;
            CursorTy end_y397 = (CursorTy) pvrtmp2648;
            CursorTy end_r651_1580 = (CursorTy) pvrtmp2641;
            CursorTy endof1436 = (CursorTy) pvrtmp2642;
            CursorTy case938 = (CursorTy) endof1436;
            CursorTy x395 = (CursorTy) case938;
            CursorTy loc950 = (CursorTy) end_y397;
            CursorCursorCursorCursorProd tmp_struct72 =
                                          _copy_ListExpr(end_r650, end_r651_1580, loc950, x395);
            CursorTy pvrtmp2649 = tmp_struct72.field0;
            CursorTy pvrtmp2650 = tmp_struct72.field1;
            CursorTy pvrtmp2651 = tmp_struct72.field2;
            CursorTy pvrtmp2652 = tmp_struct72.field3;
            CursorTy fltPrd2167 = (CursorTy) pvrtmp2651;
            CursorTy fltPrd2168 = (CursorTy) pvrtmp2652;
            CursorTy pvrtmp2654 = (CursorTy) fltPrd2168;
            CursorTy pvrtmp2653 = (CursorTy) fltPrd2167;
            CursorTy y398 = (CursorTy) pvrtmp2653;
            CursorTy fltPrd2169 = (CursorTy) pvrtmp2651;
            CursorTy fltPrd2170 = (CursorTy) pvrtmp2652;
            CursorTy pvrtmp2656 = (CursorTy) fltPrd2170;
            CursorTy pvrtmp2655 = (CursorTy) fltPrd2169;
            CursorTy end_y398 = (CursorTy) pvrtmp2656;
            CursorTy end_r651_1580_1581 = (CursorTy) pvrtmp2649;
            CursorTy endof1437 = (CursorTy) pvrtmp2650;
            CursorTy case939 = (CursorTy) endof1437;
            CursorTy x396 = (CursorTy) case939;
            CursorTy loc951 = (CursorTy) end_y398;
            CursorCursorCursorCursorProd tmp_struct73 =
                                          _copy_LAMBDACASE(end_r650, end_r651_1580_1581, loc951, x396);
            CursorTy pvrtmp2657 = tmp_struct73.field0;
            CursorTy pvrtmp2658 = tmp_struct73.field1;
            CursorTy pvrtmp2659 = tmp_struct73.field2;
            CursorTy pvrtmp2660 = tmp_struct73.field3;
            CursorTy fltPrd2171 = (CursorTy) pvrtmp2659;
            CursorTy fltPrd2172 = (CursorTy) pvrtmp2660;
            CursorTy pvrtmp2662 = (CursorTy) fltPrd2172;
            CursorTy pvrtmp2661 = (CursorTy) fltPrd2171;
            CursorTy y399 = (CursorTy) pvrtmp2661;
            CursorTy fltPrd2173 = (CursorTy) pvrtmp2659;
            CursorTy fltPrd2174 = (CursorTy) pvrtmp2660;
            CursorTy pvrtmp2664 = (CursorTy) fltPrd2174;
            CursorTy pvrtmp2663 = (CursorTy) fltPrd2173;
            CursorTy end_y399 = (CursorTy) pvrtmp2664;
            CursorTy end_r651_1580_1581_1582 = (CursorTy) pvrtmp2657;
            CursorTy endof1438 = (CursorTy) pvrtmp2658;

            *(TagTyPacked *) loc649 = 0;

            CursorTy writetag1778 = loc649 + 1;
            CursorTy writecur1779 = (CursorTy) end_y397;
            CursorTy writecur1780 = (CursorTy) end_y398;
            CursorTy writecur1781 = (CursorTy) end_y399;
            CursorTy pvrtmp2666 = (CursorTy) writecur1781;
            CursorTy pvrtmp2665 = (CursorTy) loc649;
            CursorTy taildc1439 = (CursorTy) pvrtmp2665;
            CursorTy end_taildc1439 = (CursorTy) pvrtmp2666;
            CursorTy pvrtmp2668 = (CursorTy) end_taildc1439;
            CursorTy pvrtmp2667 = (CursorTy) taildc1439;
            CursorTy fltPrd2175 = (CursorTy) pvrtmp2667;
            CursorTy fltPrd2176 = (CursorTy) pvrtmp2668;

            return (CursorCursorCursorCursorProd) {end_r651_1580_1581_1582,
                                                   endof1438, fltPrd2175,
                                                   fltPrd2176};
            break;
        }

      case 1:
        {
            CursorTy field_cur1783 = (CursorTy) tmpcur2640;
            CursorTy jump1440 = loc648 + 1;

            *(TagTyPacked *) loc649 = 1;

            CursorTy writetag1784 = loc649 + 1;
            CursorTy pvrtmp2670 = (CursorTy) writetag1784;
            CursorTy pvrtmp2669 = (CursorTy) loc649;
            CursorTy taildc1441 = (CursorTy) pvrtmp2669;
            CursorTy end_taildc1441 = (CursorTy) pvrtmp2670;
            CursorTy pvrtmp2672 = (CursorTy) end_taildc1441;
            CursorTy pvrtmp2671 = (CursorTy) taildc1441;
            CursorTy fltPrd2177 = (CursorTy) pvrtmp2671;
            CursorTy fltPrd2178 = (CursorTy) pvrtmp2672;

            return (CursorCursorCursorCursorProd) {end_r651, jump1440,
                                                   fltPrd2177, fltPrd2178};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3470 = *(CursorTy *) tmpcur2640;
            CursorTy tmpaftercur3471 = tmpcur2640 + 8;
            TagTyPacked tagtmp3472 = *(TagTyPacked *) tmpcur3470;
            CursorTy tailtmp3473 = tmpcur3470 + 1;

            tmpval2639 = tagtmp3472;
            tmpcur2640 = tailtmp3473;
            goto switch2673;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3470 = *(CursorTy *) tmpcur2640;
            CursorTy tmpaftercur3471 = tmpcur2640 + 8;
            TagTyPacked tagtmp3472 = *(TagTyPacked *) tmpcur3470;
            CursorTy tailtmp3473 = tmpcur3470 + 1;

            tmpval2639 = tagtmp3472;
            tmpcur2640 = tailtmp3473;
            goto switch2673;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2639");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_LAMBDACASE(CursorTy end_r653, CursorTy arg400)
{
    CursorTy loc652 = (CursorTy) arg400;
    TagTyPacked tmpval2674 = *(TagTyPacked *) arg400;
    CursorTy tmpcur2675 = arg400 + 1;


  switch2682:
    ;
    switch (tmpval2674) {

      case 0:
        {
            CursorTy field_cur1786 = (CursorTy) tmpcur2675;
            CursorTy case958 = (CursorTy) field_cur1786;
            CursorTy x401 = (CursorTy) case958;
            CursorInt64Prod tmp_struct77 =  _traverse_Formals(end_r653, x401);
            CursorTy pvrtmp2676 = tmp_struct77.field0;
            IntTy pvrtmp2677 = tmp_struct77.field1;
            CursorTy endof1442 = (CursorTy) pvrtmp2676;
            IntTy y404 = (IntTy) pvrtmp2677;
            CursorTy case959 = (CursorTy) endof1442;
            CursorTy x402 = (CursorTy) case959;
            CursorInt64Prod tmp_struct78 =  _traverse_ListExpr(end_r653, x402);
            CursorTy pvrtmp2678 = tmp_struct78.field0;
            IntTy pvrtmp2679 = tmp_struct78.field1;
            CursorTy endof1443 = (CursorTy) pvrtmp2678;
            IntTy y405 = (IntTy) pvrtmp2679;
            CursorTy case960 = (CursorTy) endof1443;
            CursorTy x403 = (CursorTy) case960;
            CursorInt64Prod tmp_struct79 =
                             _traverse_LAMBDACASE(end_r653, x403);
            CursorTy pvrtmp2680 = tmp_struct79.field0;
            IntTy pvrtmp2681 = tmp_struct79.field1;
            CursorTy endof1445 = (CursorTy) pvrtmp2680;
            IntTy y406 = (IntTy) pvrtmp2681;
            IntTy fltLitTail1444 = (IntTy) 42;

            return (CursorInt64Prod) {endof1445, fltLitTail1444};
            break;
        }

      case 1:
        {
            CursorTy field_cur1790 = (CursorTy) tmpcur2675;
            CursorTy jump1446 = loc652 + 1;
            IntTy fltLitTail1447 = (IntTy) 42;

            return (CursorInt64Prod) {jump1446, fltLitTail1447};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3474 = *(CursorTy *) tmpcur2675;
            CursorTy tmpaftercur3475 = tmpcur2675 + 8;
            TagTyPacked tagtmp3476 = *(TagTyPacked *) tmpcur3474;
            CursorTy tailtmp3477 = tmpcur3474 + 1;

            tmpval2674 = tagtmp3476;
            tmpcur2675 = tailtmp3477;
            goto switch2682;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3474 = *(CursorTy *) tmpcur2675;
            CursorTy tmpaftercur3475 = tmpcur2675 + 8;
            TagTyPacked tagtmp3476 = *(TagTyPacked *) tmpcur3474;
            CursorTy tailtmp3477 = tmpcur3474 + 1;

            tmpval2674 = tagtmp3476;
            tmpcur2675 = tailtmp3477;
            goto switch2682;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2674");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r656, CursorTy end_r657,
                                          CursorTy loc655, CursorTy arg407)
{
    CursorTy loc654 = (CursorTy) arg407;

    if (loc655 + 18 > end_r657) {
        ChunkTy new_chunk83 = alloc_chunk(end_r657);
        CursorTy chunk_start84 = new_chunk83.start_ptr;
        CursorTy chunk_end85 = new_chunk83.end_ptr;

        end_r657 = chunk_end85;
        *(TagTyPacked *) loc655 = 255;

        CursorTy redir = loc655 + 1;

        *(CursorTy *) redir = chunk_start84;
        loc655 = chunk_start84;
    }

    TagTyPacked tmpval2683 = *(TagTyPacked *) arg407;
    CursorTy tmpcur2684 = arg407 + 1;


  switch2717:
    ;
    switch (tmpval2683) {

      case 0:
        {
            CursorTy field_cur1791 = (CursorTy) tmpcur2684;
            CursorTy case969 = (CursorTy) field_cur1791;
            CursorTy x408 = (CursorTy) case969;
            CursorTy loc981 = loc655 + 1;
            CursorCursorCursorCursorProd tmp_struct80 =
                                          _copy_ListSym(end_r656, end_r657, loc981, x408);
            CursorTy pvrtmp2685 = tmp_struct80.field0;
            CursorTy pvrtmp2686 = tmp_struct80.field1;
            CursorTy pvrtmp2687 = tmp_struct80.field2;
            CursorTy pvrtmp2688 = tmp_struct80.field3;
            CursorTy fltPrd2179 = (CursorTy) pvrtmp2687;
            CursorTy fltPrd2180 = (CursorTy) pvrtmp2688;
            CursorTy pvrtmp2690 = (CursorTy) fltPrd2180;
            CursorTy pvrtmp2689 = (CursorTy) fltPrd2179;
            CursorTy y411 = (CursorTy) pvrtmp2689;
            CursorTy fltPrd2181 = (CursorTy) pvrtmp2687;
            CursorTy fltPrd2182 = (CursorTy) pvrtmp2688;
            CursorTy pvrtmp2692 = (CursorTy) fltPrd2182;
            CursorTy pvrtmp2691 = (CursorTy) fltPrd2181;
            CursorTy end_y411 = (CursorTy) pvrtmp2692;
            CursorTy end_r657_1583 = (CursorTy) pvrtmp2685;
            CursorTy endof1448 = (CursorTy) pvrtmp2686;
            CursorTy case970 = (CursorTy) endof1448;
            CursorTy x409 = (CursorTy) case970;
            CursorTy loc982 = (CursorTy) end_y411;
            CursorCursorCursorCursorProd tmp_struct81 =
                                          _copy_Expr(end_r656, end_r657_1583, loc982, x409);
            CursorTy pvrtmp2693 = tmp_struct81.field0;
            CursorTy pvrtmp2694 = tmp_struct81.field1;
            CursorTy pvrtmp2695 = tmp_struct81.field2;
            CursorTy pvrtmp2696 = tmp_struct81.field3;
            CursorTy fltPrd2183 = (CursorTy) pvrtmp2695;
            CursorTy fltPrd2184 = (CursorTy) pvrtmp2696;
            CursorTy pvrtmp2698 = (CursorTy) fltPrd2184;
            CursorTy pvrtmp2697 = (CursorTy) fltPrd2183;
            CursorTy y412 = (CursorTy) pvrtmp2697;
            CursorTy fltPrd2185 = (CursorTy) pvrtmp2695;
            CursorTy fltPrd2186 = (CursorTy) pvrtmp2696;
            CursorTy pvrtmp2700 = (CursorTy) fltPrd2186;
            CursorTy pvrtmp2699 = (CursorTy) fltPrd2185;
            CursorTy end_y412 = (CursorTy) pvrtmp2700;
            CursorTy end_r657_1583_1584 = (CursorTy) pvrtmp2693;
            CursorTy endof1449 = (CursorTy) pvrtmp2694;
            CursorTy case971 = (CursorTy) endof1449;
            CursorTy x410 = (CursorTy) case971;
            CursorTy loc983 = (CursorTy) end_y412;
            CursorCursorCursorCursorProd tmp_struct82 =
                                          _copy_LVBIND(end_r656, end_r657_1583_1584, loc983, x410);
            CursorTy pvrtmp2701 = tmp_struct82.field0;
            CursorTy pvrtmp2702 = tmp_struct82.field1;
            CursorTy pvrtmp2703 = tmp_struct82.field2;
            CursorTy pvrtmp2704 = tmp_struct82.field3;
            CursorTy fltPrd2187 = (CursorTy) pvrtmp2703;
            CursorTy fltPrd2188 = (CursorTy) pvrtmp2704;
            CursorTy pvrtmp2706 = (CursorTy) fltPrd2188;
            CursorTy pvrtmp2705 = (CursorTy) fltPrd2187;
            CursorTy y413 = (CursorTy) pvrtmp2705;
            CursorTy fltPrd2189 = (CursorTy) pvrtmp2703;
            CursorTy fltPrd2190 = (CursorTy) pvrtmp2704;
            CursorTy pvrtmp2708 = (CursorTy) fltPrd2190;
            CursorTy pvrtmp2707 = (CursorTy) fltPrd2189;
            CursorTy end_y413 = (CursorTy) pvrtmp2708;
            CursorTy end_r657_1583_1584_1585 = (CursorTy) pvrtmp2701;
            CursorTy endof1450 = (CursorTy) pvrtmp2702;

            *(TagTyPacked *) loc655 = 0;

            CursorTy writetag1795 = loc655 + 1;
            CursorTy writecur1796 = (CursorTy) end_y411;
            CursorTy writecur1797 = (CursorTy) end_y412;
            CursorTy writecur1798 = (CursorTy) end_y413;
            CursorTy pvrtmp2710 = (CursorTy) writecur1798;
            CursorTy pvrtmp2709 = (CursorTy) loc655;
            CursorTy taildc1451 = (CursorTy) pvrtmp2709;
            CursorTy end_taildc1451 = (CursorTy) pvrtmp2710;
            CursorTy pvrtmp2712 = (CursorTy) end_taildc1451;
            CursorTy pvrtmp2711 = (CursorTy) taildc1451;
            CursorTy fltPrd2191 = (CursorTy) pvrtmp2711;
            CursorTy fltPrd2192 = (CursorTy) pvrtmp2712;

            return (CursorCursorCursorCursorProd) {end_r657_1583_1584_1585,
                                                   endof1450, fltPrd2191,
                                                   fltPrd2192};
            break;
        }

      case 1:
        {
            CursorTy field_cur1800 = (CursorTy) tmpcur2684;
            CursorTy jump1452 = loc654 + 1;

            *(TagTyPacked *) loc655 = 1;

            CursorTy writetag1801 = loc655 + 1;
            CursorTy pvrtmp2714 = (CursorTy) writetag1801;
            CursorTy pvrtmp2713 = (CursorTy) loc655;
            CursorTy taildc1453 = (CursorTy) pvrtmp2713;
            CursorTy end_taildc1453 = (CursorTy) pvrtmp2714;
            CursorTy pvrtmp2716 = (CursorTy) end_taildc1453;
            CursorTy pvrtmp2715 = (CursorTy) taildc1453;
            CursorTy fltPrd2193 = (CursorTy) pvrtmp2715;
            CursorTy fltPrd2194 = (CursorTy) pvrtmp2716;

            return (CursorCursorCursorCursorProd) {end_r657, jump1452,
                                                   fltPrd2193, fltPrd2194};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3478 = *(CursorTy *) tmpcur2684;
            CursorTy tmpaftercur3479 = tmpcur2684 + 8;
            TagTyPacked tagtmp3480 = *(TagTyPacked *) tmpcur3478;
            CursorTy tailtmp3481 = tmpcur3478 + 1;

            tmpval2683 = tagtmp3480;
            tmpcur2684 = tailtmp3481;
            goto switch2717;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3478 = *(CursorTy *) tmpcur2684;
            CursorTy tmpaftercur3479 = tmpcur2684 + 8;
            TagTyPacked tagtmp3480 = *(TagTyPacked *) tmpcur3478;
            CursorTy tailtmp3481 = tmpcur3478 + 1;

            tmpval2683 = tagtmp3480;
            tmpcur2684 = tailtmp3481;
            goto switch2717;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2683");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_LVBIND(CursorTy end_r659, CursorTy arg414)
{
    CursorTy loc658 = (CursorTy) arg414;
    TagTyPacked tmpval2718 = *(TagTyPacked *) arg414;
    CursorTy tmpcur2719 = arg414 + 1;


  switch2726:
    ;
    switch (tmpval2718) {

      case 0:
        {
            CursorTy field_cur1803 = (CursorTy) tmpcur2719;
            CursorTy case990 = (CursorTy) field_cur1803;
            CursorTy x415 = (CursorTy) case990;
            CursorInt64Prod tmp_struct86 =  _traverse_ListSym(end_r659, x415);
            CursorTy pvrtmp2720 = tmp_struct86.field0;
            IntTy pvrtmp2721 = tmp_struct86.field1;
            CursorTy endof1454 = (CursorTy) pvrtmp2720;
            IntTy y418 = (IntTy) pvrtmp2721;
            CursorTy case991 = (CursorTy) endof1454;
            CursorTy x416 = (CursorTy) case991;
            CursorInt64Prod tmp_struct87 =  _traverse_Expr(end_r659, x416);
            CursorTy pvrtmp2722 = tmp_struct87.field0;
            IntTy pvrtmp2723 = tmp_struct87.field1;
            CursorTy endof1455 = (CursorTy) pvrtmp2722;
            IntTy y419 = (IntTy) pvrtmp2723;
            CursorTy case992 = (CursorTy) endof1455;
            CursorTy x417 = (CursorTy) case992;
            CursorInt64Prod tmp_struct88 =  _traverse_LVBIND(end_r659, x417);
            CursorTy pvrtmp2724 = tmp_struct88.field0;
            IntTy pvrtmp2725 = tmp_struct88.field1;
            CursorTy endof1457 = (CursorTy) pvrtmp2724;
            IntTy y420 = (IntTy) pvrtmp2725;
            IntTy fltLitTail1456 = (IntTy) 42;

            return (CursorInt64Prod) {endof1457, fltLitTail1456};
            break;
        }

      case 1:
        {
            CursorTy field_cur1807 = (CursorTy) tmpcur2719;
            CursorTy jump1458 = loc658 + 1;
            IntTy fltLitTail1459 = (IntTy) 42;

            return (CursorInt64Prod) {jump1458, fltLitTail1459};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3482 = *(CursorTy *) tmpcur2719;
            CursorTy tmpaftercur3483 = tmpcur2719 + 8;
            TagTyPacked tagtmp3484 = *(TagTyPacked *) tmpcur3482;
            CursorTy tailtmp3485 = tmpcur3482 + 1;

            tmpval2718 = tagtmp3484;
            tmpcur2719 = tailtmp3485;
            goto switch2726;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3482 = *(CursorTy *) tmpcur2719;
            CursorTy tmpaftercur3483 = tmpcur2719 + 8;
            TagTyPacked tagtmp3484 = *(TagTyPacked *) tmpcur3482;
            CursorTy tailtmp3485 = tmpcur3482 + 1;

            tmpval2718 = tagtmp3484;
            tmpcur2719 = tailtmp3485;
            goto switch2726;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2718");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r662, CursorTy end_r663,
                                        CursorTy loc661, CursorTy arg421)
{
    CursorTy loc660 = (CursorTy) arg421;

    if (loc661 + 18 > end_r663) {
        ChunkTy new_chunk111 = alloc_chunk(end_r663);
        CursorTy chunk_start112 = new_chunk111.start_ptr;
        CursorTy chunk_end113 = new_chunk111.end_ptr;

        end_r663 = chunk_end113;
        *(TagTyPacked *) loc661 = 255;

        CursorTy redir = loc661 + 1;

        *(CursorTy *) redir = chunk_start112;
        loc661 = chunk_start112;
    }

    CursorTy loc1088 = loc661 + 1;
    CursorTy loc1089 = loc1088 + 8;
    TagTyPacked tmpval2727 = *(TagTyPacked *) arg421;
    CursorTy tmpcur2728 = arg421 + 1;


  switch2987:
    ;
    switch (tmpval2727) {

      case 0:
        {
            CursorTy field_cur1808 = (CursorTy) tmpcur2728;
            CursorTy case1001 = (CursorTy) field_cur1808;
            SymTy tmpval2729 = *(SymTy *) case1001;
            CursorTy tmpcur2730 = case1001 + sizeof(SymTy);
            SymTy x422 = (SymTy) tmpval2729;
            CursorTy end_x422 = (CursorTy) tmpcur2730;
            CursorTy jump1460 = case1001 + 8;

            *(TagTyPacked *) loc661 = 0;

            CursorTy writetag1810 = loc661 + 1;

            *(SymTy *) writetag1810 = x422;

            CursorTy writecur1811 = writetag1810 + sizeof(SymTy);
            CursorTy pvrtmp2732 = (CursorTy) writecur1811;
            CursorTy pvrtmp2731 = (CursorTy) loc661;
            CursorTy taildc1461 = (CursorTy) pvrtmp2731;
            CursorTy end_taildc1461 = (CursorTy) pvrtmp2732;
            CursorTy pvrtmp2734 = (CursorTy) end_taildc1461;
            CursorTy pvrtmp2733 = (CursorTy) taildc1461;
            CursorTy fltPrd2195 = (CursorTy) pvrtmp2733;
            CursorTy fltPrd2196 = (CursorTy) pvrtmp2734;

            return (CursorCursorCursorCursorProd) {end_r663, jump1460,
                                                   fltPrd2195, fltPrd2196};
            break;
        }

      case 1:
        {
            CursorTy field_cur1813 = (CursorTy) tmpcur2728;
            CursorTy case1005 = (CursorTy) field_cur1813;
            CursorTy x424 = (CursorTy) case1005;
            CursorTy loc1013 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct89 =
                                          _copy_Formals(end_r662, end_r663, loc1013, x424);
            CursorTy pvrtmp2735 = tmp_struct89.field0;
            CursorTy pvrtmp2736 = tmp_struct89.field1;
            CursorTy pvrtmp2737 = tmp_struct89.field2;
            CursorTy pvrtmp2738 = tmp_struct89.field3;
            CursorTy fltPrd2197 = (CursorTy) pvrtmp2737;
            CursorTy fltPrd2198 = (CursorTy) pvrtmp2738;
            CursorTy pvrtmp2740 = (CursorTy) fltPrd2198;
            CursorTy pvrtmp2739 = (CursorTy) fltPrd2197;
            CursorTy y426 = (CursorTy) pvrtmp2739;
            CursorTy fltPrd2199 = (CursorTy) pvrtmp2737;
            CursorTy fltPrd2200 = (CursorTy) pvrtmp2738;
            CursorTy pvrtmp2742 = (CursorTy) fltPrd2200;
            CursorTy pvrtmp2741 = (CursorTy) fltPrd2199;
            CursorTy end_y426 = (CursorTy) pvrtmp2742;
            CursorTy end_r663_1586 = (CursorTy) pvrtmp2735;
            CursorTy endof1462 = (CursorTy) pvrtmp2736;
            CursorTy case1006 = (CursorTy) endof1462;
            CursorTy x425 = (CursorTy) case1006;
            CursorTy loc1014 = (CursorTy) end_y426;
            CursorCursorCursorCursorProd tmp_struct90 =
                                          _copy_ListExpr(end_r662, end_r663_1586, loc1014, x425);
            CursorTy pvrtmp2743 = tmp_struct90.field0;
            CursorTy pvrtmp2744 = tmp_struct90.field1;
            CursorTy pvrtmp2745 = tmp_struct90.field2;
            CursorTy pvrtmp2746 = tmp_struct90.field3;
            CursorTy fltPrd2201 = (CursorTy) pvrtmp2745;
            CursorTy fltPrd2202 = (CursorTy) pvrtmp2746;
            CursorTy pvrtmp2748 = (CursorTy) fltPrd2202;
            CursorTy pvrtmp2747 = (CursorTy) fltPrd2201;
            CursorTy y427 = (CursorTy) pvrtmp2747;
            CursorTy fltPrd2203 = (CursorTy) pvrtmp2745;
            CursorTy fltPrd2204 = (CursorTy) pvrtmp2746;
            CursorTy pvrtmp2750 = (CursorTy) fltPrd2204;
            CursorTy pvrtmp2749 = (CursorTy) fltPrd2203;
            CursorTy end_y427 = (CursorTy) pvrtmp2750;
            CursorTy end_r663_1586_1587 = (CursorTy) pvrtmp2743;
            CursorTy endof1463 = (CursorTy) pvrtmp2744;

            *(TagTyPacked *) loc661 = 1;

            CursorTy writetag1816 = loc661 + 1;
            CursorTy writecur1817 = (CursorTy) end_y426;
            CursorTy writecur1818 = (CursorTy) end_y427;
            CursorTy pvrtmp2752 = (CursorTy) writecur1818;
            CursorTy pvrtmp2751 = (CursorTy) loc661;
            CursorTy taildc1464 = (CursorTy) pvrtmp2751;
            CursorTy end_taildc1464 = (CursorTy) pvrtmp2752;
            CursorTy pvrtmp2754 = (CursorTy) end_taildc1464;
            CursorTy pvrtmp2753 = (CursorTy) taildc1464;
            CursorTy fltPrd2205 = (CursorTy) pvrtmp2753;
            CursorTy fltPrd2206 = (CursorTy) pvrtmp2754;

            return (CursorCursorCursorCursorProd) {end_r663_1586_1587,
                                                   endof1463, fltPrd2205,
                                                   fltPrd2206};
            break;
        }

      case 2:
        {
            CursorTy field_cur1820 = (CursorTy) tmpcur2728;
            CursorTy case1017 = (CursorTy) field_cur1820;
            CursorTy x428 = (CursorTy) case1017;
            CursorTy loc1021 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct91 =
                                          _copy_LAMBDACASE(end_r662, end_r663, loc1021, x428);
            CursorTy pvrtmp2755 = tmp_struct91.field0;
            CursorTy pvrtmp2756 = tmp_struct91.field1;
            CursorTy pvrtmp2757 = tmp_struct91.field2;
            CursorTy pvrtmp2758 = tmp_struct91.field3;
            CursorTy fltPrd2207 = (CursorTy) pvrtmp2757;
            CursorTy fltPrd2208 = (CursorTy) pvrtmp2758;
            CursorTy pvrtmp2760 = (CursorTy) fltPrd2208;
            CursorTy pvrtmp2759 = (CursorTy) fltPrd2207;
            CursorTy y429 = (CursorTy) pvrtmp2759;
            CursorTy fltPrd2209 = (CursorTy) pvrtmp2757;
            CursorTy fltPrd2210 = (CursorTy) pvrtmp2758;
            CursorTy pvrtmp2762 = (CursorTy) fltPrd2210;
            CursorTy pvrtmp2761 = (CursorTy) fltPrd2209;
            CursorTy end_y429 = (CursorTy) pvrtmp2762;
            CursorTy end_r663_1588 = (CursorTy) pvrtmp2755;
            CursorTy endof1465 = (CursorTy) pvrtmp2756;

            *(TagTyPacked *) loc661 = 2;

            CursorTy writetag1822 = loc661 + 1;
            CursorTy writecur1823 = (CursorTy) end_y429;
            CursorTy pvrtmp2764 = (CursorTy) writecur1823;
            CursorTy pvrtmp2763 = (CursorTy) loc661;
            CursorTy taildc1466 = (CursorTy) pvrtmp2763;
            CursorTy end_taildc1466 = (CursorTy) pvrtmp2764;
            CursorTy pvrtmp2766 = (CursorTy) end_taildc1466;
            CursorTy pvrtmp2765 = (CursorTy) taildc1466;
            CursorTy fltPrd2211 = (CursorTy) pvrtmp2765;
            CursorTy fltPrd2212 = (CursorTy) pvrtmp2766;

            return (CursorCursorCursorCursorProd) {end_r663_1588, endof1465,
                                                   fltPrd2211, fltPrd2212};
            break;
        }

      case 3:
        {
            CursorTy field_cur1825 = (CursorTy) tmpcur2728;
            CursorTy case1023 = (CursorTy) field_cur1825;
            CursorTy x430 = (CursorTy) case1023;
            CursorTy loc1035 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct92 =
                                          _copy_Expr(end_r662, end_r663, loc1035, x430);
            CursorTy pvrtmp2767 = tmp_struct92.field0;
            CursorTy pvrtmp2768 = tmp_struct92.field1;
            CursorTy pvrtmp2769 = tmp_struct92.field2;
            CursorTy pvrtmp2770 = tmp_struct92.field3;
            CursorTy fltPrd2213 = (CursorTy) pvrtmp2769;
            CursorTy fltPrd2214 = (CursorTy) pvrtmp2770;
            CursorTy pvrtmp2772 = (CursorTy) fltPrd2214;
            CursorTy pvrtmp2771 = (CursorTy) fltPrd2213;
            CursorTy y433 = (CursorTy) pvrtmp2771;
            CursorTy fltPrd2215 = (CursorTy) pvrtmp2769;
            CursorTy fltPrd2216 = (CursorTy) pvrtmp2770;
            CursorTy pvrtmp2774 = (CursorTy) fltPrd2216;
            CursorTy pvrtmp2773 = (CursorTy) fltPrd2215;
            CursorTy end_y433 = (CursorTy) pvrtmp2774;
            CursorTy end_r663_1589 = (CursorTy) pvrtmp2767;
            CursorTy endof1467 = (CursorTy) pvrtmp2768;
            CursorTy case1024 = (CursorTy) endof1467;
            CursorTy x431 = (CursorTy) case1024;
            CursorTy loc1036 = (CursorTy) end_y433;
            CursorCursorCursorCursorProd tmp_struct93 =
                                          _copy_Expr(end_r662, end_r663_1589, loc1036, x431);
            CursorTy pvrtmp2775 = tmp_struct93.field0;
            CursorTy pvrtmp2776 = tmp_struct93.field1;
            CursorTy pvrtmp2777 = tmp_struct93.field2;
            CursorTy pvrtmp2778 = tmp_struct93.field3;
            CursorTy fltPrd2217 = (CursorTy) pvrtmp2777;
            CursorTy fltPrd2218 = (CursorTy) pvrtmp2778;
            CursorTy pvrtmp2780 = (CursorTy) fltPrd2218;
            CursorTy pvrtmp2779 = (CursorTy) fltPrd2217;
            CursorTy y434 = (CursorTy) pvrtmp2779;
            CursorTy fltPrd2219 = (CursorTy) pvrtmp2777;
            CursorTy fltPrd2220 = (CursorTy) pvrtmp2778;
            CursorTy pvrtmp2782 = (CursorTy) fltPrd2220;
            CursorTy pvrtmp2781 = (CursorTy) fltPrd2219;
            CursorTy end_y434 = (CursorTy) pvrtmp2782;
            CursorTy end_r663_1589_1590 = (CursorTy) pvrtmp2775;
            CursorTy endof1468 = (CursorTy) pvrtmp2776;
            CursorTy case1025 = (CursorTy) endof1468;
            CursorTy x432 = (CursorTy) case1025;
            CursorTy loc1037 = (CursorTy) end_y434;
            CursorCursorCursorCursorProd tmp_struct94 =
                                          _copy_Expr(end_r662, end_r663_1589_1590, loc1037, x432);
            CursorTy pvrtmp2783 = tmp_struct94.field0;
            CursorTy pvrtmp2784 = tmp_struct94.field1;
            CursorTy pvrtmp2785 = tmp_struct94.field2;
            CursorTy pvrtmp2786 = tmp_struct94.field3;
            CursorTy fltPrd2221 = (CursorTy) pvrtmp2785;
            CursorTy fltPrd2222 = (CursorTy) pvrtmp2786;
            CursorTy pvrtmp2788 = (CursorTy) fltPrd2222;
            CursorTy pvrtmp2787 = (CursorTy) fltPrd2221;
            CursorTy y435 = (CursorTy) pvrtmp2787;
            CursorTy fltPrd2223 = (CursorTy) pvrtmp2785;
            CursorTy fltPrd2224 = (CursorTy) pvrtmp2786;
            CursorTy pvrtmp2790 = (CursorTy) fltPrd2224;
            CursorTy pvrtmp2789 = (CursorTy) fltPrd2223;
            CursorTy end_y435 = (CursorTy) pvrtmp2790;
            CursorTy end_r663_1589_1590_1591 = (CursorTy) pvrtmp2783;
            CursorTy endof1469 = (CursorTy) pvrtmp2784;

            *(TagTyPacked *) loc661 = 3;

            CursorTy writetag1829 = loc661 + 1;
            CursorTy writecur1830 = (CursorTy) end_y433;
            CursorTy writecur1831 = (CursorTy) end_y434;
            CursorTy writecur1832 = (CursorTy) end_y435;
            CursorTy pvrtmp2792 = (CursorTy) writecur1832;
            CursorTy pvrtmp2791 = (CursorTy) loc661;
            CursorTy taildc1470 = (CursorTy) pvrtmp2791;
            CursorTy end_taildc1470 = (CursorTy) pvrtmp2792;
            CursorTy pvrtmp2794 = (CursorTy) end_taildc1470;
            CursorTy pvrtmp2793 = (CursorTy) taildc1470;
            CursorTy fltPrd2225 = (CursorTy) pvrtmp2793;
            CursorTy fltPrd2226 = (CursorTy) pvrtmp2794;

            return (CursorCursorCursorCursorProd) {end_r663_1589_1590_1591,
                                                   endof1469, fltPrd2225,
                                                   fltPrd2226};
            break;
        }

      case 4:
        {
            CursorTy field_cur1834 = (CursorTy) tmpcur2728;
            CursorTy case1041 = (CursorTy) field_cur1834;
            CursorTy x436 = (CursorTy) case1041;
            CursorTy loc1045 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct95 =
                                          _copy_ListExpr(end_r662, end_r663, loc1045, x436);
            CursorTy pvrtmp2795 = tmp_struct95.field0;
            CursorTy pvrtmp2796 = tmp_struct95.field1;
            CursorTy pvrtmp2797 = tmp_struct95.field2;
            CursorTy pvrtmp2798 = tmp_struct95.field3;
            CursorTy fltPrd2227 = (CursorTy) pvrtmp2797;
            CursorTy fltPrd2228 = (CursorTy) pvrtmp2798;
            CursorTy pvrtmp2800 = (CursorTy) fltPrd2228;
            CursorTy pvrtmp2799 = (CursorTy) fltPrd2227;
            CursorTy y437 = (CursorTy) pvrtmp2799;
            CursorTy fltPrd2229 = (CursorTy) pvrtmp2797;
            CursorTy fltPrd2230 = (CursorTy) pvrtmp2798;
            CursorTy pvrtmp2802 = (CursorTy) fltPrd2230;
            CursorTy pvrtmp2801 = (CursorTy) fltPrd2229;
            CursorTy end_y437 = (CursorTy) pvrtmp2802;
            CursorTy end_r663_1592 = (CursorTy) pvrtmp2795;
            CursorTy endof1471 = (CursorTy) pvrtmp2796;

            *(TagTyPacked *) loc661 = 4;

            CursorTy writetag1836 = loc661 + 1;
            CursorTy writecur1837 = (CursorTy) end_y437;
            CursorTy pvrtmp2804 = (CursorTy) writecur1837;
            CursorTy pvrtmp2803 = (CursorTy) loc661;
            CursorTy taildc1472 = (CursorTy) pvrtmp2803;
            CursorTy end_taildc1472 = (CursorTy) pvrtmp2804;
            CursorTy pvrtmp2806 = (CursorTy) end_taildc1472;
            CursorTy pvrtmp2805 = (CursorTy) taildc1472;
            CursorTy fltPrd2231 = (CursorTy) pvrtmp2805;
            CursorTy fltPrd2232 = (CursorTy) pvrtmp2806;

            return (CursorCursorCursorCursorProd) {end_r663_1592, endof1471,
                                                   fltPrd2231, fltPrd2232};
            break;
        }

      case 5:
        {
            CursorTy field_cur1839 = (CursorTy) tmpcur2728;
            CursorTy case1047 = (CursorTy) field_cur1839;
            CursorTy x438 = (CursorTy) case1047;
            CursorTy loc1055 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct96 =
                                          _copy_Expr(end_r662, end_r663, loc1055, x438);
            CursorTy pvrtmp2807 = tmp_struct96.field0;
            CursorTy pvrtmp2808 = tmp_struct96.field1;
            CursorTy pvrtmp2809 = tmp_struct96.field2;
            CursorTy pvrtmp2810 = tmp_struct96.field3;
            CursorTy fltPrd2233 = (CursorTy) pvrtmp2809;
            CursorTy fltPrd2234 = (CursorTy) pvrtmp2810;
            CursorTy pvrtmp2812 = (CursorTy) fltPrd2234;
            CursorTy pvrtmp2811 = (CursorTy) fltPrd2233;
            CursorTy y440 = (CursorTy) pvrtmp2811;
            CursorTy fltPrd2235 = (CursorTy) pvrtmp2809;
            CursorTy fltPrd2236 = (CursorTy) pvrtmp2810;
            CursorTy pvrtmp2814 = (CursorTy) fltPrd2236;
            CursorTy pvrtmp2813 = (CursorTy) fltPrd2235;
            CursorTy end_y440 = (CursorTy) pvrtmp2814;
            CursorTy end_r663_1593 = (CursorTy) pvrtmp2807;
            CursorTy endof1473 = (CursorTy) pvrtmp2808;
            CursorTy case1048 = (CursorTy) endof1473;
            CursorTy x439 = (CursorTy) case1048;
            CursorTy loc1056 = (CursorTy) end_y440;
            CursorCursorCursorCursorProd tmp_struct97 =
                                          _copy_ListExpr(end_r662, end_r663_1593, loc1056, x439);
            CursorTy pvrtmp2815 = tmp_struct97.field0;
            CursorTy pvrtmp2816 = tmp_struct97.field1;
            CursorTy pvrtmp2817 = tmp_struct97.field2;
            CursorTy pvrtmp2818 = tmp_struct97.field3;
            CursorTy fltPrd2237 = (CursorTy) pvrtmp2817;
            CursorTy fltPrd2238 = (CursorTy) pvrtmp2818;
            CursorTy pvrtmp2820 = (CursorTy) fltPrd2238;
            CursorTy pvrtmp2819 = (CursorTy) fltPrd2237;
            CursorTy y441 = (CursorTy) pvrtmp2819;
            CursorTy fltPrd2239 = (CursorTy) pvrtmp2817;
            CursorTy fltPrd2240 = (CursorTy) pvrtmp2818;
            CursorTy pvrtmp2822 = (CursorTy) fltPrd2240;
            CursorTy pvrtmp2821 = (CursorTy) fltPrd2239;
            CursorTy end_y441 = (CursorTy) pvrtmp2822;
            CursorTy end_r663_1593_1594 = (CursorTy) pvrtmp2815;
            CursorTy endof1474 = (CursorTy) pvrtmp2816;

            *(TagTyPacked *) loc661 = 5;

            CursorTy writetag1842 = loc661 + 1;
            CursorTy writecur1843 = (CursorTy) end_y440;
            CursorTy writecur1844 = (CursorTy) end_y441;
            CursorTy pvrtmp2824 = (CursorTy) writecur1844;
            CursorTy pvrtmp2823 = (CursorTy) loc661;
            CursorTy taildc1475 = (CursorTy) pvrtmp2823;
            CursorTy end_taildc1475 = (CursorTy) pvrtmp2824;
            CursorTy pvrtmp2826 = (CursorTy) end_taildc1475;
            CursorTy pvrtmp2825 = (CursorTy) taildc1475;
            CursorTy fltPrd2241 = (CursorTy) pvrtmp2825;
            CursorTy fltPrd2242 = (CursorTy) pvrtmp2826;

            return (CursorCursorCursorCursorProd) {end_r663_1593_1594,
                                                   endof1474, fltPrd2241,
                                                   fltPrd2242};
            break;
        }

      case 6:
        {
            CursorTy field_cur1846 = (CursorTy) tmpcur2728;
            CursorTy case1059 = (CursorTy) field_cur1846;
            CursorTy x442 = (CursorTy) case1059;
            CursorTy loc1067 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct98 =
                                          _copy_LVBIND(end_r662, end_r663, loc1067, x442);
            CursorTy pvrtmp2827 = tmp_struct98.field0;
            CursorTy pvrtmp2828 = tmp_struct98.field1;
            CursorTy pvrtmp2829 = tmp_struct98.field2;
            CursorTy pvrtmp2830 = tmp_struct98.field3;
            CursorTy fltPrd2243 = (CursorTy) pvrtmp2829;
            CursorTy fltPrd2244 = (CursorTy) pvrtmp2830;
            CursorTy pvrtmp2832 = (CursorTy) fltPrd2244;
            CursorTy pvrtmp2831 = (CursorTy) fltPrd2243;
            CursorTy y444 = (CursorTy) pvrtmp2831;
            CursorTy fltPrd2245 = (CursorTy) pvrtmp2829;
            CursorTy fltPrd2246 = (CursorTy) pvrtmp2830;
            CursorTy pvrtmp2834 = (CursorTy) fltPrd2246;
            CursorTy pvrtmp2833 = (CursorTy) fltPrd2245;
            CursorTy end_y444 = (CursorTy) pvrtmp2834;
            CursorTy end_r663_1595 = (CursorTy) pvrtmp2827;
            CursorTy endof1476 = (CursorTy) pvrtmp2828;
            CursorTy case1060 = (CursorTy) endof1476;
            CursorTy x443 = (CursorTy) case1060;
            CursorTy loc1068 = (CursorTy) end_y444;
            CursorCursorCursorCursorProd tmp_struct99 =
                                          _copy_ListExpr(end_r662, end_r663_1595, loc1068, x443);
            CursorTy pvrtmp2835 = tmp_struct99.field0;
            CursorTy pvrtmp2836 = tmp_struct99.field1;
            CursorTy pvrtmp2837 = tmp_struct99.field2;
            CursorTy pvrtmp2838 = tmp_struct99.field3;
            CursorTy fltPrd2247 = (CursorTy) pvrtmp2837;
            CursorTy fltPrd2248 = (CursorTy) pvrtmp2838;
            CursorTy pvrtmp2840 = (CursorTy) fltPrd2248;
            CursorTy pvrtmp2839 = (CursorTy) fltPrd2247;
            CursorTy y445 = (CursorTy) pvrtmp2839;
            CursorTy fltPrd2249 = (CursorTy) pvrtmp2837;
            CursorTy fltPrd2250 = (CursorTy) pvrtmp2838;
            CursorTy pvrtmp2842 = (CursorTy) fltPrd2250;
            CursorTy pvrtmp2841 = (CursorTy) fltPrd2249;
            CursorTy end_y445 = (CursorTy) pvrtmp2842;
            CursorTy end_r663_1595_1596 = (CursorTy) pvrtmp2835;
            CursorTy endof1477 = (CursorTy) pvrtmp2836;

            *(TagTyPacked *) loc661 = 6;

            CursorTy writetag1849 = loc661 + 1;
            CursorTy writecur1850 = (CursorTy) end_y444;
            CursorTy writecur1851 = (CursorTy) end_y445;
            CursorTy pvrtmp2844 = (CursorTy) writecur1851;
            CursorTy pvrtmp2843 = (CursorTy) loc661;
            CursorTy taildc1478 = (CursorTy) pvrtmp2843;
            CursorTy end_taildc1478 = (CursorTy) pvrtmp2844;
            CursorTy pvrtmp2846 = (CursorTy) end_taildc1478;
            CursorTy pvrtmp2845 = (CursorTy) taildc1478;
            CursorTy fltPrd2251 = (CursorTy) pvrtmp2845;
            CursorTy fltPrd2252 = (CursorTy) pvrtmp2846;

            return (CursorCursorCursorCursorProd) {end_r663_1595_1596,
                                                   endof1477, fltPrd2251,
                                                   fltPrd2252};
            break;
        }

      case 7:
        {
            CursorTy field_cur1853 = (CursorTy) tmpcur2728;
            CursorTy case1071 = (CursorTy) field_cur1853;
            CursorTy x446 = (CursorTy) case1071;
            CursorTy loc1079 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct100 =
                                          _copy_LVBIND(end_r662, end_r663, loc1079, x446);
            CursorTy pvrtmp2847 = tmp_struct100.field0;
            CursorTy pvrtmp2848 = tmp_struct100.field1;
            CursorTy pvrtmp2849 = tmp_struct100.field2;
            CursorTy pvrtmp2850 = tmp_struct100.field3;
            CursorTy fltPrd2253 = (CursorTy) pvrtmp2849;
            CursorTy fltPrd2254 = (CursorTy) pvrtmp2850;
            CursorTy pvrtmp2852 = (CursorTy) fltPrd2254;
            CursorTy pvrtmp2851 = (CursorTy) fltPrd2253;
            CursorTy y448 = (CursorTy) pvrtmp2851;
            CursorTy fltPrd2255 = (CursorTy) pvrtmp2849;
            CursorTy fltPrd2256 = (CursorTy) pvrtmp2850;
            CursorTy pvrtmp2854 = (CursorTy) fltPrd2256;
            CursorTy pvrtmp2853 = (CursorTy) fltPrd2255;
            CursorTy end_y448 = (CursorTy) pvrtmp2854;
            CursorTy end_r663_1597 = (CursorTy) pvrtmp2847;
            CursorTy endof1479 = (CursorTy) pvrtmp2848;
            CursorTy case1072 = (CursorTy) endof1479;
            CursorTy x447 = (CursorTy) case1072;
            CursorTy loc1080 = (CursorTy) end_y448;
            CursorCursorCursorCursorProd tmp_struct101 =
                                          _copy_ListExpr(end_r662, end_r663_1597, loc1080, x447);
            CursorTy pvrtmp2855 = tmp_struct101.field0;
            CursorTy pvrtmp2856 = tmp_struct101.field1;
            CursorTy pvrtmp2857 = tmp_struct101.field2;
            CursorTy pvrtmp2858 = tmp_struct101.field3;
            CursorTy fltPrd2257 = (CursorTy) pvrtmp2857;
            CursorTy fltPrd2258 = (CursorTy) pvrtmp2858;
            CursorTy pvrtmp2860 = (CursorTy) fltPrd2258;
            CursorTy pvrtmp2859 = (CursorTy) fltPrd2257;
            CursorTy y449 = (CursorTy) pvrtmp2859;
            CursorTy fltPrd2259 = (CursorTy) pvrtmp2857;
            CursorTy fltPrd2260 = (CursorTy) pvrtmp2858;
            CursorTy pvrtmp2862 = (CursorTy) fltPrd2260;
            CursorTy pvrtmp2861 = (CursorTy) fltPrd2259;
            CursorTy end_y449 = (CursorTy) pvrtmp2862;
            CursorTy end_r663_1597_1598 = (CursorTy) pvrtmp2855;
            CursorTy endof1480 = (CursorTy) pvrtmp2856;

            *(TagTyPacked *) loc661 = 7;

            CursorTy writetag1856 = loc661 + 1;
            CursorTy writecur1857 = (CursorTy) end_y448;
            CursorTy writecur1858 = (CursorTy) end_y449;
            CursorTy pvrtmp2864 = (CursorTy) writecur1858;
            CursorTy pvrtmp2863 = (CursorTy) loc661;
            CursorTy taildc1481 = (CursorTy) pvrtmp2863;
            CursorTy end_taildc1481 = (CursorTy) pvrtmp2864;
            CursorTy pvrtmp2866 = (CursorTy) end_taildc1481;
            CursorTy pvrtmp2865 = (CursorTy) taildc1481;
            CursorTy fltPrd2261 = (CursorTy) pvrtmp2865;
            CursorTy fltPrd2262 = (CursorTy) pvrtmp2866;

            return (CursorCursorCursorCursorProd) {end_r663_1597_1598,
                                                   endof1480, fltPrd2261,
                                                   fltPrd2262};
            break;
        }

      case 8:
        {
            CursorTy field_cur1860 = (CursorTy) tmpcur2728;
            CursorTy case1083 = (CursorTy) field_cur1860;
            SymTy tmpval2867 = *(SymTy *) case1083;
            CursorTy tmpcur2868 = case1083 + sizeof(SymTy);
            SymTy x450 = (SymTy) tmpval2867;
            CursorTy end_x450 = (CursorTy) tmpcur2868;
            CursorTy case1084 = (CursorTy) end_x450;
            CursorTy x451 = (CursorTy) case1084;
            CursorTy jump1482 = case1083 + 8;
            CursorCursorCursorCursorProd tmp_struct102 =
                                          _copy_Expr(end_r662, end_r663, loc1089, x451);
            CursorTy pvrtmp2869 = tmp_struct102.field0;
            CursorTy pvrtmp2870 = tmp_struct102.field1;
            CursorTy pvrtmp2871 = tmp_struct102.field2;
            CursorTy pvrtmp2872 = tmp_struct102.field3;
            CursorTy fltPrd2263 = (CursorTy) pvrtmp2871;
            CursorTy fltPrd2264 = (CursorTy) pvrtmp2872;
            CursorTy pvrtmp2874 = (CursorTy) fltPrd2264;
            CursorTy pvrtmp2873 = (CursorTy) fltPrd2263;
            CursorTy y453 = (CursorTy) pvrtmp2873;
            CursorTy fltPrd2265 = (CursorTy) pvrtmp2871;
            CursorTy fltPrd2266 = (CursorTy) pvrtmp2872;
            CursorTy pvrtmp2876 = (CursorTy) fltPrd2266;
            CursorTy pvrtmp2875 = (CursorTy) fltPrd2265;
            CursorTy end_y453 = (CursorTy) pvrtmp2876;
            CursorTy end_r663_1599 = (CursorTy) pvrtmp2869;
            CursorTy endof1483 = (CursorTy) pvrtmp2870;

            *(TagTyPacked *) loc661 = 8;

            CursorTy writetag1863 = loc661 + 1;

            *(SymTy *) writetag1863 = x450;

            CursorTy writecur1864 = writetag1863 + sizeof(SymTy);
            CursorTy writecur1865 = (CursorTy) end_y453;
            CursorTy pvrtmp2878 = (CursorTy) writecur1865;
            CursorTy pvrtmp2877 = (CursorTy) loc661;
            CursorTy taildc1484 = (CursorTy) pvrtmp2877;
            CursorTy end_taildc1484 = (CursorTy) pvrtmp2878;
            CursorTy pvrtmp2880 = (CursorTy) end_taildc1484;
            CursorTy pvrtmp2879 = (CursorTy) taildc1484;
            CursorTy fltPrd2267 = (CursorTy) pvrtmp2879;
            CursorTy fltPrd2268 = (CursorTy) pvrtmp2880;

            return (CursorCursorCursorCursorProd) {end_r663_1599, endof1483,
                                                   fltPrd2267, fltPrd2268};
            break;
        }

      case 9:
        {
            CursorTy field_cur1867 = (CursorTy) tmpcur2728;
            CursorTy case1093 = (CursorTy) field_cur1867;
            CursorTy x454 = (CursorTy) case1093;
            CursorTy loc1097 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct103 =
                                          _copy_Datum(end_r662, end_r663, loc1097, x454);
            CursorTy pvrtmp2881 = tmp_struct103.field0;
            CursorTy pvrtmp2882 = tmp_struct103.field1;
            CursorTy pvrtmp2883 = tmp_struct103.field2;
            CursorTy pvrtmp2884 = tmp_struct103.field3;
            CursorTy fltPrd2269 = (CursorTy) pvrtmp2883;
            CursorTy fltPrd2270 = (CursorTy) pvrtmp2884;
            CursorTy pvrtmp2886 = (CursorTy) fltPrd2270;
            CursorTy pvrtmp2885 = (CursorTy) fltPrd2269;
            CursorTy y455 = (CursorTy) pvrtmp2885;
            CursorTy fltPrd2271 = (CursorTy) pvrtmp2883;
            CursorTy fltPrd2272 = (CursorTy) pvrtmp2884;
            CursorTy pvrtmp2888 = (CursorTy) fltPrd2272;
            CursorTy pvrtmp2887 = (CursorTy) fltPrd2271;
            CursorTy end_y455 = (CursorTy) pvrtmp2888;
            CursorTy end_r663_1600 = (CursorTy) pvrtmp2881;
            CursorTy endof1485 = (CursorTy) pvrtmp2882;

            *(TagTyPacked *) loc661 = 9;

            CursorTy writetag1869 = loc661 + 1;
            CursorTy writecur1870 = (CursorTy) end_y455;
            CursorTy pvrtmp2890 = (CursorTy) writecur1870;
            CursorTy pvrtmp2889 = (CursorTy) loc661;
            CursorTy taildc1486 = (CursorTy) pvrtmp2889;
            CursorTy end_taildc1486 = (CursorTy) pvrtmp2890;
            CursorTy pvrtmp2892 = (CursorTy) end_taildc1486;
            CursorTy pvrtmp2891 = (CursorTy) taildc1486;
            CursorTy fltPrd2273 = (CursorTy) pvrtmp2891;
            CursorTy fltPrd2274 = (CursorTy) pvrtmp2892;

            return (CursorCursorCursorCursorProd) {end_r663_1600, endof1485,
                                                   fltPrd2273, fltPrd2274};
            break;
        }

      case 10:
        {
            CursorTy field_cur1872 = (CursorTy) tmpcur2728;
            CursorTy case1099 = (CursorTy) field_cur1872;
            CursorTy x456 = (CursorTy) case1099;
            CursorTy loc1103 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct104 =
                                          _copy_Datum(end_r662, end_r663, loc1103, x456);
            CursorTy pvrtmp2893 = tmp_struct104.field0;
            CursorTy pvrtmp2894 = tmp_struct104.field1;
            CursorTy pvrtmp2895 = tmp_struct104.field2;
            CursorTy pvrtmp2896 = tmp_struct104.field3;
            CursorTy fltPrd2275 = (CursorTy) pvrtmp2895;
            CursorTy fltPrd2276 = (CursorTy) pvrtmp2896;
            CursorTy pvrtmp2898 = (CursorTy) fltPrd2276;
            CursorTy pvrtmp2897 = (CursorTy) fltPrd2275;
            CursorTy y457 = (CursorTy) pvrtmp2897;
            CursorTy fltPrd2277 = (CursorTy) pvrtmp2895;
            CursorTy fltPrd2278 = (CursorTy) pvrtmp2896;
            CursorTy pvrtmp2900 = (CursorTy) fltPrd2278;
            CursorTy pvrtmp2899 = (CursorTy) fltPrd2277;
            CursorTy end_y457 = (CursorTy) pvrtmp2900;
            CursorTy end_r663_1601 = (CursorTy) pvrtmp2893;
            CursorTy endof1487 = (CursorTy) pvrtmp2894;

            *(TagTyPacked *) loc661 = 10;

            CursorTy writetag1874 = loc661 + 1;
            CursorTy writecur1875 = (CursorTy) end_y457;
            CursorTy pvrtmp2902 = (CursorTy) writecur1875;
            CursorTy pvrtmp2901 = (CursorTy) loc661;
            CursorTy taildc1488 = (CursorTy) pvrtmp2901;
            CursorTy end_taildc1488 = (CursorTy) pvrtmp2902;
            CursorTy pvrtmp2904 = (CursorTy) end_taildc1488;
            CursorTy pvrtmp2903 = (CursorTy) taildc1488;
            CursorTy fltPrd2279 = (CursorTy) pvrtmp2903;
            CursorTy fltPrd2280 = (CursorTy) pvrtmp2904;

            return (CursorCursorCursorCursorProd) {end_r663_1601, endof1487,
                                                   fltPrd2279, fltPrd2280};
            break;
        }

      case 11:
        {
            CursorTy field_cur1877 = (CursorTy) tmpcur2728;
            CursorTy case1105 = (CursorTy) field_cur1877;
            CursorTy x458 = (CursorTy) case1105;
            CursorTy loc1109 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct105 =
                                          _copy_Datum(end_r662, end_r663, loc1109, x458);
            CursorTy pvrtmp2905 = tmp_struct105.field0;
            CursorTy pvrtmp2906 = tmp_struct105.field1;
            CursorTy pvrtmp2907 = tmp_struct105.field2;
            CursorTy pvrtmp2908 = tmp_struct105.field3;
            CursorTy fltPrd2281 = (CursorTy) pvrtmp2907;
            CursorTy fltPrd2282 = (CursorTy) pvrtmp2908;
            CursorTy pvrtmp2910 = (CursorTy) fltPrd2282;
            CursorTy pvrtmp2909 = (CursorTy) fltPrd2281;
            CursorTy y459 = (CursorTy) pvrtmp2909;
            CursorTy fltPrd2283 = (CursorTy) pvrtmp2907;
            CursorTy fltPrd2284 = (CursorTy) pvrtmp2908;
            CursorTy pvrtmp2912 = (CursorTy) fltPrd2284;
            CursorTy pvrtmp2911 = (CursorTy) fltPrd2283;
            CursorTy end_y459 = (CursorTy) pvrtmp2912;
            CursorTy end_r663_1602 = (CursorTy) pvrtmp2905;
            CursorTy endof1489 = (CursorTy) pvrtmp2906;

            *(TagTyPacked *) loc661 = 11;

            CursorTy writetag1879 = loc661 + 1;
            CursorTy writecur1880 = (CursorTy) end_y459;
            CursorTy pvrtmp2914 = (CursorTy) writecur1880;
            CursorTy pvrtmp2913 = (CursorTy) loc661;
            CursorTy taildc1490 = (CursorTy) pvrtmp2913;
            CursorTy end_taildc1490 = (CursorTy) pvrtmp2914;
            CursorTy pvrtmp2916 = (CursorTy) end_taildc1490;
            CursorTy pvrtmp2915 = (CursorTy) taildc1490;
            CursorTy fltPrd2285 = (CursorTy) pvrtmp2915;
            CursorTy fltPrd2286 = (CursorTy) pvrtmp2916;

            return (CursorCursorCursorCursorProd) {end_r663_1602, endof1489,
                                                   fltPrd2285, fltPrd2286};
            break;
        }

      case 12:
        {
            CursorTy field_cur1882 = (CursorTy) tmpcur2728;
            CursorTy case1111 = (CursorTy) field_cur1882;
            CursorTy x460 = (CursorTy) case1111;
            CursorTy loc1123 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct106 =
                                          _copy_Expr(end_r662, end_r663, loc1123, x460);
            CursorTy pvrtmp2917 = tmp_struct106.field0;
            CursorTy pvrtmp2918 = tmp_struct106.field1;
            CursorTy pvrtmp2919 = tmp_struct106.field2;
            CursorTy pvrtmp2920 = tmp_struct106.field3;
            CursorTy fltPrd2287 = (CursorTy) pvrtmp2919;
            CursorTy fltPrd2288 = (CursorTy) pvrtmp2920;
            CursorTy pvrtmp2922 = (CursorTy) fltPrd2288;
            CursorTy pvrtmp2921 = (CursorTy) fltPrd2287;
            CursorTy y463 = (CursorTy) pvrtmp2921;
            CursorTy fltPrd2289 = (CursorTy) pvrtmp2919;
            CursorTy fltPrd2290 = (CursorTy) pvrtmp2920;
            CursorTy pvrtmp2924 = (CursorTy) fltPrd2290;
            CursorTy pvrtmp2923 = (CursorTy) fltPrd2289;
            CursorTy end_y463 = (CursorTy) pvrtmp2924;
            CursorTy end_r663_1603 = (CursorTy) pvrtmp2917;
            CursorTy endof1491 = (CursorTy) pvrtmp2918;
            CursorTy case1112 = (CursorTy) endof1491;
            CursorTy x461 = (CursorTy) case1112;
            CursorTy loc1124 = (CursorTy) end_y463;
            CursorCursorCursorCursorProd tmp_struct107 =
                                          _copy_Expr(end_r662, end_r663_1603, loc1124, x461);
            CursorTy pvrtmp2925 = tmp_struct107.field0;
            CursorTy pvrtmp2926 = tmp_struct107.field1;
            CursorTy pvrtmp2927 = tmp_struct107.field2;
            CursorTy pvrtmp2928 = tmp_struct107.field3;
            CursorTy fltPrd2291 = (CursorTy) pvrtmp2927;
            CursorTy fltPrd2292 = (CursorTy) pvrtmp2928;
            CursorTy pvrtmp2930 = (CursorTy) fltPrd2292;
            CursorTy pvrtmp2929 = (CursorTy) fltPrd2291;
            CursorTy y464 = (CursorTy) pvrtmp2929;
            CursorTy fltPrd2293 = (CursorTy) pvrtmp2927;
            CursorTy fltPrd2294 = (CursorTy) pvrtmp2928;
            CursorTy pvrtmp2932 = (CursorTy) fltPrd2294;
            CursorTy pvrtmp2931 = (CursorTy) fltPrd2293;
            CursorTy end_y464 = (CursorTy) pvrtmp2932;
            CursorTy end_r663_1603_1604 = (CursorTy) pvrtmp2925;
            CursorTy endof1492 = (CursorTy) pvrtmp2926;
            CursorTy case1113 = (CursorTy) endof1492;
            CursorTy x462 = (CursorTy) case1113;
            CursorTy loc1125 = (CursorTy) end_y464;
            CursorCursorCursorCursorProd tmp_struct108 =
                                          _copy_Expr(end_r662, end_r663_1603_1604, loc1125, x462);
            CursorTy pvrtmp2933 = tmp_struct108.field0;
            CursorTy pvrtmp2934 = tmp_struct108.field1;
            CursorTy pvrtmp2935 = tmp_struct108.field2;
            CursorTy pvrtmp2936 = tmp_struct108.field3;
            CursorTy fltPrd2295 = (CursorTy) pvrtmp2935;
            CursorTy fltPrd2296 = (CursorTy) pvrtmp2936;
            CursorTy pvrtmp2938 = (CursorTy) fltPrd2296;
            CursorTy pvrtmp2937 = (CursorTy) fltPrd2295;
            CursorTy y465 = (CursorTy) pvrtmp2937;
            CursorTy fltPrd2297 = (CursorTy) pvrtmp2935;
            CursorTy fltPrd2298 = (CursorTy) pvrtmp2936;
            CursorTy pvrtmp2940 = (CursorTy) fltPrd2298;
            CursorTy pvrtmp2939 = (CursorTy) fltPrd2297;
            CursorTy end_y465 = (CursorTy) pvrtmp2940;
            CursorTy end_r663_1603_1604_1605 = (CursorTy) pvrtmp2933;
            CursorTy endof1493 = (CursorTy) pvrtmp2934;

            *(TagTyPacked *) loc661 = 12;

            CursorTy writetag1886 = loc661 + 1;
            CursorTy writecur1887 = (CursorTy) end_y463;
            CursorTy writecur1888 = (CursorTy) end_y464;
            CursorTy writecur1889 = (CursorTy) end_y465;
            CursorTy pvrtmp2942 = (CursorTy) writecur1889;
            CursorTy pvrtmp2941 = (CursorTy) loc661;
            CursorTy taildc1494 = (CursorTy) pvrtmp2941;
            CursorTy end_taildc1494 = (CursorTy) pvrtmp2942;
            CursorTy pvrtmp2944 = (CursorTy) end_taildc1494;
            CursorTy pvrtmp2943 = (CursorTy) taildc1494;
            CursorTy fltPrd2299 = (CursorTy) pvrtmp2943;
            CursorTy fltPrd2300 = (CursorTy) pvrtmp2944;

            return (CursorCursorCursorCursorProd) {end_r663_1603_1604_1605,
                                                   endof1493, fltPrd2299,
                                                   fltPrd2300};
            break;
        }

      case 13:
        {
            CursorTy field_cur1891 = (CursorTy) tmpcur2728;
            CursorTy case1129 = (CursorTy) field_cur1891;
            CursorTy x466 = (CursorTy) case1129;
            CursorTy loc1137 = loc661 + 1;
            CursorCursorCursorCursorProd tmp_struct109 =
                                          _copy_Expr(end_r662, end_r663, loc1137, x466);
            CursorTy pvrtmp2945 = tmp_struct109.field0;
            CursorTy pvrtmp2946 = tmp_struct109.field1;
            CursorTy pvrtmp2947 = tmp_struct109.field2;
            CursorTy pvrtmp2948 = tmp_struct109.field3;
            CursorTy fltPrd2301 = (CursorTy) pvrtmp2947;
            CursorTy fltPrd2302 = (CursorTy) pvrtmp2948;
            CursorTy pvrtmp2950 = (CursorTy) fltPrd2302;
            CursorTy pvrtmp2949 = (CursorTy) fltPrd2301;
            CursorTy y468 = (CursorTy) pvrtmp2949;
            CursorTy fltPrd2303 = (CursorTy) pvrtmp2947;
            CursorTy fltPrd2304 = (CursorTy) pvrtmp2948;
            CursorTy pvrtmp2952 = (CursorTy) fltPrd2304;
            CursorTy pvrtmp2951 = (CursorTy) fltPrd2303;
            CursorTy end_y468 = (CursorTy) pvrtmp2952;
            CursorTy end_r663_1606 = (CursorTy) pvrtmp2945;
            CursorTy endof1495 = (CursorTy) pvrtmp2946;
            CursorTy case1130 = (CursorTy) endof1495;
            CursorTy x467 = (CursorTy) case1130;
            CursorTy loc1138 = (CursorTy) end_y468;
            CursorCursorCursorCursorProd tmp_struct110 =
                                          _copy_ListExpr(end_r662, end_r663_1606, loc1138, x467);
            CursorTy pvrtmp2953 = tmp_struct110.field0;
            CursorTy pvrtmp2954 = tmp_struct110.field1;
            CursorTy pvrtmp2955 = tmp_struct110.field2;
            CursorTy pvrtmp2956 = tmp_struct110.field3;
            CursorTy fltPrd2305 = (CursorTy) pvrtmp2955;
            CursorTy fltPrd2306 = (CursorTy) pvrtmp2956;
            CursorTy pvrtmp2958 = (CursorTy) fltPrd2306;
            CursorTy pvrtmp2957 = (CursorTy) fltPrd2305;
            CursorTy y469 = (CursorTy) pvrtmp2957;
            CursorTy fltPrd2307 = (CursorTy) pvrtmp2955;
            CursorTy fltPrd2308 = (CursorTy) pvrtmp2956;
            CursorTy pvrtmp2960 = (CursorTy) fltPrd2308;
            CursorTy pvrtmp2959 = (CursorTy) fltPrd2307;
            CursorTy end_y469 = (CursorTy) pvrtmp2960;
            CursorTy end_r663_1606_1607 = (CursorTy) pvrtmp2953;
            CursorTy endof1496 = (CursorTy) pvrtmp2954;

            *(TagTyPacked *) loc661 = 13;

            CursorTy writetag1894 = loc661 + 1;
            CursorTy writecur1895 = (CursorTy) end_y468;
            CursorTy writecur1896 = (CursorTy) end_y469;
            CursorTy pvrtmp2962 = (CursorTy) writecur1896;
            CursorTy pvrtmp2961 = (CursorTy) loc661;
            CursorTy taildc1497 = (CursorTy) pvrtmp2961;
            CursorTy end_taildc1497 = (CursorTy) pvrtmp2962;
            CursorTy pvrtmp2964 = (CursorTy) end_taildc1497;
            CursorTy pvrtmp2963 = (CursorTy) taildc1497;
            CursorTy fltPrd2309 = (CursorTy) pvrtmp2963;
            CursorTy fltPrd2310 = (CursorTy) pvrtmp2964;

            return (CursorCursorCursorCursorProd) {end_r663_1606_1607,
                                                   endof1496, fltPrd2309,
                                                   fltPrd2310};
            break;
        }

      case 14:
        {
            CursorTy field_cur1898 = (CursorTy) tmpcur2728;
            CursorTy case1141 = (CursorTy) field_cur1898;
            SymTy tmpval2965 = *(SymTy *) case1141;
            CursorTy tmpcur2966 = case1141 + sizeof(SymTy);
            SymTy x470 = (SymTy) tmpval2965;
            CursorTy end_x470 = (CursorTy) tmpcur2966;
            CursorTy jump1498 = case1141 + 8;

            *(TagTyPacked *) loc661 = 14;

            CursorTy writetag1900 = loc661 + 1;

            *(SymTy *) writetag1900 = x470;

            CursorTy writecur1901 = writetag1900 + sizeof(SymTy);
            CursorTy pvrtmp2968 = (CursorTy) writecur1901;
            CursorTy pvrtmp2967 = (CursorTy) loc661;
            CursorTy taildc1499 = (CursorTy) pvrtmp2967;
            CursorTy end_taildc1499 = (CursorTy) pvrtmp2968;
            CursorTy pvrtmp2970 = (CursorTy) end_taildc1499;
            CursorTy pvrtmp2969 = (CursorTy) taildc1499;
            CursorTy fltPrd2311 = (CursorTy) pvrtmp2969;
            CursorTy fltPrd2312 = (CursorTy) pvrtmp2970;

            return (CursorCursorCursorCursorProd) {end_r663, jump1498,
                                                   fltPrd2311, fltPrd2312};
            break;
        }

      case 15:
        {
            CursorTy field_cur1903 = (CursorTy) tmpcur2728;
            CursorTy case1145 = (CursorTy) field_cur1903;
            SymTy tmpval2971 = *(SymTy *) case1145;
            CursorTy tmpcur2972 = case1145 + sizeof(SymTy);
            SymTy x472 = (SymTy) tmpval2971;
            CursorTy end_x472 = (CursorTy) tmpcur2972;
            CursorTy jump1500 = case1145 + 8;

            *(TagTyPacked *) loc661 = 15;

            CursorTy writetag1905 = loc661 + 1;

            *(SymTy *) writetag1905 = x472;

            CursorTy writecur1906 = writetag1905 + sizeof(SymTy);
            CursorTy pvrtmp2974 = (CursorTy) writecur1906;
            CursorTy pvrtmp2973 = (CursorTy) loc661;
            CursorTy taildc1501 = (CursorTy) pvrtmp2973;
            CursorTy end_taildc1501 = (CursorTy) pvrtmp2974;
            CursorTy pvrtmp2976 = (CursorTy) end_taildc1501;
            CursorTy pvrtmp2975 = (CursorTy) taildc1501;
            CursorTy fltPrd2313 = (CursorTy) pvrtmp2975;
            CursorTy fltPrd2314 = (CursorTy) pvrtmp2976;

            return (CursorCursorCursorCursorProd) {end_r663, jump1500,
                                                   fltPrd2313, fltPrd2314};
            break;
        }

      case 16:
        {
            CursorTy field_cur1908 = (CursorTy) tmpcur2728;
            CursorTy case1149 = (CursorTy) field_cur1908;
            SymTy tmpval2977 = *(SymTy *) case1149;
            CursorTy tmpcur2978 = case1149 + sizeof(SymTy);
            SymTy x474 = (SymTy) tmpval2977;
            CursorTy end_x474 = (CursorTy) tmpcur2978;
            CursorTy jump1502 = case1149 + 8;

            *(TagTyPacked *) loc661 = 16;

            CursorTy writetag1910 = loc661 + 1;

            *(SymTy *) writetag1910 = x474;

            CursorTy writecur1911 = writetag1910 + sizeof(SymTy);
            CursorTy pvrtmp2980 = (CursorTy) writecur1911;
            CursorTy pvrtmp2979 = (CursorTy) loc661;
            CursorTy taildc1503 = (CursorTy) pvrtmp2979;
            CursorTy end_taildc1503 = (CursorTy) pvrtmp2980;
            CursorTy pvrtmp2982 = (CursorTy) end_taildc1503;
            CursorTy pvrtmp2981 = (CursorTy) taildc1503;
            CursorTy fltPrd2315 = (CursorTy) pvrtmp2981;
            CursorTy fltPrd2316 = (CursorTy) pvrtmp2982;

            return (CursorCursorCursorCursorProd) {end_r663, jump1502,
                                                   fltPrd2315, fltPrd2316};
            break;
        }

      case 17:
        {
            CursorTy field_cur1913 = (CursorTy) tmpcur2728;
            CursorTy jump1504 = loc660 + 1;

            *(TagTyPacked *) loc661 = 17;

            CursorTy writetag1914 = loc661 + 1;
            CursorTy pvrtmp2984 = (CursorTy) writetag1914;
            CursorTy pvrtmp2983 = (CursorTy) loc661;
            CursorTy taildc1505 = (CursorTy) pvrtmp2983;
            CursorTy end_taildc1505 = (CursorTy) pvrtmp2984;
            CursorTy pvrtmp2986 = (CursorTy) end_taildc1505;
            CursorTy pvrtmp2985 = (CursorTy) taildc1505;
            CursorTy fltPrd2317 = (CursorTy) pvrtmp2985;
            CursorTy fltPrd2318 = (CursorTy) pvrtmp2986;

            return (CursorCursorCursorCursorProd) {end_r663, jump1504,
                                                   fltPrd2317, fltPrd2318};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3486 = *(CursorTy *) tmpcur2728;
            CursorTy tmpaftercur3487 = tmpcur2728 + 8;
            TagTyPacked tagtmp3488 = *(TagTyPacked *) tmpcur3486;
            CursorTy tailtmp3489 = tmpcur3486 + 1;

            tmpval2727 = tagtmp3488;
            tmpcur2728 = tailtmp3489;
            goto switch2987;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3486 = *(CursorTy *) tmpcur2728;
            CursorTy tmpaftercur3487 = tmpcur2728 + 8;
            TagTyPacked tagtmp3488 = *(TagTyPacked *) tmpcur3486;
            CursorTy tailtmp3489 = tmpcur3486 + 1;

            tmpval2727 = tagtmp3488;
            tmpcur2728 = tailtmp3489;
            goto switch2987;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2727");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Expr(CursorTy end_r665, CursorTy arg476)
{
    CursorTy loc664 = (CursorTy) arg476;
    TagTyPacked tmpval2988 = *(TagTyPacked *) arg476;
    CursorTy tmpcur2989 = arg476 + 1;


  switch3044:
    ;
    switch (tmpval2988) {

      case 0:
        {
            CursorTy field_cur1916 = (CursorTy) tmpcur2989;
            CursorTy case1156 = (CursorTy) field_cur1916;
            SymTy tmpval2990 = *(SymTy *) case1156;
            CursorTy tmpcur2991 = case1156 + sizeof(SymTy);
            SymTy x477 = (SymTy) tmpval2990;
            CursorTy end_x477 = (CursorTy) tmpcur2991;
            CursorTy jump1506 = case1156 + 8;
            IntTy fltLitTail1507 = (IntTy) 42;

            return (CursorInt64Prod) {jump1506, fltLitTail1507};
            break;
        }

      case 1:
        {
            CursorTy field_cur1918 = (CursorTy) tmpcur2989;
            CursorTy case1157 = (CursorTy) field_cur1918;
            CursorTy x479 = (CursorTy) case1157;
            CursorInt64Prod tmp_struct114 =  _traverse_Formals(end_r665, x479);
            CursorTy pvrtmp2992 = tmp_struct114.field0;
            IntTy pvrtmp2993 = tmp_struct114.field1;
            CursorTy endof1508 = (CursorTy) pvrtmp2992;
            IntTy y481 = (IntTy) pvrtmp2993;
            CursorTy case1158 = (CursorTy) endof1508;
            CursorTy x480 = (CursorTy) case1158;
            CursorInt64Prod tmp_struct115 =  _traverse_ListExpr(end_r665, x480);
            CursorTy pvrtmp2994 = tmp_struct115.field0;
            IntTy pvrtmp2995 = tmp_struct115.field1;
            CursorTy endof1510 = (CursorTy) pvrtmp2994;
            IntTy y482 = (IntTy) pvrtmp2995;
            IntTy fltLitTail1509 = (IntTy) 42;

            return (CursorInt64Prod) {endof1510, fltLitTail1509};
            break;
        }

      case 2:
        {
            CursorTy field_cur1921 = (CursorTy) tmpcur2989;
            CursorTy case1163 = (CursorTy) field_cur1921;
            CursorTy x483 = (CursorTy) case1163;
            CursorInt64Prod tmp_struct116 =
                             _traverse_LAMBDACASE(end_r665, x483);
            CursorTy pvrtmp2996 = tmp_struct116.field0;
            IntTy pvrtmp2997 = tmp_struct116.field1;
            CursorTy endof1512 = (CursorTy) pvrtmp2996;
            IntTy y484 = (IntTy) pvrtmp2997;
            IntTy fltLitTail1511 = (IntTy) 42;

            return (CursorInt64Prod) {endof1512, fltLitTail1511};
            break;
        }

      case 3:
        {
            CursorTy field_cur1923 = (CursorTy) tmpcur2989;
            CursorTy case1166 = (CursorTy) field_cur1923;
            CursorTy x485 = (CursorTy) case1166;
            CursorInt64Prod tmp_struct117 =  _traverse_Expr(end_r665, x485);
            CursorTy pvrtmp2998 = tmp_struct117.field0;
            IntTy pvrtmp2999 = tmp_struct117.field1;
            CursorTy endof1513 = (CursorTy) pvrtmp2998;
            IntTy y488 = (IntTy) pvrtmp2999;
            CursorTy case1167 = (CursorTy) endof1513;
            CursorTy x486 = (CursorTy) case1167;
            CursorInt64Prod tmp_struct118 =  _traverse_Expr(end_r665, x486);
            CursorTy pvrtmp3000 = tmp_struct118.field0;
            IntTy pvrtmp3001 = tmp_struct118.field1;
            CursorTy endof1514 = (CursorTy) pvrtmp3000;
            IntTy y489 = (IntTy) pvrtmp3001;
            CursorTy case1168 = (CursorTy) endof1514;
            CursorTy x487 = (CursorTy) case1168;
            CursorInt64Prod tmp_struct119 =  _traverse_Expr(end_r665, x487);
            CursorTy pvrtmp3002 = tmp_struct119.field0;
            IntTy pvrtmp3003 = tmp_struct119.field1;
            CursorTy endof1516 = (CursorTy) pvrtmp3002;
            IntTy y490 = (IntTy) pvrtmp3003;
            IntTy fltLitTail1515 = (IntTy) 42;

            return (CursorInt64Prod) {endof1516, fltLitTail1515};
            break;
        }

      case 4:
        {
            CursorTy field_cur1927 = (CursorTy) tmpcur2989;
            CursorTy case1175 = (CursorTy) field_cur1927;
            CursorTy x491 = (CursorTy) case1175;
            CursorInt64Prod tmp_struct120 =  _traverse_ListExpr(end_r665, x491);
            CursorTy pvrtmp3004 = tmp_struct120.field0;
            IntTy pvrtmp3005 = tmp_struct120.field1;
            CursorTy endof1518 = (CursorTy) pvrtmp3004;
            IntTy y492 = (IntTy) pvrtmp3005;
            IntTy fltLitTail1517 = (IntTy) 42;

            return (CursorInt64Prod) {endof1518, fltLitTail1517};
            break;
        }

      case 5:
        {
            CursorTy field_cur1929 = (CursorTy) tmpcur2989;
            CursorTy case1178 = (CursorTy) field_cur1929;
            CursorTy x493 = (CursorTy) case1178;
            CursorInt64Prod tmp_struct121 =  _traverse_Expr(end_r665, x493);
            CursorTy pvrtmp3006 = tmp_struct121.field0;
            IntTy pvrtmp3007 = tmp_struct121.field1;
            CursorTy endof1519 = (CursorTy) pvrtmp3006;
            IntTy y495 = (IntTy) pvrtmp3007;
            CursorTy case1179 = (CursorTy) endof1519;
            CursorTy x494 = (CursorTy) case1179;
            CursorInt64Prod tmp_struct122 =  _traverse_ListExpr(end_r665, x494);
            CursorTy pvrtmp3008 = tmp_struct122.field0;
            IntTy pvrtmp3009 = tmp_struct122.field1;
            CursorTy endof1521 = (CursorTy) pvrtmp3008;
            IntTy y496 = (IntTy) pvrtmp3009;
            IntTy fltLitTail1520 = (IntTy) 42;

            return (CursorInt64Prod) {endof1521, fltLitTail1520};
            break;
        }

      case 6:
        {
            CursorTy field_cur1932 = (CursorTy) tmpcur2989;
            CursorTy case1184 = (CursorTy) field_cur1932;
            CursorTy x497 = (CursorTy) case1184;
            CursorInt64Prod tmp_struct123 =  _traverse_LVBIND(end_r665, x497);
            CursorTy pvrtmp3010 = tmp_struct123.field0;
            IntTy pvrtmp3011 = tmp_struct123.field1;
            CursorTy endof1522 = (CursorTy) pvrtmp3010;
            IntTy y499 = (IntTy) pvrtmp3011;
            CursorTy case1185 = (CursorTy) endof1522;
            CursorTy x498 = (CursorTy) case1185;
            CursorInt64Prod tmp_struct124 =  _traverse_ListExpr(end_r665, x498);
            CursorTy pvrtmp3012 = tmp_struct124.field0;
            IntTy pvrtmp3013 = tmp_struct124.field1;
            CursorTy endof1524 = (CursorTy) pvrtmp3012;
            IntTy y500 = (IntTy) pvrtmp3013;
            IntTy fltLitTail1523 = (IntTy) 42;

            return (CursorInt64Prod) {endof1524, fltLitTail1523};
            break;
        }

      case 7:
        {
            CursorTy field_cur1935 = (CursorTy) tmpcur2989;
            CursorTy case1190 = (CursorTy) field_cur1935;
            CursorTy x501 = (CursorTy) case1190;
            CursorInt64Prod tmp_struct125 =  _traverse_LVBIND(end_r665, x501);
            CursorTy pvrtmp3014 = tmp_struct125.field0;
            IntTy pvrtmp3015 = tmp_struct125.field1;
            CursorTy endof1525 = (CursorTy) pvrtmp3014;
            IntTy y503 = (IntTy) pvrtmp3015;
            CursorTy case1191 = (CursorTy) endof1525;
            CursorTy x502 = (CursorTy) case1191;
            CursorInt64Prod tmp_struct126 =  _traverse_ListExpr(end_r665, x502);
            CursorTy pvrtmp3016 = tmp_struct126.field0;
            IntTy pvrtmp3017 = tmp_struct126.field1;
            CursorTy endof1527 = (CursorTy) pvrtmp3016;
            IntTy y504 = (IntTy) pvrtmp3017;
            IntTy fltLitTail1526 = (IntTy) 42;

            return (CursorInt64Prod) {endof1527, fltLitTail1526};
            break;
        }

      case 8:
        {
            CursorTy field_cur1938 = (CursorTy) tmpcur2989;
            CursorTy case1196 = (CursorTy) field_cur1938;
            SymTy tmpval3018 = *(SymTy *) case1196;
            CursorTy tmpcur3019 = case1196 + sizeof(SymTy);
            SymTy x505 = (SymTy) tmpval3018;
            CursorTy end_x505 = (CursorTy) tmpcur3019;
            CursorTy case1197 = (CursorTy) end_x505;
            CursorTy x506 = (CursorTy) case1197;
            CursorTy jump1528 = case1196 + 8;
            CursorInt64Prod tmp_struct127 =  _traverse_Expr(end_r665, x506);
            CursorTy pvrtmp3020 = tmp_struct127.field0;
            IntTy pvrtmp3021 = tmp_struct127.field1;
            CursorTy endof1530 = (CursorTy) pvrtmp3020;
            IntTy y508 = (IntTy) pvrtmp3021;
            IntTy fltLitTail1529 = (IntTy) 42;

            return (CursorInt64Prod) {endof1530, fltLitTail1529};
            break;
        }

      case 9:
        {
            CursorTy field_cur1941 = (CursorTy) tmpcur2989;
            CursorTy case1200 = (CursorTy) field_cur1941;
            CursorTy x509 = (CursorTy) case1200;
            CursorInt64Prod tmp_struct128 =  _traverse_Datum(end_r665, x509);
            CursorTy pvrtmp3022 = tmp_struct128.field0;
            IntTy pvrtmp3023 = tmp_struct128.field1;
            CursorTy endof1532 = (CursorTy) pvrtmp3022;
            IntTy y510 = (IntTy) pvrtmp3023;
            IntTy fltLitTail1531 = (IntTy) 42;

            return (CursorInt64Prod) {endof1532, fltLitTail1531};
            break;
        }

      case 10:
        {
            CursorTy field_cur1943 = (CursorTy) tmpcur2989;
            CursorTy case1203 = (CursorTy) field_cur1943;
            CursorTy x511 = (CursorTy) case1203;
            CursorInt64Prod tmp_struct129 =  _traverse_Datum(end_r665, x511);
            CursorTy pvrtmp3024 = tmp_struct129.field0;
            IntTy pvrtmp3025 = tmp_struct129.field1;
            CursorTy endof1534 = (CursorTy) pvrtmp3024;
            IntTy y512 = (IntTy) pvrtmp3025;
            IntTy fltLitTail1533 = (IntTy) 42;

            return (CursorInt64Prod) {endof1534, fltLitTail1533};
            break;
        }

      case 11:
        {
            CursorTy field_cur1945 = (CursorTy) tmpcur2989;
            CursorTy case1206 = (CursorTy) field_cur1945;
            CursorTy x513 = (CursorTy) case1206;
            CursorInt64Prod tmp_struct130 =  _traverse_Datum(end_r665, x513);
            CursorTy pvrtmp3026 = tmp_struct130.field0;
            IntTy pvrtmp3027 = tmp_struct130.field1;
            CursorTy endof1536 = (CursorTy) pvrtmp3026;
            IntTy y514 = (IntTy) pvrtmp3027;
            IntTy fltLitTail1535 = (IntTy) 42;

            return (CursorInt64Prod) {endof1536, fltLitTail1535};
            break;
        }

      case 12:
        {
            CursorTy field_cur1947 = (CursorTy) tmpcur2989;
            CursorTy case1209 = (CursorTy) field_cur1947;
            CursorTy x515 = (CursorTy) case1209;
            CursorInt64Prod tmp_struct131 =  _traverse_Expr(end_r665, x515);
            CursorTy pvrtmp3028 = tmp_struct131.field0;
            IntTy pvrtmp3029 = tmp_struct131.field1;
            CursorTy endof1537 = (CursorTy) pvrtmp3028;
            IntTy y518 = (IntTy) pvrtmp3029;
            CursorTy case1210 = (CursorTy) endof1537;
            CursorTy x516 = (CursorTy) case1210;
            CursorInt64Prod tmp_struct132 =  _traverse_Expr(end_r665, x516);
            CursorTy pvrtmp3030 = tmp_struct132.field0;
            IntTy pvrtmp3031 = tmp_struct132.field1;
            CursorTy endof1538 = (CursorTy) pvrtmp3030;
            IntTy y519 = (IntTy) pvrtmp3031;
            CursorTy case1211 = (CursorTy) endof1538;
            CursorTy x517 = (CursorTy) case1211;
            CursorInt64Prod tmp_struct133 =  _traverse_Expr(end_r665, x517);
            CursorTy pvrtmp3032 = tmp_struct133.field0;
            IntTy pvrtmp3033 = tmp_struct133.field1;
            CursorTy endof1540 = (CursorTy) pvrtmp3032;
            IntTy y520 = (IntTy) pvrtmp3033;
            IntTy fltLitTail1539 = (IntTy) 42;

            return (CursorInt64Prod) {endof1540, fltLitTail1539};
            break;
        }

      case 13:
        {
            CursorTy field_cur1951 = (CursorTy) tmpcur2989;
            CursorTy case1218 = (CursorTy) field_cur1951;
            CursorTy x521 = (CursorTy) case1218;
            CursorInt64Prod tmp_struct134 =  _traverse_Expr(end_r665, x521);
            CursorTy pvrtmp3034 = tmp_struct134.field0;
            IntTy pvrtmp3035 = tmp_struct134.field1;
            CursorTy endof1541 = (CursorTy) pvrtmp3034;
            IntTy y523 = (IntTy) pvrtmp3035;
            CursorTy case1219 = (CursorTy) endof1541;
            CursorTy x522 = (CursorTy) case1219;
            CursorInt64Prod tmp_struct135 =  _traverse_ListExpr(end_r665, x522);
            CursorTy pvrtmp3036 = tmp_struct135.field0;
            IntTy pvrtmp3037 = tmp_struct135.field1;
            CursorTy endof1543 = (CursorTy) pvrtmp3036;
            IntTy y524 = (IntTy) pvrtmp3037;
            IntTy fltLitTail1542 = (IntTy) 42;

            return (CursorInt64Prod) {endof1543, fltLitTail1542};
            break;
        }

      case 14:
        {
            CursorTy field_cur1954 = (CursorTy) tmpcur2989;
            CursorTy case1224 = (CursorTy) field_cur1954;
            SymTy tmpval3038 = *(SymTy *) case1224;
            CursorTy tmpcur3039 = case1224 + sizeof(SymTy);
            SymTy x525 = (SymTy) tmpval3038;
            CursorTy end_x525 = (CursorTy) tmpcur3039;
            CursorTy jump1544 = case1224 + 8;
            IntTy fltLitTail1545 = (IntTy) 42;

            return (CursorInt64Prod) {jump1544, fltLitTail1545};
            break;
        }

      case 15:
        {
            CursorTy field_cur1956 = (CursorTy) tmpcur2989;
            CursorTy case1225 = (CursorTy) field_cur1956;
            SymTy tmpval3040 = *(SymTy *) case1225;
            CursorTy tmpcur3041 = case1225 + sizeof(SymTy);
            SymTy x527 = (SymTy) tmpval3040;
            CursorTy end_x527 = (CursorTy) tmpcur3041;
            CursorTy jump1546 = case1225 + 8;
            IntTy fltLitTail1547 = (IntTy) 42;

            return (CursorInt64Prod) {jump1546, fltLitTail1547};
            break;
        }

      case 16:
        {
            CursorTy field_cur1958 = (CursorTy) tmpcur2989;
            CursorTy case1226 = (CursorTy) field_cur1958;
            SymTy tmpval3042 = *(SymTy *) case1226;
            CursorTy tmpcur3043 = case1226 + sizeof(SymTy);
            SymTy x529 = (SymTy) tmpval3042;
            CursorTy end_x529 = (CursorTy) tmpcur3043;
            CursorTy jump1548 = case1226 + 8;
            IntTy fltLitTail1549 = (IntTy) 42;

            return (CursorInt64Prod) {jump1548, fltLitTail1549};
            break;
        }

      case 17:
        {
            CursorTy field_cur1960 = (CursorTy) tmpcur2989;
            CursorTy jump1550 = loc664 + 1;
            IntTy fltLitTail1551 = (IntTy) 42;

            return (CursorInt64Prod) {jump1550, fltLitTail1551};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3490 = *(CursorTy *) tmpcur2989;
            CursorTy tmpaftercur3491 = tmpcur2989 + 8;
            TagTyPacked tagtmp3492 = *(TagTyPacked *) tmpcur3490;
            CursorTy tailtmp3493 = tmpcur3490 + 1;

            tmpval2988 = tagtmp3492;
            tmpcur2989 = tailtmp3493;
            goto switch3044;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3490 = *(CursorTy *) tmpcur2989;
            CursorTy tmpaftercur3491 = tmpcur2989 + 8;
            TagTyPacked tagtmp3492 = *(TagTyPacked *) tmpcur3490;
            CursorTy tailtmp3493 = tmpcur3490 + 1;

            tmpval2988 = tagtmp3492;
            tmpcur2989 = tailtmp3493;
            goto switch3044;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval2988");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r668, CursorTy end_r669,
                                          CursorTy loc667, CursorTy arg531)
{
    CursorTy loc666 = (CursorTy) arg531;

    if (loc667 + 18 > end_r669) {
        ChunkTy new_chunk142 = alloc_chunk(end_r669);
        CursorTy chunk_start143 = new_chunk142.start_ptr;
        CursorTy chunk_end144 = new_chunk142.end_ptr;

        end_r669 = chunk_end144;
        *(TagTyPacked *) loc667 = 255;

        CursorTy redir = loc667 + 1;

        *(CursorTy *) redir = chunk_start143;
        loc667 = chunk_start143;
    }

    TagTyPacked tmpval3045 = *(TagTyPacked *) arg531;
    CursorTy tmpcur3046 = arg531 + 1;


  switch3111:
    ;
    switch (tmpval3045) {

      case 0:
        {
            CursorTy field_cur1961 = (CursorTy) tmpcur3046;
            CursorTy case1229 = (CursorTy) field_cur1961;
            CursorTy x532 = (CursorTy) case1229;
            CursorTy loc1237 = loc667 + 1;
            CursorCursorCursorCursorProd tmp_struct136 =
                                          _copy_ListSym(end_r668, end_r669, loc1237, x532);
            CursorTy pvrtmp3047 = tmp_struct136.field0;
            CursorTy pvrtmp3048 = tmp_struct136.field1;
            CursorTy pvrtmp3049 = tmp_struct136.field2;
            CursorTy pvrtmp3050 = tmp_struct136.field3;
            CursorTy fltPrd2319 = (CursorTy) pvrtmp3049;
            CursorTy fltPrd2320 = (CursorTy) pvrtmp3050;
            CursorTy pvrtmp3052 = (CursorTy) fltPrd2320;
            CursorTy pvrtmp3051 = (CursorTy) fltPrd2319;
            CursorTy y534 = (CursorTy) pvrtmp3051;
            CursorTy fltPrd2321 = (CursorTy) pvrtmp3049;
            CursorTy fltPrd2322 = (CursorTy) pvrtmp3050;
            CursorTy pvrtmp3054 = (CursorTy) fltPrd2322;
            CursorTy pvrtmp3053 = (CursorTy) fltPrd2321;
            CursorTy end_y534 = (CursorTy) pvrtmp3054;
            CursorTy end_r669_1608 = (CursorTy) pvrtmp3047;
            CursorTy endof1552 = (CursorTy) pvrtmp3048;
            CursorTy case1230 = (CursorTy) endof1552;
            CursorTy x533 = (CursorTy) case1230;
            CursorTy loc1238 = (CursorTy) end_y534;
            CursorCursorCursorCursorProd tmp_struct137 =
                                          _copy_Expr(end_r668, end_r669_1608, loc1238, x533);
            CursorTy pvrtmp3055 = tmp_struct137.field0;
            CursorTy pvrtmp3056 = tmp_struct137.field1;
            CursorTy pvrtmp3057 = tmp_struct137.field2;
            CursorTy pvrtmp3058 = tmp_struct137.field3;
            CursorTy fltPrd2323 = (CursorTy) pvrtmp3057;
            CursorTy fltPrd2324 = (CursorTy) pvrtmp3058;
            CursorTy pvrtmp3060 = (CursorTy) fltPrd2324;
            CursorTy pvrtmp3059 = (CursorTy) fltPrd2323;
            CursorTy y535 = (CursorTy) pvrtmp3059;
            CursorTy fltPrd2325 = (CursorTy) pvrtmp3057;
            CursorTy fltPrd2326 = (CursorTy) pvrtmp3058;
            CursorTy pvrtmp3062 = (CursorTy) fltPrd2326;
            CursorTy pvrtmp3061 = (CursorTy) fltPrd2325;
            CursorTy end_y535 = (CursorTy) pvrtmp3062;
            CursorTy end_r669_1608_1609 = (CursorTy) pvrtmp3055;
            CursorTy endof1553 = (CursorTy) pvrtmp3056;

            *(TagTyPacked *) loc667 = 0;

            CursorTy writetag1964 = loc667 + 1;
            CursorTy writecur1965 = (CursorTy) end_y534;
            CursorTy writecur1966 = (CursorTy) end_y535;
            CursorTy pvrtmp3064 = (CursorTy) writecur1966;
            CursorTy pvrtmp3063 = (CursorTy) loc667;
            CursorTy taildc1554 = (CursorTy) pvrtmp3063;
            CursorTy end_taildc1554 = (CursorTy) pvrtmp3064;
            CursorTy pvrtmp3066 = (CursorTy) end_taildc1554;
            CursorTy pvrtmp3065 = (CursorTy) taildc1554;
            CursorTy fltPrd2327 = (CursorTy) pvrtmp3065;
            CursorTy fltPrd2328 = (CursorTy) pvrtmp3066;

            return (CursorCursorCursorCursorProd) {end_r669_1608_1609,
                                                   endof1553, fltPrd2327,
                                                   fltPrd2328};
            break;
        }

      case 1:
        {
            CursorTy field_cur1968 = (CursorTy) tmpcur3046;
            CursorTy case1241 = (CursorTy) field_cur1968;
            CursorTy x536 = (CursorTy) case1241;
            CursorTy loc1249 = loc667 + 1;
            CursorCursorCursorCursorProd tmp_struct138 =
                                          _copy_ListSym(end_r668, end_r669, loc1249, x536);
            CursorTy pvrtmp3067 = tmp_struct138.field0;
            CursorTy pvrtmp3068 = tmp_struct138.field1;
            CursorTy pvrtmp3069 = tmp_struct138.field2;
            CursorTy pvrtmp3070 = tmp_struct138.field3;
            CursorTy fltPrd2329 = (CursorTy) pvrtmp3069;
            CursorTy fltPrd2330 = (CursorTy) pvrtmp3070;
            CursorTy pvrtmp3072 = (CursorTy) fltPrd2330;
            CursorTy pvrtmp3071 = (CursorTy) fltPrd2329;
            CursorTy y538 = (CursorTy) pvrtmp3071;
            CursorTy fltPrd2331 = (CursorTy) pvrtmp3069;
            CursorTy fltPrd2332 = (CursorTy) pvrtmp3070;
            CursorTy pvrtmp3074 = (CursorTy) fltPrd2332;
            CursorTy pvrtmp3073 = (CursorTy) fltPrd2331;
            CursorTy end_y538 = (CursorTy) pvrtmp3074;
            CursorTy end_r669_1610 = (CursorTy) pvrtmp3067;
            CursorTy endof1555 = (CursorTy) pvrtmp3068;
            CursorTy case1242 = (CursorTy) endof1555;
            CursorTy x537 = (CursorTy) case1242;
            CursorTy loc1250 = (CursorTy) end_y538;
            CursorCursorCursorCursorProd tmp_struct139 =
                                          _copy_Expr(end_r668, end_r669_1610, loc1250, x537);
            CursorTy pvrtmp3075 = tmp_struct139.field0;
            CursorTy pvrtmp3076 = tmp_struct139.field1;
            CursorTy pvrtmp3077 = tmp_struct139.field2;
            CursorTy pvrtmp3078 = tmp_struct139.field3;
            CursorTy fltPrd2333 = (CursorTy) pvrtmp3077;
            CursorTy fltPrd2334 = (CursorTy) pvrtmp3078;
            CursorTy pvrtmp3080 = (CursorTy) fltPrd2334;
            CursorTy pvrtmp3079 = (CursorTy) fltPrd2333;
            CursorTy y539 = (CursorTy) pvrtmp3079;
            CursorTy fltPrd2335 = (CursorTy) pvrtmp3077;
            CursorTy fltPrd2336 = (CursorTy) pvrtmp3078;
            CursorTy pvrtmp3082 = (CursorTy) fltPrd2336;
            CursorTy pvrtmp3081 = (CursorTy) fltPrd2335;
            CursorTy end_y539 = (CursorTy) pvrtmp3082;
            CursorTy end_r669_1610_1611 = (CursorTy) pvrtmp3075;
            CursorTy endof1556 = (CursorTy) pvrtmp3076;

            *(TagTyPacked *) loc667 = 1;

            CursorTy writetag1971 = loc667 + 1;
            CursorTy writecur1972 = (CursorTy) end_y538;
            CursorTy writecur1973 = (CursorTy) end_y539;
            CursorTy pvrtmp3084 = (CursorTy) writecur1973;
            CursorTy pvrtmp3083 = (CursorTy) loc667;
            CursorTy taildc1557 = (CursorTy) pvrtmp3083;
            CursorTy end_taildc1557 = (CursorTy) pvrtmp3084;
            CursorTy pvrtmp3086 = (CursorTy) end_taildc1557;
            CursorTy pvrtmp3085 = (CursorTy) taildc1557;
            CursorTy fltPrd2337 = (CursorTy) pvrtmp3085;
            CursorTy fltPrd2338 = (CursorTy) pvrtmp3086;

            return (CursorCursorCursorCursorProd) {end_r669_1610_1611,
                                                   endof1556, fltPrd2337,
                                                   fltPrd2338};
            break;
        }

      case 2:
        {
            CursorTy field_cur1975 = (CursorTy) tmpcur3046;
            CursorTy case1253 = (CursorTy) field_cur1975;
            CursorTy x540 = (CursorTy) case1253;
            CursorTy loc1257 = loc667 + 1;
            CursorCursorCursorCursorProd tmp_struct140 =
                                          _copy_ListToplvl(end_r668, end_r669, loc1257, x540);
            CursorTy pvrtmp3087 = tmp_struct140.field0;
            CursorTy pvrtmp3088 = tmp_struct140.field1;
            CursorTy pvrtmp3089 = tmp_struct140.field2;
            CursorTy pvrtmp3090 = tmp_struct140.field3;
            CursorTy fltPrd2339 = (CursorTy) pvrtmp3089;
            CursorTy fltPrd2340 = (CursorTy) pvrtmp3090;
            CursorTy pvrtmp3092 = (CursorTy) fltPrd2340;
            CursorTy pvrtmp3091 = (CursorTy) fltPrd2339;
            CursorTy y541 = (CursorTy) pvrtmp3091;
            CursorTy fltPrd2341 = (CursorTy) pvrtmp3089;
            CursorTy fltPrd2342 = (CursorTy) pvrtmp3090;
            CursorTy pvrtmp3094 = (CursorTy) fltPrd2342;
            CursorTy pvrtmp3093 = (CursorTy) fltPrd2341;
            CursorTy end_y541 = (CursorTy) pvrtmp3094;
            CursorTy end_r669_1612 = (CursorTy) pvrtmp3087;
            CursorTy endof1558 = (CursorTy) pvrtmp3088;

            *(TagTyPacked *) loc667 = 2;

            CursorTy writetag1977 = loc667 + 1;
            CursorTy writecur1978 = (CursorTy) end_y541;
            CursorTy pvrtmp3096 = (CursorTy) writecur1978;
            CursorTy pvrtmp3095 = (CursorTy) loc667;
            CursorTy taildc1559 = (CursorTy) pvrtmp3095;
            CursorTy end_taildc1559 = (CursorTy) pvrtmp3096;
            CursorTy pvrtmp3098 = (CursorTy) end_taildc1559;
            CursorTy pvrtmp3097 = (CursorTy) taildc1559;
            CursorTy fltPrd2343 = (CursorTy) pvrtmp3097;
            CursorTy fltPrd2344 = (CursorTy) pvrtmp3098;

            return (CursorCursorCursorCursorProd) {end_r669_1612, endof1558,
                                                   fltPrd2343, fltPrd2344};
            break;
        }

      case 3:
        {
            CursorTy field_cur1980 = (CursorTy) tmpcur3046;
            CursorTy case1259 = (CursorTy) field_cur1980;
            CursorTy x542 = (CursorTy) case1259;
            CursorTy loc1263 = loc667 + 1;
            CursorCursorCursorCursorProd tmp_struct141 =
                                          _copy_Expr(end_r668, end_r669, loc1263, x542);
            CursorTy pvrtmp3099 = tmp_struct141.field0;
            CursorTy pvrtmp3100 = tmp_struct141.field1;
            CursorTy pvrtmp3101 = tmp_struct141.field2;
            CursorTy pvrtmp3102 = tmp_struct141.field3;
            CursorTy fltPrd2345 = (CursorTy) pvrtmp3101;
            CursorTy fltPrd2346 = (CursorTy) pvrtmp3102;
            CursorTy pvrtmp3104 = (CursorTy) fltPrd2346;
            CursorTy pvrtmp3103 = (CursorTy) fltPrd2345;
            CursorTy y543 = (CursorTy) pvrtmp3103;
            CursorTy fltPrd2347 = (CursorTy) pvrtmp3101;
            CursorTy fltPrd2348 = (CursorTy) pvrtmp3102;
            CursorTy pvrtmp3106 = (CursorTy) fltPrd2348;
            CursorTy pvrtmp3105 = (CursorTy) fltPrd2347;
            CursorTy end_y543 = (CursorTy) pvrtmp3106;
            CursorTy end_r669_1613 = (CursorTy) pvrtmp3099;
            CursorTy endof1560 = (CursorTy) pvrtmp3100;

            *(TagTyPacked *) loc667 = 3;

            CursorTy writetag1982 = loc667 + 1;
            CursorTy writecur1983 = (CursorTy) end_y543;
            CursorTy pvrtmp3108 = (CursorTy) writecur1983;
            CursorTy pvrtmp3107 = (CursorTy) loc667;
            CursorTy taildc1561 = (CursorTy) pvrtmp3107;
            CursorTy end_taildc1561 = (CursorTy) pvrtmp3108;
            CursorTy pvrtmp3110 = (CursorTy) end_taildc1561;
            CursorTy pvrtmp3109 = (CursorTy) taildc1561;
            CursorTy fltPrd2349 = (CursorTy) pvrtmp3109;
            CursorTy fltPrd2350 = (CursorTy) pvrtmp3110;

            return (CursorCursorCursorCursorProd) {end_r669_1613, endof1560,
                                                   fltPrd2349, fltPrd2350};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3494 = *(CursorTy *) tmpcur3046;
            CursorTy tmpaftercur3495 = tmpcur3046 + 8;
            TagTyPacked tagtmp3496 = *(TagTyPacked *) tmpcur3494;
            CursorTy tailtmp3497 = tmpcur3494 + 1;

            tmpval3045 = tagtmp3496;
            tmpcur3046 = tailtmp3497;
            goto switch3111;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3494 = *(CursorTy *) tmpcur3046;
            CursorTy tmpaftercur3495 = tmpcur3046 + 8;
            TagTyPacked tagtmp3496 = *(TagTyPacked *) tmpcur3494;
            CursorTy tailtmp3497 = tmpcur3494 + 1;

            tmpval3045 = tagtmp3496;
            tmpcur3046 = tailtmp3497;
            goto switch3111;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval3045");
            exit(1);
        }
    }
}
CursorInt64Prod _traverse_Toplvl(CursorTy end_r671, CursorTy arg544)
{
    CursorTy loc670 = (CursorTy) arg544;
    TagTyPacked tmpval3112 = *(TagTyPacked *) arg544;
    CursorTy tmpcur3113 = arg544 + 1;


  switch3126:
    ;
    switch (tmpval3112) {

      case 0:
        {
            CursorTy field_cur1985 = (CursorTy) tmpcur3113;
            CursorTy case1267 = (CursorTy) field_cur1985;
            CursorTy x545 = (CursorTy) case1267;
            CursorInt64Prod tmp_struct145 =  _traverse_ListSym(end_r671, x545);
            CursorTy pvrtmp3114 = tmp_struct145.field0;
            IntTy pvrtmp3115 = tmp_struct145.field1;
            CursorTy endof1562 = (CursorTy) pvrtmp3114;
            IntTy y547 = (IntTy) pvrtmp3115;
            CursorTy case1268 = (CursorTy) endof1562;
            CursorTy x546 = (CursorTy) case1268;
            CursorInt64Prod tmp_struct146 =  _traverse_Expr(end_r671, x546);
            CursorTy pvrtmp3116 = tmp_struct146.field0;
            IntTy pvrtmp3117 = tmp_struct146.field1;
            CursorTy endof1564 = (CursorTy) pvrtmp3116;
            IntTy y548 = (IntTy) pvrtmp3117;
            IntTy fltLitTail1563 = (IntTy) 42;

            return (CursorInt64Prod) {endof1564, fltLitTail1563};
            break;
        }

      case 1:
        {
            CursorTy field_cur1988 = (CursorTy) tmpcur3113;
            CursorTy case1273 = (CursorTy) field_cur1988;
            CursorTy x549 = (CursorTy) case1273;
            CursorInt64Prod tmp_struct147 =  _traverse_ListSym(end_r671, x549);
            CursorTy pvrtmp3118 = tmp_struct147.field0;
            IntTy pvrtmp3119 = tmp_struct147.field1;
            CursorTy endof1565 = (CursorTy) pvrtmp3118;
            IntTy y551 = (IntTy) pvrtmp3119;
            CursorTy case1274 = (CursorTy) endof1565;
            CursorTy x550 = (CursorTy) case1274;
            CursorInt64Prod tmp_struct148 =  _traverse_Expr(end_r671, x550);
            CursorTy pvrtmp3120 = tmp_struct148.field0;
            IntTy pvrtmp3121 = tmp_struct148.field1;
            CursorTy endof1567 = (CursorTy) pvrtmp3120;
            IntTy y552 = (IntTy) pvrtmp3121;
            IntTy fltLitTail1566 = (IntTy) 42;

            return (CursorInt64Prod) {endof1567, fltLitTail1566};
            break;
        }

      case 2:
        {
            CursorTy field_cur1991 = (CursorTy) tmpcur3113;
            CursorTy case1279 = (CursorTy) field_cur1991;
            CursorTy x553 = (CursorTy) case1279;
            CursorInt64Prod tmp_struct149 =
                             _traverse_ListToplvl(end_r671, x553);
            CursorTy pvrtmp3122 = tmp_struct149.field0;
            IntTy pvrtmp3123 = tmp_struct149.field1;
            CursorTy endof1569 = (CursorTy) pvrtmp3122;
            IntTy y554 = (IntTy) pvrtmp3123;
            IntTy fltLitTail1568 = (IntTy) 42;

            return (CursorInt64Prod) {endof1569, fltLitTail1568};
            break;
        }

      case 3:
        {
            CursorTy field_cur1993 = (CursorTy) tmpcur3113;
            CursorTy case1282 = (CursorTy) field_cur1993;
            CursorTy x555 = (CursorTy) case1282;
            CursorInt64Prod tmp_struct150 =  _traverse_Expr(end_r671, x555);
            CursorTy pvrtmp3124 = tmp_struct150.field0;
            IntTy pvrtmp3125 = tmp_struct150.field1;
            CursorTy endof1571 = (CursorTy) pvrtmp3124;
            IntTy y556 = (IntTy) pvrtmp3125;
            IntTy fltLitTail1570 = (IntTy) 42;

            return (CursorInt64Prod) {endof1571, fltLitTail1570};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3498 = *(CursorTy *) tmpcur3113;
            CursorTy tmpaftercur3499 = tmpcur3113 + 8;
            TagTyPacked tagtmp3500 = *(TagTyPacked *) tmpcur3498;
            CursorTy tailtmp3501 = tmpcur3498 + 1;

            tmpval3112 = tagtmp3500;
            tmpcur3113 = tailtmp3501;
            goto switch3126;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3498 = *(CursorTy *) tmpcur3113;
            CursorTy tmpaftercur3499 = tmpcur3113 + 8;
            TagTyPacked tagtmp3500 = *(TagTyPacked *) tmpcur3498;
            CursorTy tailtmp3501 = tmpcur3498 + 1;

            tmpval3112 = tagtmp3500;
            tmpcur3113 = tailtmp3501;
            goto switch3126;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval3112");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_ListSym(CursorTy p3127)
{
    TagTyPacked tag3128 = *(TagTyPacked *) p3127;
    CursorTy tail3129 = p3127 + 1;


  switch3136:
    ;
    switch (tag3128) {

      case 0:
        {
            SymTy val3130 = *(SymTy *) tail3129;
            CursorTy tail3131 = tail3129 + sizeof(SymTy);
            PtrCursorProd tmp_struct151 =  _unpack_ListSym(tail3131);
            PtrTy ptr3132 = tmp_struct151.field0;
            CursorTy tail3133 = tmp_struct151.field1;
            PtrTy ptr3134 = ALLOC(sizeof(TagSymCursorProd));

            ((TagSymCursorProd *) ptr3134)->field0 = tag3128;
            ((TagSymCursorProd *) ptr3134)->field1 = val3130;
            ((TagSymCursorProd *) ptr3134)->field2 = ptr3132;
            return (PtrCursorProd) {ptr3134, tail3133};
            break;
        }

      case 1:
        {
            PtrTy ptr3135 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr3135)->field0 = tag3128;
            return (PtrCursorProd) {ptr3135, tail3129};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3502 = *(CursorTy *) tail3129;
            CursorTy tmpaftercur3503 = tail3129 + 8;
            TagTyPacked tagtmp3504 = *(TagTyPacked *) tmpcur3502;
            CursorTy tailtmp3505 = tmpcur3502 + 1;

            tag3128 = tagtmp3504;
            tail3129 = tailtmp3505;
            goto switch3136;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3502 = *(CursorTy *) tail3129;
            CursorTy tmpaftercur3503 = tail3129 + 8;
            TagTyPacked tagtmp3504 = *(TagTyPacked *) tmpcur3502;
            CursorTy tailtmp3505 = tmpcur3502 + 1;

            tag3128 = tagtmp3504;
            tail3129 = tailtmp3505;
            goto switch3136;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3136");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_ListExpr(CursorTy p3137)
{
    TagTyPacked tag3138 = *(TagTyPacked *) p3137;
    CursorTy tail3139 = p3137 + 1;


  switch3146:
    ;
    switch (tag3138) {

      case 0:
        {
            PtrCursorProd tmp_struct152 =  _unpack_Expr(tail3139);
            PtrTy ptr3140 = tmp_struct152.field0;
            CursorTy tail3141 = tmp_struct152.field1;
            PtrCursorProd tmp_struct153 =  _unpack_ListExpr(tail3141);
            PtrTy ptr3142 = tmp_struct153.field0;
            CursorTy tail3143 = tmp_struct153.field1;
            PtrTy ptr3144 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3144)->field0 = tag3138;
            ((TagCursorCursorProd *) ptr3144)->field1 = ptr3140;
            ((TagCursorCursorProd *) ptr3144)->field2 = ptr3142;
            return (PtrCursorProd) {ptr3144, tail3143};
            break;
        }

      case 1:
        {
            PtrTy ptr3145 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr3145)->field0 = tag3138;
            return (PtrCursorProd) {ptr3145, tail3139};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3506 = *(CursorTy *) tail3139;
            CursorTy tmpaftercur3507 = tail3139 + 8;
            TagTyPacked tagtmp3508 = *(TagTyPacked *) tmpcur3506;
            CursorTy tailtmp3509 = tmpcur3506 + 1;

            tag3138 = tagtmp3508;
            tail3139 = tailtmp3509;
            goto switch3146;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3506 = *(CursorTy *) tail3139;
            CursorTy tmpaftercur3507 = tail3139 + 8;
            TagTyPacked tagtmp3508 = *(TagTyPacked *) tmpcur3506;
            CursorTy tailtmp3509 = tmpcur3506 + 1;

            tag3138 = tagtmp3508;
            tail3139 = tailtmp3509;
            goto switch3146;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3146");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_ListToplvl(CursorTy p3147)
{
    TagTyPacked tag3148 = *(TagTyPacked *) p3147;
    CursorTy tail3149 = p3147 + 1;


  switch3156:
    ;
    switch (tag3148) {

      case 0:
        {
            PtrCursorProd tmp_struct154 =  _unpack_Toplvl(tail3149);
            PtrTy ptr3150 = tmp_struct154.field0;
            CursorTy tail3151 = tmp_struct154.field1;
            PtrCursorProd tmp_struct155 =  _unpack_ListToplvl(tail3151);
            PtrTy ptr3152 = tmp_struct155.field0;
            CursorTy tail3153 = tmp_struct155.field1;
            PtrTy ptr3154 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3154)->field0 = tag3148;
            ((TagCursorCursorProd *) ptr3154)->field1 = ptr3150;
            ((TagCursorCursorProd *) ptr3154)->field2 = ptr3152;
            return (PtrCursorProd) {ptr3154, tail3153};
            break;
        }

      case 1:
        {
            PtrTy ptr3155 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr3155)->field0 = tag3148;
            return (PtrCursorProd) {ptr3155, tail3149};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3510 = *(CursorTy *) tail3149;
            CursorTy tmpaftercur3511 = tail3149 + 8;
            TagTyPacked tagtmp3512 = *(TagTyPacked *) tmpcur3510;
            CursorTy tailtmp3513 = tmpcur3510 + 1;

            tag3148 = tagtmp3512;
            tail3149 = tailtmp3513;
            goto switch3156;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3510 = *(CursorTy *) tail3149;
            CursorTy tmpaftercur3511 = tail3149 + 8;
            TagTyPacked tagtmp3512 = *(TagTyPacked *) tmpcur3510;
            CursorTy tailtmp3513 = tmpcur3510 + 1;

            tag3148 = tagtmp3512;
            tail3149 = tailtmp3513;
            goto switch3156;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3156");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Formals(CursorTy p3157)
{
    TagTyPacked tag3158 = *(TagTyPacked *) p3157;
    CursorTy tail3159 = p3157 + 1;


  switch3171:
    ;
    switch (tag3158) {

      case 0:
        {
            PtrCursorProd tmp_struct156 =  _unpack_ListSym(tail3159);
            PtrTy ptr3160 = tmp_struct156.field0;
            CursorTy tail3161 = tmp_struct156.field1;
            PtrTy ptr3162 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3162)->field0 = tag3158;
            ((TagCursorProd *) ptr3162)->field1 = ptr3160;
            return (PtrCursorProd) {ptr3162, tail3161};
            break;
        }

      case 1:
        {
            PtrCursorProd tmp_struct157 =  _unpack_ListSym(tail3159);
            PtrTy ptr3163 = tmp_struct157.field0;
            CursorTy tail3164 = tmp_struct157.field1;
            SymTy val3165 = *(SymTy *) tail3164;
            CursorTy tail3166 = tail3164 + sizeof(SymTy);
            PtrTy ptr3167 = ALLOC(sizeof(TagCursorSymProd));

            ((TagCursorSymProd *) ptr3167)->field0 = tag3158;
            ((TagCursorSymProd *) ptr3167)->field1 = ptr3163;
            ((TagCursorSymProd *) ptr3167)->field2 = val3165;
            return (PtrCursorProd) {ptr3167, tail3166};
            break;
        }

      case 2:
        {
            SymTy val3168 = *(SymTy *) tail3159;
            CursorTy tail3169 = tail3159 + sizeof(SymTy);
            PtrTy ptr3170 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr3170)->field0 = tag3158;
            ((TagSymProd *) ptr3170)->field1 = val3168;
            return (PtrCursorProd) {ptr3170, tail3169};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3514 = *(CursorTy *) tail3159;
            CursorTy tmpaftercur3515 = tail3159 + 8;
            TagTyPacked tagtmp3516 = *(TagTyPacked *) tmpcur3514;
            CursorTy tailtmp3517 = tmpcur3514 + 1;

            tag3158 = tagtmp3516;
            tail3159 = tailtmp3517;
            goto switch3171;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3514 = *(CursorTy *) tail3159;
            CursorTy tmpaftercur3515 = tail3159 + 8;
            TagTyPacked tagtmp3516 = *(TagTyPacked *) tmpcur3514;
            CursorTy tailtmp3517 = tmpcur3514 + 1;

            tag3158 = tagtmp3516;
            tail3159 = tailtmp3517;
            goto switch3171;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3171");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Datum(CursorTy p3172)
{
    TagTyPacked tag3173 = *(TagTyPacked *) p3172;
    CursorTy tail3174 = p3172 + 1;


  switch3178:
    ;
    switch (tag3173) {

      case 0:
        {
            IntTy val3175 = *(IntTy *) tail3174;
            CursorTy tail3176 = tail3174 + sizeof(IntTy);
            PtrTy ptr3177 = ALLOC(sizeof(TagInt64Prod));

            ((TagInt64Prod *) ptr3177)->field0 = tag3173;
            ((TagInt64Prod *) ptr3177)->field1 = val3175;
            return (PtrCursorProd) {ptr3177, tail3176};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3518 = *(CursorTy *) tail3174;
            CursorTy tmpaftercur3519 = tail3174 + 8;
            TagTyPacked tagtmp3520 = *(TagTyPacked *) tmpcur3518;
            CursorTy tailtmp3521 = tmpcur3518 + 1;

            tag3173 = tagtmp3520;
            tail3174 = tailtmp3521;
            goto switch3178;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3518 = *(CursorTy *) tail3174;
            CursorTy tmpaftercur3519 = tail3174 + 8;
            TagTyPacked tagtmp3520 = *(TagTyPacked *) tmpcur3518;
            CursorTy tailtmp3521 = tmpcur3518 + 1;

            tag3173 = tagtmp3520;
            tail3174 = tailtmp3521;
            goto switch3178;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3178");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_LAMBDACASE(CursorTy p3179)
{
    TagTyPacked tag3180 = *(TagTyPacked *) p3179;
    CursorTy tail3181 = p3179 + 1;


  switch3190:
    ;
    switch (tag3180) {

      case 0:
        {
            PtrCursorProd tmp_struct158 =  _unpack_Formals(tail3181);
            PtrTy ptr3182 = tmp_struct158.field0;
            CursorTy tail3183 = tmp_struct158.field1;
            PtrCursorProd tmp_struct159 =  _unpack_ListExpr(tail3183);
            PtrTy ptr3184 = tmp_struct159.field0;
            CursorTy tail3185 = tmp_struct159.field1;
            PtrCursorProd tmp_struct160 =  _unpack_LAMBDACASE(tail3185);
            PtrTy ptr3186 = tmp_struct160.field0;
            CursorTy tail3187 = tmp_struct160.field1;
            PtrTy ptr3188 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr3188)->field0 = tag3180;
            ((TagCursorCursorCursorProd *) ptr3188)->field1 = ptr3182;
            ((TagCursorCursorCursorProd *) ptr3188)->field2 = ptr3184;
            ((TagCursorCursorCursorProd *) ptr3188)->field3 = ptr3186;
            return (PtrCursorProd) {ptr3188, tail3187};
            break;
        }

      case 1:
        {
            PtrTy ptr3189 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr3189)->field0 = tag3180;
            return (PtrCursorProd) {ptr3189, tail3181};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3522 = *(CursorTy *) tail3181;
            CursorTy tmpaftercur3523 = tail3181 + 8;
            TagTyPacked tagtmp3524 = *(TagTyPacked *) tmpcur3522;
            CursorTy tailtmp3525 = tmpcur3522 + 1;

            tag3180 = tagtmp3524;
            tail3181 = tailtmp3525;
            goto switch3190;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3522 = *(CursorTy *) tail3181;
            CursorTy tmpaftercur3523 = tail3181 + 8;
            TagTyPacked tagtmp3524 = *(TagTyPacked *) tmpcur3522;
            CursorTy tailtmp3525 = tmpcur3522 + 1;

            tag3180 = tagtmp3524;
            tail3181 = tailtmp3525;
            goto switch3190;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3190");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_LVBIND(CursorTy p3191)
{
    TagTyPacked tag3192 = *(TagTyPacked *) p3191;
    CursorTy tail3193 = p3191 + 1;


  switch3202:
    ;
    switch (tag3192) {

      case 0:
        {
            PtrCursorProd tmp_struct161 =  _unpack_ListSym(tail3193);
            PtrTy ptr3194 = tmp_struct161.field0;
            CursorTy tail3195 = tmp_struct161.field1;
            PtrCursorProd tmp_struct162 =  _unpack_Expr(tail3195);
            PtrTy ptr3196 = tmp_struct162.field0;
            CursorTy tail3197 = tmp_struct162.field1;
            PtrCursorProd tmp_struct163 =  _unpack_LVBIND(tail3197);
            PtrTy ptr3198 = tmp_struct163.field0;
            CursorTy tail3199 = tmp_struct163.field1;
            PtrTy ptr3200 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr3200)->field0 = tag3192;
            ((TagCursorCursorCursorProd *) ptr3200)->field1 = ptr3194;
            ((TagCursorCursorCursorProd *) ptr3200)->field2 = ptr3196;
            ((TagCursorCursorCursorProd *) ptr3200)->field3 = ptr3198;
            return (PtrCursorProd) {ptr3200, tail3199};
            break;
        }

      case 1:
        {
            PtrTy ptr3201 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr3201)->field0 = tag3192;
            return (PtrCursorProd) {ptr3201, tail3193};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3526 = *(CursorTy *) tail3193;
            CursorTy tmpaftercur3527 = tail3193 + 8;
            TagTyPacked tagtmp3528 = *(TagTyPacked *) tmpcur3526;
            CursorTy tailtmp3529 = tmpcur3526 + 1;

            tag3192 = tagtmp3528;
            tail3193 = tailtmp3529;
            goto switch3202;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3526 = *(CursorTy *) tail3193;
            CursorTy tmpaftercur3527 = tail3193 + 8;
            TagTyPacked tagtmp3528 = *(TagTyPacked *) tmpcur3526;
            CursorTy tailtmp3529 = tmpcur3526 + 1;

            tag3192 = tagtmp3528;
            tail3193 = tailtmp3529;
            goto switch3202;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3202");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Expr(CursorTy p3203)
{
    TagTyPacked tag3204 = *(TagTyPacked *) p3203;
    CursorTy tail3205 = p3203 + 1;


  switch3278:
    ;
    switch (tag3204) {

      case 0:
        {
            SymTy val3206 = *(SymTy *) tail3205;
            CursorTy tail3207 = tail3205 + sizeof(SymTy);
            PtrTy ptr3208 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr3208)->field0 = tag3204;
            ((TagSymProd *) ptr3208)->field1 = val3206;
            return (PtrCursorProd) {ptr3208, tail3207};
            break;
        }

      case 1:
        {
            PtrCursorProd tmp_struct164 =  _unpack_Formals(tail3205);
            PtrTy ptr3209 = tmp_struct164.field0;
            CursorTy tail3210 = tmp_struct164.field1;
            PtrCursorProd tmp_struct165 =  _unpack_ListExpr(tail3210);
            PtrTy ptr3211 = tmp_struct165.field0;
            CursorTy tail3212 = tmp_struct165.field1;
            PtrTy ptr3213 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3213)->field0 = tag3204;
            ((TagCursorCursorProd *) ptr3213)->field1 = ptr3209;
            ((TagCursorCursorProd *) ptr3213)->field2 = ptr3211;
            return (PtrCursorProd) {ptr3213, tail3212};
            break;
        }

      case 2:
        {
            PtrCursorProd tmp_struct166 =  _unpack_LAMBDACASE(tail3205);
            PtrTy ptr3214 = tmp_struct166.field0;
            CursorTy tail3215 = tmp_struct166.field1;
            PtrTy ptr3216 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3216)->field0 = tag3204;
            ((TagCursorProd *) ptr3216)->field1 = ptr3214;
            return (PtrCursorProd) {ptr3216, tail3215};
            break;
        }

      case 3:
        {
            PtrCursorProd tmp_struct167 =  _unpack_Expr(tail3205);
            PtrTy ptr3217 = tmp_struct167.field0;
            CursorTy tail3218 = tmp_struct167.field1;
            PtrCursorProd tmp_struct168 =  _unpack_Expr(tail3218);
            PtrTy ptr3219 = tmp_struct168.field0;
            CursorTy tail3220 = tmp_struct168.field1;
            PtrCursorProd tmp_struct169 =  _unpack_Expr(tail3220);
            PtrTy ptr3221 = tmp_struct169.field0;
            CursorTy tail3222 = tmp_struct169.field1;
            PtrTy ptr3223 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr3223)->field0 = tag3204;
            ((TagCursorCursorCursorProd *) ptr3223)->field1 = ptr3217;
            ((TagCursorCursorCursorProd *) ptr3223)->field2 = ptr3219;
            ((TagCursorCursorCursorProd *) ptr3223)->field3 = ptr3221;
            return (PtrCursorProd) {ptr3223, tail3222};
            break;
        }

      case 4:
        {
            PtrCursorProd tmp_struct170 =  _unpack_ListExpr(tail3205);
            PtrTy ptr3224 = tmp_struct170.field0;
            CursorTy tail3225 = tmp_struct170.field1;
            PtrTy ptr3226 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3226)->field0 = tag3204;
            ((TagCursorProd *) ptr3226)->field1 = ptr3224;
            return (PtrCursorProd) {ptr3226, tail3225};
            break;
        }

      case 5:
        {
            PtrCursorProd tmp_struct171 =  _unpack_Expr(tail3205);
            PtrTy ptr3227 = tmp_struct171.field0;
            CursorTy tail3228 = tmp_struct171.field1;
            PtrCursorProd tmp_struct172 =  _unpack_ListExpr(tail3228);
            PtrTy ptr3229 = tmp_struct172.field0;
            CursorTy tail3230 = tmp_struct172.field1;
            PtrTy ptr3231 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3231)->field0 = tag3204;
            ((TagCursorCursorProd *) ptr3231)->field1 = ptr3227;
            ((TagCursorCursorProd *) ptr3231)->field2 = ptr3229;
            return (PtrCursorProd) {ptr3231, tail3230};
            break;
        }

      case 6:
        {
            PtrCursorProd tmp_struct173 =  _unpack_LVBIND(tail3205);
            PtrTy ptr3232 = tmp_struct173.field0;
            CursorTy tail3233 = tmp_struct173.field1;
            PtrCursorProd tmp_struct174 =  _unpack_ListExpr(tail3233);
            PtrTy ptr3234 = tmp_struct174.field0;
            CursorTy tail3235 = tmp_struct174.field1;
            PtrTy ptr3236 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3236)->field0 = tag3204;
            ((TagCursorCursorProd *) ptr3236)->field1 = ptr3232;
            ((TagCursorCursorProd *) ptr3236)->field2 = ptr3234;
            return (PtrCursorProd) {ptr3236, tail3235};
            break;
        }

      case 7:
        {
            PtrCursorProd tmp_struct175 =  _unpack_LVBIND(tail3205);
            PtrTy ptr3237 = tmp_struct175.field0;
            CursorTy tail3238 = tmp_struct175.field1;
            PtrCursorProd tmp_struct176 =  _unpack_ListExpr(tail3238);
            PtrTy ptr3239 = tmp_struct176.field0;
            CursorTy tail3240 = tmp_struct176.field1;
            PtrTy ptr3241 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3241)->field0 = tag3204;
            ((TagCursorCursorProd *) ptr3241)->field1 = ptr3237;
            ((TagCursorCursorProd *) ptr3241)->field2 = ptr3239;
            return (PtrCursorProd) {ptr3241, tail3240};
            break;
        }

      case 8:
        {
            SymTy val3242 = *(SymTy *) tail3205;
            CursorTy tail3243 = tail3205 + sizeof(SymTy);
            PtrCursorProd tmp_struct177 =  _unpack_Expr(tail3243);
            PtrTy ptr3244 = tmp_struct177.field0;
            CursorTy tail3245 = tmp_struct177.field1;
            PtrTy ptr3246 = ALLOC(sizeof(TagSymCursorProd));

            ((TagSymCursorProd *) ptr3246)->field0 = tag3204;
            ((TagSymCursorProd *) ptr3246)->field1 = val3242;
            ((TagSymCursorProd *) ptr3246)->field2 = ptr3244;
            return (PtrCursorProd) {ptr3246, tail3245};
            break;
        }

      case 9:
        {
            PtrCursorProd tmp_struct178 =  _unpack_Datum(tail3205);
            PtrTy ptr3247 = tmp_struct178.field0;
            CursorTy tail3248 = tmp_struct178.field1;
            PtrTy ptr3249 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3249)->field0 = tag3204;
            ((TagCursorProd *) ptr3249)->field1 = ptr3247;
            return (PtrCursorProd) {ptr3249, tail3248};
            break;
        }

      case 10:
        {
            PtrCursorProd tmp_struct179 =  _unpack_Datum(tail3205);
            PtrTy ptr3250 = tmp_struct179.field0;
            CursorTy tail3251 = tmp_struct179.field1;
            PtrTy ptr3252 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3252)->field0 = tag3204;
            ((TagCursorProd *) ptr3252)->field1 = ptr3250;
            return (PtrCursorProd) {ptr3252, tail3251};
            break;
        }

      case 11:
        {
            PtrCursorProd tmp_struct180 =  _unpack_Datum(tail3205);
            PtrTy ptr3253 = tmp_struct180.field0;
            CursorTy tail3254 = tmp_struct180.field1;
            PtrTy ptr3255 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3255)->field0 = tag3204;
            ((TagCursorProd *) ptr3255)->field1 = ptr3253;
            return (PtrCursorProd) {ptr3255, tail3254};
            break;
        }

      case 12:
        {
            PtrCursorProd tmp_struct181 =  _unpack_Expr(tail3205);
            PtrTy ptr3256 = tmp_struct181.field0;
            CursorTy tail3257 = tmp_struct181.field1;
            PtrCursorProd tmp_struct182 =  _unpack_Expr(tail3257);
            PtrTy ptr3258 = tmp_struct182.field0;
            CursorTy tail3259 = tmp_struct182.field1;
            PtrCursorProd tmp_struct183 =  _unpack_Expr(tail3259);
            PtrTy ptr3260 = tmp_struct183.field0;
            CursorTy tail3261 = tmp_struct183.field1;
            PtrTy ptr3262 = ALLOC(sizeof(TagCursorCursorCursorProd));

            ((TagCursorCursorCursorProd *) ptr3262)->field0 = tag3204;
            ((TagCursorCursorCursorProd *) ptr3262)->field1 = ptr3256;
            ((TagCursorCursorCursorProd *) ptr3262)->field2 = ptr3258;
            ((TagCursorCursorCursorProd *) ptr3262)->field3 = ptr3260;
            return (PtrCursorProd) {ptr3262, tail3261};
            break;
        }

      case 13:
        {
            PtrCursorProd tmp_struct184 =  _unpack_Expr(tail3205);
            PtrTy ptr3263 = tmp_struct184.field0;
            CursorTy tail3264 = tmp_struct184.field1;
            PtrCursorProd tmp_struct185 =  _unpack_ListExpr(tail3264);
            PtrTy ptr3265 = tmp_struct185.field0;
            CursorTy tail3266 = tmp_struct185.field1;
            PtrTy ptr3267 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3267)->field0 = tag3204;
            ((TagCursorCursorProd *) ptr3267)->field1 = ptr3263;
            ((TagCursorCursorProd *) ptr3267)->field2 = ptr3265;
            return (PtrCursorProd) {ptr3267, tail3266};
            break;
        }

      case 14:
        {
            SymTy val3268 = *(SymTy *) tail3205;
            CursorTy tail3269 = tail3205 + sizeof(SymTy);
            PtrTy ptr3270 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr3270)->field0 = tag3204;
            ((TagSymProd *) ptr3270)->field1 = val3268;
            return (PtrCursorProd) {ptr3270, tail3269};
            break;
        }

      case 15:
        {
            SymTy val3271 = *(SymTy *) tail3205;
            CursorTy tail3272 = tail3205 + sizeof(SymTy);
            PtrTy ptr3273 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr3273)->field0 = tag3204;
            ((TagSymProd *) ptr3273)->field1 = val3271;
            return (PtrCursorProd) {ptr3273, tail3272};
            break;
        }

      case 16:
        {
            SymTy val3274 = *(SymTy *) tail3205;
            CursorTy tail3275 = tail3205 + sizeof(SymTy);
            PtrTy ptr3276 = ALLOC(sizeof(TagSymProd));

            ((TagSymProd *) ptr3276)->field0 = tag3204;
            ((TagSymProd *) ptr3276)->field1 = val3274;
            return (PtrCursorProd) {ptr3276, tail3275};
            break;
        }

      case 17:
        {
            PtrTy ptr3277 = ALLOC(sizeof(TagProd));

            ((TagProd *) ptr3277)->field0 = tag3204;
            return (PtrCursorProd) {ptr3277, tail3205};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3530 = *(CursorTy *) tail3205;
            CursorTy tmpaftercur3531 = tail3205 + 8;
            TagTyPacked tagtmp3532 = *(TagTyPacked *) tmpcur3530;
            CursorTy tailtmp3533 = tmpcur3530 + 1;

            tag3204 = tagtmp3532;
            tail3205 = tailtmp3533;
            goto switch3278;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3530 = *(CursorTy *) tail3205;
            CursorTy tmpaftercur3531 = tail3205 + 8;
            TagTyPacked tagtmp3532 = *(TagTyPacked *) tmpcur3530;
            CursorTy tailtmp3533 = tmpcur3530 + 1;

            tag3204 = tagtmp3532;
            tail3205 = tailtmp3533;
            goto switch3278;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3278");
            exit(1);
        }
    }
}
PtrCursorProd _unpack_Toplvl(CursorTy p3279)
{
    TagTyPacked tag3280 = *(TagTyPacked *) p3279;
    CursorTy tail3281 = p3279 + 1;


  switch3298:
    ;
    switch (tag3280) {

      case 0:
        {
            PtrCursorProd tmp_struct186 =  _unpack_ListSym(tail3281);
            PtrTy ptr3282 = tmp_struct186.field0;
            CursorTy tail3283 = tmp_struct186.field1;
            PtrCursorProd tmp_struct187 =  _unpack_Expr(tail3283);
            PtrTy ptr3284 = tmp_struct187.field0;
            CursorTy tail3285 = tmp_struct187.field1;
            PtrTy ptr3286 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3286)->field0 = tag3280;
            ((TagCursorCursorProd *) ptr3286)->field1 = ptr3282;
            ((TagCursorCursorProd *) ptr3286)->field2 = ptr3284;
            return (PtrCursorProd) {ptr3286, tail3285};
            break;
        }

      case 1:
        {
            PtrCursorProd tmp_struct188 =  _unpack_ListSym(tail3281);
            PtrTy ptr3287 = tmp_struct188.field0;
            CursorTy tail3288 = tmp_struct188.field1;
            PtrCursorProd tmp_struct189 =  _unpack_Expr(tail3288);
            PtrTy ptr3289 = tmp_struct189.field0;
            CursorTy tail3290 = tmp_struct189.field1;
            PtrTy ptr3291 = ALLOC(sizeof(TagCursorCursorProd));

            ((TagCursorCursorProd *) ptr3291)->field0 = tag3280;
            ((TagCursorCursorProd *) ptr3291)->field1 = ptr3287;
            ((TagCursorCursorProd *) ptr3291)->field2 = ptr3289;
            return (PtrCursorProd) {ptr3291, tail3290};
            break;
        }

      case 2:
        {
            PtrCursorProd tmp_struct190 =  _unpack_ListToplvl(tail3281);
            PtrTy ptr3292 = tmp_struct190.field0;
            CursorTy tail3293 = tmp_struct190.field1;
            PtrTy ptr3294 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3294)->field0 = tag3280;
            ((TagCursorProd *) ptr3294)->field1 = ptr3292;
            return (PtrCursorProd) {ptr3294, tail3293};
            break;
        }

      case 3:
        {
            PtrCursorProd tmp_struct191 =  _unpack_Expr(tail3281);
            PtrTy ptr3295 = tmp_struct191.field0;
            CursorTy tail3296 = tmp_struct191.field1;
            PtrTy ptr3297 = ALLOC(sizeof(TagCursorProd));

            ((TagCursorProd *) ptr3297)->field0 = tag3280;
            ((TagCursorProd *) ptr3297)->field1 = ptr3295;
            return (PtrCursorProd) {ptr3297, tail3296};
            break;
        }

      case 255:
        {
            CursorTy tmpcur3534 = *(CursorTy *) tail3281;
            CursorTy tmpaftercur3535 = tail3281 + 8;
            TagTyPacked tagtmp3536 = *(TagTyPacked *) tmpcur3534;
            CursorTy tailtmp3537 = tmpcur3534 + 1;

            tag3280 = tagtmp3536;
            tail3281 = tailtmp3537;
            goto switch3298;
            break;
        }

      case 254:
        {
            CursorTy tmpcur3534 = *(CursorTy *) tail3281;
            CursorTy tmpaftercur3535 = tail3281 + 8;
            TagTyPacked tagtmp3536 = *(TagTyPacked *) tmpcur3534;
            CursorTy tailtmp3537 = tmpcur3534 + 1;

            tag3280 = tagtmp3536;
            tail3281 = tailtmp3537;
            goto switch3298;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3298");
            exit(1);
        }
    }
}
CursorTy _print_ListSym(CursorTy p3299)
{
    TagTyPacked tag3300 = *(TagTyPacked *) p3299;
    CursorTy tail3301 = p3299 + 1;


  switch3305:
    ;
    switch (tag3300) {

      case 0:
        {
            fputs("(CONSSYM ", stdout);

            SymTy val3302 = *(SymTy *) tail3301;
            CursorTy tail3303 = tail3301 + sizeof(SymTy);

            print_symbol(val3302);
            fputs(" ", stdout);

            CursorTy tail3304 =  _print_ListSym(tail3303);

            fputs(")", stdout);
            return tail3304;
            break;
        }

      case 1:
        {
            fputs("(NULLSYM ", stdout);
            fputs(")", stdout);
            return tail3301;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3538 = *(CursorTy *) tail3301;
            CursorTy tmpaftercur3539 = tail3301 + 8;
            TagTyPacked tagtmp3540 = *(TagTyPacked *) tmpcur3538;
            CursorTy tailtmp3541 = tmpcur3538 + 1;

            tag3300 = tagtmp3540;
            tail3301 = tailtmp3541;
            goto switch3305;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3538 = *(CursorTy *) tail3301;
            CursorTy tmpaftercur3539 = tail3301 + 8;
            TagTyPacked tagtmp3540 = *(TagTyPacked *) tmpcur3538;
            CursorTy tailtmp3541 = tmpcur3538 + 1;

            tag3300 = tagtmp3540;
            tail3301 = tailtmp3541;
            goto switch3305;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3305");
            exit(1);
        }
    }
}
CursorTy _print_ListExpr(CursorTy p3306)
{
    TagTyPacked tag3307 = *(TagTyPacked *) p3306;
    CursorTy tail3308 = p3306 + 1;


  switch3311:
    ;
    switch (tag3307) {

      case 0:
        {
            fputs("(CONSEXPR ", stdout);

            CursorTy tail3309 =  _print_Expr(tail3308);

            fputs(" ", stdout);

            CursorTy tail3310 =  _print_ListExpr(tail3309);

            fputs(")", stdout);
            return tail3310;
            break;
        }

      case 1:
        {
            fputs("(NULLEXPR ", stdout);
            fputs(")", stdout);
            return tail3308;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3542 = *(CursorTy *) tail3308;
            CursorTy tmpaftercur3543 = tail3308 + 8;
            TagTyPacked tagtmp3544 = *(TagTyPacked *) tmpcur3542;
            CursorTy tailtmp3545 = tmpcur3542 + 1;

            tag3307 = tagtmp3544;
            tail3308 = tailtmp3545;
            goto switch3311;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3542 = *(CursorTy *) tail3308;
            CursorTy tmpaftercur3543 = tail3308 + 8;
            TagTyPacked tagtmp3544 = *(TagTyPacked *) tmpcur3542;
            CursorTy tailtmp3545 = tmpcur3542 + 1;

            tag3307 = tagtmp3544;
            tail3308 = tailtmp3545;
            goto switch3311;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3311");
            exit(1);
        }
    }
}
CursorTy _print_ListToplvl(CursorTy p3312)
{
    TagTyPacked tag3313 = *(TagTyPacked *) p3312;
    CursorTy tail3314 = p3312 + 1;


  switch3317:
    ;
    switch (tag3313) {

      case 0:
        {
            fputs("(CONSTOPLVL ", stdout);

            CursorTy tail3315 =  _print_Toplvl(tail3314);

            fputs(" ", stdout);

            CursorTy tail3316 =  _print_ListToplvl(tail3315);

            fputs(")", stdout);
            return tail3316;
            break;
        }

      case 1:
        {
            fputs("(NULLTOPLVL ", stdout);
            fputs(")", stdout);
            return tail3314;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3546 = *(CursorTy *) tail3314;
            CursorTy tmpaftercur3547 = tail3314 + 8;
            TagTyPacked tagtmp3548 = *(TagTyPacked *) tmpcur3546;
            CursorTy tailtmp3549 = tmpcur3546 + 1;

            tag3313 = tagtmp3548;
            tail3314 = tailtmp3549;
            goto switch3317;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3546 = *(CursorTy *) tail3314;
            CursorTy tmpaftercur3547 = tail3314 + 8;
            TagTyPacked tagtmp3548 = *(TagTyPacked *) tmpcur3546;
            CursorTy tailtmp3549 = tmpcur3546 + 1;

            tag3313 = tagtmp3548;
            tail3314 = tailtmp3549;
            goto switch3317;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3317");
            exit(1);
        }
    }
}
CursorTy _print_Formals(CursorTy p3318)
{
    TagTyPacked tag3319 = *(TagTyPacked *) p3318;
    CursorTy tail3320 = p3318 + 1;


  switch3327:
    ;
    switch (tag3319) {

      case 0:
        {
            fputs("(F1 ", stdout);

            CursorTy tail3321 =  _print_ListSym(tail3320);

            fputs(")", stdout);
            return tail3321;
            break;
        }

      case 1:
        {
            fputs("(F2 ", stdout);

            CursorTy tail3322 =  _print_ListSym(tail3320);

            fputs(" ", stdout);

            SymTy val3323 = *(SymTy *) tail3322;
            CursorTy tail3324 = tail3322 + sizeof(SymTy);

            print_symbol(val3323);
            fputs(")", stdout);
            return tail3324;
            break;
        }

      case 2:
        {
            fputs("(F3 ", stdout);

            SymTy val3325 = *(SymTy *) tail3320;
            CursorTy tail3326 = tail3320 + sizeof(SymTy);

            print_symbol(val3325);
            fputs(")", stdout);
            return tail3326;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3550 = *(CursorTy *) tail3320;
            CursorTy tmpaftercur3551 = tail3320 + 8;
            TagTyPacked tagtmp3552 = *(TagTyPacked *) tmpcur3550;
            CursorTy tailtmp3553 = tmpcur3550 + 1;

            tag3319 = tagtmp3552;
            tail3320 = tailtmp3553;
            goto switch3327;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3550 = *(CursorTy *) tail3320;
            CursorTy tmpaftercur3551 = tail3320 + 8;
            TagTyPacked tagtmp3552 = *(TagTyPacked *) tmpcur3550;
            CursorTy tailtmp3553 = tmpcur3550 + 1;

            tag3319 = tagtmp3552;
            tail3320 = tailtmp3553;
            goto switch3327;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3327");
            exit(1);
        }
    }
}
CursorTy _print_Datum(CursorTy p3328)
{
    TagTyPacked tag3329 = *(TagTyPacked *) p3328;
    CursorTy tail3330 = p3328 + 1;


  switch3333:
    ;
    switch (tag3329) {

      case 0:
        {
            fputs("(INTLIT ", stdout);

            IntTy val3331 = *(IntTy *) tail3330;
            CursorTy tail3332 = tail3330 + sizeof(IntTy);

            printf("%lld", val3331);
            fputs(")", stdout);
            return tail3332;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3554 = *(CursorTy *) tail3330;
            CursorTy tmpaftercur3555 = tail3330 + 8;
            TagTyPacked tagtmp3556 = *(TagTyPacked *) tmpcur3554;
            CursorTy tailtmp3557 = tmpcur3554 + 1;

            tag3329 = tagtmp3556;
            tail3330 = tailtmp3557;
            goto switch3333;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3554 = *(CursorTy *) tail3330;
            CursorTy tmpaftercur3555 = tail3330 + 8;
            TagTyPacked tagtmp3556 = *(TagTyPacked *) tmpcur3554;
            CursorTy tailtmp3557 = tmpcur3554 + 1;

            tag3329 = tagtmp3556;
            tail3330 = tailtmp3557;
            goto switch3333;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3333");
            exit(1);
        }
    }
}
CursorTy _print_LAMBDACASE(CursorTy p3334)
{
    TagTyPacked tag3335 = *(TagTyPacked *) p3334;
    CursorTy tail3336 = p3334 + 1;


  switch3340:
    ;
    switch (tag3335) {

      case 0:
        {
            fputs("(CONSLAMBDACASE ", stdout);

            CursorTy tail3337 =  _print_Formals(tail3336);

            fputs(" ", stdout);

            CursorTy tail3338 =  _print_ListExpr(tail3337);

            fputs(" ", stdout);

            CursorTy tail3339 =  _print_LAMBDACASE(tail3338);

            fputs(")", stdout);
            return tail3339;
            break;
        }

      case 1:
        {
            fputs("(NULLLAMBDACASE ", stdout);
            fputs(")", stdout);
            return tail3336;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3558 = *(CursorTy *) tail3336;
            CursorTy tmpaftercur3559 = tail3336 + 8;
            TagTyPacked tagtmp3560 = *(TagTyPacked *) tmpcur3558;
            CursorTy tailtmp3561 = tmpcur3558 + 1;

            tag3335 = tagtmp3560;
            tail3336 = tailtmp3561;
            goto switch3340;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3558 = *(CursorTy *) tail3336;
            CursorTy tmpaftercur3559 = tail3336 + 8;
            TagTyPacked tagtmp3560 = *(TagTyPacked *) tmpcur3558;
            CursorTy tailtmp3561 = tmpcur3558 + 1;

            tag3335 = tagtmp3560;
            tail3336 = tailtmp3561;
            goto switch3340;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3340");
            exit(1);
        }
    }
}
CursorTy _print_LVBIND(CursorTy p3341)
{
    TagTyPacked tag3342 = *(TagTyPacked *) p3341;
    CursorTy tail3343 = p3341 + 1;


  switch3347:
    ;
    switch (tag3342) {

      case 0:
        {
            fputs("(CONSLVBIND ", stdout);

            CursorTy tail3344 =  _print_ListSym(tail3343);

            fputs(" ", stdout);

            CursorTy tail3345 =  _print_Expr(tail3344);

            fputs(" ", stdout);

            CursorTy tail3346 =  _print_LVBIND(tail3345);

            fputs(")", stdout);
            return tail3346;
            break;
        }

      case 1:
        {
            fputs("(NULLLVBIND ", stdout);
            fputs(")", stdout);
            return tail3343;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3562 = *(CursorTy *) tail3343;
            CursorTy tmpaftercur3563 = tail3343 + 8;
            TagTyPacked tagtmp3564 = *(TagTyPacked *) tmpcur3562;
            CursorTy tailtmp3565 = tmpcur3562 + 1;

            tag3342 = tagtmp3564;
            tail3343 = tailtmp3565;
            goto switch3347;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3562 = *(CursorTy *) tail3343;
            CursorTy tmpaftercur3563 = tail3343 + 8;
            TagTyPacked tagtmp3564 = *(TagTyPacked *) tmpcur3562;
            CursorTy tailtmp3565 = tmpcur3562 + 1;

            tag3342 = tagtmp3564;
            tail3343 = tailtmp3565;
            goto switch3347;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3347");
            exit(1);
        }
    }
}
CursorTy _print_Expr(CursorTy p3348)
{
    TagTyPacked tag3349 = *(TagTyPacked *) p3348;
    CursorTy tail3350 = p3348 + 1;


  switch3383:
    ;
    switch (tag3349) {

      case 0:
        {
            fputs("(VARREF ", stdout);

            SymTy val3351 = *(SymTy *) tail3350;
            CursorTy tail3352 = tail3350 + sizeof(SymTy);

            print_symbol(val3351);
            fputs(")", stdout);
            return tail3352;
            break;
        }

      case 1:
        {
            fputs("(Lambda ", stdout);

            CursorTy tail3353 =  _print_Formals(tail3350);

            fputs(" ", stdout);

            CursorTy tail3354 =  _print_ListExpr(tail3353);

            fputs(")", stdout);
            return tail3354;
            break;
        }

      case 2:
        {
            fputs("(CaseLambda ", stdout);

            CursorTy tail3355 =  _print_LAMBDACASE(tail3350);

            fputs(")", stdout);
            return tail3355;
            break;
        }

      case 3:
        {
            fputs("(If ", stdout);

            CursorTy tail3356 =  _print_Expr(tail3350);

            fputs(" ", stdout);

            CursorTy tail3357 =  _print_Expr(tail3356);

            fputs(" ", stdout);

            CursorTy tail3358 =  _print_Expr(tail3357);

            fputs(")", stdout);
            return tail3358;
            break;
        }

      case 4:
        {
            fputs("(Begin ", stdout);

            CursorTy tail3359 =  _print_ListExpr(tail3350);

            fputs(")", stdout);
            return tail3359;
            break;
        }

      case 5:
        {
            fputs("(Begin0 ", stdout);

            CursorTy tail3360 =  _print_Expr(tail3350);

            fputs(" ", stdout);

            CursorTy tail3361 =  _print_ListExpr(tail3360);

            fputs(")", stdout);
            return tail3361;
            break;
        }

      case 6:
        {
            fputs("(LetValues ", stdout);

            CursorTy tail3362 =  _print_LVBIND(tail3350);

            fputs(" ", stdout);

            CursorTy tail3363 =  _print_ListExpr(tail3362);

            fputs(")", stdout);
            return tail3363;
            break;
        }

      case 7:
        {
            fputs("(LetrecValues ", stdout);

            CursorTy tail3364 =  _print_LVBIND(tail3350);

            fputs(" ", stdout);

            CursorTy tail3365 =  _print_ListExpr(tail3364);

            fputs(")", stdout);
            return tail3365;
            break;
        }

      case 8:
        {
            fputs("(SetBang ", stdout);

            SymTy val3366 = *(SymTy *) tail3350;
            CursorTy tail3367 = tail3350 + sizeof(SymTy);

            print_symbol(val3366);
            fputs(" ", stdout);

            CursorTy tail3368 =  _print_Expr(tail3367);

            fputs(")", stdout);
            return tail3368;
            break;
        }

      case 9:
        {
            fputs("(Quote ", stdout);

            CursorTy tail3369 =  _print_Datum(tail3350);

            fputs(")", stdout);
            return tail3369;
            break;
        }

      case 10:
        {
            fputs("(QuoteSyntax ", stdout);

            CursorTy tail3370 =  _print_Datum(tail3350);

            fputs(")", stdout);
            return tail3370;
            break;
        }

      case 11:
        {
            fputs("(QuoteSyntaxLocal ", stdout);

            CursorTy tail3371 =  _print_Datum(tail3350);

            fputs(")", stdout);
            return tail3371;
            break;
        }

      case 12:
        {
            fputs("(WithContinuationMark ", stdout);

            CursorTy tail3372 =  _print_Expr(tail3350);

            fputs(" ", stdout);

            CursorTy tail3373 =  _print_Expr(tail3372);

            fputs(" ", stdout);

            CursorTy tail3374 =  _print_Expr(tail3373);

            fputs(")", stdout);
            return tail3374;
            break;
        }

      case 13:
        {
            fputs("(App ", stdout);

            CursorTy tail3375 =  _print_Expr(tail3350);

            fputs(" ", stdout);

            CursorTy tail3376 =  _print_ListExpr(tail3375);

            fputs(")", stdout);
            return tail3376;
            break;
        }

      case 14:
        {
            fputs("(Top ", stdout);

            SymTy val3377 = *(SymTy *) tail3350;
            CursorTy tail3378 = tail3350 + sizeof(SymTy);

            print_symbol(val3377);
            fputs(")", stdout);
            return tail3378;
            break;
        }

      case 15:
        {
            fputs("(VariableReference ", stdout);

            SymTy val3379 = *(SymTy *) tail3350;
            CursorTy tail3380 = tail3350 + sizeof(SymTy);

            print_symbol(val3379);
            fputs(")", stdout);
            return tail3380;
            break;
        }

      case 16:
        {
            fputs("(VariableReferenceTop ", stdout);

            SymTy val3381 = *(SymTy *) tail3350;
            CursorTy tail3382 = tail3350 + sizeof(SymTy);

            print_symbol(val3381);
            fputs(")", stdout);
            return tail3382;
            break;
        }

      case 17:
        {
            fputs("(VariableReferenceNull ", stdout);
            fputs(")", stdout);
            return tail3350;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3566 = *(CursorTy *) tail3350;
            CursorTy tmpaftercur3567 = tail3350 + 8;
            TagTyPacked tagtmp3568 = *(TagTyPacked *) tmpcur3566;
            CursorTy tailtmp3569 = tmpcur3566 + 1;

            tag3349 = tagtmp3568;
            tail3350 = tailtmp3569;
            goto switch3383;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3566 = *(CursorTy *) tail3350;
            CursorTy tmpaftercur3567 = tail3350 + 8;
            TagTyPacked tagtmp3568 = *(TagTyPacked *) tmpcur3566;
            CursorTy tailtmp3569 = tmpcur3566 + 1;

            tag3349 = tagtmp3568;
            tail3350 = tailtmp3569;
            goto switch3383;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3383");
            exit(1);
        }
    }
}
CursorTy _print_Toplvl(CursorTy p3384)
{
    TagTyPacked tag3385 = *(TagTyPacked *) p3384;
    CursorTy tail3386 = p3384 + 1;


  switch3393:
    ;
    switch (tag3385) {

      case 0:
        {
            fputs("(DefineValues ", stdout);

            CursorTy tail3387 =  _print_ListSym(tail3386);

            fputs(" ", stdout);

            CursorTy tail3388 =  _print_Expr(tail3387);

            fputs(")", stdout);
            return tail3388;
            break;
        }

      case 1:
        {
            fputs("(DefineSyntaxes ", stdout);

            CursorTy tail3389 =  _print_ListSym(tail3386);

            fputs(" ", stdout);

            CursorTy tail3390 =  _print_Expr(tail3389);

            fputs(")", stdout);
            return tail3390;
            break;
        }

      case 2:
        {
            fputs("(BeginTop ", stdout);

            CursorTy tail3391 =  _print_ListToplvl(tail3386);

            fputs(")", stdout);
            return tail3391;
            break;
        }

      case 3:
        {
            fputs("(Expression ", stdout);

            CursorTy tail3392 =  _print_Expr(tail3386);

            fputs(")", stdout);
            return tail3392;
            break;
        }

      case 255:
        {
            fputs(" ->r ", stdout);

            CursorTy tmpcur3570 = *(CursorTy *) tail3386;
            CursorTy tmpaftercur3571 = tail3386 + 8;
            TagTyPacked tagtmp3572 = *(TagTyPacked *) tmpcur3570;
            CursorTy tailtmp3573 = tmpcur3570 + 1;

            tag3385 = tagtmp3572;
            tail3386 = tailtmp3573;
            goto switch3393;
            break;
        }

      case 254:
        {
            fputs(" ->i ", stdout);

            CursorTy tmpcur3570 = *(CursorTy *) tail3386;
            CursorTy tmpaftercur3571 = tail3386 + 8;
            TagTyPacked tagtmp3572 = *(TagTyPacked *) tmpcur3570;
            CursorTy tailtmp3573 = tmpcur3570 + 1;

            tag3385 = tagtmp3572;
            tail3386 = tailtmp3573;
            goto switch3393;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: switch3393");
            exit(1);
        }
    }
}
void __main_expr()
{
    IntTy timed2114;
    UT_array *times195;


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
        CursorTy r672 = (CursorTy) bnch;
        IntTy sizeof_end_r6722351 = bnch_size;
        CursorTy end_r672 = r672 + sizeof_end_r6722351;

        CursorInt64Prod i = _traverse_Toplvl(end_r672, r672);

    utarray_new(times195, &double_icd);

    struct timespec begin_timed2114;
    struct timespec end_timed2114;

    for (long long iters_timed2114 = 0; iters_timed2114 < global_iters_param;
         iters_timed2114++) {
        if (iters_timed2114 != global_iters_param - 1)
            save_alloc_state();
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed2114);

        CursorInt64Prod tmp_struct192 =  countnodes(end_r672, bnch);
        CursorTy pvrtmp2352 = tmp_struct192.field0;
        IntTy pvrtmp2353 = tmp_struct192.field1;
        CursorTy endof1572 = (CursorTy) pvrtmp2352;
        IntTy benchres = (IntTy) pvrtmp2353;

        timed2114 = benchres;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed2114);
        if (iters_timed2114 != global_iters_param - 1)
            restore_alloc_state();

        double batchtime193 = difftimespecs(&begin_timed2114, &end_timed2114);

        utarray_push_back(times195, &batchtime193);
    }
    utarray_sort(times195, compare_doubles);

    double *tmp196 = (double *) utarray_eltptr(times195, global_iters_param /
                                               2);
    double selftimed194 = *tmp196;

    print_timing_array(times195);
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("SELFTIMED: %e\n", selftimed194);
    printf("%lld", timed2114);
    fputs("\n", stdout);
    free_symtable();
    return;
}
