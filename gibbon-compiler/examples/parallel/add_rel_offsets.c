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
static long long global_init_biginf_buf_size = (4 * GB);

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
typedef struct TagInt64Int64Int64CursorCursorCursorProd_struct {
            TagTyPacked field0;
            IntTy field1;
            IntTy field2;
            IntTy field3;
            CursorTy field4;
            CursorTy field5;
            CursorTy field6;
        } TagInt64Int64Int64CursorCursorCursorProd;
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
typedef struct TagCursorCursorCursorCursorCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
            CursorTy field2;
            CursorTy field3;
            CursorTy field4;
            CursorTy field5;
        } TagCursorCursorCursorCursorCursorProd;
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


CursorCursorCursorCursorProd
_add_size_and_rel_offsets_ListSym(CursorTy end_r2711, CursorTy end_r2712,
                                  CursorTy loc2710, CursorTy arg1795);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_ListExpr(CursorTy end_r2715, CursorTy end_r2716,
                                   CursorTy loc2714, CursorTy arg1800);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_ListToplvl(CursorTy end_r2719, CursorTy end_r2720,
                                     CursorTy loc2718, CursorTy arg1809);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Formals(CursorTy end_r2723, CursorTy end_r2724,
                                  CursorTy loc2722, CursorTy arg1818);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Datum(CursorTy end_r2727,
                                                             CursorTy end_r2728,
                                                             CursorTy loc2726,
                                                             CursorTy arg1827);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_LAMBDACASE(CursorTy end_r2731, CursorTy end_r2732,
                                     CursorTy loc2730, CursorTy arg1830);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_LVBIND(CursorTy end_r2735, CursorTy end_r2736,
                                 CursorTy loc2734, CursorTy arg1837);
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Expr(CursorTy end_r2739,
                                                            CursorTy end_r2740,
                                                            CursorTy loc2738,
                                                            CursorTy arg1844);
CursorCursorCursorCursorProd
_add_size_and_rel_offsets_Toplvl(CursorTy end_r2743, CursorTy end_r2744,
                                 CursorTy loc2742, CursorTy arg1931);


// OFFSETS START HERE

CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListSym(CursorTy end_r2656,
                                                               CursorTy end_r2657,
                                                               CursorTy loc2655,
                                                               CursorTy arg1778)
{
    CursorTy loc2654 = (CursorTy) arg1778;

    if (loc2655 + 18 > end_r2657) {
        ChunkTy new_chunk332 = alloc_chunk(end_r2657);
        CursorTy chunk_start333 = new_chunk332.start_ptr;
        CursorTy chunk_end334 = new_chunk332.end_ptr;

        end_r2657 = chunk_end334;
        *(TagTyPacked *) loc2655 = 255;

        CursorTy redir = loc2655 + 1;

        *(CursorTy *) redir = chunk_start333;
        loc2655 = chunk_start333;
    }

    CursorTy loc4323 = loc2655 + 1;
    CursorTy loc4324 = loc4323 + 8;
    TagTyPacked tmpval9695 = *(TagTyPacked *) arg1778;
    CursorTy tmpcur9696 = arg1778 + 1;


  switch9715:
    ;
    switch (tmpval9695) {

      case 0:
        {
            CursorTy field_cur6660 = (CursorTy) tmpcur9696;
            CursorTy case4318 = (CursorTy) field_cur6660;
            SymTy tmpval9697 = *(SymTy *) case4318;
            CursorTy tmpcur9698 = case4318 + sizeof(SymTy);
            SymTy x1779 = (SymTy) tmpval9697;
            CursorTy end_x1779 = (CursorTy) tmpcur9698;
            CursorTy case4319 = (CursorTy) end_x1779;
            CursorTy x1780 = (CursorTy) case4319;
            CursorTy jump5428 = case4318 + 8;
            CursorCursorCursorCursorProd tmp_struct331 =
                                          _add_size_and_rel_offsets_ListSym(end_r2656, end_r2657, loc4324, x1780);
            CursorTy pvrtmp9699 = tmp_struct331.field0;
            CursorTy pvrtmp9700 = tmp_struct331.field1;
            CursorTy pvrtmp9701 = tmp_struct331.field2;
            CursorTy pvrtmp9702 = tmp_struct331.field3;
            CursorTy fltPrd7687 = (CursorTy) pvrtmp9701;
            CursorTy fltPrd7688 = (CursorTy) pvrtmp9702;
            CursorTy pvrtmp9704 = (CursorTy) fltPrd7688;
            CursorTy pvrtmp9703 = (CursorTy) fltPrd7687;
            CursorTy y1782 = (CursorTy) pvrtmp9703;
            CursorTy fltPrd7689 = (CursorTy) pvrtmp9701;
            CursorTy fltPrd7690 = (CursorTy) pvrtmp9702;
            CursorTy pvrtmp9706 = (CursorTy) fltPrd7690;
            CursorTy pvrtmp9705 = (CursorTy) fltPrd7689;
            CursorTy end_y1782 = (CursorTy) pvrtmp9706;
            CursorTy end_r2657_5605 = (CursorTy) pvrtmp9699;
            CursorTy endof5429 = (CursorTy) pvrtmp9700;

            *(TagTyPacked *) loc2655 = 0;

            CursorTy writetag6663 = loc2655 + 1;

            *(SymTy *) writetag6663 = x1779;

            CursorTy writecur6664 = writetag6663 + sizeof(SymTy);
            CursorTy writecur6665 = (CursorTy) end_y1782;
            CursorTy pvrtmp9708 = (CursorTy) writecur6665;
            CursorTy pvrtmp9707 = (CursorTy) loc2655;
            CursorTy taildc5430 = (CursorTy) pvrtmp9707;
            CursorTy end_taildc5430 = (CursorTy) pvrtmp9708;
            CursorTy pvrtmp9710 = (CursorTy) end_taildc5430;
            CursorTy pvrtmp9709 = (CursorTy) taildc5430;
            CursorTy fltPrd7691 = (CursorTy) pvrtmp9709;
            CursorTy fltPrd7692 = (CursorTy) pvrtmp9710;

            return (CursorCursorCursorCursorProd) {end_r2657_5605, endof5429,
                                                   fltPrd7691, fltPrd7692};
            break;
        }

      case 1:
        {
            CursorTy field_cur6667 = (CursorTy) tmpcur9696;
            CursorTy jump5431 = loc2654 + 1;

            *(TagTyPacked *) loc2655 = 1;

            CursorTy writetag6668 = loc2655 + 1;
            CursorTy pvrtmp9712 = (CursorTy) writetag6668;
            CursorTy pvrtmp9711 = (CursorTy) loc2655;
            CursorTy taildc5432 = (CursorTy) pvrtmp9711;
            CursorTy end_taildc5432 = (CursorTy) pvrtmp9712;
            CursorTy pvrtmp9714 = (CursorTy) end_taildc5432;
            CursorTy pvrtmp9713 = (CursorTy) taildc5432;
            CursorTy fltPrd7693 = (CursorTy) pvrtmp9713;
            CursorTy fltPrd7694 = (CursorTy) pvrtmp9714;

            return (CursorCursorCursorCursorProd) {end_r2657, jump5431,
                                                   fltPrd7693, fltPrd7694};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10879 = *(CursorTy *) tmpcur9696;
            CursorTy tmpaftercur10880 = tmpcur9696 + 8;
            TagTyPacked tagtmp10881 = *(TagTyPacked *) tmpcur10879;
            CursorTy tailtmp10882 = tmpcur10879 + 1;

            tmpval9695 = tagtmp10881;
            tmpcur9696 = tailtmp10882;
            goto switch9715;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10879 = *(CursorTy *) tmpcur9696;
            CursorTy tmpaftercur10880 = tmpcur9696 + 8;
            TagTyPacked tagtmp10881 = *(TagTyPacked *) tmpcur10879;
            CursorTy tailtmp10882 = tmpcur10879 + 1;

            tmpval9695 = tagtmp10881;
            tmpcur9696 = tailtmp10882;
            goto switch9715;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9695");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListExpr(CursorTy end_r2660,
                                                                CursorTy end_r2661,
                                                                CursorTy loc2659,
                                                                CursorTy arg1783)
{
    CursorTy loc2658 = (CursorTy) arg1783;

    if (loc2659 + 18 > end_r2661) {
        ChunkTy new_chunk337 = alloc_chunk(end_r2661);
        CursorTy chunk_start338 = new_chunk337.start_ptr;
        CursorTy chunk_end339 = new_chunk337.end_ptr;

        end_r2661 = chunk_end339;
        *(TagTyPacked *) loc2659 = 255;

        CursorTy redir = loc2659 + 1;

        *(CursorTy *) redir = chunk_start338;
        loc2659 = chunk_start338;
    }

    TagTyPacked tmpval9716 = *(TagTyPacked *) arg1783;
    CursorTy tmpcur9717 = arg1783 + 1;


  switch9742:
    ;
    switch (tmpval9716) {

      case 0:
        {
            CursorTy field_cur6670 = (CursorTy) tmpcur9717;
            CursorTy case4331 = (CursorTy) field_cur6670;
            CursorTy x1784 = (CursorTy) case4331;
            CursorTy loc4339 = loc2659 + 1;
            CursorCursorCursorCursorProd tmp_struct335 =
                                          _add_size_and_rel_offsets_Expr(end_r2660, end_r2661, loc4339, x1784);
            CursorTy pvrtmp9718 = tmp_struct335.field0;
            CursorTy pvrtmp9719 = tmp_struct335.field1;
            CursorTy pvrtmp9720 = tmp_struct335.field2;
            CursorTy pvrtmp9721 = tmp_struct335.field3;
            CursorTy fltPrd7695 = (CursorTy) pvrtmp9720;
            CursorTy fltPrd7696 = (CursorTy) pvrtmp9721;
            CursorTy pvrtmp9723 = (CursorTy) fltPrd7696;
            CursorTy pvrtmp9722 = (CursorTy) fltPrd7695;
            CursorTy y1786 = (CursorTy) pvrtmp9722;
            CursorTy fltPrd7697 = (CursorTy) pvrtmp9720;
            CursorTy fltPrd7698 = (CursorTy) pvrtmp9721;
            CursorTy pvrtmp9725 = (CursorTy) fltPrd7698;
            CursorTy pvrtmp9724 = (CursorTy) fltPrd7697;
            CursorTy end_y1786 = (CursorTy) pvrtmp9725;
            CursorTy end_r2661_5606 = (CursorTy) pvrtmp9718;
            CursorTy endof5433 = (CursorTy) pvrtmp9719;
            CursorTy case4332 = (CursorTy) endof5433;
            CursorTy x1785 = (CursorTy) case4332;
            CursorTy loc4340 = (CursorTy) end_y1786;
            CursorCursorCursorCursorProd tmp_struct336 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2660, end_r2661_5606, loc4340, x1785);
            CursorTy pvrtmp9726 = tmp_struct336.field0;
            CursorTy pvrtmp9727 = tmp_struct336.field1;
            CursorTy pvrtmp9728 = tmp_struct336.field2;
            CursorTy pvrtmp9729 = tmp_struct336.field3;
            CursorTy fltPrd7699 = (CursorTy) pvrtmp9728;
            CursorTy fltPrd7700 = (CursorTy) pvrtmp9729;
            CursorTy pvrtmp9731 = (CursorTy) fltPrd7700;
            CursorTy pvrtmp9730 = (CursorTy) fltPrd7699;
            CursorTy y1787 = (CursorTy) pvrtmp9730;
            CursorTy fltPrd7701 = (CursorTy) pvrtmp9728;
            CursorTy fltPrd7702 = (CursorTy) pvrtmp9729;
            CursorTy pvrtmp9733 = (CursorTy) fltPrd7702;
            CursorTy pvrtmp9732 = (CursorTy) fltPrd7701;
            CursorTy end_y1787 = (CursorTy) pvrtmp9733;
            CursorTy end_r2661_5606_5607 = (CursorTy) pvrtmp9726;
            CursorTy endof5434 = (CursorTy) pvrtmp9727;

            *(TagTyPacked *) loc2659 = 0;

            CursorTy writetag6673 = loc2659 + 1;
            CursorTy writecur6674 = (CursorTy) end_y1786;
            CursorTy writecur6675 = (CursorTy) end_y1787;
            CursorTy pvrtmp9735 = (CursorTy) writecur6675;
            CursorTy pvrtmp9734 = (CursorTy) loc2659;
            CursorTy taildc5435 = (CursorTy) pvrtmp9734;
            CursorTy end_taildc5435 = (CursorTy) pvrtmp9735;
            CursorTy pvrtmp9737 = (CursorTy) end_taildc5435;
            CursorTy pvrtmp9736 = (CursorTy) taildc5435;
            CursorTy fltPrd7703 = (CursorTy) pvrtmp9736;
            CursorTy fltPrd7704 = (CursorTy) pvrtmp9737;

            return (CursorCursorCursorCursorProd) {end_r2661_5606_5607,
                                                   endof5434, fltPrd7703,
                                                   fltPrd7704};
            break;
        }

      case 1:
        {
            CursorTy field_cur6677 = (CursorTy) tmpcur9717;
            CursorTy jump5436 = loc2658 + 1;

            *(TagTyPacked *) loc2659 = 1;

            CursorTy writetag6678 = loc2659 + 1;
            CursorTy pvrtmp9739 = (CursorTy) writetag6678;
            CursorTy pvrtmp9738 = (CursorTy) loc2659;
            CursorTy taildc5437 = (CursorTy) pvrtmp9738;
            CursorTy end_taildc5437 = (CursorTy) pvrtmp9739;
            CursorTy pvrtmp9741 = (CursorTy) end_taildc5437;
            CursorTy pvrtmp9740 = (CursorTy) taildc5437;
            CursorTy fltPrd7705 = (CursorTy) pvrtmp9740;
            CursorTy fltPrd7706 = (CursorTy) pvrtmp9741;

            return (CursorCursorCursorCursorProd) {end_r2661, jump5436,
                                                   fltPrd7705, fltPrd7706};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10883 = *(CursorTy *) tmpcur9717;
            CursorTy tmpaftercur10884 = tmpcur9717 + 8;
            TagTyPacked tagtmp10885 = *(TagTyPacked *) tmpcur10883;
            CursorTy tailtmp10886 = tmpcur10883 + 1;

            tmpval9716 = tagtmp10885;
            tmpcur9717 = tailtmp10886;
            goto switch9742;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10883 = *(CursorTy *) tmpcur9717;
            CursorTy tmpaftercur10884 = tmpcur9717 + 8;
            TagTyPacked tagtmp10885 = *(TagTyPacked *) tmpcur10883;
            CursorTy tailtmp10886 = tmpcur10883 + 1;

            tmpval9716 = tagtmp10885;
            tmpcur9717 = tailtmp10886;
            goto switch9742;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9716");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListToplvl(CursorTy end_r2664,
                                                                  CursorTy end_r2665,
                                                                  CursorTy loc2663,
                                                                  CursorTy arg1788)
{
    CursorTy loc2662 = (CursorTy) arg1788;

    if (loc2663 + 26 > end_r2665) {
        ChunkTy new_chunk342 = alloc_chunk(end_r2665);
        CursorTy chunk_start343 = new_chunk342.start_ptr;
        CursorTy chunk_end344 = new_chunk342.end_ptr;

        end_r2665 = chunk_end344;
        *(TagTyPacked *) loc2663 = 255;

        CursorTy redir = loc2663 + 1;

        *(CursorTy *) redir = chunk_start343;
        loc2663 = chunk_start343;
    }

    CursorTy loc4354 = loc2663 + 1;
    CursorTy loc4355 = loc4354 + 8;
    CursorTy loc4356 = loc4355 + 8;
    TagTyPacked tmpval9743 = *(TagTyPacked *) arg1788;
    CursorTy tmpcur9744 = arg1788 + 1;


  switch9769:
    ;
    switch (tmpval9743) {

      case 0:
        {
            CursorTy field_cur6680 = (CursorTy) tmpcur9744;
            CursorTy case4346 = (CursorTy) field_cur6680;
            CursorTy x1789 = (CursorTy) case4346;
            CursorCursorCursorCursorProd tmp_struct340 =
                                          _add_size_and_rel_offsets_Toplvl(end_r2664, end_r2665, loc4356, x1789);
            CursorTy pvrtmp9745 = tmp_struct340.field0;
            CursorTy pvrtmp9746 = tmp_struct340.field1;
            CursorTy pvrtmp9747 = tmp_struct340.field2;
            CursorTy pvrtmp9748 = tmp_struct340.field3;
            CursorTy fltPrd7707 = (CursorTy) pvrtmp9747;
            CursorTy fltPrd7708 = (CursorTy) pvrtmp9748;
            CursorTy pvrtmp9750 = (CursorTy) fltPrd7708;
            CursorTy pvrtmp9749 = (CursorTy) fltPrd7707;
            CursorTy y1791 = (CursorTy) pvrtmp9749;
            CursorTy fltPrd7709 = (CursorTy) pvrtmp9747;
            CursorTy fltPrd7710 = (CursorTy) pvrtmp9748;
            CursorTy pvrtmp9752 = (CursorTy) fltPrd7710;
            CursorTy pvrtmp9751 = (CursorTy) fltPrd7709;
            CursorTy end_y1791 = (CursorTy) pvrtmp9752;
            CursorTy end_r2665_5608 = (CursorTy) pvrtmp9745;
            CursorTy endof5438 = (CursorTy) pvrtmp9746;
            CursorTy case4347 = (CursorTy) endof5438;
            CursorTy x1790 = (CursorTy) case4347;
            CursorTy loc4357 = (CursorTy) end_y1791;
            CursorCursorCursorCursorProd tmp_struct341 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r2664, end_r2665_5608, loc4357, x1790);
            CursorTy pvrtmp9753 = tmp_struct341.field0;
            CursorTy pvrtmp9754 = tmp_struct341.field1;
            CursorTy pvrtmp9755 = tmp_struct341.field2;
            CursorTy pvrtmp9756 = tmp_struct341.field3;
            CursorTy fltPrd7711 = (CursorTy) pvrtmp9755;
            CursorTy fltPrd7712 = (CursorTy) pvrtmp9756;
            CursorTy pvrtmp9758 = (CursorTy) fltPrd7712;
            CursorTy pvrtmp9757 = (CursorTy) fltPrd7711;
            CursorTy y1792 = (CursorTy) pvrtmp9757;
            CursorTy fltPrd7713 = (CursorTy) pvrtmp9755;
            CursorTy fltPrd7714 = (CursorTy) pvrtmp9756;
            CursorTy pvrtmp9760 = (CursorTy) fltPrd7714;
            CursorTy pvrtmp9759 = (CursorTy) fltPrd7713;
            CursorTy end_y1792 = (CursorTy) pvrtmp9760;
            CursorTy end_r2665_5608_5609 = (CursorTy) pvrtmp9753;
            CursorTy endof5439 = (CursorTy) pvrtmp9754;
            IntTy sizeof_y1791_1793 = end_y1791 - y1791;
            IntTy sizeof_y1792_1794 = end_y1792 - y1792;
            IntTy fltPrm2461 = sizeof_y1791_1793 + 0;
            IntTy offset_1795 = 0 + fltPrm2461;
            IntTy fltPrm2462 = sizeof_y1791_1793 + sizeof_y1792_1794;
            IntTy size_dcon1796 = 9 + fltPrm2462;

            *(TagTyPacked *) loc2663 = 153;

            CursorTy writetag6683 = loc2663 + 1;

            *(IntTy *) writetag6683 = size_dcon1796;

            CursorTy writecur6684 = writetag6683 + sizeof(IntTy);

            *(IntTy *) writecur6684 = offset_1795;

            CursorTy writecur6685 = writecur6684 + sizeof(IntTy);
            CursorTy writecur6686 = (CursorTy) end_y1791;
            CursorTy writecur6687 = (CursorTy) end_y1792;
            CursorTy pvrtmp9762 = (CursorTy) writecur6687;
            CursorTy pvrtmp9761 = (CursorTy) loc2663;
            CursorTy taildc5440 = (CursorTy) pvrtmp9761;
            CursorTy end_taildc5440 = (CursorTy) pvrtmp9762;
            CursorTy pvrtmp9764 = (CursorTy) end_taildc5440;
            CursorTy pvrtmp9763 = (CursorTy) taildc5440;
            CursorTy fltPrd7715 = (CursorTy) pvrtmp9763;
            CursorTy fltPrd7716 = (CursorTy) pvrtmp9764;

            return (CursorCursorCursorCursorProd) {end_r2665_5608_5609,
                                                   endof5439, fltPrd7715,
                                                   fltPrd7716};
            break;
        }

      case 1:
        {
            CursorTy field_cur6689 = (CursorTy) tmpcur9744;
            CursorTy jump5441 = loc2662 + 1;

            *(TagTyPacked *) loc2663 = 1;

            CursorTy writetag6690 = loc2663 + 1;
            CursorTy pvrtmp9766 = (CursorTy) writetag6690;
            CursorTy pvrtmp9765 = (CursorTy) loc2663;
            CursorTy taildc5442 = (CursorTy) pvrtmp9765;
            CursorTy end_taildc5442 = (CursorTy) pvrtmp9766;
            CursorTy pvrtmp9768 = (CursorTy) end_taildc5442;
            CursorTy pvrtmp9767 = (CursorTy) taildc5442;
            CursorTy fltPrd7717 = (CursorTy) pvrtmp9767;
            CursorTy fltPrd7718 = (CursorTy) pvrtmp9768;

            return (CursorCursorCursorCursorProd) {end_r2665, jump5441,
                                                   fltPrd7717, fltPrd7718};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10887 = *(CursorTy *) tmpcur9744;
            CursorTy tmpaftercur10888 = tmpcur9744 + 8;
            TagTyPacked tagtmp10889 = *(TagTyPacked *) tmpcur10887;
            CursorTy tailtmp10890 = tmpcur10887 + 1;

            tmpval9743 = tagtmp10889;
            tmpcur9744 = tailtmp10890;
            goto switch9769;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10887 = *(CursorTy *) tmpcur9744;
            CursorTy tmpaftercur10888 = tmpcur9744 + 8;
            TagTyPacked tagtmp10889 = *(TagTyPacked *) tmpcur10887;
            CursorTy tailtmp10890 = tmpcur10887 + 1;

            tmpval9743 = tagtmp10889;
            tmpcur9744 = tailtmp10890;
            goto switch9769;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9743");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Formals(CursorTy end_r2668,
                                                               CursorTy end_r2669,
                                                               CursorTy loc2667,
                                                               CursorTy arg1797)
{
    CursorTy loc2666 = (CursorTy) arg1797;

    if (loc2667 + 18 > end_r2669) {
        ChunkTy new_chunk347 = alloc_chunk(end_r2669);
        CursorTy chunk_start348 = new_chunk347.start_ptr;
        CursorTy chunk_end349 = new_chunk347.end_ptr;

        end_r2669 = chunk_end349;
        *(TagTyPacked *) loc2667 = 255;

        CursorTy redir = loc2667 + 1;

        *(CursorTy *) redir = chunk_start348;
        loc2667 = chunk_start348;
    }

    TagTyPacked tmpval9770 = *(TagTyPacked *) arg1797;
    CursorTy tmpcur9771 = arg1797 + 1;


  switch9804:
    ;
    switch (tmpval9770) {

      case 0:
        {
            CursorTy field_cur6692 = (CursorTy) tmpcur9771;
            CursorTy case4367 = (CursorTy) field_cur6692;
            CursorTy x1798 = (CursorTy) case4367;
            CursorTy loc4371 = loc2667 + 1;
            CursorCursorCursorCursorProd tmp_struct345 =
                                          _add_size_and_rel_offsets_ListSym(end_r2668, end_r2669, loc4371, x1798);
            CursorTy pvrtmp9772 = tmp_struct345.field0;
            CursorTy pvrtmp9773 = tmp_struct345.field1;
            CursorTy pvrtmp9774 = tmp_struct345.field2;
            CursorTy pvrtmp9775 = tmp_struct345.field3;
            CursorTy fltPrd7719 = (CursorTy) pvrtmp9774;
            CursorTy fltPrd7720 = (CursorTy) pvrtmp9775;
            CursorTy pvrtmp9777 = (CursorTy) fltPrd7720;
            CursorTy pvrtmp9776 = (CursorTy) fltPrd7719;
            CursorTy y1799 = (CursorTy) pvrtmp9776;
            CursorTy fltPrd7721 = (CursorTy) pvrtmp9774;
            CursorTy fltPrd7722 = (CursorTy) pvrtmp9775;
            CursorTy pvrtmp9779 = (CursorTy) fltPrd7722;
            CursorTy pvrtmp9778 = (CursorTy) fltPrd7721;
            CursorTy end_y1799 = (CursorTy) pvrtmp9779;
            CursorTy end_r2669_5610 = (CursorTy) pvrtmp9772;
            CursorTy endof5443 = (CursorTy) pvrtmp9773;

            *(TagTyPacked *) loc2667 = 0;

            CursorTy writetag6694 = loc2667 + 1;
            CursorTy writecur6695 = (CursorTy) end_y1799;
            CursorTy pvrtmp9781 = (CursorTy) writecur6695;
            CursorTy pvrtmp9780 = (CursorTy) loc2667;
            CursorTy taildc5444 = (CursorTy) pvrtmp9780;
            CursorTy end_taildc5444 = (CursorTy) pvrtmp9781;
            CursorTy pvrtmp9783 = (CursorTy) end_taildc5444;
            CursorTy pvrtmp9782 = (CursorTy) taildc5444;
            CursorTy fltPrd7723 = (CursorTy) pvrtmp9782;
            CursorTy fltPrd7724 = (CursorTy) pvrtmp9783;

            return (CursorCursorCursorCursorProd) {end_r2669_5610, endof5443,
                                                   fltPrd7723, fltPrd7724};
            break;
        }

      case 1:
        {
            CursorTy field_cur6697 = (CursorTy) tmpcur9771;
            CursorTy case4373 = (CursorTy) field_cur6697;
            CursorTy x1800 = (CursorTy) case4373;
            CursorTy loc4378 = loc2667 + 1;
            CursorCursorCursorCursorProd tmp_struct346 =
                                          _add_size_and_rel_offsets_ListSym(end_r2668, end_r2669, loc4378, x1800);
            CursorTy pvrtmp9784 = tmp_struct346.field0;
            CursorTy pvrtmp9785 = tmp_struct346.field1;
            CursorTy pvrtmp9786 = tmp_struct346.field2;
            CursorTy pvrtmp9787 = tmp_struct346.field3;
            CursorTy fltPrd7725 = (CursorTy) pvrtmp9786;
            CursorTy fltPrd7726 = (CursorTy) pvrtmp9787;
            CursorTy pvrtmp9789 = (CursorTy) fltPrd7726;
            CursorTy pvrtmp9788 = (CursorTy) fltPrd7725;
            CursorTy y1802 = (CursorTy) pvrtmp9788;
            CursorTy fltPrd7727 = (CursorTy) pvrtmp9786;
            CursorTy fltPrd7728 = (CursorTy) pvrtmp9787;
            CursorTy pvrtmp9791 = (CursorTy) fltPrd7728;
            CursorTy pvrtmp9790 = (CursorTy) fltPrd7727;
            CursorTy end_y1802 = (CursorTy) pvrtmp9791;
            CursorTy end_r2669_5611 = (CursorTy) pvrtmp9784;
            CursorTy endof5446 = (CursorTy) pvrtmp9785;
            CursorTy case4374 = (CursorTy) endof5446;
            CursorTy jump5445 = case4374 + 8;
            SymTy tmpval9792 = *(SymTy *) case4374;
            CursorTy tmpcur9793 = case4374 + sizeof(SymTy);
            SymTy x1801 = (SymTy) tmpval9792;
            CursorTy end_x1801 = (CursorTy) tmpcur9793;

            *(TagTyPacked *) loc2667 = 1;

            CursorTy writetag6700 = loc2667 + 1;
            CursorTy writecur6701 = (CursorTy) end_y1802;

            *(SymTy *) writecur6701 = x1801;

            CursorTy writecur6702 = writecur6701 + sizeof(SymTy);
            CursorTy pvrtmp9795 = (CursorTy) writecur6702;
            CursorTy pvrtmp9794 = (CursorTy) loc2667;
            CursorTy taildc5447 = (CursorTy) pvrtmp9794;
            CursorTy end_taildc5447 = (CursorTy) pvrtmp9795;
            CursorTy pvrtmp9797 = (CursorTy) end_taildc5447;
            CursorTy pvrtmp9796 = (CursorTy) taildc5447;
            CursorTy fltPrd7729 = (CursorTy) pvrtmp9796;
            CursorTy fltPrd7730 = (CursorTy) pvrtmp9797;

            return (CursorCursorCursorCursorProd) {end_r2669_5611, jump5445,
                                                   fltPrd7729, fltPrd7730};
            break;
        }

      case 2:
        {
            CursorTy field_cur6704 = (CursorTy) tmpcur9771;
            CursorTy case4383 = (CursorTy) field_cur6704;
            SymTy tmpval9798 = *(SymTy *) case4383;
            CursorTy tmpcur9799 = case4383 + sizeof(SymTy);
            SymTy x1804 = (SymTy) tmpval9798;
            CursorTy end_x1804 = (CursorTy) tmpcur9799;
            CursorTy jump5448 = case4383 + 8;

            *(TagTyPacked *) loc2667 = 2;

            CursorTy writetag6706 = loc2667 + 1;

            *(SymTy *) writetag6706 = x1804;

            CursorTy writecur6707 = writetag6706 + sizeof(SymTy);
            CursorTy pvrtmp9801 = (CursorTy) writecur6707;
            CursorTy pvrtmp9800 = (CursorTy) loc2667;
            CursorTy taildc5449 = (CursorTy) pvrtmp9800;
            CursorTy end_taildc5449 = (CursorTy) pvrtmp9801;
            CursorTy pvrtmp9803 = (CursorTy) end_taildc5449;
            CursorTy pvrtmp9802 = (CursorTy) taildc5449;
            CursorTy fltPrd7731 = (CursorTy) pvrtmp9802;
            CursorTy fltPrd7732 = (CursorTy) pvrtmp9803;

            return (CursorCursorCursorCursorProd) {end_r2669, jump5448,
                                                   fltPrd7731, fltPrd7732};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10891 = *(CursorTy *) tmpcur9771;
            CursorTy tmpaftercur10892 = tmpcur9771 + 8;
            TagTyPacked tagtmp10893 = *(TagTyPacked *) tmpcur10891;
            CursorTy tailtmp10894 = tmpcur10891 + 1;

            tmpval9770 = tagtmp10893;
            tmpcur9771 = tailtmp10894;
            goto switch9804;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10891 = *(CursorTy *) tmpcur9771;
            CursorTy tmpaftercur10892 = tmpcur9771 + 8;
            TagTyPacked tagtmp10893 = *(TagTyPacked *) tmpcur10891;
            CursorTy tailtmp10894 = tmpcur10891 + 1;

            tmpval9770 = tagtmp10893;
            tmpcur9771 = tailtmp10894;
            goto switch9804;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9770");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Datum(CursorTy end_r2672,
                                                             CursorTy end_r2673,
                                                             CursorTy loc2671,
                                                             CursorTy arg1806)
{
    CursorTy loc2670 = (CursorTy) arg1806;

    if (loc2671 + 18 > end_r2673) {
        ChunkTy new_chunk350 = alloc_chunk(end_r2673);
        CursorTy chunk_start351 = new_chunk350.start_ptr;
        CursorTy chunk_end352 = new_chunk350.end_ptr;

        end_r2673 = chunk_end352;
        *(TagTyPacked *) loc2671 = 255;

        CursorTy redir = loc2671 + 1;

        *(CursorTy *) redir = chunk_start351;
        loc2671 = chunk_start351;
    }

    TagTyPacked tmpval9805 = *(TagTyPacked *) arg1806;
    CursorTy tmpcur9806 = arg1806 + 1;


  switch9813:
    ;
    switch (tmpval9805) {

      case 0:
        {
            CursorTy field_cur6709 = (CursorTy) tmpcur9806;
            CursorTy case4389 = (CursorTy) field_cur6709;
            IntTy tmpval9807 = *(IntTy *) case4389;
            CursorTy tmpcur9808 = case4389 + sizeof(IntTy);
            IntTy x1807 = (IntTy) tmpval9807;
            CursorTy end_x1807 = (CursorTy) tmpcur9808;
            CursorTy jump5450 = case4389 + 8;

            *(TagTyPacked *) loc2671 = 0;

            CursorTy writetag6711 = loc2671 + 1;

            *(IntTy *) writetag6711 = x1807;

            CursorTy writecur6712 = writetag6711 + sizeof(IntTy);
            CursorTy pvrtmp9810 = (CursorTy) writecur6712;
            CursorTy pvrtmp9809 = (CursorTy) loc2671;
            CursorTy taildc5451 = (CursorTy) pvrtmp9809;
            CursorTy end_taildc5451 = (CursorTy) pvrtmp9810;
            CursorTy pvrtmp9812 = (CursorTy) end_taildc5451;
            CursorTy pvrtmp9811 = (CursorTy) taildc5451;
            CursorTy fltPrd7733 = (CursorTy) pvrtmp9811;
            CursorTy fltPrd7734 = (CursorTy) pvrtmp9812;

            return (CursorCursorCursorCursorProd) {end_r2673, jump5450,
                                                   fltPrd7733, fltPrd7734};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10895 = *(CursorTy *) tmpcur9806;
            CursorTy tmpaftercur10896 = tmpcur9806 + 8;
            TagTyPacked tagtmp10897 = *(TagTyPacked *) tmpcur10895;
            CursorTy tailtmp10898 = tmpcur10895 + 1;

            tmpval9805 = tagtmp10897;
            tmpcur9806 = tailtmp10898;
            goto switch9813;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10895 = *(CursorTy *) tmpcur9806;
            CursorTy tmpaftercur10896 = tmpcur9806 + 8;
            TagTyPacked tagtmp10897 = *(TagTyPacked *) tmpcur10895;
            CursorTy tailtmp10898 = tmpcur10895 + 1;

            tmpval9805 = tagtmp10897;
            tmpcur9806 = tailtmp10898;
            goto switch9813;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9805");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LAMBDACASE(CursorTy end_r2676,
                                                                  CursorTy end_r2677,
                                                                  CursorTy loc2675,
                                                                  CursorTy arg1809)
{
    CursorTy loc2674 = (CursorTy) arg1809;

    if (loc2675 + 18 > end_r2677) {
        ChunkTy new_chunk356 = alloc_chunk(end_r2677);
        CursorTy chunk_start357 = new_chunk356.start_ptr;
        CursorTy chunk_end358 = new_chunk356.end_ptr;

        end_r2677 = chunk_end358;
        *(TagTyPacked *) loc2675 = 255;

        CursorTy redir = loc2675 + 1;

        *(CursorTy *) redir = chunk_start357;
        loc2675 = chunk_start357;
    }

    TagTyPacked tmpval9814 = *(TagTyPacked *) arg1809;
    CursorTy tmpcur9815 = arg1809 + 1;


  switch9848:
    ;
    switch (tmpval9814) {

      case 0:
        {
            CursorTy field_cur6714 = (CursorTy) tmpcur9815;
            CursorTy case4395 = (CursorTy) field_cur6714;
            CursorTy x1810 = (CursorTy) case4395;
            CursorTy loc4407 = loc2675 + 1;
            CursorCursorCursorCursorProd tmp_struct353 =
                                          _add_size_and_rel_offsets_Formals(end_r2676, end_r2677, loc4407, x1810);
            CursorTy pvrtmp9816 = tmp_struct353.field0;
            CursorTy pvrtmp9817 = tmp_struct353.field1;
            CursorTy pvrtmp9818 = tmp_struct353.field2;
            CursorTy pvrtmp9819 = tmp_struct353.field3;
            CursorTy fltPrd7735 = (CursorTy) pvrtmp9818;
            CursorTy fltPrd7736 = (CursorTy) pvrtmp9819;
            CursorTy pvrtmp9821 = (CursorTy) fltPrd7736;
            CursorTy pvrtmp9820 = (CursorTy) fltPrd7735;
            CursorTy y1813 = (CursorTy) pvrtmp9820;
            CursorTy fltPrd7737 = (CursorTy) pvrtmp9818;
            CursorTy fltPrd7738 = (CursorTy) pvrtmp9819;
            CursorTy pvrtmp9823 = (CursorTy) fltPrd7738;
            CursorTy pvrtmp9822 = (CursorTy) fltPrd7737;
            CursorTy end_y1813 = (CursorTy) pvrtmp9823;
            CursorTy end_r2677_5612 = (CursorTy) pvrtmp9816;
            CursorTy endof5452 = (CursorTy) pvrtmp9817;
            CursorTy case4396 = (CursorTy) endof5452;
            CursorTy x1811 = (CursorTy) case4396;
            CursorTy loc4408 = (CursorTy) end_y1813;
            CursorCursorCursorCursorProd tmp_struct354 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2676, end_r2677_5612, loc4408, x1811);
            CursorTy pvrtmp9824 = tmp_struct354.field0;
            CursorTy pvrtmp9825 = tmp_struct354.field1;
            CursorTy pvrtmp9826 = tmp_struct354.field2;
            CursorTy pvrtmp9827 = tmp_struct354.field3;
            CursorTy fltPrd7739 = (CursorTy) pvrtmp9826;
            CursorTy fltPrd7740 = (CursorTy) pvrtmp9827;
            CursorTy pvrtmp9829 = (CursorTy) fltPrd7740;
            CursorTy pvrtmp9828 = (CursorTy) fltPrd7739;
            CursorTy y1814 = (CursorTy) pvrtmp9828;
            CursorTy fltPrd7741 = (CursorTy) pvrtmp9826;
            CursorTy fltPrd7742 = (CursorTy) pvrtmp9827;
            CursorTy pvrtmp9831 = (CursorTy) fltPrd7742;
            CursorTy pvrtmp9830 = (CursorTy) fltPrd7741;
            CursorTy end_y1814 = (CursorTy) pvrtmp9831;
            CursorTy end_r2677_5612_5613 = (CursorTy) pvrtmp9824;
            CursorTy endof5453 = (CursorTy) pvrtmp9825;
            CursorTy case4397 = (CursorTy) endof5453;
            CursorTy x1812 = (CursorTy) case4397;
            CursorTy loc4409 = (CursorTy) end_y1814;
            CursorCursorCursorCursorProd tmp_struct355 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r2676, end_r2677_5612_5613, loc4409, x1812);
            CursorTy pvrtmp9832 = tmp_struct355.field0;
            CursorTy pvrtmp9833 = tmp_struct355.field1;
            CursorTy pvrtmp9834 = tmp_struct355.field2;
            CursorTy pvrtmp9835 = tmp_struct355.field3;
            CursorTy fltPrd7743 = (CursorTy) pvrtmp9834;
            CursorTy fltPrd7744 = (CursorTy) pvrtmp9835;
            CursorTy pvrtmp9837 = (CursorTy) fltPrd7744;
            CursorTy pvrtmp9836 = (CursorTy) fltPrd7743;
            CursorTy y1815 = (CursorTy) pvrtmp9836;
            CursorTy fltPrd7745 = (CursorTy) pvrtmp9834;
            CursorTy fltPrd7746 = (CursorTy) pvrtmp9835;
            CursorTy pvrtmp9839 = (CursorTy) fltPrd7746;
            CursorTy pvrtmp9838 = (CursorTy) fltPrd7745;
            CursorTy end_y1815 = (CursorTy) pvrtmp9839;
            CursorTy end_r2677_5612_5613_5614 = (CursorTy) pvrtmp9832;
            CursorTy endof5454 = (CursorTy) pvrtmp9833;

            *(TagTyPacked *) loc2675 = 0;

            CursorTy writetag6718 = loc2675 + 1;
            CursorTy writecur6719 = (CursorTy) end_y1813;
            CursorTy writecur6720 = (CursorTy) end_y1814;
            CursorTy writecur6721 = (CursorTy) end_y1815;
            CursorTy pvrtmp9841 = (CursorTy) writecur6721;
            CursorTy pvrtmp9840 = (CursorTy) loc2675;
            CursorTy taildc5455 = (CursorTy) pvrtmp9840;
            CursorTy end_taildc5455 = (CursorTy) pvrtmp9841;
            CursorTy pvrtmp9843 = (CursorTy) end_taildc5455;
            CursorTy pvrtmp9842 = (CursorTy) taildc5455;
            CursorTy fltPrd7747 = (CursorTy) pvrtmp9842;
            CursorTy fltPrd7748 = (CursorTy) pvrtmp9843;

            return (CursorCursorCursorCursorProd) {end_r2677_5612_5613_5614,
                                                   endof5454, fltPrd7747,
                                                   fltPrd7748};
            break;
        }

      case 1:
        {
            CursorTy field_cur6723 = (CursorTy) tmpcur9815;
            CursorTy jump5456 = loc2674 + 1;

            *(TagTyPacked *) loc2675 = 1;

            CursorTy writetag6724 = loc2675 + 1;
            CursorTy pvrtmp9845 = (CursorTy) writetag6724;
            CursorTy pvrtmp9844 = (CursorTy) loc2675;
            CursorTy taildc5457 = (CursorTy) pvrtmp9844;
            CursorTy end_taildc5457 = (CursorTy) pvrtmp9845;
            CursorTy pvrtmp9847 = (CursorTy) end_taildc5457;
            CursorTy pvrtmp9846 = (CursorTy) taildc5457;
            CursorTy fltPrd7749 = (CursorTy) pvrtmp9846;
            CursorTy fltPrd7750 = (CursorTy) pvrtmp9847;

            return (CursorCursorCursorCursorProd) {end_r2677, jump5456,
                                                   fltPrd7749, fltPrd7750};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10899 = *(CursorTy *) tmpcur9815;
            CursorTy tmpaftercur10900 = tmpcur9815 + 8;
            TagTyPacked tagtmp10901 = *(TagTyPacked *) tmpcur10899;
            CursorTy tailtmp10902 = tmpcur10899 + 1;

            tmpval9814 = tagtmp10901;
            tmpcur9815 = tailtmp10902;
            goto switch9848;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10899 = *(CursorTy *) tmpcur9815;
            CursorTy tmpaftercur10900 = tmpcur9815 + 8;
            TagTyPacked tagtmp10901 = *(TagTyPacked *) tmpcur10899;
            CursorTy tailtmp10902 = tmpcur10899 + 1;

            tmpval9814 = tagtmp10901;
            tmpcur9815 = tailtmp10902;
            goto switch9848;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9814");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LVBIND(CursorTy end_r2680,
                                                              CursorTy end_r2681,
                                                              CursorTy loc2679,
                                                              CursorTy arg1816)
{
    CursorTy loc2678 = (CursorTy) arg1816;

    if (loc2679 + 18 > end_r2681) {
        ChunkTy new_chunk362 = alloc_chunk(end_r2681);
        CursorTy chunk_start363 = new_chunk362.start_ptr;
        CursorTy chunk_end364 = new_chunk362.end_ptr;

        end_r2681 = chunk_end364;
        *(TagTyPacked *) loc2679 = 255;

        CursorTy redir = loc2679 + 1;

        *(CursorTy *) redir = chunk_start363;
        loc2679 = chunk_start363;
    }

    TagTyPacked tmpval9849 = *(TagTyPacked *) arg1816;
    CursorTy tmpcur9850 = arg1816 + 1;


  switch9883:
    ;
    switch (tmpval9849) {

      case 0:
        {
            CursorTy field_cur6726 = (CursorTy) tmpcur9850;
            CursorTy case4416 = (CursorTy) field_cur6726;
            CursorTy x1817 = (CursorTy) case4416;
            CursorTy loc4428 = loc2679 + 1;
            CursorCursorCursorCursorProd tmp_struct359 =
                                          _add_size_and_rel_offsets_ListSym(end_r2680, end_r2681, loc4428, x1817);
            CursorTy pvrtmp9851 = tmp_struct359.field0;
            CursorTy pvrtmp9852 = tmp_struct359.field1;
            CursorTy pvrtmp9853 = tmp_struct359.field2;
            CursorTy pvrtmp9854 = tmp_struct359.field3;
            CursorTy fltPrd7751 = (CursorTy) pvrtmp9853;
            CursorTy fltPrd7752 = (CursorTy) pvrtmp9854;
            CursorTy pvrtmp9856 = (CursorTy) fltPrd7752;
            CursorTy pvrtmp9855 = (CursorTy) fltPrd7751;
            CursorTy y1820 = (CursorTy) pvrtmp9855;
            CursorTy fltPrd7753 = (CursorTy) pvrtmp9853;
            CursorTy fltPrd7754 = (CursorTy) pvrtmp9854;
            CursorTy pvrtmp9858 = (CursorTy) fltPrd7754;
            CursorTy pvrtmp9857 = (CursorTy) fltPrd7753;
            CursorTy end_y1820 = (CursorTy) pvrtmp9858;
            CursorTy end_r2681_5615 = (CursorTy) pvrtmp9851;
            CursorTy endof5458 = (CursorTy) pvrtmp9852;
            CursorTy case4417 = (CursorTy) endof5458;
            CursorTy x1818 = (CursorTy) case4417;
            CursorTy loc4429 = (CursorTy) end_y1820;
            CursorCursorCursorCursorProd tmp_struct360 =
                                          _add_size_and_rel_offsets_Expr(end_r2680, end_r2681_5615, loc4429, x1818);
            CursorTy pvrtmp9859 = tmp_struct360.field0;
            CursorTy pvrtmp9860 = tmp_struct360.field1;
            CursorTy pvrtmp9861 = tmp_struct360.field2;
            CursorTy pvrtmp9862 = tmp_struct360.field3;
            CursorTy fltPrd7755 = (CursorTy) pvrtmp9861;
            CursorTy fltPrd7756 = (CursorTy) pvrtmp9862;
            CursorTy pvrtmp9864 = (CursorTy) fltPrd7756;
            CursorTy pvrtmp9863 = (CursorTy) fltPrd7755;
            CursorTy y1821 = (CursorTy) pvrtmp9863;
            CursorTy fltPrd7757 = (CursorTy) pvrtmp9861;
            CursorTy fltPrd7758 = (CursorTy) pvrtmp9862;
            CursorTy pvrtmp9866 = (CursorTy) fltPrd7758;
            CursorTy pvrtmp9865 = (CursorTy) fltPrd7757;
            CursorTy end_y1821 = (CursorTy) pvrtmp9866;
            CursorTy end_r2681_5615_5616 = (CursorTy) pvrtmp9859;
            CursorTy endof5459 = (CursorTy) pvrtmp9860;
            CursorTy case4418 = (CursorTy) endof5459;
            CursorTy x1819 = (CursorTy) case4418;
            CursorTy loc4430 = (CursorTy) end_y1821;
            CursorCursorCursorCursorProd tmp_struct361 =
                                          _add_size_and_rel_offsets_LVBIND(end_r2680, end_r2681_5615_5616, loc4430, x1819);
            CursorTy pvrtmp9867 = tmp_struct361.field0;
            CursorTy pvrtmp9868 = tmp_struct361.field1;
            CursorTy pvrtmp9869 = tmp_struct361.field2;
            CursorTy pvrtmp9870 = tmp_struct361.field3;
            CursorTy fltPrd7759 = (CursorTy) pvrtmp9869;
            CursorTy fltPrd7760 = (CursorTy) pvrtmp9870;
            CursorTy pvrtmp9872 = (CursorTy) fltPrd7760;
            CursorTy pvrtmp9871 = (CursorTy) fltPrd7759;
            CursorTy y1822 = (CursorTy) pvrtmp9871;
            CursorTy fltPrd7761 = (CursorTy) pvrtmp9869;
            CursorTy fltPrd7762 = (CursorTy) pvrtmp9870;
            CursorTy pvrtmp9874 = (CursorTy) fltPrd7762;
            CursorTy pvrtmp9873 = (CursorTy) fltPrd7761;
            CursorTy end_y1822 = (CursorTy) pvrtmp9874;
            CursorTy end_r2681_5615_5616_5617 = (CursorTy) pvrtmp9867;
            CursorTy endof5460 = (CursorTy) pvrtmp9868;

            *(TagTyPacked *) loc2679 = 0;

            CursorTy writetag6730 = loc2679 + 1;
            CursorTy writecur6731 = (CursorTy) end_y1820;
            CursorTy writecur6732 = (CursorTy) end_y1821;
            CursorTy writecur6733 = (CursorTy) end_y1822;
            CursorTy pvrtmp9876 = (CursorTy) writecur6733;
            CursorTy pvrtmp9875 = (CursorTy) loc2679;
            CursorTy taildc5461 = (CursorTy) pvrtmp9875;
            CursorTy end_taildc5461 = (CursorTy) pvrtmp9876;
            CursorTy pvrtmp9878 = (CursorTy) end_taildc5461;
            CursorTy pvrtmp9877 = (CursorTy) taildc5461;
            CursorTy fltPrd7763 = (CursorTy) pvrtmp9877;
            CursorTy fltPrd7764 = (CursorTy) pvrtmp9878;

            return (CursorCursorCursorCursorProd) {end_r2681_5615_5616_5617,
                                                   endof5460, fltPrd7763,
                                                   fltPrd7764};
            break;
        }

      case 1:
        {
            CursorTy field_cur6735 = (CursorTy) tmpcur9850;
            CursorTy jump5462 = loc2678 + 1;

            *(TagTyPacked *) loc2679 = 1;

            CursorTy writetag6736 = loc2679 + 1;
            CursorTy pvrtmp9880 = (CursorTy) writetag6736;
            CursorTy pvrtmp9879 = (CursorTy) loc2679;
            CursorTy taildc5463 = (CursorTy) pvrtmp9879;
            CursorTy end_taildc5463 = (CursorTy) pvrtmp9880;
            CursorTy pvrtmp9882 = (CursorTy) end_taildc5463;
            CursorTy pvrtmp9881 = (CursorTy) taildc5463;
            CursorTy fltPrd7765 = (CursorTy) pvrtmp9881;
            CursorTy fltPrd7766 = (CursorTy) pvrtmp9882;

            return (CursorCursorCursorCursorProd) {end_r2681, jump5462,
                                                   fltPrd7765, fltPrd7766};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10903 = *(CursorTy *) tmpcur9850;
            CursorTy tmpaftercur10904 = tmpcur9850 + 8;
            TagTyPacked tagtmp10905 = *(TagTyPacked *) tmpcur10903;
            CursorTy tailtmp10906 = tmpcur10903 + 1;

            tmpval9849 = tagtmp10905;
            tmpcur9850 = tailtmp10906;
            goto switch9883;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10903 = *(CursorTy *) tmpcur9850;
            CursorTy tmpaftercur10904 = tmpcur9850 + 8;
            TagTyPacked tagtmp10905 = *(TagTyPacked *) tmpcur10903;
            CursorTy tailtmp10906 = tmpcur10903 + 1;

            tmpval9849 = tagtmp10905;
            tmpcur9850 = tailtmp10906;
            goto switch9883;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9849");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Expr(CursorTy end_r2684,
                                                            CursorTy end_r2685,
                                                            CursorTy loc2683,
                                                            CursorTy arg1823)
{
    CursorTy loc2682 = (CursorTy) arg1823;

    if (loc2683 + 34 > end_r2685) {
        ChunkTy new_chunk387 = alloc_chunk(end_r2685);
        CursorTy chunk_start388 = new_chunk387.start_ptr;
        CursorTy chunk_end389 = new_chunk387.end_ptr;

        end_r2685 = chunk_end389;
        *(TagTyPacked *) loc2683 = 255;

        CursorTy redir = loc2683 + 1;

        *(CursorTy *) redir = chunk_start388;
        loc2683 = chunk_start388;
    }

    CursorTy loc4449 = loc2683 + 1;
    CursorTy loc4450 = loc4449 + 8;
    CursorTy loc4451 = loc4450 + 8;
    CursorTy loc4477 = loc2683 + 1;
    CursorTy loc4478 = loc4477 + 8;
    CursorTy loc4479 = loc4478 + 8;
    CursorTy loc4480 = loc4479 + 8;
    CursorTy loc4506 = loc2683 + 1;
    CursorTy loc4507 = loc4506 + 8;
    CursorTy loc4508 = loc4507 + 8;
    CursorTy loc4524 = loc2683 + 1;
    CursorTy loc4525 = loc4524 + 8;
    CursorTy loc4526 = loc4525 + 8;
    CursorTy loc4542 = loc2683 + 1;
    CursorTy loc4543 = loc4542 + 8;
    CursorTy loc4544 = loc4543 + 8;
    CursorTy loc4557 = loc2683 + 1;
    CursorTy loc4558 = loc4557 + 8;
    CursorTy loc4592 = loc2683 + 1;
    CursorTy loc4593 = loc4592 + 8;
    CursorTy loc4594 = loc4593 + 8;
    CursorTy loc4595 = loc4594 + 8;
    CursorTy loc4615 = loc2683 + 1;
    CursorTy loc4616 = loc4615 + 8;
    CursorTy loc4617 = loc4616 + 8;
    TagTyPacked tmpval9884 = *(TagTyPacked *) arg1823;
    CursorTy tmpcur9885 = arg1823 + 1;


  switch10144:
    ;
    switch (tmpval9884) {

      case 0:
        {
            CursorTy field_cur6738 = (CursorTy) tmpcur9885;
            CursorTy case4437 = (CursorTy) field_cur6738;
            SymTy tmpval9886 = *(SymTy *) case4437;
            CursorTy tmpcur9887 = case4437 + sizeof(SymTy);
            SymTy x1824 = (SymTy) tmpval9886;
            CursorTy end_x1824 = (CursorTy) tmpcur9887;
            CursorTy jump5464 = case4437 + 8;

            *(TagTyPacked *) loc2683 = 0;

            CursorTy writetag6740 = loc2683 + 1;

            *(SymTy *) writetag6740 = x1824;

            CursorTy writecur6741 = writetag6740 + sizeof(SymTy);
            CursorTy pvrtmp9889 = (CursorTy) writecur6741;
            CursorTy pvrtmp9888 = (CursorTy) loc2683;
            CursorTy taildc5465 = (CursorTy) pvrtmp9888;
            CursorTy end_taildc5465 = (CursorTy) pvrtmp9889;
            CursorTy pvrtmp9891 = (CursorTy) end_taildc5465;
            CursorTy pvrtmp9890 = (CursorTy) taildc5465;
            CursorTy fltPrd7767 = (CursorTy) pvrtmp9890;
            CursorTy fltPrd7768 = (CursorTy) pvrtmp9891;

            return (CursorCursorCursorCursorProd) {end_r2685, jump5464,
                                                   fltPrd7767, fltPrd7768};
            break;
        }

      case 1:
        {
            CursorTy field_cur6743 = (CursorTy) tmpcur9885;
            CursorTy case4441 = (CursorTy) field_cur6743;
            CursorTy x1826 = (CursorTy) case4441;
            CursorCursorCursorCursorProd tmp_struct365 =
                                          _add_size_and_rel_offsets_Formals(end_r2684, end_r2685, loc4451, x1826);
            CursorTy pvrtmp9892 = tmp_struct365.field0;
            CursorTy pvrtmp9893 = tmp_struct365.field1;
            CursorTy pvrtmp9894 = tmp_struct365.field2;
            CursorTy pvrtmp9895 = tmp_struct365.field3;
            CursorTy fltPrd7769 = (CursorTy) pvrtmp9894;
            CursorTy fltPrd7770 = (CursorTy) pvrtmp9895;
            CursorTy pvrtmp9897 = (CursorTy) fltPrd7770;
            CursorTy pvrtmp9896 = (CursorTy) fltPrd7769;
            CursorTy y1828 = (CursorTy) pvrtmp9896;
            CursorTy fltPrd7771 = (CursorTy) pvrtmp9894;
            CursorTy fltPrd7772 = (CursorTy) pvrtmp9895;
            CursorTy pvrtmp9899 = (CursorTy) fltPrd7772;
            CursorTy pvrtmp9898 = (CursorTy) fltPrd7771;
            CursorTy end_y1828 = (CursorTy) pvrtmp9899;
            CursorTy end_r2685_5618 = (CursorTy) pvrtmp9892;
            CursorTy endof5466 = (CursorTy) pvrtmp9893;
            CursorTy case4442 = (CursorTy) endof5466;
            CursorTy x1827 = (CursorTy) case4442;
            CursorTy loc4452 = (CursorTy) end_y1828;
            CursorCursorCursorCursorProd tmp_struct366 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2684, end_r2685_5618, loc4452, x1827);
            CursorTy pvrtmp9900 = tmp_struct366.field0;
            CursorTy pvrtmp9901 = tmp_struct366.field1;
            CursorTy pvrtmp9902 = tmp_struct366.field2;
            CursorTy pvrtmp9903 = tmp_struct366.field3;
            CursorTy fltPrd7773 = (CursorTy) pvrtmp9902;
            CursorTy fltPrd7774 = (CursorTy) pvrtmp9903;
            CursorTy pvrtmp9905 = (CursorTy) fltPrd7774;
            CursorTy pvrtmp9904 = (CursorTy) fltPrd7773;
            CursorTy y1829 = (CursorTy) pvrtmp9904;
            CursorTy fltPrd7775 = (CursorTy) pvrtmp9902;
            CursorTy fltPrd7776 = (CursorTy) pvrtmp9903;
            CursorTy pvrtmp9907 = (CursorTy) fltPrd7776;
            CursorTy pvrtmp9906 = (CursorTy) fltPrd7775;
            CursorTy end_y1829 = (CursorTy) pvrtmp9907;
            CursorTy end_r2685_5618_5619 = (CursorTy) pvrtmp9900;
            CursorTy endof5467 = (CursorTy) pvrtmp9901;
            IntTy sizeof_y1828_1830 = end_y1828 - y1828;
            IntTy sizeof_y1829_1831 = end_y1829 - y1829;
            IntTy fltPrm2463 = sizeof_y1828_1830 + 0;
            IntTy offset_1832 = 0 + fltPrm2463;
            IntTy fltPrm2464 = sizeof_y1828_1830 + sizeof_y1829_1831;
            IntTy size_dcon1833 = 9 + fltPrm2464;

            *(TagTyPacked *) loc2683 = 169;

            CursorTy writetag6746 = loc2683 + 1;

            *(IntTy *) writetag6746 = size_dcon1833;

            CursorTy writecur6747 = writetag6746 + sizeof(IntTy);

            *(IntTy *) writecur6747 = offset_1832;

            CursorTy writecur6748 = writecur6747 + sizeof(IntTy);
            CursorTy writecur6749 = (CursorTy) end_y1828;
            CursorTy writecur6750 = (CursorTy) end_y1829;
            CursorTy pvrtmp9909 = (CursorTy) writecur6750;
            CursorTy pvrtmp9908 = (CursorTy) loc2683;
            CursorTy taildc5468 = (CursorTy) pvrtmp9908;
            CursorTy end_taildc5468 = (CursorTy) pvrtmp9909;
            CursorTy pvrtmp9911 = (CursorTy) end_taildc5468;
            CursorTy pvrtmp9910 = (CursorTy) taildc5468;
            CursorTy fltPrd7777 = (CursorTy) pvrtmp9910;
            CursorTy fltPrd7778 = (CursorTy) pvrtmp9911;

            return (CursorCursorCursorCursorProd) {end_r2685_5618_5619,
                                                   endof5467, fltPrd7777,
                                                   fltPrd7778};
            break;
        }

      case 2:
        {
            CursorTy field_cur6752 = (CursorTy) tmpcur9885;
            CursorTy case4459 = (CursorTy) field_cur6752;
            CursorTy x1834 = (CursorTy) case4459;
            CursorTy loc4463 = loc2683 + 1;
            CursorCursorCursorCursorProd tmp_struct367 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r2684, end_r2685, loc4463, x1834);
            CursorTy pvrtmp9912 = tmp_struct367.field0;
            CursorTy pvrtmp9913 = tmp_struct367.field1;
            CursorTy pvrtmp9914 = tmp_struct367.field2;
            CursorTy pvrtmp9915 = tmp_struct367.field3;
            CursorTy fltPrd7779 = (CursorTy) pvrtmp9914;
            CursorTy fltPrd7780 = (CursorTy) pvrtmp9915;
            CursorTy pvrtmp9917 = (CursorTy) fltPrd7780;
            CursorTy pvrtmp9916 = (CursorTy) fltPrd7779;
            CursorTy y1835 = (CursorTy) pvrtmp9916;
            CursorTy fltPrd7781 = (CursorTy) pvrtmp9914;
            CursorTy fltPrd7782 = (CursorTy) pvrtmp9915;
            CursorTy pvrtmp9919 = (CursorTy) fltPrd7782;
            CursorTy pvrtmp9918 = (CursorTy) fltPrd7781;
            CursorTy end_y1835 = (CursorTy) pvrtmp9919;
            CursorTy end_r2685_5620 = (CursorTy) pvrtmp9912;
            CursorTy endof5469 = (CursorTy) pvrtmp9913;

            *(TagTyPacked *) loc2683 = 2;

            CursorTy writetag6754 = loc2683 + 1;
            CursorTy writecur6755 = (CursorTy) end_y1835;
            CursorTy pvrtmp9921 = (CursorTy) writecur6755;
            CursorTy pvrtmp9920 = (CursorTy) loc2683;
            CursorTy taildc5470 = (CursorTy) pvrtmp9920;
            CursorTy end_taildc5470 = (CursorTy) pvrtmp9921;
            CursorTy pvrtmp9923 = (CursorTy) end_taildc5470;
            CursorTy pvrtmp9922 = (CursorTy) taildc5470;
            CursorTy fltPrd7783 = (CursorTy) pvrtmp9922;
            CursorTy fltPrd7784 = (CursorTy) pvrtmp9923;

            return (CursorCursorCursorCursorProd) {end_r2685_5620, endof5469,
                                                   fltPrd7783, fltPrd7784};
            break;
        }

      case 3:
        {
            CursorTy field_cur6757 = (CursorTy) tmpcur9885;
            CursorTy case4465 = (CursorTy) field_cur6757;
            CursorTy x1836 = (CursorTy) case4465;
            CursorCursorCursorCursorProd tmp_struct368 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685, loc4480, x1836);
            CursorTy pvrtmp9924 = tmp_struct368.field0;
            CursorTy pvrtmp9925 = tmp_struct368.field1;
            CursorTy pvrtmp9926 = tmp_struct368.field2;
            CursorTy pvrtmp9927 = tmp_struct368.field3;
            CursorTy fltPrd7785 = (CursorTy) pvrtmp9926;
            CursorTy fltPrd7786 = (CursorTy) pvrtmp9927;
            CursorTy pvrtmp9929 = (CursorTy) fltPrd7786;
            CursorTy pvrtmp9928 = (CursorTy) fltPrd7785;
            CursorTy y1839 = (CursorTy) pvrtmp9928;
            CursorTy fltPrd7787 = (CursorTy) pvrtmp9926;
            CursorTy fltPrd7788 = (CursorTy) pvrtmp9927;
            CursorTy pvrtmp9931 = (CursorTy) fltPrd7788;
            CursorTy pvrtmp9930 = (CursorTy) fltPrd7787;
            CursorTy end_y1839 = (CursorTy) pvrtmp9931;
            CursorTy end_r2685_5621 = (CursorTy) pvrtmp9924;
            CursorTy endof5471 = (CursorTy) pvrtmp9925;
            CursorTy case4466 = (CursorTy) endof5471;
            CursorTy x1837 = (CursorTy) case4466;
            CursorTy loc4481 = (CursorTy) end_y1839;
            CursorCursorCursorCursorProd tmp_struct369 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685_5621, loc4481, x1837);
            CursorTy pvrtmp9932 = tmp_struct369.field0;
            CursorTy pvrtmp9933 = tmp_struct369.field1;
            CursorTy pvrtmp9934 = tmp_struct369.field2;
            CursorTy pvrtmp9935 = tmp_struct369.field3;
            CursorTy fltPrd7789 = (CursorTy) pvrtmp9934;
            CursorTy fltPrd7790 = (CursorTy) pvrtmp9935;
            CursorTy pvrtmp9937 = (CursorTy) fltPrd7790;
            CursorTy pvrtmp9936 = (CursorTy) fltPrd7789;
            CursorTy y1840 = (CursorTy) pvrtmp9936;
            CursorTy fltPrd7791 = (CursorTy) pvrtmp9934;
            CursorTy fltPrd7792 = (CursorTy) pvrtmp9935;
            CursorTy pvrtmp9939 = (CursorTy) fltPrd7792;
            CursorTy pvrtmp9938 = (CursorTy) fltPrd7791;
            CursorTy end_y1840 = (CursorTy) pvrtmp9939;
            CursorTy end_r2685_5621_5622 = (CursorTy) pvrtmp9932;
            CursorTy endof5472 = (CursorTy) pvrtmp9933;
            CursorTy case4467 = (CursorTy) endof5472;
            CursorTy x1838 = (CursorTy) case4467;
            CursorTy loc4482 = (CursorTy) end_y1840;
            CursorCursorCursorCursorProd tmp_struct370 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685_5621_5622, loc4482, x1838);
            CursorTy pvrtmp9940 = tmp_struct370.field0;
            CursorTy pvrtmp9941 = tmp_struct370.field1;
            CursorTy pvrtmp9942 = tmp_struct370.field2;
            CursorTy pvrtmp9943 = tmp_struct370.field3;
            CursorTy fltPrd7793 = (CursorTy) pvrtmp9942;
            CursorTy fltPrd7794 = (CursorTy) pvrtmp9943;
            CursorTy pvrtmp9945 = (CursorTy) fltPrd7794;
            CursorTy pvrtmp9944 = (CursorTy) fltPrd7793;
            CursorTy y1841 = (CursorTy) pvrtmp9944;
            CursorTy fltPrd7795 = (CursorTy) pvrtmp9942;
            CursorTy fltPrd7796 = (CursorTy) pvrtmp9943;
            CursorTy pvrtmp9947 = (CursorTy) fltPrd7796;
            CursorTy pvrtmp9946 = (CursorTy) fltPrd7795;
            CursorTy end_y1841 = (CursorTy) pvrtmp9947;
            CursorTy end_r2685_5621_5622_5623 = (CursorTy) pvrtmp9940;
            CursorTy endof5473 = (CursorTy) pvrtmp9941;
            IntTy sizeof_y1839_1842 = end_y1839 - y1839;
            IntTy sizeof_y1840_1843 = end_y1840 - y1840;
            IntTy sizeof_y1841_1844 = end_y1841 - y1841;
            IntTy fltPrm2465 = sizeof_y1839_1842 + 0;
            IntTy offset_1845 = 8 + fltPrm2465;
            IntTy fltPrm2466 = sizeof_y1839_1842 + sizeof_y1840_1843;
            IntTy offset_1846 = 0 + fltPrm2466;
            IntTy fltPrm2468 = sizeof_y1840_1843 + sizeof_y1841_1844;
            IntTy fltPrm2467 = sizeof_y1839_1842 + fltPrm2468;
            IntTy size_dcon1847 = 17 + fltPrm2467;

            *(TagTyPacked *) loc2683 = 171;

            CursorTy writetag6761 = loc2683 + 1;

            *(IntTy *) writetag6761 = size_dcon1847;

            CursorTy writecur6762 = writetag6761 + sizeof(IntTy);

            *(IntTy *) writecur6762 = offset_1845;

            CursorTy writecur6763 = writecur6762 + sizeof(IntTy);

            *(IntTy *) writecur6763 = offset_1846;

            CursorTy writecur6764 = writecur6763 + sizeof(IntTy);
            CursorTy writecur6765 = (CursorTy) end_y1839;
            CursorTy writecur6766 = (CursorTy) end_y1840;
            CursorTy writecur6767 = (CursorTy) end_y1841;
            CursorTy pvrtmp9949 = (CursorTy) writecur6767;
            CursorTy pvrtmp9948 = (CursorTy) loc2683;
            CursorTy taildc5474 = (CursorTy) pvrtmp9948;
            CursorTy end_taildc5474 = (CursorTy) pvrtmp9949;
            CursorTy pvrtmp9951 = (CursorTy) end_taildc5474;
            CursorTy pvrtmp9950 = (CursorTy) taildc5474;
            CursorTy fltPrd7797 = (CursorTy) pvrtmp9950;
            CursorTy fltPrd7798 = (CursorTy) pvrtmp9951;

            return (CursorCursorCursorCursorProd) {end_r2685_5621_5622_5623,
                                                   endof5473, fltPrd7797,
                                                   fltPrd7798};
            break;
        }

      case 4:
        {
            CursorTy field_cur6769 = (CursorTy) tmpcur9885;
            CursorTy case4492 = (CursorTy) field_cur6769;
            CursorTy x1848 = (CursorTy) case4492;
            CursorTy loc4496 = loc2683 + 1;
            CursorCursorCursorCursorProd tmp_struct371 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2684, end_r2685, loc4496, x1848);
            CursorTy pvrtmp9952 = tmp_struct371.field0;
            CursorTy pvrtmp9953 = tmp_struct371.field1;
            CursorTy pvrtmp9954 = tmp_struct371.field2;
            CursorTy pvrtmp9955 = tmp_struct371.field3;
            CursorTy fltPrd7799 = (CursorTy) pvrtmp9954;
            CursorTy fltPrd7800 = (CursorTy) pvrtmp9955;
            CursorTy pvrtmp9957 = (CursorTy) fltPrd7800;
            CursorTy pvrtmp9956 = (CursorTy) fltPrd7799;
            CursorTy y1849 = (CursorTy) pvrtmp9956;
            CursorTy fltPrd7801 = (CursorTy) pvrtmp9954;
            CursorTy fltPrd7802 = (CursorTy) pvrtmp9955;
            CursorTy pvrtmp9959 = (CursorTy) fltPrd7802;
            CursorTy pvrtmp9958 = (CursorTy) fltPrd7801;
            CursorTy end_y1849 = (CursorTy) pvrtmp9959;
            CursorTy end_r2685_5624 = (CursorTy) pvrtmp9952;
            CursorTy endof5475 = (CursorTy) pvrtmp9953;

            *(TagTyPacked *) loc2683 = 4;

            CursorTy writetag6771 = loc2683 + 1;
            CursorTy writecur6772 = (CursorTy) end_y1849;
            CursorTy pvrtmp9961 = (CursorTy) writecur6772;
            CursorTy pvrtmp9960 = (CursorTy) loc2683;
            CursorTy taildc5476 = (CursorTy) pvrtmp9960;
            CursorTy end_taildc5476 = (CursorTy) pvrtmp9961;
            CursorTy pvrtmp9963 = (CursorTy) end_taildc5476;
            CursorTy pvrtmp9962 = (CursorTy) taildc5476;
            CursorTy fltPrd7803 = (CursorTy) pvrtmp9962;
            CursorTy fltPrd7804 = (CursorTy) pvrtmp9963;

            return (CursorCursorCursorCursorProd) {end_r2685_5624, endof5475,
                                                   fltPrd7803, fltPrd7804};
            break;
        }

      case 5:
        {
            CursorTy field_cur6774 = (CursorTy) tmpcur9885;
            CursorTy case4498 = (CursorTy) field_cur6774;
            CursorTy x1850 = (CursorTy) case4498;
            CursorCursorCursorCursorProd tmp_struct372 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685, loc4508, x1850);
            CursorTy pvrtmp9964 = tmp_struct372.field0;
            CursorTy pvrtmp9965 = tmp_struct372.field1;
            CursorTy pvrtmp9966 = tmp_struct372.field2;
            CursorTy pvrtmp9967 = tmp_struct372.field3;
            CursorTy fltPrd7805 = (CursorTy) pvrtmp9966;
            CursorTy fltPrd7806 = (CursorTy) pvrtmp9967;
            CursorTy pvrtmp9969 = (CursorTy) fltPrd7806;
            CursorTy pvrtmp9968 = (CursorTy) fltPrd7805;
            CursorTy y1852 = (CursorTy) pvrtmp9968;
            CursorTy fltPrd7807 = (CursorTy) pvrtmp9966;
            CursorTy fltPrd7808 = (CursorTy) pvrtmp9967;
            CursorTy pvrtmp9971 = (CursorTy) fltPrd7808;
            CursorTy pvrtmp9970 = (CursorTy) fltPrd7807;
            CursorTy end_y1852 = (CursorTy) pvrtmp9971;
            CursorTy end_r2685_5625 = (CursorTy) pvrtmp9964;
            CursorTy endof5477 = (CursorTy) pvrtmp9965;
            CursorTy case4499 = (CursorTy) endof5477;
            CursorTy x1851 = (CursorTy) case4499;
            CursorTy loc4509 = (CursorTy) end_y1852;
            CursorCursorCursorCursorProd tmp_struct373 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2684, end_r2685_5625, loc4509, x1851);
            CursorTy pvrtmp9972 = tmp_struct373.field0;
            CursorTy pvrtmp9973 = tmp_struct373.field1;
            CursorTy pvrtmp9974 = tmp_struct373.field2;
            CursorTy pvrtmp9975 = tmp_struct373.field3;
            CursorTy fltPrd7809 = (CursorTy) pvrtmp9974;
            CursorTy fltPrd7810 = (CursorTy) pvrtmp9975;
            CursorTy pvrtmp9977 = (CursorTy) fltPrd7810;
            CursorTy pvrtmp9976 = (CursorTy) fltPrd7809;
            CursorTy y1853 = (CursorTy) pvrtmp9976;
            CursorTy fltPrd7811 = (CursorTy) pvrtmp9974;
            CursorTy fltPrd7812 = (CursorTy) pvrtmp9975;
            CursorTy pvrtmp9979 = (CursorTy) fltPrd7812;
            CursorTy pvrtmp9978 = (CursorTy) fltPrd7811;
            CursorTy end_y1853 = (CursorTy) pvrtmp9979;
            CursorTy end_r2685_5625_5626 = (CursorTy) pvrtmp9972;
            CursorTy endof5478 = (CursorTy) pvrtmp9973;
            IntTy sizeof_y1852_1854 = end_y1852 - y1852;
            IntTy sizeof_y1853_1855 = end_y1853 - y1853;
            IntTy fltPrm2469 = sizeof_y1852_1854 + 0;
            IntTy offset_1856 = 0 + fltPrm2469;
            IntTy fltPrm2470 = sizeof_y1852_1854 + sizeof_y1853_1855;
            IntTy size_dcon1857 = 9 + fltPrm2470;

            *(TagTyPacked *) loc2683 = 173;

            CursorTy writetag6777 = loc2683 + 1;

            *(IntTy *) writetag6777 = size_dcon1857;

            CursorTy writecur6778 = writetag6777 + sizeof(IntTy);

            *(IntTy *) writecur6778 = offset_1856;

            CursorTy writecur6779 = writecur6778 + sizeof(IntTy);
            CursorTy writecur6780 = (CursorTy) end_y1852;
            CursorTy writecur6781 = (CursorTy) end_y1853;
            CursorTy pvrtmp9981 = (CursorTy) writecur6781;
            CursorTy pvrtmp9980 = (CursorTy) loc2683;
            CursorTy taildc5479 = (CursorTy) pvrtmp9980;
            CursorTy end_taildc5479 = (CursorTy) pvrtmp9981;
            CursorTy pvrtmp9983 = (CursorTy) end_taildc5479;
            CursorTy pvrtmp9982 = (CursorTy) taildc5479;
            CursorTy fltPrd7813 = (CursorTy) pvrtmp9982;
            CursorTy fltPrd7814 = (CursorTy) pvrtmp9983;

            return (CursorCursorCursorCursorProd) {end_r2685_5625_5626,
                                                   endof5478, fltPrd7813,
                                                   fltPrd7814};
            break;
        }

      case 6:
        {
            CursorTy field_cur6783 = (CursorTy) tmpcur9885;
            CursorTy case4516 = (CursorTy) field_cur6783;
            CursorTy x1858 = (CursorTy) case4516;
            CursorCursorCursorCursorProd tmp_struct374 =
                                          _add_size_and_rel_offsets_LVBIND(end_r2684, end_r2685, loc4526, x1858);
            CursorTy pvrtmp9984 = tmp_struct374.field0;
            CursorTy pvrtmp9985 = tmp_struct374.field1;
            CursorTy pvrtmp9986 = tmp_struct374.field2;
            CursorTy pvrtmp9987 = tmp_struct374.field3;
            CursorTy fltPrd7815 = (CursorTy) pvrtmp9986;
            CursorTy fltPrd7816 = (CursorTy) pvrtmp9987;
            CursorTy pvrtmp9989 = (CursorTy) fltPrd7816;
            CursorTy pvrtmp9988 = (CursorTy) fltPrd7815;
            CursorTy y1860 = (CursorTy) pvrtmp9988;
            CursorTy fltPrd7817 = (CursorTy) pvrtmp9986;
            CursorTy fltPrd7818 = (CursorTy) pvrtmp9987;
            CursorTy pvrtmp9991 = (CursorTy) fltPrd7818;
            CursorTy pvrtmp9990 = (CursorTy) fltPrd7817;
            CursorTy end_y1860 = (CursorTy) pvrtmp9991;
            CursorTy end_r2685_5627 = (CursorTy) pvrtmp9984;
            CursorTy endof5480 = (CursorTy) pvrtmp9985;
            CursorTy case4517 = (CursorTy) endof5480;
            CursorTy x1859 = (CursorTy) case4517;
            CursorTy loc4527 = (CursorTy) end_y1860;
            CursorCursorCursorCursorProd tmp_struct375 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2684, end_r2685_5627, loc4527, x1859);
            CursorTy pvrtmp9992 = tmp_struct375.field0;
            CursorTy pvrtmp9993 = tmp_struct375.field1;
            CursorTy pvrtmp9994 = tmp_struct375.field2;
            CursorTy pvrtmp9995 = tmp_struct375.field3;
            CursorTy fltPrd7819 = (CursorTy) pvrtmp9994;
            CursorTy fltPrd7820 = (CursorTy) pvrtmp9995;
            CursorTy pvrtmp9997 = (CursorTy) fltPrd7820;
            CursorTy pvrtmp9996 = (CursorTy) fltPrd7819;
            CursorTy y1861 = (CursorTy) pvrtmp9996;
            CursorTy fltPrd7821 = (CursorTy) pvrtmp9994;
            CursorTy fltPrd7822 = (CursorTy) pvrtmp9995;
            CursorTy pvrtmp9999 = (CursorTy) fltPrd7822;
            CursorTy pvrtmp9998 = (CursorTy) fltPrd7821;
            CursorTy end_y1861 = (CursorTy) pvrtmp9999;
            CursorTy end_r2685_5627_5628 = (CursorTy) pvrtmp9992;
            CursorTy endof5481 = (CursorTy) pvrtmp9993;
            IntTy sizeof_y1860_1862 = end_y1860 - y1860;
            IntTy sizeof_y1861_1863 = end_y1861 - y1861;
            IntTy fltPrm2471 = sizeof_y1860_1862 + 0;
            IntTy offset_1864 = 0 + fltPrm2471;
            IntTy fltPrm2472 = sizeof_y1860_1862 + sizeof_y1861_1863;
            IntTy size_dcon1865 = 9 + fltPrm2472;

            *(TagTyPacked *) loc2683 = 175;

            CursorTy writetag6786 = loc2683 + 1;

            *(IntTy *) writetag6786 = size_dcon1865;

            CursorTy writecur6787 = writetag6786 + sizeof(IntTy);

            *(IntTy *) writecur6787 = offset_1864;

            CursorTy writecur6788 = writecur6787 + sizeof(IntTy);
            CursorTy writecur6789 = (CursorTy) end_y1860;
            CursorTy writecur6790 = (CursorTy) end_y1861;
            CursorTy pvrtmp10001 = (CursorTy) writecur6790;
            CursorTy pvrtmp10000 = (CursorTy) loc2683;
            CursorTy taildc5482 = (CursorTy) pvrtmp10000;
            CursorTy end_taildc5482 = (CursorTy) pvrtmp10001;
            CursorTy pvrtmp10003 = (CursorTy) end_taildc5482;
            CursorTy pvrtmp10002 = (CursorTy) taildc5482;
            CursorTy fltPrd7823 = (CursorTy) pvrtmp10002;
            CursorTy fltPrd7824 = (CursorTy) pvrtmp10003;

            return (CursorCursorCursorCursorProd) {end_r2685_5627_5628,
                                                   endof5481, fltPrd7823,
                                                   fltPrd7824};
            break;
        }

      case 7:
        {
            CursorTy field_cur6792 = (CursorTy) tmpcur9885;
            CursorTy case4534 = (CursorTy) field_cur6792;
            CursorTy x1866 = (CursorTy) case4534;
            CursorCursorCursorCursorProd tmp_struct376 =
                                          _add_size_and_rel_offsets_LVBIND(end_r2684, end_r2685, loc4544, x1866);
            CursorTy pvrtmp10004 = tmp_struct376.field0;
            CursorTy pvrtmp10005 = tmp_struct376.field1;
            CursorTy pvrtmp10006 = tmp_struct376.field2;
            CursorTy pvrtmp10007 = tmp_struct376.field3;
            CursorTy fltPrd7825 = (CursorTy) pvrtmp10006;
            CursorTy fltPrd7826 = (CursorTy) pvrtmp10007;
            CursorTy pvrtmp10009 = (CursorTy) fltPrd7826;
            CursorTy pvrtmp10008 = (CursorTy) fltPrd7825;
            CursorTy y1868 = (CursorTy) pvrtmp10008;
            CursorTy fltPrd7827 = (CursorTy) pvrtmp10006;
            CursorTy fltPrd7828 = (CursorTy) pvrtmp10007;
            CursorTy pvrtmp10011 = (CursorTy) fltPrd7828;
            CursorTy pvrtmp10010 = (CursorTy) fltPrd7827;
            CursorTy end_y1868 = (CursorTy) pvrtmp10011;
            CursorTy end_r2685_5629 = (CursorTy) pvrtmp10004;
            CursorTy endof5483 = (CursorTy) pvrtmp10005;
            CursorTy case4535 = (CursorTy) endof5483;
            CursorTy x1867 = (CursorTy) case4535;
            CursorTy loc4545 = (CursorTy) end_y1868;
            CursorCursorCursorCursorProd tmp_struct377 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2684, end_r2685_5629, loc4545, x1867);
            CursorTy pvrtmp10012 = tmp_struct377.field0;
            CursorTy pvrtmp10013 = tmp_struct377.field1;
            CursorTy pvrtmp10014 = tmp_struct377.field2;
            CursorTy pvrtmp10015 = tmp_struct377.field3;
            CursorTy fltPrd7829 = (CursorTy) pvrtmp10014;
            CursorTy fltPrd7830 = (CursorTy) pvrtmp10015;
            CursorTy pvrtmp10017 = (CursorTy) fltPrd7830;
            CursorTy pvrtmp10016 = (CursorTy) fltPrd7829;
            CursorTy y1869 = (CursorTy) pvrtmp10016;
            CursorTy fltPrd7831 = (CursorTy) pvrtmp10014;
            CursorTy fltPrd7832 = (CursorTy) pvrtmp10015;
            CursorTy pvrtmp10019 = (CursorTy) fltPrd7832;
            CursorTy pvrtmp10018 = (CursorTy) fltPrd7831;
            CursorTy end_y1869 = (CursorTy) pvrtmp10019;
            CursorTy end_r2685_5629_5630 = (CursorTy) pvrtmp10012;
            CursorTy endof5484 = (CursorTy) pvrtmp10013;
            IntTy sizeof_y1868_1870 = end_y1868 - y1868;
            IntTy sizeof_y1869_1871 = end_y1869 - y1869;
            IntTy fltPrm2473 = sizeof_y1868_1870 + 0;
            IntTy offset_1872 = 0 + fltPrm2473;
            IntTy fltPrm2474 = sizeof_y1868_1870 + sizeof_y1869_1871;
            IntTy size_dcon1873 = 9 + fltPrm2474;

            *(TagTyPacked *) loc2683 = 177;

            CursorTy writetag6795 = loc2683 + 1;

            *(IntTy *) writetag6795 = size_dcon1873;

            CursorTy writecur6796 = writetag6795 + sizeof(IntTy);

            *(IntTy *) writecur6796 = offset_1872;

            CursorTy writecur6797 = writecur6796 + sizeof(IntTy);
            CursorTy writecur6798 = (CursorTy) end_y1868;
            CursorTy writecur6799 = (CursorTy) end_y1869;
            CursorTy pvrtmp10021 = (CursorTy) writecur6799;
            CursorTy pvrtmp10020 = (CursorTy) loc2683;
            CursorTy taildc5485 = (CursorTy) pvrtmp10020;
            CursorTy end_taildc5485 = (CursorTy) pvrtmp10021;
            CursorTy pvrtmp10023 = (CursorTy) end_taildc5485;
            CursorTy pvrtmp10022 = (CursorTy) taildc5485;
            CursorTy fltPrd7833 = (CursorTy) pvrtmp10022;
            CursorTy fltPrd7834 = (CursorTy) pvrtmp10023;

            return (CursorCursorCursorCursorProd) {end_r2685_5629_5630,
                                                   endof5484, fltPrd7833,
                                                   fltPrd7834};
            break;
        }

      case 8:
        {
            CursorTy field_cur6801 = (CursorTy) tmpcur9885;
            CursorTy case4552 = (CursorTy) field_cur6801;
            SymTy tmpval10024 = *(SymTy *) case4552;
            CursorTy tmpcur10025 = case4552 + sizeof(SymTy);
            SymTy x1874 = (SymTy) tmpval10024;
            CursorTy end_x1874 = (CursorTy) tmpcur10025;
            CursorTy case4553 = (CursorTy) end_x1874;
            CursorTy x1875 = (CursorTy) case4553;
            CursorTy jump5486 = case4552 + 8;
            CursorCursorCursorCursorProd tmp_struct378 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685, loc4558, x1875);
            CursorTy pvrtmp10026 = tmp_struct378.field0;
            CursorTy pvrtmp10027 = tmp_struct378.field1;
            CursorTy pvrtmp10028 = tmp_struct378.field2;
            CursorTy pvrtmp10029 = tmp_struct378.field3;
            CursorTy fltPrd7835 = (CursorTy) pvrtmp10028;
            CursorTy fltPrd7836 = (CursorTy) pvrtmp10029;
            CursorTy pvrtmp10031 = (CursorTy) fltPrd7836;
            CursorTy pvrtmp10030 = (CursorTy) fltPrd7835;
            CursorTy y1877 = (CursorTy) pvrtmp10030;
            CursorTy fltPrd7837 = (CursorTy) pvrtmp10028;
            CursorTy fltPrd7838 = (CursorTy) pvrtmp10029;
            CursorTy pvrtmp10033 = (CursorTy) fltPrd7838;
            CursorTy pvrtmp10032 = (CursorTy) fltPrd7837;
            CursorTy end_y1877 = (CursorTy) pvrtmp10033;
            CursorTy end_r2685_5631 = (CursorTy) pvrtmp10026;
            CursorTy endof5487 = (CursorTy) pvrtmp10027;

            *(TagTyPacked *) loc2683 = 8;

            CursorTy writetag6804 = loc2683 + 1;

            *(SymTy *) writetag6804 = x1874;

            CursorTy writecur6805 = writetag6804 + sizeof(SymTy);
            CursorTy writecur6806 = (CursorTy) end_y1877;
            CursorTy pvrtmp10035 = (CursorTy) writecur6806;
            CursorTy pvrtmp10034 = (CursorTy) loc2683;
            CursorTy taildc5488 = (CursorTy) pvrtmp10034;
            CursorTy end_taildc5488 = (CursorTy) pvrtmp10035;
            CursorTy pvrtmp10037 = (CursorTy) end_taildc5488;
            CursorTy pvrtmp10036 = (CursorTy) taildc5488;
            CursorTy fltPrd7839 = (CursorTy) pvrtmp10036;
            CursorTy fltPrd7840 = (CursorTy) pvrtmp10037;

            return (CursorCursorCursorCursorProd) {end_r2685_5631, endof5487,
                                                   fltPrd7839, fltPrd7840};
            break;
        }

      case 9:
        {
            CursorTy field_cur6808 = (CursorTy) tmpcur9885;
            CursorTy case4562 = (CursorTy) field_cur6808;
            CursorTy x1878 = (CursorTy) case4562;
            CursorTy loc4566 = loc2683 + 1;
            CursorCursorCursorCursorProd tmp_struct379 =
                                          _add_size_and_rel_offsets_Datum(end_r2684, end_r2685, loc4566, x1878);
            CursorTy pvrtmp10038 = tmp_struct379.field0;
            CursorTy pvrtmp10039 = tmp_struct379.field1;
            CursorTy pvrtmp10040 = tmp_struct379.field2;
            CursorTy pvrtmp10041 = tmp_struct379.field3;
            CursorTy fltPrd7841 = (CursorTy) pvrtmp10040;
            CursorTy fltPrd7842 = (CursorTy) pvrtmp10041;
            CursorTy pvrtmp10043 = (CursorTy) fltPrd7842;
            CursorTy pvrtmp10042 = (CursorTy) fltPrd7841;
            CursorTy y1879 = (CursorTy) pvrtmp10042;
            CursorTy fltPrd7843 = (CursorTy) pvrtmp10040;
            CursorTy fltPrd7844 = (CursorTy) pvrtmp10041;
            CursorTy pvrtmp10045 = (CursorTy) fltPrd7844;
            CursorTy pvrtmp10044 = (CursorTy) fltPrd7843;
            CursorTy end_y1879 = (CursorTy) pvrtmp10045;
            CursorTy end_r2685_5632 = (CursorTy) pvrtmp10038;
            CursorTy endof5489 = (CursorTy) pvrtmp10039;

            *(TagTyPacked *) loc2683 = 9;

            CursorTy writetag6810 = loc2683 + 1;
            CursorTy writecur6811 = (CursorTy) end_y1879;
            CursorTy pvrtmp10047 = (CursorTy) writecur6811;
            CursorTy pvrtmp10046 = (CursorTy) loc2683;
            CursorTy taildc5490 = (CursorTy) pvrtmp10046;
            CursorTy end_taildc5490 = (CursorTy) pvrtmp10047;
            CursorTy pvrtmp10049 = (CursorTy) end_taildc5490;
            CursorTy pvrtmp10048 = (CursorTy) taildc5490;
            CursorTy fltPrd7845 = (CursorTy) pvrtmp10048;
            CursorTy fltPrd7846 = (CursorTy) pvrtmp10049;

            return (CursorCursorCursorCursorProd) {end_r2685_5632, endof5489,
                                                   fltPrd7845, fltPrd7846};
            break;
        }

      case 10:
        {
            CursorTy field_cur6813 = (CursorTy) tmpcur9885;
            CursorTy case4568 = (CursorTy) field_cur6813;
            CursorTy x1880 = (CursorTy) case4568;
            CursorTy loc4572 = loc2683 + 1;
            CursorCursorCursorCursorProd tmp_struct380 =
                                          _add_size_and_rel_offsets_Datum(end_r2684, end_r2685, loc4572, x1880);
            CursorTy pvrtmp10050 = tmp_struct380.field0;
            CursorTy pvrtmp10051 = tmp_struct380.field1;
            CursorTy pvrtmp10052 = tmp_struct380.field2;
            CursorTy pvrtmp10053 = tmp_struct380.field3;
            CursorTy fltPrd7847 = (CursorTy) pvrtmp10052;
            CursorTy fltPrd7848 = (CursorTy) pvrtmp10053;
            CursorTy pvrtmp10055 = (CursorTy) fltPrd7848;
            CursorTy pvrtmp10054 = (CursorTy) fltPrd7847;
            CursorTy y1881 = (CursorTy) pvrtmp10054;
            CursorTy fltPrd7849 = (CursorTy) pvrtmp10052;
            CursorTy fltPrd7850 = (CursorTy) pvrtmp10053;
            CursorTy pvrtmp10057 = (CursorTy) fltPrd7850;
            CursorTy pvrtmp10056 = (CursorTy) fltPrd7849;
            CursorTy end_y1881 = (CursorTy) pvrtmp10057;
            CursorTy end_r2685_5633 = (CursorTy) pvrtmp10050;
            CursorTy endof5491 = (CursorTy) pvrtmp10051;

            *(TagTyPacked *) loc2683 = 10;

            CursorTy writetag6815 = loc2683 + 1;
            CursorTy writecur6816 = (CursorTy) end_y1881;
            CursorTy pvrtmp10059 = (CursorTy) writecur6816;
            CursorTy pvrtmp10058 = (CursorTy) loc2683;
            CursorTy taildc5492 = (CursorTy) pvrtmp10058;
            CursorTy end_taildc5492 = (CursorTy) pvrtmp10059;
            CursorTy pvrtmp10061 = (CursorTy) end_taildc5492;
            CursorTy pvrtmp10060 = (CursorTy) taildc5492;
            CursorTy fltPrd7851 = (CursorTy) pvrtmp10060;
            CursorTy fltPrd7852 = (CursorTy) pvrtmp10061;

            return (CursorCursorCursorCursorProd) {end_r2685_5633, endof5491,
                                                   fltPrd7851, fltPrd7852};
            break;
        }

      case 11:
        {
            CursorTy field_cur6818 = (CursorTy) tmpcur9885;
            CursorTy case4574 = (CursorTy) field_cur6818;
            CursorTy x1882 = (CursorTy) case4574;
            CursorTy loc4578 = loc2683 + 1;
            CursorCursorCursorCursorProd tmp_struct381 =
                                          _add_size_and_rel_offsets_Datum(end_r2684, end_r2685, loc4578, x1882);
            CursorTy pvrtmp10062 = tmp_struct381.field0;
            CursorTy pvrtmp10063 = tmp_struct381.field1;
            CursorTy pvrtmp10064 = tmp_struct381.field2;
            CursorTy pvrtmp10065 = tmp_struct381.field3;
            CursorTy fltPrd7853 = (CursorTy) pvrtmp10064;
            CursorTy fltPrd7854 = (CursorTy) pvrtmp10065;
            CursorTy pvrtmp10067 = (CursorTy) fltPrd7854;
            CursorTy pvrtmp10066 = (CursorTy) fltPrd7853;
            CursorTy y1883 = (CursorTy) pvrtmp10066;
            CursorTy fltPrd7855 = (CursorTy) pvrtmp10064;
            CursorTy fltPrd7856 = (CursorTy) pvrtmp10065;
            CursorTy pvrtmp10069 = (CursorTy) fltPrd7856;
            CursorTy pvrtmp10068 = (CursorTy) fltPrd7855;
            CursorTy end_y1883 = (CursorTy) pvrtmp10069;
            CursorTy end_r2685_5634 = (CursorTy) pvrtmp10062;
            CursorTy endof5493 = (CursorTy) pvrtmp10063;

            *(TagTyPacked *) loc2683 = 11;

            CursorTy writetag6820 = loc2683 + 1;
            CursorTy writecur6821 = (CursorTy) end_y1883;
            CursorTy pvrtmp10071 = (CursorTy) writecur6821;
            CursorTy pvrtmp10070 = (CursorTy) loc2683;
            CursorTy taildc5494 = (CursorTy) pvrtmp10070;
            CursorTy end_taildc5494 = (CursorTy) pvrtmp10071;
            CursorTy pvrtmp10073 = (CursorTy) end_taildc5494;
            CursorTy pvrtmp10072 = (CursorTy) taildc5494;
            CursorTy fltPrd7857 = (CursorTy) pvrtmp10072;
            CursorTy fltPrd7858 = (CursorTy) pvrtmp10073;

            return (CursorCursorCursorCursorProd) {end_r2685_5634, endof5493,
                                                   fltPrd7857, fltPrd7858};
            break;
        }

      case 12:
        {
            CursorTy field_cur6823 = (CursorTy) tmpcur9885;
            CursorTy case4580 = (CursorTy) field_cur6823;
            CursorTy x1884 = (CursorTy) case4580;
            CursorCursorCursorCursorProd tmp_struct382 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685, loc4595, x1884);
            CursorTy pvrtmp10074 = tmp_struct382.field0;
            CursorTy pvrtmp10075 = tmp_struct382.field1;
            CursorTy pvrtmp10076 = tmp_struct382.field2;
            CursorTy pvrtmp10077 = tmp_struct382.field3;
            CursorTy fltPrd7859 = (CursorTy) pvrtmp10076;
            CursorTy fltPrd7860 = (CursorTy) pvrtmp10077;
            CursorTy pvrtmp10079 = (CursorTy) fltPrd7860;
            CursorTy pvrtmp10078 = (CursorTy) fltPrd7859;
            CursorTy y1887 = (CursorTy) pvrtmp10078;
            CursorTy fltPrd7861 = (CursorTy) pvrtmp10076;
            CursorTy fltPrd7862 = (CursorTy) pvrtmp10077;
            CursorTy pvrtmp10081 = (CursorTy) fltPrd7862;
            CursorTy pvrtmp10080 = (CursorTy) fltPrd7861;
            CursorTy end_y1887 = (CursorTy) pvrtmp10081;
            CursorTy end_r2685_5635 = (CursorTy) pvrtmp10074;
            CursorTy endof5495 = (CursorTy) pvrtmp10075;
            CursorTy case4581 = (CursorTy) endof5495;
            CursorTy x1885 = (CursorTy) case4581;
            CursorTy loc4596 = (CursorTy) end_y1887;
            CursorCursorCursorCursorProd tmp_struct383 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685_5635, loc4596, x1885);
            CursorTy pvrtmp10082 = tmp_struct383.field0;
            CursorTy pvrtmp10083 = tmp_struct383.field1;
            CursorTy pvrtmp10084 = tmp_struct383.field2;
            CursorTy pvrtmp10085 = tmp_struct383.field3;
            CursorTy fltPrd7863 = (CursorTy) pvrtmp10084;
            CursorTy fltPrd7864 = (CursorTy) pvrtmp10085;
            CursorTy pvrtmp10087 = (CursorTy) fltPrd7864;
            CursorTy pvrtmp10086 = (CursorTy) fltPrd7863;
            CursorTy y1888 = (CursorTy) pvrtmp10086;
            CursorTy fltPrd7865 = (CursorTy) pvrtmp10084;
            CursorTy fltPrd7866 = (CursorTy) pvrtmp10085;
            CursorTy pvrtmp10089 = (CursorTy) fltPrd7866;
            CursorTy pvrtmp10088 = (CursorTy) fltPrd7865;
            CursorTy end_y1888 = (CursorTy) pvrtmp10089;
            CursorTy end_r2685_5635_5636 = (CursorTy) pvrtmp10082;
            CursorTy endof5496 = (CursorTy) pvrtmp10083;
            CursorTy case4582 = (CursorTy) endof5496;
            CursorTy x1886 = (CursorTy) case4582;
            CursorTy loc4597 = (CursorTy) end_y1888;
            CursorCursorCursorCursorProd tmp_struct384 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685_5635_5636, loc4597, x1886);
            CursorTy pvrtmp10090 = tmp_struct384.field0;
            CursorTy pvrtmp10091 = tmp_struct384.field1;
            CursorTy pvrtmp10092 = tmp_struct384.field2;
            CursorTy pvrtmp10093 = tmp_struct384.field3;
            CursorTy fltPrd7867 = (CursorTy) pvrtmp10092;
            CursorTy fltPrd7868 = (CursorTy) pvrtmp10093;
            CursorTy pvrtmp10095 = (CursorTy) fltPrd7868;
            CursorTy pvrtmp10094 = (CursorTy) fltPrd7867;
            CursorTy y1889 = (CursorTy) pvrtmp10094;
            CursorTy fltPrd7869 = (CursorTy) pvrtmp10092;
            CursorTy fltPrd7870 = (CursorTy) pvrtmp10093;
            CursorTy pvrtmp10097 = (CursorTy) fltPrd7870;
            CursorTy pvrtmp10096 = (CursorTy) fltPrd7869;
            CursorTy end_y1889 = (CursorTy) pvrtmp10097;
            CursorTy end_r2685_5635_5636_5637 = (CursorTy) pvrtmp10090;
            CursorTy endof5497 = (CursorTy) pvrtmp10091;
            IntTy sizeof_y1887_1890 = end_y1887 - y1887;
            IntTy sizeof_y1888_1891 = end_y1888 - y1888;
            IntTy sizeof_y1889_1892 = end_y1889 - y1889;
            IntTy fltPrm2475 = sizeof_y1887_1890 + 0;
            IntTy offset_1893 = 8 + fltPrm2475;
            IntTy fltPrm2476 = sizeof_y1887_1890 + sizeof_y1888_1891;
            IntTy offset_1894 = 0 + fltPrm2476;
            IntTy fltPrm2478 = sizeof_y1888_1891 + sizeof_y1889_1892;
            IntTy fltPrm2477 = sizeof_y1887_1890 + fltPrm2478;
            IntTy size_dcon1895 = 17 + fltPrm2477;

            *(TagTyPacked *) loc2683 = 179;

            CursorTy writetag6827 = loc2683 + 1;

            *(IntTy *) writetag6827 = size_dcon1895;

            CursorTy writecur6828 = writetag6827 + sizeof(IntTy);

            *(IntTy *) writecur6828 = offset_1893;

            CursorTy writecur6829 = writecur6828 + sizeof(IntTy);

            *(IntTy *) writecur6829 = offset_1894;

            CursorTy writecur6830 = writecur6829 + sizeof(IntTy);
            CursorTy writecur6831 = (CursorTy) end_y1887;
            CursorTy writecur6832 = (CursorTy) end_y1888;
            CursorTy writecur6833 = (CursorTy) end_y1889;
            CursorTy pvrtmp10099 = (CursorTy) writecur6833;
            CursorTy pvrtmp10098 = (CursorTy) loc2683;
            CursorTy taildc5498 = (CursorTy) pvrtmp10098;
            CursorTy end_taildc5498 = (CursorTy) pvrtmp10099;
            CursorTy pvrtmp10101 = (CursorTy) end_taildc5498;
            CursorTy pvrtmp10100 = (CursorTy) taildc5498;
            CursorTy fltPrd7871 = (CursorTy) pvrtmp10100;
            CursorTy fltPrd7872 = (CursorTy) pvrtmp10101;

            return (CursorCursorCursorCursorProd) {end_r2685_5635_5636_5637,
                                                   endof5497, fltPrd7871,
                                                   fltPrd7872};
            break;
        }

      case 13:
        {
            CursorTy field_cur6835 = (CursorTy) tmpcur9885;
            CursorTy case4607 = (CursorTy) field_cur6835;
            CursorTy x1896 = (CursorTy) case4607;
            CursorCursorCursorCursorProd tmp_struct385 =
                                          _add_size_and_rel_offsets_Expr(end_r2684, end_r2685, loc4617, x1896);
            CursorTy pvrtmp10102 = tmp_struct385.field0;
            CursorTy pvrtmp10103 = tmp_struct385.field1;
            CursorTy pvrtmp10104 = tmp_struct385.field2;
            CursorTy pvrtmp10105 = tmp_struct385.field3;
            CursorTy fltPrd7873 = (CursorTy) pvrtmp10104;
            CursorTy fltPrd7874 = (CursorTy) pvrtmp10105;
            CursorTy pvrtmp10107 = (CursorTy) fltPrd7874;
            CursorTy pvrtmp10106 = (CursorTy) fltPrd7873;
            CursorTy y1898 = (CursorTy) pvrtmp10106;
            CursorTy fltPrd7875 = (CursorTy) pvrtmp10104;
            CursorTy fltPrd7876 = (CursorTy) pvrtmp10105;
            CursorTy pvrtmp10109 = (CursorTy) fltPrd7876;
            CursorTy pvrtmp10108 = (CursorTy) fltPrd7875;
            CursorTy end_y1898 = (CursorTy) pvrtmp10109;
            CursorTy end_r2685_5638 = (CursorTy) pvrtmp10102;
            CursorTy endof5499 = (CursorTy) pvrtmp10103;
            CursorTy case4608 = (CursorTy) endof5499;
            CursorTy x1897 = (CursorTy) case4608;
            CursorTy loc4618 = (CursorTy) end_y1898;
            CursorCursorCursorCursorProd tmp_struct386 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2684, end_r2685_5638, loc4618, x1897);
            CursorTy pvrtmp10110 = tmp_struct386.field0;
            CursorTy pvrtmp10111 = tmp_struct386.field1;
            CursorTy pvrtmp10112 = tmp_struct386.field2;
            CursorTy pvrtmp10113 = tmp_struct386.field3;
            CursorTy fltPrd7877 = (CursorTy) pvrtmp10112;
            CursorTy fltPrd7878 = (CursorTy) pvrtmp10113;
            CursorTy pvrtmp10115 = (CursorTy) fltPrd7878;
            CursorTy pvrtmp10114 = (CursorTy) fltPrd7877;
            CursorTy y1899 = (CursorTy) pvrtmp10114;
            CursorTy fltPrd7879 = (CursorTy) pvrtmp10112;
            CursorTy fltPrd7880 = (CursorTy) pvrtmp10113;
            CursorTy pvrtmp10117 = (CursorTy) fltPrd7880;
            CursorTy pvrtmp10116 = (CursorTy) fltPrd7879;
            CursorTy end_y1899 = (CursorTy) pvrtmp10117;
            CursorTy end_r2685_5638_5639 = (CursorTy) pvrtmp10110;
            CursorTy endof5500 = (CursorTy) pvrtmp10111;
            IntTy sizeof_y1898_1900 = end_y1898 - y1898;
            IntTy sizeof_y1899_1901 = end_y1899 - y1899;
            IntTy fltPrm2479 = sizeof_y1898_1900 + 0;
            IntTy offset_1902 = 0 + fltPrm2479;
            IntTy fltPrm2480 = sizeof_y1898_1900 + sizeof_y1899_1901;
            IntTy size_dcon1903 = 9 + fltPrm2480;

            *(TagTyPacked *) loc2683 = 181;

            CursorTy writetag6838 = loc2683 + 1;

            *(IntTy *) writetag6838 = size_dcon1903;

            CursorTy writecur6839 = writetag6838 + sizeof(IntTy);

            *(IntTy *) writecur6839 = offset_1902;

            CursorTy writecur6840 = writecur6839 + sizeof(IntTy);
            CursorTy writecur6841 = (CursorTy) end_y1898;
            CursorTy writecur6842 = (CursorTy) end_y1899;
            CursorTy pvrtmp10119 = (CursorTy) writecur6842;
            CursorTy pvrtmp10118 = (CursorTy) loc2683;
            CursorTy taildc5501 = (CursorTy) pvrtmp10118;
            CursorTy end_taildc5501 = (CursorTy) pvrtmp10119;
            CursorTy pvrtmp10121 = (CursorTy) end_taildc5501;
            CursorTy pvrtmp10120 = (CursorTy) taildc5501;
            CursorTy fltPrd7881 = (CursorTy) pvrtmp10120;
            CursorTy fltPrd7882 = (CursorTy) pvrtmp10121;

            return (CursorCursorCursorCursorProd) {end_r2685_5638_5639,
                                                   endof5500, fltPrd7881,
                                                   fltPrd7882};
            break;
        }

      case 14:
        {
            CursorTy field_cur6844 = (CursorTy) tmpcur9885;
            CursorTy case4625 = (CursorTy) field_cur6844;
            SymTy tmpval10122 = *(SymTy *) case4625;
            CursorTy tmpcur10123 = case4625 + sizeof(SymTy);
            SymTy x1904 = (SymTy) tmpval10122;
            CursorTy end_x1904 = (CursorTy) tmpcur10123;
            CursorTy jump5502 = case4625 + 8;

            *(TagTyPacked *) loc2683 = 14;

            CursorTy writetag6846 = loc2683 + 1;

            *(SymTy *) writetag6846 = x1904;

            CursorTy writecur6847 = writetag6846 + sizeof(SymTy);
            CursorTy pvrtmp10125 = (CursorTy) writecur6847;
            CursorTy pvrtmp10124 = (CursorTy) loc2683;
            CursorTy taildc5503 = (CursorTy) pvrtmp10124;
            CursorTy end_taildc5503 = (CursorTy) pvrtmp10125;
            CursorTy pvrtmp10127 = (CursorTy) end_taildc5503;
            CursorTy pvrtmp10126 = (CursorTy) taildc5503;
            CursorTy fltPrd7883 = (CursorTy) pvrtmp10126;
            CursorTy fltPrd7884 = (CursorTy) pvrtmp10127;

            return (CursorCursorCursorCursorProd) {end_r2685, jump5502,
                                                   fltPrd7883, fltPrd7884};
            break;
        }

      case 15:
        {
            CursorTy field_cur6849 = (CursorTy) tmpcur9885;
            CursorTy case4629 = (CursorTy) field_cur6849;
            SymTy tmpval10128 = *(SymTy *) case4629;
            CursorTy tmpcur10129 = case4629 + sizeof(SymTy);
            SymTy x1906 = (SymTy) tmpval10128;
            CursorTy end_x1906 = (CursorTy) tmpcur10129;
            CursorTy jump5504 = case4629 + 8;

            *(TagTyPacked *) loc2683 = 15;

            CursorTy writetag6851 = loc2683 + 1;

            *(SymTy *) writetag6851 = x1906;

            CursorTy writecur6852 = writetag6851 + sizeof(SymTy);
            CursorTy pvrtmp10131 = (CursorTy) writecur6852;
            CursorTy pvrtmp10130 = (CursorTy) loc2683;
            CursorTy taildc5505 = (CursorTy) pvrtmp10130;
            CursorTy end_taildc5505 = (CursorTy) pvrtmp10131;
            CursorTy pvrtmp10133 = (CursorTy) end_taildc5505;
            CursorTy pvrtmp10132 = (CursorTy) taildc5505;
            CursorTy fltPrd7885 = (CursorTy) pvrtmp10132;
            CursorTy fltPrd7886 = (CursorTy) pvrtmp10133;

            return (CursorCursorCursorCursorProd) {end_r2685, jump5504,
                                                   fltPrd7885, fltPrd7886};
            break;
        }

      case 16:
        {
            CursorTy field_cur6854 = (CursorTy) tmpcur9885;
            CursorTy case4633 = (CursorTy) field_cur6854;
            SymTy tmpval10134 = *(SymTy *) case4633;
            CursorTy tmpcur10135 = case4633 + sizeof(SymTy);
            SymTy x1908 = (SymTy) tmpval10134;
            CursorTy end_x1908 = (CursorTy) tmpcur10135;
            CursorTy jump5506 = case4633 + 8;

            *(TagTyPacked *) loc2683 = 16;

            CursorTy writetag6856 = loc2683 + 1;

            *(SymTy *) writetag6856 = x1908;

            CursorTy writecur6857 = writetag6856 + sizeof(SymTy);
            CursorTy pvrtmp10137 = (CursorTy) writecur6857;
            CursorTy pvrtmp10136 = (CursorTy) loc2683;
            CursorTy taildc5507 = (CursorTy) pvrtmp10136;
            CursorTy end_taildc5507 = (CursorTy) pvrtmp10137;
            CursorTy pvrtmp10139 = (CursorTy) end_taildc5507;
            CursorTy pvrtmp10138 = (CursorTy) taildc5507;
            CursorTy fltPrd7887 = (CursorTy) pvrtmp10138;
            CursorTy fltPrd7888 = (CursorTy) pvrtmp10139;

            return (CursorCursorCursorCursorProd) {end_r2685, jump5506,
                                                   fltPrd7887, fltPrd7888};
            break;
        }

      case 17:
        {
            CursorTy field_cur6859 = (CursorTy) tmpcur9885;
            CursorTy jump5508 = loc2682 + 1;

            *(TagTyPacked *) loc2683 = 17;

            CursorTy writetag6860 = loc2683 + 1;
            CursorTy pvrtmp10141 = (CursorTy) writetag6860;
            CursorTy pvrtmp10140 = (CursorTy) loc2683;
            CursorTy taildc5509 = (CursorTy) pvrtmp10140;
            CursorTy end_taildc5509 = (CursorTy) pvrtmp10141;
            CursorTy pvrtmp10143 = (CursorTy) end_taildc5509;
            CursorTy pvrtmp10142 = (CursorTy) taildc5509;
            CursorTy fltPrd7889 = (CursorTy) pvrtmp10142;
            CursorTy fltPrd7890 = (CursorTy) pvrtmp10143;

            return (CursorCursorCursorCursorProd) {end_r2685, jump5508,
                                                   fltPrd7889, fltPrd7890};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10907 = *(CursorTy *) tmpcur9885;
            CursorTy tmpaftercur10908 = tmpcur9885 + 8;
            TagTyPacked tagtmp10909 = *(TagTyPacked *) tmpcur10907;
            CursorTy tailtmp10910 = tmpcur10907 + 1;

            tmpval9884 = tagtmp10909;
            tmpcur9885 = tailtmp10910;
            goto switch10144;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10907 = *(CursorTy *) tmpcur9885;
            CursorTy tmpaftercur10908 = tmpcur9885 + 8;
            TagTyPacked tagtmp10909 = *(TagTyPacked *) tmpcur10907;
            CursorTy tailtmp10910 = tmpcur10907 + 1;

            tmpval9884 = tagtmp10909;
            tmpcur9885 = tailtmp10910;
            goto switch10144;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval9884");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Toplvl(CursorTy end_r2688,
                                                              CursorTy end_r2689,
                                                              CursorTy loc2687,
                                                              CursorTy arg1910)
{
    CursorTy loc2686 = (CursorTy) arg1910;

    if (loc2687 + 26 > end_r2689) {
        ChunkTy new_chunk396 = alloc_chunk(end_r2689);
        CursorTy chunk_start397 = new_chunk396.start_ptr;
        CursorTy chunk_end398 = new_chunk396.end_ptr;

        end_r2689 = chunk_end398;
        *(TagTyPacked *) loc2687 = 255;

        CursorTy redir = loc2687 + 1;

        *(CursorTy *) redir = chunk_start397;
        loc2687 = chunk_start397;
    }

    CursorTy loc4648 = loc2687 + 1;
    CursorTy loc4649 = loc4648 + 8;
    CursorTy loc4650 = loc4649 + 8;
    CursorTy loc4666 = loc2687 + 1;
    CursorTy loc4667 = loc4666 + 8;
    CursorTy loc4668 = loc4667 + 8;
    TagTyPacked tmpval10145 = *(TagTyPacked *) arg1910;
    CursorTy tmpcur10146 = arg1910 + 1;


  switch10211:
    ;
    switch (tmpval10145) {

      case 0:
        {
            CursorTy field_cur6862 = (CursorTy) tmpcur10146;
            CursorTy case4640 = (CursorTy) field_cur6862;
            CursorTy x1911 = (CursorTy) case4640;
            CursorCursorCursorCursorProd tmp_struct390 =
                                          _add_size_and_rel_offsets_ListSym(end_r2688, end_r2689, loc4650, x1911);
            CursorTy pvrtmp10147 = tmp_struct390.field0;
            CursorTy pvrtmp10148 = tmp_struct390.field1;
            CursorTy pvrtmp10149 = tmp_struct390.field2;
            CursorTy pvrtmp10150 = tmp_struct390.field3;
            CursorTy fltPrd7891 = (CursorTy) pvrtmp10149;
            CursorTy fltPrd7892 = (CursorTy) pvrtmp10150;
            CursorTy pvrtmp10152 = (CursorTy) fltPrd7892;
            CursorTy pvrtmp10151 = (CursorTy) fltPrd7891;
            CursorTy y1913 = (CursorTy) pvrtmp10151;
            CursorTy fltPrd7893 = (CursorTy) pvrtmp10149;
            CursorTy fltPrd7894 = (CursorTy) pvrtmp10150;
            CursorTy pvrtmp10154 = (CursorTy) fltPrd7894;
            CursorTy pvrtmp10153 = (CursorTy) fltPrd7893;
            CursorTy end_y1913 = (CursorTy) pvrtmp10154;
            CursorTy end_r2689_5640 = (CursorTy) pvrtmp10147;
            CursorTy endof5510 = (CursorTy) pvrtmp10148;
            CursorTy case4641 = (CursorTy) endof5510;
            CursorTy x1912 = (CursorTy) case4641;
            CursorTy loc4651 = (CursorTy) end_y1913;
            CursorCursorCursorCursorProd tmp_struct391 =
                                          _add_size_and_rel_offsets_Expr(end_r2688, end_r2689_5640, loc4651, x1912);
            CursorTy pvrtmp10155 = tmp_struct391.field0;
            CursorTy pvrtmp10156 = tmp_struct391.field1;
            CursorTy pvrtmp10157 = tmp_struct391.field2;
            CursorTy pvrtmp10158 = tmp_struct391.field3;
            CursorTy fltPrd7895 = (CursorTy) pvrtmp10157;
            CursorTy fltPrd7896 = (CursorTy) pvrtmp10158;
            CursorTy pvrtmp10160 = (CursorTy) fltPrd7896;
            CursorTy pvrtmp10159 = (CursorTy) fltPrd7895;
            CursorTy y1914 = (CursorTy) pvrtmp10159;
            CursorTy fltPrd7897 = (CursorTy) pvrtmp10157;
            CursorTy fltPrd7898 = (CursorTy) pvrtmp10158;
            CursorTy pvrtmp10162 = (CursorTy) fltPrd7898;
            CursorTy pvrtmp10161 = (CursorTy) fltPrd7897;
            CursorTy end_y1914 = (CursorTy) pvrtmp10162;
            CursorTy end_r2689_5640_5641 = (CursorTy) pvrtmp10155;
            CursorTy endof5511 = (CursorTy) pvrtmp10156;
            IntTy sizeof_y1913_1915 = end_y1913 - y1913;
            IntTy sizeof_y1914_1916 = end_y1914 - y1914;
            IntTy fltPrm2481 = sizeof_y1913_1915 + 0;
            IntTy offset_1917 = 0 + fltPrm2481;
            IntTy fltPrm2482 = sizeof_y1913_1915 + sizeof_y1914_1916;
            IntTy size_dcon1918 = 9 + fltPrm2482;

            *(TagTyPacked *) loc2687 = 155;

            CursorTy writetag6865 = loc2687 + 1;

            *(IntTy *) writetag6865 = size_dcon1918;

            CursorTy writecur6866 = writetag6865 + sizeof(IntTy);

            *(IntTy *) writecur6866 = offset_1917;

            CursorTy writecur6867 = writecur6866 + sizeof(IntTy);
            CursorTy writecur6868 = (CursorTy) end_y1913;
            CursorTy writecur6869 = (CursorTy) end_y1914;
            CursorTy pvrtmp10164 = (CursorTy) writecur6869;
            CursorTy pvrtmp10163 = (CursorTy) loc2687;
            CursorTy taildc5512 = (CursorTy) pvrtmp10163;
            CursorTy end_taildc5512 = (CursorTy) pvrtmp10164;
            CursorTy pvrtmp10166 = (CursorTy) end_taildc5512;
            CursorTy pvrtmp10165 = (CursorTy) taildc5512;
            CursorTy fltPrd7899 = (CursorTy) pvrtmp10165;
            CursorTy fltPrd7900 = (CursorTy) pvrtmp10166;

            return (CursorCursorCursorCursorProd) {end_r2689_5640_5641,
                                                   endof5511, fltPrd7899,
                                                   fltPrd7900};
            break;
        }

      case 1:
        {
            CursorTy field_cur6871 = (CursorTy) tmpcur10146;
            CursorTy case4658 = (CursorTy) field_cur6871;
            CursorTy x1919 = (CursorTy) case4658;
            CursorCursorCursorCursorProd tmp_struct392 =
                                          _add_size_and_rel_offsets_ListSym(end_r2688, end_r2689, loc4668, x1919);
            CursorTy pvrtmp10167 = tmp_struct392.field0;
            CursorTy pvrtmp10168 = tmp_struct392.field1;
            CursorTy pvrtmp10169 = tmp_struct392.field2;
            CursorTy pvrtmp10170 = tmp_struct392.field3;
            CursorTy fltPrd7901 = (CursorTy) pvrtmp10169;
            CursorTy fltPrd7902 = (CursorTy) pvrtmp10170;
            CursorTy pvrtmp10172 = (CursorTy) fltPrd7902;
            CursorTy pvrtmp10171 = (CursorTy) fltPrd7901;
            CursorTy y1921 = (CursorTy) pvrtmp10171;
            CursorTy fltPrd7903 = (CursorTy) pvrtmp10169;
            CursorTy fltPrd7904 = (CursorTy) pvrtmp10170;
            CursorTy pvrtmp10174 = (CursorTy) fltPrd7904;
            CursorTy pvrtmp10173 = (CursorTy) fltPrd7903;
            CursorTy end_y1921 = (CursorTy) pvrtmp10174;
            CursorTy end_r2689_5642 = (CursorTy) pvrtmp10167;
            CursorTy endof5513 = (CursorTy) pvrtmp10168;
            CursorTy case4659 = (CursorTy) endof5513;
            CursorTy x1920 = (CursorTy) case4659;
            CursorTy loc4669 = (CursorTy) end_y1921;
            CursorCursorCursorCursorProd tmp_struct393 =
                                          _add_size_and_rel_offsets_Expr(end_r2688, end_r2689_5642, loc4669, x1920);
            CursorTy pvrtmp10175 = tmp_struct393.field0;
            CursorTy pvrtmp10176 = tmp_struct393.field1;
            CursorTy pvrtmp10177 = tmp_struct393.field2;
            CursorTy pvrtmp10178 = tmp_struct393.field3;
            CursorTy fltPrd7905 = (CursorTy) pvrtmp10177;
            CursorTy fltPrd7906 = (CursorTy) pvrtmp10178;
            CursorTy pvrtmp10180 = (CursorTy) fltPrd7906;
            CursorTy pvrtmp10179 = (CursorTy) fltPrd7905;
            CursorTy y1922 = (CursorTy) pvrtmp10179;
            CursorTy fltPrd7907 = (CursorTy) pvrtmp10177;
            CursorTy fltPrd7908 = (CursorTy) pvrtmp10178;
            CursorTy pvrtmp10182 = (CursorTy) fltPrd7908;
            CursorTy pvrtmp10181 = (CursorTy) fltPrd7907;
            CursorTy end_y1922 = (CursorTy) pvrtmp10182;
            CursorTy end_r2689_5642_5643 = (CursorTy) pvrtmp10175;
            CursorTy endof5514 = (CursorTy) pvrtmp10176;
            IntTy sizeof_y1921_1923 = end_y1921 - y1921;
            IntTy sizeof_y1922_1924 = end_y1922 - y1922;
            IntTy fltPrm2483 = sizeof_y1921_1923 + 0;
            IntTy offset_1925 = 0 + fltPrm2483;
            IntTy fltPrm2484 = sizeof_y1921_1923 + sizeof_y1922_1924;
            IntTy size_dcon1926 = 9 + fltPrm2484;

            *(TagTyPacked *) loc2687 = 157;

            CursorTy writetag6874 = loc2687 + 1;

            *(IntTy *) writetag6874 = size_dcon1926;

            CursorTy writecur6875 = writetag6874 + sizeof(IntTy);

            *(IntTy *) writecur6875 = offset_1925;

            CursorTy writecur6876 = writecur6875 + sizeof(IntTy);
            CursorTy writecur6877 = (CursorTy) end_y1921;
            CursorTy writecur6878 = (CursorTy) end_y1922;
            CursorTy pvrtmp10184 = (CursorTy) writecur6878;
            CursorTy pvrtmp10183 = (CursorTy) loc2687;
            CursorTy taildc5515 = (CursorTy) pvrtmp10183;
            CursorTy end_taildc5515 = (CursorTy) pvrtmp10184;
            CursorTy pvrtmp10186 = (CursorTy) end_taildc5515;
            CursorTy pvrtmp10185 = (CursorTy) taildc5515;
            CursorTy fltPrd7909 = (CursorTy) pvrtmp10185;
            CursorTy fltPrd7910 = (CursorTy) pvrtmp10186;

            return (CursorCursorCursorCursorProd) {end_r2689_5642_5643,
                                                   endof5514, fltPrd7909,
                                                   fltPrd7910};
            break;
        }

      case 2:
        {
            CursorTy field_cur6880 = (CursorTy) tmpcur10146;
            CursorTy case4676 = (CursorTy) field_cur6880;
            CursorTy x1927 = (CursorTy) case4676;
            CursorTy loc4680 = loc2687 + 1;
            CursorCursorCursorCursorProd tmp_struct394 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r2688, end_r2689, loc4680, x1927);
            CursorTy pvrtmp10187 = tmp_struct394.field0;
            CursorTy pvrtmp10188 = tmp_struct394.field1;
            CursorTy pvrtmp10189 = tmp_struct394.field2;
            CursorTy pvrtmp10190 = tmp_struct394.field3;
            CursorTy fltPrd7911 = (CursorTy) pvrtmp10189;
            CursorTy fltPrd7912 = (CursorTy) pvrtmp10190;
            CursorTy pvrtmp10192 = (CursorTy) fltPrd7912;
            CursorTy pvrtmp10191 = (CursorTy) fltPrd7911;
            CursorTy y1928 = (CursorTy) pvrtmp10191;
            CursorTy fltPrd7913 = (CursorTy) pvrtmp10189;
            CursorTy fltPrd7914 = (CursorTy) pvrtmp10190;
            CursorTy pvrtmp10194 = (CursorTy) fltPrd7914;
            CursorTy pvrtmp10193 = (CursorTy) fltPrd7913;
            CursorTy end_y1928 = (CursorTy) pvrtmp10194;
            CursorTy end_r2689_5644 = (CursorTy) pvrtmp10187;
            CursorTy endof5516 = (CursorTy) pvrtmp10188;

            *(TagTyPacked *) loc2687 = 2;

            CursorTy writetag6882 = loc2687 + 1;
            CursorTy writecur6883 = (CursorTy) end_y1928;
            CursorTy pvrtmp10196 = (CursorTy) writecur6883;
            CursorTy pvrtmp10195 = (CursorTy) loc2687;
            CursorTy taildc5517 = (CursorTy) pvrtmp10195;
            CursorTy end_taildc5517 = (CursorTy) pvrtmp10196;
            CursorTy pvrtmp10198 = (CursorTy) end_taildc5517;
            CursorTy pvrtmp10197 = (CursorTy) taildc5517;
            CursorTy fltPrd7915 = (CursorTy) pvrtmp10197;
            CursorTy fltPrd7916 = (CursorTy) pvrtmp10198;

            return (CursorCursorCursorCursorProd) {end_r2689_5644, endof5516,
                                                   fltPrd7915, fltPrd7916};
            break;
        }

      case 3:
        {
            CursorTy field_cur6885 = (CursorTy) tmpcur10146;
            CursorTy case4682 = (CursorTy) field_cur6885;
            CursorTy x1929 = (CursorTy) case4682;
            CursorTy loc4686 = loc2687 + 1;
            CursorCursorCursorCursorProd tmp_struct395 =
                                          _add_size_and_rel_offsets_Expr(end_r2688, end_r2689, loc4686, x1929);
            CursorTy pvrtmp10199 = tmp_struct395.field0;
            CursorTy pvrtmp10200 = tmp_struct395.field1;
            CursorTy pvrtmp10201 = tmp_struct395.field2;
            CursorTy pvrtmp10202 = tmp_struct395.field3;
            CursorTy fltPrd7917 = (CursorTy) pvrtmp10201;
            CursorTy fltPrd7918 = (CursorTy) pvrtmp10202;
            CursorTy pvrtmp10204 = (CursorTy) fltPrd7918;
            CursorTy pvrtmp10203 = (CursorTy) fltPrd7917;
            CursorTy y1930 = (CursorTy) pvrtmp10203;
            CursorTy fltPrd7919 = (CursorTy) pvrtmp10201;
            CursorTy fltPrd7920 = (CursorTy) pvrtmp10202;
            CursorTy pvrtmp10206 = (CursorTy) fltPrd7920;
            CursorTy pvrtmp10205 = (CursorTy) fltPrd7919;
            CursorTy end_y1930 = (CursorTy) pvrtmp10206;
            CursorTy end_r2689_5645 = (CursorTy) pvrtmp10199;
            CursorTy endof5518 = (CursorTy) pvrtmp10200;

            *(TagTyPacked *) loc2687 = 3;

            CursorTy writetag6887 = loc2687 + 1;
            CursorTy writecur6888 = (CursorTy) end_y1930;
            CursorTy pvrtmp10208 = (CursorTy) writecur6888;
            CursorTy pvrtmp10207 = (CursorTy) loc2687;
            CursorTy taildc5519 = (CursorTy) pvrtmp10207;
            CursorTy end_taildc5519 = (CursorTy) pvrtmp10208;
            CursorTy pvrtmp10210 = (CursorTy) end_taildc5519;
            CursorTy pvrtmp10209 = (CursorTy) taildc5519;
            CursorTy fltPrd7921 = (CursorTy) pvrtmp10209;
            CursorTy fltPrd7922 = (CursorTy) pvrtmp10210;

            return (CursorCursorCursorCursorProd) {end_r2689_5645, endof5518,
                                                   fltPrd7921, fltPrd7922};
            break;
        }

      case 255:
        {
            CursorTy tmpcur10911 = *(CursorTy *) tmpcur10146;
            CursorTy tmpaftercur10912 = tmpcur10146 + 8;
            TagTyPacked tagtmp10913 = *(TagTyPacked *) tmpcur10911;
            CursorTy tailtmp10914 = tmpcur10911 + 1;

            tmpval10145 = tagtmp10913;
            tmpcur10146 = tailtmp10914;
            goto switch10211;
            break;
        }

      case 254:
        {
            CursorTy tmpcur10911 = *(CursorTy *) tmpcur10146;
            CursorTy tmpaftercur10912 = tmpcur10146 + 8;
            TagTyPacked tagtmp10913 = *(TagTyPacked *) tmpcur10911;
            CursorTy tailtmp10914 = tmpcur10911 + 1;

            tmpval10145 = tagtmp10913;
            tmpcur10146 = tailtmp10914;
            goto switch10211;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval10145");
            exit(1);
        }
    }
}

// OFFSETS END HERE

void __main_expr () {

    // read in file
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
    CursorTy r2565 = ptr;
    CursorTy end_r2565 = r2565 + bnch_size;

    // transform
    RegionTy *region = alloc_region(global_init_biginf_buf_size);
    CursorTy out_reg = region->start_ptr;
    CursorTy end_out_reg = out_reg + global_init_biginf_buf_size;
    CursorCursorCursorCursorProd tmp_struct =
        _add_size_and_rel_offsets_Toplvl(end_r2565, end_out_reg, out_reg, r2565);
    CursorTy val_start = tmp_struct.field2;
    CursorTy val_end = tmp_struct.field3;
    IntTy val_size = (IntTy) (val_end - val_start);
    printf("Added offsets. New size: %lld\n", val_size);

    // write output file
    size_t len = strlen(global_benchfile_param);
    char* suffix = ".offsets";
    size_t suffix_len = strlen(suffix);
    char *output_filename = malloc(len + suffix_len + 1);
    strcpy(output_filename, global_benchfile_param);
    strcat(output_filename, suffix);
    FILE *out_hdl = fopen(output_filename, "wb");
    const size_t wrote = fwrite(val_start, val_size, 1, out_hdl);
    fclose(out_hdl);
    printf("Wrote: %s\n", output_filename);
}
