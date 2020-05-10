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

CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListSym(CursorTy end_r2043,
                                                               CursorTy end_r2044,
                                                               CursorTy loc2042,
                                                               CursorTy arg1479)
{
    CursorTy loc2041 = (CursorTy) arg1479;

    if (loc2042 + 18 > end_r2044) {
        ChunkTy new_chunk199 = alloc_chunk(end_r2044);
        CursorTy chunk_start200 = new_chunk199.start_ptr;
        CursorTy chunk_end201 = new_chunk199.end_ptr;

        end_r2044 = chunk_end201;
        *(TagTyPacked *) loc2042 = 255;

        CursorTy redir = loc2042 + 1;

        *(CursorTy *) redir = chunk_start200;
        loc2042 = chunk_start200;
    }

    CursorTy loc2958 = loc2042 + 1;
    CursorTy loc2959 = loc2958 + 8;
    TagTyPacked tmpval6469 = *(TagTyPacked *) arg1479;
    CursorTy tmpcur6470 = arg1479 + 1;


  switch6489:
    ;
    switch (tmpval6469) {

      case 0:
        {
            CursorTy field_cur4414 = (CursorTy) tmpcur6470;
            CursorTy case2953 = (CursorTy) field_cur4414;
            SymTy tmpval6471 = *(SymTy *) case2953;
            CursorTy tmpcur6472 = case2953 + sizeof(SymTy);
            SymTy x1480 = (SymTy) tmpval6471;
            CursorTy end_x1480 = (CursorTy) tmpcur6472;
            CursorTy case2954 = (CursorTy) end_x1480;
            CursorTy x1481 = (CursorTy) case2954;
            CursorTy jump3683 = case2953 + 8;
            CursorCursorCursorCursorProd tmp_struct198 =
                                          _add_size_and_rel_offsets_ListSym(end_r2043, end_r2044, loc2959, x1481);
            CursorTy pvrtmp6473 = tmp_struct198.field0;
            CursorTy pvrtmp6474 = tmp_struct198.field1;
            CursorTy pvrtmp6475 = tmp_struct198.field2;
            CursorTy pvrtmp6476 = tmp_struct198.field3;
            CursorTy fltPrd5191 = (CursorTy) pvrtmp6475;
            CursorTy fltPrd5192 = (CursorTy) pvrtmp6476;
            CursorTy pvrtmp6478 = (CursorTy) fltPrd5192;
            CursorTy pvrtmp6477 = (CursorTy) fltPrd5191;
            CursorTy y1483 = (CursorTy) pvrtmp6477;
            CursorTy fltPrd5193 = (CursorTy) pvrtmp6475;
            CursorTy fltPrd5194 = (CursorTy) pvrtmp6476;
            CursorTy pvrtmp6480 = (CursorTy) fltPrd5194;
            CursorTy pvrtmp6479 = (CursorTy) fltPrd5193;
            CursorTy end_y1483 = (CursorTy) pvrtmp6480;
            CursorTy end_r2044_3828 = (CursorTy) pvrtmp6473;
            CursorTy endof3684 = (CursorTy) pvrtmp6474;

            *(TagTyPacked *) loc2042 = 0;

            CursorTy writetag4417 = loc2042 + 1;

            *(SymTy *) writetag4417 = x1480;

            CursorTy writecur4418 = writetag4417 + sizeof(SymTy);
            CursorTy writecur4419 = (CursorTy) end_y1483;
            CursorTy pvrtmp6482 = (CursorTy) writecur4419;
            CursorTy pvrtmp6481 = (CursorTy) loc2042;
            CursorTy taildc3685 = (CursorTy) pvrtmp6481;
            CursorTy end_taildc3685 = (CursorTy) pvrtmp6482;
            CursorTy pvrtmp6484 = (CursorTy) end_taildc3685;
            CursorTy pvrtmp6483 = (CursorTy) taildc3685;
            CursorTy fltPrd5195 = (CursorTy) pvrtmp6483;
            CursorTy fltPrd5196 = (CursorTy) pvrtmp6484;

            return (CursorCursorCursorCursorProd) {end_r2044_3828, endof3684,
                                                   fltPrd5195, fltPrd5196};
            break;
        }

      case 1:
        {
            CursorTy field_cur4421 = (CursorTy) tmpcur6470;
            CursorTy jump3686 = loc2041 + 1;

            *(TagTyPacked *) loc2042 = 1;

            CursorTy writetag4422 = loc2042 + 1;
            CursorTy pvrtmp6486 = (CursorTy) writetag4422;
            CursorTy pvrtmp6485 = (CursorTy) loc2042;
            CursorTy taildc3687 = (CursorTy) pvrtmp6485;
            CursorTy end_taildc3687 = (CursorTy) pvrtmp6486;
            CursorTy pvrtmp6488 = (CursorTy) end_taildc3687;
            CursorTy pvrtmp6487 = (CursorTy) taildc3687;
            CursorTy fltPrd5197 = (CursorTy) pvrtmp6487;
            CursorTy fltPrd5198 = (CursorTy) pvrtmp6488;

            return (CursorCursorCursorCursorProd) {end_r2044, jump3686,
                                                   fltPrd5197, fltPrd5198};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7444 = *(CursorTy *) tmpcur6470;
            CursorTy tmpaftercur7445 = tmpcur6470 + 8;
            TagTyPacked tagtmp7446 = *(TagTyPacked *) tmpcur7444;
            CursorTy tailtmp7447 = tmpcur7444 + 1;

            tmpval6469 = tagtmp7446;
            tmpcur6470 = tailtmp7447;
            goto switch6489;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7444 = *(CursorTy *) tmpcur6470;
            CursorTy tmpaftercur7445 = tmpcur6470 + 8;
            TagTyPacked tagtmp7446 = *(TagTyPacked *) tmpcur7444;
            CursorTy tailtmp7447 = tmpcur7444 + 1;

            tmpval6469 = tagtmp7446;
            tmpcur6470 = tailtmp7447;
            goto switch6489;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6469");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListExpr(CursorTy end_r2047,
                                                                CursorTy end_r2048,
                                                                CursorTy loc2046,
                                                                CursorTy arg1484)
{
    CursorTy loc2045 = (CursorTy) arg1484;

    if (loc2046 + 18 > end_r2048) {
        ChunkTy new_chunk204 = alloc_chunk(end_r2048);
        CursorTy chunk_start205 = new_chunk204.start_ptr;
        CursorTy chunk_end206 = new_chunk204.end_ptr;

        end_r2048 = chunk_end206;
        *(TagTyPacked *) loc2046 = 255;

        CursorTy redir = loc2046 + 1;

        *(CursorTy *) redir = chunk_start205;
        loc2046 = chunk_start205;
    }

    TagTyPacked tmpval6490 = *(TagTyPacked *) arg1484;
    CursorTy tmpcur6491 = arg1484 + 1;


  switch6516:
    ;
    switch (tmpval6490) {

      case 0:
        {
            CursorTy field_cur4424 = (CursorTy) tmpcur6491;
            CursorTy case2966 = (CursorTy) field_cur4424;
            CursorTy x1485 = (CursorTy) case2966;
            CursorTy loc2974 = loc2046 + 1;
            CursorCursorCursorCursorProd tmp_struct202 =
                                          _add_size_and_rel_offsets_Expr(end_r2047, end_r2048, loc2974, x1485);
            CursorTy pvrtmp6492 = tmp_struct202.field0;
            CursorTy pvrtmp6493 = tmp_struct202.field1;
            CursorTy pvrtmp6494 = tmp_struct202.field2;
            CursorTy pvrtmp6495 = tmp_struct202.field3;
            CursorTy fltPrd5199 = (CursorTy) pvrtmp6494;
            CursorTy fltPrd5200 = (CursorTy) pvrtmp6495;
            CursorTy pvrtmp6497 = (CursorTy) fltPrd5200;
            CursorTy pvrtmp6496 = (CursorTy) fltPrd5199;
            CursorTy y1487 = (CursorTy) pvrtmp6496;
            CursorTy fltPrd5201 = (CursorTy) pvrtmp6494;
            CursorTy fltPrd5202 = (CursorTy) pvrtmp6495;
            CursorTy pvrtmp6499 = (CursorTy) fltPrd5202;
            CursorTy pvrtmp6498 = (CursorTy) fltPrd5201;
            CursorTy end_y1487 = (CursorTy) pvrtmp6499;
            CursorTy end_r2048_3829 = (CursorTy) pvrtmp6492;
            CursorTy endof3688 = (CursorTy) pvrtmp6493;
            CursorTy case2967 = (CursorTy) endof3688;
            CursorTy x1486 = (CursorTy) case2967;
            CursorTy loc2975 = (CursorTy) end_y1487;
            CursorCursorCursorCursorProd tmp_struct203 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2047, end_r2048_3829, loc2975, x1486);
            CursorTy pvrtmp6500 = tmp_struct203.field0;
            CursorTy pvrtmp6501 = tmp_struct203.field1;
            CursorTy pvrtmp6502 = tmp_struct203.field2;
            CursorTy pvrtmp6503 = tmp_struct203.field3;
            CursorTy fltPrd5203 = (CursorTy) pvrtmp6502;
            CursorTy fltPrd5204 = (CursorTy) pvrtmp6503;
            CursorTy pvrtmp6505 = (CursorTy) fltPrd5204;
            CursorTy pvrtmp6504 = (CursorTy) fltPrd5203;
            CursorTy y1488 = (CursorTy) pvrtmp6504;
            CursorTy fltPrd5205 = (CursorTy) pvrtmp6502;
            CursorTy fltPrd5206 = (CursorTy) pvrtmp6503;
            CursorTy pvrtmp6507 = (CursorTy) fltPrd5206;
            CursorTy pvrtmp6506 = (CursorTy) fltPrd5205;
            CursorTy end_y1488 = (CursorTy) pvrtmp6507;
            CursorTy end_r2048_3829_3830 = (CursorTy) pvrtmp6500;
            CursorTy endof3689 = (CursorTy) pvrtmp6501;

            *(TagTyPacked *) loc2046 = 0;

            CursorTy writetag4427 = loc2046 + 1;
            CursorTy writecur4428 = (CursorTy) end_y1487;
            CursorTy writecur4429 = (CursorTy) end_y1488;
            CursorTy pvrtmp6509 = (CursorTy) writecur4429;
            CursorTy pvrtmp6508 = (CursorTy) loc2046;
            CursorTy taildc3690 = (CursorTy) pvrtmp6508;
            CursorTy end_taildc3690 = (CursorTy) pvrtmp6509;
            CursorTy pvrtmp6511 = (CursorTy) end_taildc3690;
            CursorTy pvrtmp6510 = (CursorTy) taildc3690;
            CursorTy fltPrd5207 = (CursorTy) pvrtmp6510;
            CursorTy fltPrd5208 = (CursorTy) pvrtmp6511;

            return (CursorCursorCursorCursorProd) {end_r2048_3829_3830,
                                                   endof3689, fltPrd5207,
                                                   fltPrd5208};
            break;
        }

      case 1:
        {
            CursorTy field_cur4431 = (CursorTy) tmpcur6491;
            CursorTy jump3691 = loc2045 + 1;

            *(TagTyPacked *) loc2046 = 1;

            CursorTy writetag4432 = loc2046 + 1;
            CursorTy pvrtmp6513 = (CursorTy) writetag4432;
            CursorTy pvrtmp6512 = (CursorTy) loc2046;
            CursorTy taildc3692 = (CursorTy) pvrtmp6512;
            CursorTy end_taildc3692 = (CursorTy) pvrtmp6513;
            CursorTy pvrtmp6515 = (CursorTy) end_taildc3692;
            CursorTy pvrtmp6514 = (CursorTy) taildc3692;
            CursorTy fltPrd5209 = (CursorTy) pvrtmp6514;
            CursorTy fltPrd5210 = (CursorTy) pvrtmp6515;

            return (CursorCursorCursorCursorProd) {end_r2048, jump3691,
                                                   fltPrd5209, fltPrd5210};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7448 = *(CursorTy *) tmpcur6491;
            CursorTy tmpaftercur7449 = tmpcur6491 + 8;
            TagTyPacked tagtmp7450 = *(TagTyPacked *) tmpcur7448;
            CursorTy tailtmp7451 = tmpcur7448 + 1;

            tmpval6490 = tagtmp7450;
            tmpcur6491 = tailtmp7451;
            goto switch6516;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7448 = *(CursorTy *) tmpcur6491;
            CursorTy tmpaftercur7449 = tmpcur6491 + 8;
            TagTyPacked tagtmp7450 = *(TagTyPacked *) tmpcur7448;
            CursorTy tailtmp7451 = tmpcur7448 + 1;

            tmpval6490 = tagtmp7450;
            tmpcur6491 = tailtmp7451;
            goto switch6516;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6490");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListToplvl(CursorTy end_r2051,
                                                                  CursorTy end_r2052,
                                                                  CursorTy loc2050,
                                                                  CursorTy arg1489)
{
    CursorTy loc2049 = (CursorTy) arg1489;

    if (loc2050 + 26 > end_r2052) {
        ChunkTy new_chunk209 = alloc_chunk(end_r2052);
        CursorTy chunk_start210 = new_chunk209.start_ptr;
        CursorTy chunk_end211 = new_chunk209.end_ptr;

        end_r2052 = chunk_end211;
        *(TagTyPacked *) loc2050 = 255;

        CursorTy redir = loc2050 + 1;

        *(CursorTy *) redir = chunk_start210;
        loc2050 = chunk_start210;
    }

    CursorTy loc2989 = loc2050 + 1;
    CursorTy loc2990 = loc2989 + 8;
    CursorTy loc2991 = loc2990 + 8;
    TagTyPacked tmpval6517 = *(TagTyPacked *) arg1489;
    CursorTy tmpcur6518 = arg1489 + 1;


  switch6543:
    ;
    switch (tmpval6517) {

      case 0:
        {
            CursorTy field_cur4434 = (CursorTy) tmpcur6518;
            CursorTy case2981 = (CursorTy) field_cur4434;
            CursorTy x1490 = (CursorTy) case2981;
            CursorCursorCursorCursorProd tmp_struct207 =
                                          _add_size_and_rel_offsets_Toplvl(end_r2051, end_r2052, loc2991, x1490);
            CursorTy pvrtmp6519 = tmp_struct207.field0;
            CursorTy pvrtmp6520 = tmp_struct207.field1;
            CursorTy pvrtmp6521 = tmp_struct207.field2;
            CursorTy pvrtmp6522 = tmp_struct207.field3;
            CursorTy fltPrd5211 = (CursorTy) pvrtmp6521;
            CursorTy fltPrd5212 = (CursorTy) pvrtmp6522;
            CursorTy pvrtmp6524 = (CursorTy) fltPrd5212;
            CursorTy pvrtmp6523 = (CursorTy) fltPrd5211;
            CursorTy y1492 = (CursorTy) pvrtmp6523;
            CursorTy fltPrd5213 = (CursorTy) pvrtmp6521;
            CursorTy fltPrd5214 = (CursorTy) pvrtmp6522;
            CursorTy pvrtmp6526 = (CursorTy) fltPrd5214;
            CursorTy pvrtmp6525 = (CursorTy) fltPrd5213;
            CursorTy end_y1492 = (CursorTy) pvrtmp6526;
            CursorTy end_r2052_3831 = (CursorTy) pvrtmp6519;
            CursorTy endof3693 = (CursorTy) pvrtmp6520;
            CursorTy case2982 = (CursorTy) endof3693;
            CursorTy x1491 = (CursorTy) case2982;
            CursorTy loc2992 = (CursorTy) end_y1492;
            CursorCursorCursorCursorProd tmp_struct208 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r2051, end_r2052_3831, loc2992, x1491);
            CursorTy pvrtmp6527 = tmp_struct208.field0;
            CursorTy pvrtmp6528 = tmp_struct208.field1;
            CursorTy pvrtmp6529 = tmp_struct208.field2;
            CursorTy pvrtmp6530 = tmp_struct208.field3;
            CursorTy fltPrd5215 = (CursorTy) pvrtmp6529;
            CursorTy fltPrd5216 = (CursorTy) pvrtmp6530;
            CursorTy pvrtmp6532 = (CursorTy) fltPrd5216;
            CursorTy pvrtmp6531 = (CursorTy) fltPrd5215;
            CursorTy y1493 = (CursorTy) pvrtmp6531;
            CursorTy fltPrd5217 = (CursorTy) pvrtmp6529;
            CursorTy fltPrd5218 = (CursorTy) pvrtmp6530;
            CursorTy pvrtmp6534 = (CursorTy) fltPrd5218;
            CursorTy pvrtmp6533 = (CursorTy) fltPrd5217;
            CursorTy end_y1493 = (CursorTy) pvrtmp6534;
            CursorTy end_r2052_3831_3832 = (CursorTy) pvrtmp6527;
            CursorTy endof3694 = (CursorTy) pvrtmp6528;
            IntTy sizeof_y1492_1494 = end_y1492 - y1492;
            IntTy sizeof_y1493_1495 = end_y1493 - y1493;
            IntTy fltPrm1902 = sizeof_y1492_1494 + 0;
            IntTy offset_1496 = 0 + fltPrm1902;
            IntTy fltPrm1903 = sizeof_y1492_1494 + sizeof_y1493_1495;
            IntTy size_dcon1497 = 9 + fltPrm1903;

            *(TagTyPacked *) loc2050 = 153;

            CursorTy writetag4437 = loc2050 + 1;

            *(IntTy *) writetag4437 = size_dcon1497;

            CursorTy writecur4438 = writetag4437 + sizeof(IntTy);

            *(IntTy *) writecur4438 = offset_1496;

            CursorTy writecur4439 = writecur4438 + sizeof(IntTy);
            CursorTy writecur4440 = (CursorTy) end_y1492;
            CursorTy writecur4441 = (CursorTy) end_y1493;
            CursorTy pvrtmp6536 = (CursorTy) writecur4441;
            CursorTy pvrtmp6535 = (CursorTy) loc2050;
            CursorTy taildc3695 = (CursorTy) pvrtmp6535;
            CursorTy end_taildc3695 = (CursorTy) pvrtmp6536;
            CursorTy pvrtmp6538 = (CursorTy) end_taildc3695;
            CursorTy pvrtmp6537 = (CursorTy) taildc3695;
            CursorTy fltPrd5219 = (CursorTy) pvrtmp6537;
            CursorTy fltPrd5220 = (CursorTy) pvrtmp6538;

            return (CursorCursorCursorCursorProd) {end_r2052_3831_3832,
                                                   endof3694, fltPrd5219,
                                                   fltPrd5220};
            break;
        }

      case 1:
        {
            CursorTy field_cur4443 = (CursorTy) tmpcur6518;
            CursorTy jump3696 = loc2049 + 1;

            *(TagTyPacked *) loc2050 = 1;

            CursorTy writetag4444 = loc2050 + 1;
            CursorTy pvrtmp6540 = (CursorTy) writetag4444;
            CursorTy pvrtmp6539 = (CursorTy) loc2050;
            CursorTy taildc3697 = (CursorTy) pvrtmp6539;
            CursorTy end_taildc3697 = (CursorTy) pvrtmp6540;
            CursorTy pvrtmp6542 = (CursorTy) end_taildc3697;
            CursorTy pvrtmp6541 = (CursorTy) taildc3697;
            CursorTy fltPrd5221 = (CursorTy) pvrtmp6541;
            CursorTy fltPrd5222 = (CursorTy) pvrtmp6542;

            return (CursorCursorCursorCursorProd) {end_r2052, jump3696,
                                                   fltPrd5221, fltPrd5222};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7452 = *(CursorTy *) tmpcur6518;
            CursorTy tmpaftercur7453 = tmpcur6518 + 8;
            TagTyPacked tagtmp7454 = *(TagTyPacked *) tmpcur7452;
            CursorTy tailtmp7455 = tmpcur7452 + 1;

            tmpval6517 = tagtmp7454;
            tmpcur6518 = tailtmp7455;
            goto switch6543;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7452 = *(CursorTy *) tmpcur6518;
            CursorTy tmpaftercur7453 = tmpcur6518 + 8;
            TagTyPacked tagtmp7454 = *(TagTyPacked *) tmpcur7452;
            CursorTy tailtmp7455 = tmpcur7452 + 1;

            tmpval6517 = tagtmp7454;
            tmpcur6518 = tailtmp7455;
            goto switch6543;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6517");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Formals(CursorTy end_r2055,
                                                               CursorTy end_r2056,
                                                               CursorTy loc2054,
                                                               CursorTy arg1498)
{
    CursorTy loc2053 = (CursorTy) arg1498;

    if (loc2054 + 18 > end_r2056) {
        ChunkTy new_chunk214 = alloc_chunk(end_r2056);
        CursorTy chunk_start215 = new_chunk214.start_ptr;
        CursorTy chunk_end216 = new_chunk214.end_ptr;

        end_r2056 = chunk_end216;
        *(TagTyPacked *) loc2054 = 255;

        CursorTy redir = loc2054 + 1;

        *(CursorTy *) redir = chunk_start215;
        loc2054 = chunk_start215;
    }

    TagTyPacked tmpval6544 = *(TagTyPacked *) arg1498;
    CursorTy tmpcur6545 = arg1498 + 1;


  switch6578:
    ;
    switch (tmpval6544) {

      case 0:
        {
            CursorTy field_cur4446 = (CursorTy) tmpcur6545;
            CursorTy case3002 = (CursorTy) field_cur4446;
            CursorTy x1499 = (CursorTy) case3002;
            CursorTy loc3006 = loc2054 + 1;
            CursorCursorCursorCursorProd tmp_struct212 =
                                          _add_size_and_rel_offsets_ListSym(end_r2055, end_r2056, loc3006, x1499);
            CursorTy pvrtmp6546 = tmp_struct212.field0;
            CursorTy pvrtmp6547 = tmp_struct212.field1;
            CursorTy pvrtmp6548 = tmp_struct212.field2;
            CursorTy pvrtmp6549 = tmp_struct212.field3;
            CursorTy fltPrd5223 = (CursorTy) pvrtmp6548;
            CursorTy fltPrd5224 = (CursorTy) pvrtmp6549;
            CursorTy pvrtmp6551 = (CursorTy) fltPrd5224;
            CursorTy pvrtmp6550 = (CursorTy) fltPrd5223;
            CursorTy y1500 = (CursorTy) pvrtmp6550;
            CursorTy fltPrd5225 = (CursorTy) pvrtmp6548;
            CursorTy fltPrd5226 = (CursorTy) pvrtmp6549;
            CursorTy pvrtmp6553 = (CursorTy) fltPrd5226;
            CursorTy pvrtmp6552 = (CursorTy) fltPrd5225;
            CursorTy end_y1500 = (CursorTy) pvrtmp6553;
            CursorTy end_r2056_3833 = (CursorTy) pvrtmp6546;
            CursorTy endof3698 = (CursorTy) pvrtmp6547;

            *(TagTyPacked *) loc2054 = 0;

            CursorTy writetag4448 = loc2054 + 1;
            CursorTy writecur4449 = (CursorTy) end_y1500;
            CursorTy pvrtmp6555 = (CursorTy) writecur4449;
            CursorTy pvrtmp6554 = (CursorTy) loc2054;
            CursorTy taildc3699 = (CursorTy) pvrtmp6554;
            CursorTy end_taildc3699 = (CursorTy) pvrtmp6555;
            CursorTy pvrtmp6557 = (CursorTy) end_taildc3699;
            CursorTy pvrtmp6556 = (CursorTy) taildc3699;
            CursorTy fltPrd5227 = (CursorTy) pvrtmp6556;
            CursorTy fltPrd5228 = (CursorTy) pvrtmp6557;

            return (CursorCursorCursorCursorProd) {end_r2056_3833, endof3698,
                                                   fltPrd5227, fltPrd5228};
            break;
        }

      case 1:
        {
            CursorTy field_cur4451 = (CursorTy) tmpcur6545;
            CursorTy case3008 = (CursorTy) field_cur4451;
            CursorTy x1501 = (CursorTy) case3008;
            CursorTy loc3013 = loc2054 + 1;
            CursorCursorCursorCursorProd tmp_struct213 =
                                          _add_size_and_rel_offsets_ListSym(end_r2055, end_r2056, loc3013, x1501);
            CursorTy pvrtmp6558 = tmp_struct213.field0;
            CursorTy pvrtmp6559 = tmp_struct213.field1;
            CursorTy pvrtmp6560 = tmp_struct213.field2;
            CursorTy pvrtmp6561 = tmp_struct213.field3;
            CursorTy fltPrd5229 = (CursorTy) pvrtmp6560;
            CursorTy fltPrd5230 = (CursorTy) pvrtmp6561;
            CursorTy pvrtmp6563 = (CursorTy) fltPrd5230;
            CursorTy pvrtmp6562 = (CursorTy) fltPrd5229;
            CursorTy y1503 = (CursorTy) pvrtmp6562;
            CursorTy fltPrd5231 = (CursorTy) pvrtmp6560;
            CursorTy fltPrd5232 = (CursorTy) pvrtmp6561;
            CursorTy pvrtmp6565 = (CursorTy) fltPrd5232;
            CursorTy pvrtmp6564 = (CursorTy) fltPrd5231;
            CursorTy end_y1503 = (CursorTy) pvrtmp6565;
            CursorTy end_r2056_3834 = (CursorTy) pvrtmp6558;
            CursorTy endof3701 = (CursorTy) pvrtmp6559;
            CursorTy case3009 = (CursorTy) endof3701;
            CursorTy jump3700 = case3009 + 8;
            SymTy tmpval6566 = *(SymTy *) case3009;
            CursorTy tmpcur6567 = case3009 + sizeof(SymTy);
            SymTy x1502 = (SymTy) tmpval6566;
            CursorTy end_x1502 = (CursorTy) tmpcur6567;

            *(TagTyPacked *) loc2054 = 1;

            CursorTy writetag4454 = loc2054 + 1;
            CursorTy writecur4455 = (CursorTy) end_y1503;

            *(SymTy *) writecur4455 = x1502;

            CursorTy writecur4456 = writecur4455 + sizeof(SymTy);
            CursorTy pvrtmp6569 = (CursorTy) writecur4456;
            CursorTy pvrtmp6568 = (CursorTy) loc2054;
            CursorTy taildc3702 = (CursorTy) pvrtmp6568;
            CursorTy end_taildc3702 = (CursorTy) pvrtmp6569;
            CursorTy pvrtmp6571 = (CursorTy) end_taildc3702;
            CursorTy pvrtmp6570 = (CursorTy) taildc3702;
            CursorTy fltPrd5233 = (CursorTy) pvrtmp6570;
            CursorTy fltPrd5234 = (CursorTy) pvrtmp6571;

            return (CursorCursorCursorCursorProd) {end_r2056_3834, jump3700,
                                                   fltPrd5233, fltPrd5234};
            break;
        }

      case 2:
        {
            CursorTy field_cur4458 = (CursorTy) tmpcur6545;
            CursorTy case3018 = (CursorTy) field_cur4458;
            SymTy tmpval6572 = *(SymTy *) case3018;
            CursorTy tmpcur6573 = case3018 + sizeof(SymTy);
            SymTy x1505 = (SymTy) tmpval6572;
            CursorTy end_x1505 = (CursorTy) tmpcur6573;
            CursorTy jump3703 = case3018 + 8;

            *(TagTyPacked *) loc2054 = 2;

            CursorTy writetag4460 = loc2054 + 1;

            *(SymTy *) writetag4460 = x1505;

            CursorTy writecur4461 = writetag4460 + sizeof(SymTy);
            CursorTy pvrtmp6575 = (CursorTy) writecur4461;
            CursorTy pvrtmp6574 = (CursorTy) loc2054;
            CursorTy taildc3704 = (CursorTy) pvrtmp6574;
            CursorTy end_taildc3704 = (CursorTy) pvrtmp6575;
            CursorTy pvrtmp6577 = (CursorTy) end_taildc3704;
            CursorTy pvrtmp6576 = (CursorTy) taildc3704;
            CursorTy fltPrd5235 = (CursorTy) pvrtmp6576;
            CursorTy fltPrd5236 = (CursorTy) pvrtmp6577;

            return (CursorCursorCursorCursorProd) {end_r2056, jump3703,
                                                   fltPrd5235, fltPrd5236};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7456 = *(CursorTy *) tmpcur6545;
            CursorTy tmpaftercur7457 = tmpcur6545 + 8;
            TagTyPacked tagtmp7458 = *(TagTyPacked *) tmpcur7456;
            CursorTy tailtmp7459 = tmpcur7456 + 1;

            tmpval6544 = tagtmp7458;
            tmpcur6545 = tailtmp7459;
            goto switch6578;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7456 = *(CursorTy *) tmpcur6545;
            CursorTy tmpaftercur7457 = tmpcur6545 + 8;
            TagTyPacked tagtmp7458 = *(TagTyPacked *) tmpcur7456;
            CursorTy tailtmp7459 = tmpcur7456 + 1;

            tmpval6544 = tagtmp7458;
            tmpcur6545 = tailtmp7459;
            goto switch6578;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6544");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Datum(CursorTy end_r2059,
                                                             CursorTy end_r2060,
                                                             CursorTy loc2058,
                                                             CursorTy arg1507)
{
    CursorTy loc2057 = (CursorTy) arg1507;

    if (loc2058 + 18 > end_r2060) {
        ChunkTy new_chunk217 = alloc_chunk(end_r2060);
        CursorTy chunk_start218 = new_chunk217.start_ptr;
        CursorTy chunk_end219 = new_chunk217.end_ptr;

        end_r2060 = chunk_end219;
        *(TagTyPacked *) loc2058 = 255;

        CursorTy redir = loc2058 + 1;

        *(CursorTy *) redir = chunk_start218;
        loc2058 = chunk_start218;
    }

    TagTyPacked tmpval6579 = *(TagTyPacked *) arg1507;
    CursorTy tmpcur6580 = arg1507 + 1;


  switch6587:
    ;
    switch (tmpval6579) {

      case 0:
        {
            CursorTy field_cur4463 = (CursorTy) tmpcur6580;
            CursorTy case3024 = (CursorTy) field_cur4463;
            IntTy tmpval6581 = *(IntTy *) case3024;
            CursorTy tmpcur6582 = case3024 + sizeof(IntTy);
            IntTy x1508 = (IntTy) tmpval6581;
            CursorTy end_x1508 = (CursorTy) tmpcur6582;
            CursorTy jump3705 = case3024 + 8;

            *(TagTyPacked *) loc2058 = 0;

            CursorTy writetag4465 = loc2058 + 1;

            *(IntTy *) writetag4465 = x1508;

            CursorTy writecur4466 = writetag4465 + sizeof(IntTy);
            CursorTy pvrtmp6584 = (CursorTy) writecur4466;
            CursorTy pvrtmp6583 = (CursorTy) loc2058;
            CursorTy taildc3706 = (CursorTy) pvrtmp6583;
            CursorTy end_taildc3706 = (CursorTy) pvrtmp6584;
            CursorTy pvrtmp6586 = (CursorTy) end_taildc3706;
            CursorTy pvrtmp6585 = (CursorTy) taildc3706;
            CursorTy fltPrd5237 = (CursorTy) pvrtmp6585;
            CursorTy fltPrd5238 = (CursorTy) pvrtmp6586;

            return (CursorCursorCursorCursorProd) {end_r2060, jump3705,
                                                   fltPrd5237, fltPrd5238};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7460 = *(CursorTy *) tmpcur6580;
            CursorTy tmpaftercur7461 = tmpcur6580 + 8;
            TagTyPacked tagtmp7462 = *(TagTyPacked *) tmpcur7460;
            CursorTy tailtmp7463 = tmpcur7460 + 1;

            tmpval6579 = tagtmp7462;
            tmpcur6580 = tailtmp7463;
            goto switch6587;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7460 = *(CursorTy *) tmpcur6580;
            CursorTy tmpaftercur7461 = tmpcur6580 + 8;
            TagTyPacked tagtmp7462 = *(TagTyPacked *) tmpcur7460;
            CursorTy tailtmp7463 = tmpcur7460 + 1;

            tmpval6579 = tagtmp7462;
            tmpcur6580 = tailtmp7463;
            goto switch6587;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6579");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LAMBDACASE(CursorTy end_r2063,
                                                                  CursorTy end_r2064,
                                                                  CursorTy loc2062,
                                                                  CursorTy arg1510)
{
    CursorTy loc2061 = (CursorTy) arg1510;

    if (loc2062 + 18 > end_r2064) {
        ChunkTy new_chunk223 = alloc_chunk(end_r2064);
        CursorTy chunk_start224 = new_chunk223.start_ptr;
        CursorTy chunk_end225 = new_chunk223.end_ptr;

        end_r2064 = chunk_end225;
        *(TagTyPacked *) loc2062 = 255;

        CursorTy redir = loc2062 + 1;

        *(CursorTy *) redir = chunk_start224;
        loc2062 = chunk_start224;
    }

    TagTyPacked tmpval6588 = *(TagTyPacked *) arg1510;
    CursorTy tmpcur6589 = arg1510 + 1;


  switch6622:
    ;
    switch (tmpval6588) {

      case 0:
        {
            CursorTy field_cur4468 = (CursorTy) tmpcur6589;
            CursorTy case3030 = (CursorTy) field_cur4468;
            CursorTy x1511 = (CursorTy) case3030;
            CursorTy loc3042 = loc2062 + 1;
            CursorCursorCursorCursorProd tmp_struct220 =
                                          _add_size_and_rel_offsets_Formals(end_r2063, end_r2064, loc3042, x1511);
            CursorTy pvrtmp6590 = tmp_struct220.field0;
            CursorTy pvrtmp6591 = tmp_struct220.field1;
            CursorTy pvrtmp6592 = tmp_struct220.field2;
            CursorTy pvrtmp6593 = tmp_struct220.field3;
            CursorTy fltPrd5239 = (CursorTy) pvrtmp6592;
            CursorTy fltPrd5240 = (CursorTy) pvrtmp6593;
            CursorTy pvrtmp6595 = (CursorTy) fltPrd5240;
            CursorTy pvrtmp6594 = (CursorTy) fltPrd5239;
            CursorTy y1514 = (CursorTy) pvrtmp6594;
            CursorTy fltPrd5241 = (CursorTy) pvrtmp6592;
            CursorTy fltPrd5242 = (CursorTy) pvrtmp6593;
            CursorTy pvrtmp6597 = (CursorTy) fltPrd5242;
            CursorTy pvrtmp6596 = (CursorTy) fltPrd5241;
            CursorTy end_y1514 = (CursorTy) pvrtmp6597;
            CursorTy end_r2064_3835 = (CursorTy) pvrtmp6590;
            CursorTy endof3707 = (CursorTy) pvrtmp6591;
            CursorTy case3031 = (CursorTy) endof3707;
            CursorTy x1512 = (CursorTy) case3031;
            CursorTy loc3043 = (CursorTy) end_y1514;
            CursorCursorCursorCursorProd tmp_struct221 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2063, end_r2064_3835, loc3043, x1512);
            CursorTy pvrtmp6598 = tmp_struct221.field0;
            CursorTy pvrtmp6599 = tmp_struct221.field1;
            CursorTy pvrtmp6600 = tmp_struct221.field2;
            CursorTy pvrtmp6601 = tmp_struct221.field3;
            CursorTy fltPrd5243 = (CursorTy) pvrtmp6600;
            CursorTy fltPrd5244 = (CursorTy) pvrtmp6601;
            CursorTy pvrtmp6603 = (CursorTy) fltPrd5244;
            CursorTy pvrtmp6602 = (CursorTy) fltPrd5243;
            CursorTy y1515 = (CursorTy) pvrtmp6602;
            CursorTy fltPrd5245 = (CursorTy) pvrtmp6600;
            CursorTy fltPrd5246 = (CursorTy) pvrtmp6601;
            CursorTy pvrtmp6605 = (CursorTy) fltPrd5246;
            CursorTy pvrtmp6604 = (CursorTy) fltPrd5245;
            CursorTy end_y1515 = (CursorTy) pvrtmp6605;
            CursorTy end_r2064_3835_3836 = (CursorTy) pvrtmp6598;
            CursorTy endof3708 = (CursorTy) pvrtmp6599;
            CursorTy case3032 = (CursorTy) endof3708;
            CursorTy x1513 = (CursorTy) case3032;
            CursorTy loc3044 = (CursorTy) end_y1515;
            CursorCursorCursorCursorProd tmp_struct222 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r2063, end_r2064_3835_3836, loc3044, x1513);
            CursorTy pvrtmp6606 = tmp_struct222.field0;
            CursorTy pvrtmp6607 = tmp_struct222.field1;
            CursorTy pvrtmp6608 = tmp_struct222.field2;
            CursorTy pvrtmp6609 = tmp_struct222.field3;
            CursorTy fltPrd5247 = (CursorTy) pvrtmp6608;
            CursorTy fltPrd5248 = (CursorTy) pvrtmp6609;
            CursorTy pvrtmp6611 = (CursorTy) fltPrd5248;
            CursorTy pvrtmp6610 = (CursorTy) fltPrd5247;
            CursorTy y1516 = (CursorTy) pvrtmp6610;
            CursorTy fltPrd5249 = (CursorTy) pvrtmp6608;
            CursorTy fltPrd5250 = (CursorTy) pvrtmp6609;
            CursorTy pvrtmp6613 = (CursorTy) fltPrd5250;
            CursorTy pvrtmp6612 = (CursorTy) fltPrd5249;
            CursorTy end_y1516 = (CursorTy) pvrtmp6613;
            CursorTy end_r2064_3835_3836_3837 = (CursorTy) pvrtmp6606;
            CursorTy endof3709 = (CursorTy) pvrtmp6607;

            *(TagTyPacked *) loc2062 = 0;

            CursorTy writetag4472 = loc2062 + 1;
            CursorTy writecur4473 = (CursorTy) end_y1514;
            CursorTy writecur4474 = (CursorTy) end_y1515;
            CursorTy writecur4475 = (CursorTy) end_y1516;
            CursorTy pvrtmp6615 = (CursorTy) writecur4475;
            CursorTy pvrtmp6614 = (CursorTy) loc2062;
            CursorTy taildc3710 = (CursorTy) pvrtmp6614;
            CursorTy end_taildc3710 = (CursorTy) pvrtmp6615;
            CursorTy pvrtmp6617 = (CursorTy) end_taildc3710;
            CursorTy pvrtmp6616 = (CursorTy) taildc3710;
            CursorTy fltPrd5251 = (CursorTy) pvrtmp6616;
            CursorTy fltPrd5252 = (CursorTy) pvrtmp6617;

            return (CursorCursorCursorCursorProd) {end_r2064_3835_3836_3837,
                                                   endof3709, fltPrd5251,
                                                   fltPrd5252};
            break;
        }

      case 1:
        {
            CursorTy field_cur4477 = (CursorTy) tmpcur6589;
            CursorTy jump3711 = loc2061 + 1;

            *(TagTyPacked *) loc2062 = 1;

            CursorTy writetag4478 = loc2062 + 1;
            CursorTy pvrtmp6619 = (CursorTy) writetag4478;
            CursorTy pvrtmp6618 = (CursorTy) loc2062;
            CursorTy taildc3712 = (CursorTy) pvrtmp6618;
            CursorTy end_taildc3712 = (CursorTy) pvrtmp6619;
            CursorTy pvrtmp6621 = (CursorTy) end_taildc3712;
            CursorTy pvrtmp6620 = (CursorTy) taildc3712;
            CursorTy fltPrd5253 = (CursorTy) pvrtmp6620;
            CursorTy fltPrd5254 = (CursorTy) pvrtmp6621;

            return (CursorCursorCursorCursorProd) {end_r2064, jump3711,
                                                   fltPrd5253, fltPrd5254};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7464 = *(CursorTy *) tmpcur6589;
            CursorTy tmpaftercur7465 = tmpcur6589 + 8;
            TagTyPacked tagtmp7466 = *(TagTyPacked *) tmpcur7464;
            CursorTy tailtmp7467 = tmpcur7464 + 1;

            tmpval6588 = tagtmp7466;
            tmpcur6589 = tailtmp7467;
            goto switch6622;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7464 = *(CursorTy *) tmpcur6589;
            CursorTy tmpaftercur7465 = tmpcur6589 + 8;
            TagTyPacked tagtmp7466 = *(TagTyPacked *) tmpcur7464;
            CursorTy tailtmp7467 = tmpcur7464 + 1;

            tmpval6588 = tagtmp7466;
            tmpcur6589 = tailtmp7467;
            goto switch6622;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6588");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LVBIND(CursorTy end_r2067,
                                                              CursorTy end_r2068,
                                                              CursorTy loc2066,
                                                              CursorTy arg1517)
{
    CursorTy loc2065 = (CursorTy) arg1517;

    if (loc2066 + 18 > end_r2068) {
        ChunkTy new_chunk229 = alloc_chunk(end_r2068);
        CursorTy chunk_start230 = new_chunk229.start_ptr;
        CursorTy chunk_end231 = new_chunk229.end_ptr;

        end_r2068 = chunk_end231;
        *(TagTyPacked *) loc2066 = 255;

        CursorTy redir = loc2066 + 1;

        *(CursorTy *) redir = chunk_start230;
        loc2066 = chunk_start230;
    }

    TagTyPacked tmpval6623 = *(TagTyPacked *) arg1517;
    CursorTy tmpcur6624 = arg1517 + 1;


  switch6657:
    ;
    switch (tmpval6623) {

      case 0:
        {
            CursorTy field_cur4480 = (CursorTy) tmpcur6624;
            CursorTy case3051 = (CursorTy) field_cur4480;
            CursorTy x1518 = (CursorTy) case3051;
            CursorTy loc3063 = loc2066 + 1;
            CursorCursorCursorCursorProd tmp_struct226 =
                                          _add_size_and_rel_offsets_ListSym(end_r2067, end_r2068, loc3063, x1518);
            CursorTy pvrtmp6625 = tmp_struct226.field0;
            CursorTy pvrtmp6626 = tmp_struct226.field1;
            CursorTy pvrtmp6627 = tmp_struct226.field2;
            CursorTy pvrtmp6628 = tmp_struct226.field3;
            CursorTy fltPrd5255 = (CursorTy) pvrtmp6627;
            CursorTy fltPrd5256 = (CursorTy) pvrtmp6628;
            CursorTy pvrtmp6630 = (CursorTy) fltPrd5256;
            CursorTy pvrtmp6629 = (CursorTy) fltPrd5255;
            CursorTy y1521 = (CursorTy) pvrtmp6629;
            CursorTy fltPrd5257 = (CursorTy) pvrtmp6627;
            CursorTy fltPrd5258 = (CursorTy) pvrtmp6628;
            CursorTy pvrtmp6632 = (CursorTy) fltPrd5258;
            CursorTy pvrtmp6631 = (CursorTy) fltPrd5257;
            CursorTy end_y1521 = (CursorTy) pvrtmp6632;
            CursorTy end_r2068_3838 = (CursorTy) pvrtmp6625;
            CursorTy endof3713 = (CursorTy) pvrtmp6626;
            CursorTy case3052 = (CursorTy) endof3713;
            CursorTy x1519 = (CursorTy) case3052;
            CursorTy loc3064 = (CursorTy) end_y1521;
            CursorCursorCursorCursorProd tmp_struct227 =
                                          _add_size_and_rel_offsets_Expr(end_r2067, end_r2068_3838, loc3064, x1519);
            CursorTy pvrtmp6633 = tmp_struct227.field0;
            CursorTy pvrtmp6634 = tmp_struct227.field1;
            CursorTy pvrtmp6635 = tmp_struct227.field2;
            CursorTy pvrtmp6636 = tmp_struct227.field3;
            CursorTy fltPrd5259 = (CursorTy) pvrtmp6635;
            CursorTy fltPrd5260 = (CursorTy) pvrtmp6636;
            CursorTy pvrtmp6638 = (CursorTy) fltPrd5260;
            CursorTy pvrtmp6637 = (CursorTy) fltPrd5259;
            CursorTy y1522 = (CursorTy) pvrtmp6637;
            CursorTy fltPrd5261 = (CursorTy) pvrtmp6635;
            CursorTy fltPrd5262 = (CursorTy) pvrtmp6636;
            CursorTy pvrtmp6640 = (CursorTy) fltPrd5262;
            CursorTy pvrtmp6639 = (CursorTy) fltPrd5261;
            CursorTy end_y1522 = (CursorTy) pvrtmp6640;
            CursorTy end_r2068_3838_3839 = (CursorTy) pvrtmp6633;
            CursorTy endof3714 = (CursorTy) pvrtmp6634;
            CursorTy case3053 = (CursorTy) endof3714;
            CursorTy x1520 = (CursorTy) case3053;
            CursorTy loc3065 = (CursorTy) end_y1522;
            CursorCursorCursorCursorProd tmp_struct228 =
                                          _add_size_and_rel_offsets_LVBIND(end_r2067, end_r2068_3838_3839, loc3065, x1520);
            CursorTy pvrtmp6641 = tmp_struct228.field0;
            CursorTy pvrtmp6642 = tmp_struct228.field1;
            CursorTy pvrtmp6643 = tmp_struct228.field2;
            CursorTy pvrtmp6644 = tmp_struct228.field3;
            CursorTy fltPrd5263 = (CursorTy) pvrtmp6643;
            CursorTy fltPrd5264 = (CursorTy) pvrtmp6644;
            CursorTy pvrtmp6646 = (CursorTy) fltPrd5264;
            CursorTy pvrtmp6645 = (CursorTy) fltPrd5263;
            CursorTy y1523 = (CursorTy) pvrtmp6645;
            CursorTy fltPrd5265 = (CursorTy) pvrtmp6643;
            CursorTy fltPrd5266 = (CursorTy) pvrtmp6644;
            CursorTy pvrtmp6648 = (CursorTy) fltPrd5266;
            CursorTy pvrtmp6647 = (CursorTy) fltPrd5265;
            CursorTy end_y1523 = (CursorTy) pvrtmp6648;
            CursorTy end_r2068_3838_3839_3840 = (CursorTy) pvrtmp6641;
            CursorTy endof3715 = (CursorTy) pvrtmp6642;

            *(TagTyPacked *) loc2066 = 0;

            CursorTy writetag4484 = loc2066 + 1;
            CursorTy writecur4485 = (CursorTy) end_y1521;
            CursorTy writecur4486 = (CursorTy) end_y1522;
            CursorTy writecur4487 = (CursorTy) end_y1523;
            CursorTy pvrtmp6650 = (CursorTy) writecur4487;
            CursorTy pvrtmp6649 = (CursorTy) loc2066;
            CursorTy taildc3716 = (CursorTy) pvrtmp6649;
            CursorTy end_taildc3716 = (CursorTy) pvrtmp6650;
            CursorTy pvrtmp6652 = (CursorTy) end_taildc3716;
            CursorTy pvrtmp6651 = (CursorTy) taildc3716;
            CursorTy fltPrd5267 = (CursorTy) pvrtmp6651;
            CursorTy fltPrd5268 = (CursorTy) pvrtmp6652;

            return (CursorCursorCursorCursorProd) {end_r2068_3838_3839_3840,
                                                   endof3715, fltPrd5267,
                                                   fltPrd5268};
            break;
        }

      case 1:
        {
            CursorTy field_cur4489 = (CursorTy) tmpcur6624;
            CursorTy jump3717 = loc2065 + 1;

            *(TagTyPacked *) loc2066 = 1;

            CursorTy writetag4490 = loc2066 + 1;
            CursorTy pvrtmp6654 = (CursorTy) writetag4490;
            CursorTy pvrtmp6653 = (CursorTy) loc2066;
            CursorTy taildc3718 = (CursorTy) pvrtmp6653;
            CursorTy end_taildc3718 = (CursorTy) pvrtmp6654;
            CursorTy pvrtmp6656 = (CursorTy) end_taildc3718;
            CursorTy pvrtmp6655 = (CursorTy) taildc3718;
            CursorTy fltPrd5269 = (CursorTy) pvrtmp6655;
            CursorTy fltPrd5270 = (CursorTy) pvrtmp6656;

            return (CursorCursorCursorCursorProd) {end_r2068, jump3717,
                                                   fltPrd5269, fltPrd5270};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7468 = *(CursorTy *) tmpcur6624;
            CursorTy tmpaftercur7469 = tmpcur6624 + 8;
            TagTyPacked tagtmp7470 = *(TagTyPacked *) tmpcur7468;
            CursorTy tailtmp7471 = tmpcur7468 + 1;

            tmpval6623 = tagtmp7470;
            tmpcur6624 = tailtmp7471;
            goto switch6657;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7468 = *(CursorTy *) tmpcur6624;
            CursorTy tmpaftercur7469 = tmpcur6624 + 8;
            TagTyPacked tagtmp7470 = *(TagTyPacked *) tmpcur7468;
            CursorTy tailtmp7471 = tmpcur7468 + 1;

            tmpval6623 = tagtmp7470;
            tmpcur6624 = tailtmp7471;
            goto switch6657;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6623");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Expr(CursorTy end_r2071,
                                                            CursorTy end_r2072,
                                                            CursorTy loc2070,
                                                            CursorTy arg1524)
{
    CursorTy loc2069 = (CursorTy) arg1524;

    if (loc2070 + 18 > end_r2072) {
        ChunkTy new_chunk254 = alloc_chunk(end_r2072);
        CursorTy chunk_start255 = new_chunk254.start_ptr;
        CursorTy chunk_end256 = new_chunk254.end_ptr;

        end_r2072 = chunk_end256;
        *(TagTyPacked *) loc2070 = 255;

        CursorTy redir = loc2070 + 1;

        *(CursorTy *) redir = chunk_start255;
        loc2070 = chunk_start255;
    }

    CursorTy loc3159 = loc2070 + 1;
    CursorTy loc3160 = loc3159 + 8;
    TagTyPacked tmpval6658 = *(TagTyPacked *) arg1524;
    CursorTy tmpcur6659 = arg1524 + 1;


  switch6918:
    ;
    switch (tmpval6658) {

      case 0:
        {
            CursorTy field_cur4492 = (CursorTy) tmpcur6659;
            CursorTy case3072 = (CursorTy) field_cur4492;
            SymTy tmpval6660 = *(SymTy *) case3072;
            CursorTy tmpcur6661 = case3072 + sizeof(SymTy);
            SymTy x1525 = (SymTy) tmpval6660;
            CursorTy end_x1525 = (CursorTy) tmpcur6661;
            CursorTy jump3719 = case3072 + 8;

            *(TagTyPacked *) loc2070 = 0;

            CursorTy writetag4494 = loc2070 + 1;

            *(SymTy *) writetag4494 = x1525;

            CursorTy writecur4495 = writetag4494 + sizeof(SymTy);
            CursorTy pvrtmp6663 = (CursorTy) writecur4495;
            CursorTy pvrtmp6662 = (CursorTy) loc2070;
            CursorTy taildc3720 = (CursorTy) pvrtmp6662;
            CursorTy end_taildc3720 = (CursorTy) pvrtmp6663;
            CursorTy pvrtmp6665 = (CursorTy) end_taildc3720;
            CursorTy pvrtmp6664 = (CursorTy) taildc3720;
            CursorTy fltPrd5271 = (CursorTy) pvrtmp6664;
            CursorTy fltPrd5272 = (CursorTy) pvrtmp6665;

            return (CursorCursorCursorCursorProd) {end_r2072, jump3719,
                                                   fltPrd5271, fltPrd5272};
            break;
        }

      case 1:
        {
            CursorTy field_cur4497 = (CursorTy) tmpcur6659;
            CursorTy case3076 = (CursorTy) field_cur4497;
            CursorTy x1527 = (CursorTy) case3076;
            CursorTy loc3084 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct232 =
                                          _add_size_and_rel_offsets_Formals(end_r2071, end_r2072, loc3084, x1527);
            CursorTy pvrtmp6666 = tmp_struct232.field0;
            CursorTy pvrtmp6667 = tmp_struct232.field1;
            CursorTy pvrtmp6668 = tmp_struct232.field2;
            CursorTy pvrtmp6669 = tmp_struct232.field3;
            CursorTy fltPrd5273 = (CursorTy) pvrtmp6668;
            CursorTy fltPrd5274 = (CursorTy) pvrtmp6669;
            CursorTy pvrtmp6671 = (CursorTy) fltPrd5274;
            CursorTy pvrtmp6670 = (CursorTy) fltPrd5273;
            CursorTy y1529 = (CursorTy) pvrtmp6670;
            CursorTy fltPrd5275 = (CursorTy) pvrtmp6668;
            CursorTy fltPrd5276 = (CursorTy) pvrtmp6669;
            CursorTy pvrtmp6673 = (CursorTy) fltPrd5276;
            CursorTy pvrtmp6672 = (CursorTy) fltPrd5275;
            CursorTy end_y1529 = (CursorTy) pvrtmp6673;
            CursorTy end_r2072_3841 = (CursorTy) pvrtmp6666;
            CursorTy endof3721 = (CursorTy) pvrtmp6667;
            CursorTy case3077 = (CursorTy) endof3721;
            CursorTy x1528 = (CursorTy) case3077;
            CursorTy loc3085 = (CursorTy) end_y1529;
            CursorCursorCursorCursorProd tmp_struct233 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2071, end_r2072_3841, loc3085, x1528);
            CursorTy pvrtmp6674 = tmp_struct233.field0;
            CursorTy pvrtmp6675 = tmp_struct233.field1;
            CursorTy pvrtmp6676 = tmp_struct233.field2;
            CursorTy pvrtmp6677 = tmp_struct233.field3;
            CursorTy fltPrd5277 = (CursorTy) pvrtmp6676;
            CursorTy fltPrd5278 = (CursorTy) pvrtmp6677;
            CursorTy pvrtmp6679 = (CursorTy) fltPrd5278;
            CursorTy pvrtmp6678 = (CursorTy) fltPrd5277;
            CursorTy y1530 = (CursorTy) pvrtmp6678;
            CursorTy fltPrd5279 = (CursorTy) pvrtmp6676;
            CursorTy fltPrd5280 = (CursorTy) pvrtmp6677;
            CursorTy pvrtmp6681 = (CursorTy) fltPrd5280;
            CursorTy pvrtmp6680 = (CursorTy) fltPrd5279;
            CursorTy end_y1530 = (CursorTy) pvrtmp6681;
            CursorTy end_r2072_3841_3842 = (CursorTy) pvrtmp6674;
            CursorTy endof3722 = (CursorTy) pvrtmp6675;

            *(TagTyPacked *) loc2070 = 1;

            CursorTy writetag4500 = loc2070 + 1;
            CursorTy writecur4501 = (CursorTy) end_y1529;
            CursorTy writecur4502 = (CursorTy) end_y1530;
            CursorTy pvrtmp6683 = (CursorTy) writecur4502;
            CursorTy pvrtmp6682 = (CursorTy) loc2070;
            CursorTy taildc3723 = (CursorTy) pvrtmp6682;
            CursorTy end_taildc3723 = (CursorTy) pvrtmp6683;
            CursorTy pvrtmp6685 = (CursorTy) end_taildc3723;
            CursorTy pvrtmp6684 = (CursorTy) taildc3723;
            CursorTy fltPrd5281 = (CursorTy) pvrtmp6684;
            CursorTy fltPrd5282 = (CursorTy) pvrtmp6685;

            return (CursorCursorCursorCursorProd) {end_r2072_3841_3842,
                                                   endof3722, fltPrd5281,
                                                   fltPrd5282};
            break;
        }

      case 2:
        {
            CursorTy field_cur4504 = (CursorTy) tmpcur6659;
            CursorTy case3088 = (CursorTy) field_cur4504;
            CursorTy x1531 = (CursorTy) case3088;
            CursorTy loc3092 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct234 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r2071, end_r2072, loc3092, x1531);
            CursorTy pvrtmp6686 = tmp_struct234.field0;
            CursorTy pvrtmp6687 = tmp_struct234.field1;
            CursorTy pvrtmp6688 = tmp_struct234.field2;
            CursorTy pvrtmp6689 = tmp_struct234.field3;
            CursorTy fltPrd5283 = (CursorTy) pvrtmp6688;
            CursorTy fltPrd5284 = (CursorTy) pvrtmp6689;
            CursorTy pvrtmp6691 = (CursorTy) fltPrd5284;
            CursorTy pvrtmp6690 = (CursorTy) fltPrd5283;
            CursorTy y1532 = (CursorTy) pvrtmp6690;
            CursorTy fltPrd5285 = (CursorTy) pvrtmp6688;
            CursorTy fltPrd5286 = (CursorTy) pvrtmp6689;
            CursorTy pvrtmp6693 = (CursorTy) fltPrd5286;
            CursorTy pvrtmp6692 = (CursorTy) fltPrd5285;
            CursorTy end_y1532 = (CursorTy) pvrtmp6693;
            CursorTy end_r2072_3843 = (CursorTy) pvrtmp6686;
            CursorTy endof3724 = (CursorTy) pvrtmp6687;

            *(TagTyPacked *) loc2070 = 2;

            CursorTy writetag4506 = loc2070 + 1;
            CursorTy writecur4507 = (CursorTy) end_y1532;
            CursorTy pvrtmp6695 = (CursorTy) writecur4507;
            CursorTy pvrtmp6694 = (CursorTy) loc2070;
            CursorTy taildc3725 = (CursorTy) pvrtmp6694;
            CursorTy end_taildc3725 = (CursorTy) pvrtmp6695;
            CursorTy pvrtmp6697 = (CursorTy) end_taildc3725;
            CursorTy pvrtmp6696 = (CursorTy) taildc3725;
            CursorTy fltPrd5287 = (CursorTy) pvrtmp6696;
            CursorTy fltPrd5288 = (CursorTy) pvrtmp6697;

            return (CursorCursorCursorCursorProd) {end_r2072_3843, endof3724,
                                                   fltPrd5287, fltPrd5288};
            break;
        }

      case 3:
        {
            CursorTy field_cur4509 = (CursorTy) tmpcur6659;
            CursorTy case3094 = (CursorTy) field_cur4509;
            CursorTy x1533 = (CursorTy) case3094;
            CursorTy loc3106 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct235 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072, loc3106, x1533);
            CursorTy pvrtmp6698 = tmp_struct235.field0;
            CursorTy pvrtmp6699 = tmp_struct235.field1;
            CursorTy pvrtmp6700 = tmp_struct235.field2;
            CursorTy pvrtmp6701 = tmp_struct235.field3;
            CursorTy fltPrd5289 = (CursorTy) pvrtmp6700;
            CursorTy fltPrd5290 = (CursorTy) pvrtmp6701;
            CursorTy pvrtmp6703 = (CursorTy) fltPrd5290;
            CursorTy pvrtmp6702 = (CursorTy) fltPrd5289;
            CursorTy y1536 = (CursorTy) pvrtmp6702;
            CursorTy fltPrd5291 = (CursorTy) pvrtmp6700;
            CursorTy fltPrd5292 = (CursorTy) pvrtmp6701;
            CursorTy pvrtmp6705 = (CursorTy) fltPrd5292;
            CursorTy pvrtmp6704 = (CursorTy) fltPrd5291;
            CursorTy end_y1536 = (CursorTy) pvrtmp6705;
            CursorTy end_r2072_3844 = (CursorTy) pvrtmp6698;
            CursorTy endof3726 = (CursorTy) pvrtmp6699;
            CursorTy case3095 = (CursorTy) endof3726;
            CursorTy x1534 = (CursorTy) case3095;
            CursorTy loc3107 = (CursorTy) end_y1536;
            CursorCursorCursorCursorProd tmp_struct236 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072_3844, loc3107, x1534);
            CursorTy pvrtmp6706 = tmp_struct236.field0;
            CursorTy pvrtmp6707 = tmp_struct236.field1;
            CursorTy pvrtmp6708 = tmp_struct236.field2;
            CursorTy pvrtmp6709 = tmp_struct236.field3;
            CursorTy fltPrd5293 = (CursorTy) pvrtmp6708;
            CursorTy fltPrd5294 = (CursorTy) pvrtmp6709;
            CursorTy pvrtmp6711 = (CursorTy) fltPrd5294;
            CursorTy pvrtmp6710 = (CursorTy) fltPrd5293;
            CursorTy y1537 = (CursorTy) pvrtmp6710;
            CursorTy fltPrd5295 = (CursorTy) pvrtmp6708;
            CursorTy fltPrd5296 = (CursorTy) pvrtmp6709;
            CursorTy pvrtmp6713 = (CursorTy) fltPrd5296;
            CursorTy pvrtmp6712 = (CursorTy) fltPrd5295;
            CursorTy end_y1537 = (CursorTy) pvrtmp6713;
            CursorTy end_r2072_3844_3845 = (CursorTy) pvrtmp6706;
            CursorTy endof3727 = (CursorTy) pvrtmp6707;
            CursorTy case3096 = (CursorTy) endof3727;
            CursorTy x1535 = (CursorTy) case3096;
            CursorTy loc3108 = (CursorTy) end_y1537;
            CursorCursorCursorCursorProd tmp_struct237 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072_3844_3845, loc3108, x1535);
            CursorTy pvrtmp6714 = tmp_struct237.field0;
            CursorTy pvrtmp6715 = tmp_struct237.field1;
            CursorTy pvrtmp6716 = tmp_struct237.field2;
            CursorTy pvrtmp6717 = tmp_struct237.field3;
            CursorTy fltPrd5297 = (CursorTy) pvrtmp6716;
            CursorTy fltPrd5298 = (CursorTy) pvrtmp6717;
            CursorTy pvrtmp6719 = (CursorTy) fltPrd5298;
            CursorTy pvrtmp6718 = (CursorTy) fltPrd5297;
            CursorTy y1538 = (CursorTy) pvrtmp6718;
            CursorTy fltPrd5299 = (CursorTy) pvrtmp6716;
            CursorTy fltPrd5300 = (CursorTy) pvrtmp6717;
            CursorTy pvrtmp6721 = (CursorTy) fltPrd5300;
            CursorTy pvrtmp6720 = (CursorTy) fltPrd5299;
            CursorTy end_y1538 = (CursorTy) pvrtmp6721;
            CursorTy end_r2072_3844_3845_3846 = (CursorTy) pvrtmp6714;
            CursorTy endof3728 = (CursorTy) pvrtmp6715;

            *(TagTyPacked *) loc2070 = 3;

            CursorTy writetag4513 = loc2070 + 1;
            CursorTy writecur4514 = (CursorTy) end_y1536;
            CursorTy writecur4515 = (CursorTy) end_y1537;
            CursorTy writecur4516 = (CursorTy) end_y1538;
            CursorTy pvrtmp6723 = (CursorTy) writecur4516;
            CursorTy pvrtmp6722 = (CursorTy) loc2070;
            CursorTy taildc3729 = (CursorTy) pvrtmp6722;
            CursorTy end_taildc3729 = (CursorTy) pvrtmp6723;
            CursorTy pvrtmp6725 = (CursorTy) end_taildc3729;
            CursorTy pvrtmp6724 = (CursorTy) taildc3729;
            CursorTy fltPrd5301 = (CursorTy) pvrtmp6724;
            CursorTy fltPrd5302 = (CursorTy) pvrtmp6725;

            return (CursorCursorCursorCursorProd) {end_r2072_3844_3845_3846,
                                                   endof3728, fltPrd5301,
                                                   fltPrd5302};
            break;
        }

      case 4:
        {
            CursorTy field_cur4518 = (CursorTy) tmpcur6659;
            CursorTy case3112 = (CursorTy) field_cur4518;
            CursorTy x1539 = (CursorTy) case3112;
            CursorTy loc3116 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct238 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2071, end_r2072, loc3116, x1539);
            CursorTy pvrtmp6726 = tmp_struct238.field0;
            CursorTy pvrtmp6727 = tmp_struct238.field1;
            CursorTy pvrtmp6728 = tmp_struct238.field2;
            CursorTy pvrtmp6729 = tmp_struct238.field3;
            CursorTy fltPrd5303 = (CursorTy) pvrtmp6728;
            CursorTy fltPrd5304 = (CursorTy) pvrtmp6729;
            CursorTy pvrtmp6731 = (CursorTy) fltPrd5304;
            CursorTy pvrtmp6730 = (CursorTy) fltPrd5303;
            CursorTy y1540 = (CursorTy) pvrtmp6730;
            CursorTy fltPrd5305 = (CursorTy) pvrtmp6728;
            CursorTy fltPrd5306 = (CursorTy) pvrtmp6729;
            CursorTy pvrtmp6733 = (CursorTy) fltPrd5306;
            CursorTy pvrtmp6732 = (CursorTy) fltPrd5305;
            CursorTy end_y1540 = (CursorTy) pvrtmp6733;
            CursorTy end_r2072_3847 = (CursorTy) pvrtmp6726;
            CursorTy endof3730 = (CursorTy) pvrtmp6727;

            *(TagTyPacked *) loc2070 = 4;

            CursorTy writetag4520 = loc2070 + 1;
            CursorTy writecur4521 = (CursorTy) end_y1540;
            CursorTy pvrtmp6735 = (CursorTy) writecur4521;
            CursorTy pvrtmp6734 = (CursorTy) loc2070;
            CursorTy taildc3731 = (CursorTy) pvrtmp6734;
            CursorTy end_taildc3731 = (CursorTy) pvrtmp6735;
            CursorTy pvrtmp6737 = (CursorTy) end_taildc3731;
            CursorTy pvrtmp6736 = (CursorTy) taildc3731;
            CursorTy fltPrd5307 = (CursorTy) pvrtmp6736;
            CursorTy fltPrd5308 = (CursorTy) pvrtmp6737;

            return (CursorCursorCursorCursorProd) {end_r2072_3847, endof3730,
                                                   fltPrd5307, fltPrd5308};
            break;
        }

      case 5:
        {
            CursorTy field_cur4523 = (CursorTy) tmpcur6659;
            CursorTy case3118 = (CursorTy) field_cur4523;
            CursorTy x1541 = (CursorTy) case3118;
            CursorTy loc3126 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct239 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072, loc3126, x1541);
            CursorTy pvrtmp6738 = tmp_struct239.field0;
            CursorTy pvrtmp6739 = tmp_struct239.field1;
            CursorTy pvrtmp6740 = tmp_struct239.field2;
            CursorTy pvrtmp6741 = tmp_struct239.field3;
            CursorTy fltPrd5309 = (CursorTy) pvrtmp6740;
            CursorTy fltPrd5310 = (CursorTy) pvrtmp6741;
            CursorTy pvrtmp6743 = (CursorTy) fltPrd5310;
            CursorTy pvrtmp6742 = (CursorTy) fltPrd5309;
            CursorTy y1543 = (CursorTy) pvrtmp6742;
            CursorTy fltPrd5311 = (CursorTy) pvrtmp6740;
            CursorTy fltPrd5312 = (CursorTy) pvrtmp6741;
            CursorTy pvrtmp6745 = (CursorTy) fltPrd5312;
            CursorTy pvrtmp6744 = (CursorTy) fltPrd5311;
            CursorTy end_y1543 = (CursorTy) pvrtmp6745;
            CursorTy end_r2072_3848 = (CursorTy) pvrtmp6738;
            CursorTy endof3732 = (CursorTy) pvrtmp6739;
            CursorTy case3119 = (CursorTy) endof3732;
            CursorTy x1542 = (CursorTy) case3119;
            CursorTy loc3127 = (CursorTy) end_y1543;
            CursorCursorCursorCursorProd tmp_struct240 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2071, end_r2072_3848, loc3127, x1542);
            CursorTy pvrtmp6746 = tmp_struct240.field0;
            CursorTy pvrtmp6747 = tmp_struct240.field1;
            CursorTy pvrtmp6748 = tmp_struct240.field2;
            CursorTy pvrtmp6749 = tmp_struct240.field3;
            CursorTy fltPrd5313 = (CursorTy) pvrtmp6748;
            CursorTy fltPrd5314 = (CursorTy) pvrtmp6749;
            CursorTy pvrtmp6751 = (CursorTy) fltPrd5314;
            CursorTy pvrtmp6750 = (CursorTy) fltPrd5313;
            CursorTy y1544 = (CursorTy) pvrtmp6750;
            CursorTy fltPrd5315 = (CursorTy) pvrtmp6748;
            CursorTy fltPrd5316 = (CursorTy) pvrtmp6749;
            CursorTy pvrtmp6753 = (CursorTy) fltPrd5316;
            CursorTy pvrtmp6752 = (CursorTy) fltPrd5315;
            CursorTy end_y1544 = (CursorTy) pvrtmp6753;
            CursorTy end_r2072_3848_3849 = (CursorTy) pvrtmp6746;
            CursorTy endof3733 = (CursorTy) pvrtmp6747;

            *(TagTyPacked *) loc2070 = 5;

            CursorTy writetag4526 = loc2070 + 1;
            CursorTy writecur4527 = (CursorTy) end_y1543;
            CursorTy writecur4528 = (CursorTy) end_y1544;
            CursorTy pvrtmp6755 = (CursorTy) writecur4528;
            CursorTy pvrtmp6754 = (CursorTy) loc2070;
            CursorTy taildc3734 = (CursorTy) pvrtmp6754;
            CursorTy end_taildc3734 = (CursorTy) pvrtmp6755;
            CursorTy pvrtmp6757 = (CursorTy) end_taildc3734;
            CursorTy pvrtmp6756 = (CursorTy) taildc3734;
            CursorTy fltPrd5317 = (CursorTy) pvrtmp6756;
            CursorTy fltPrd5318 = (CursorTy) pvrtmp6757;

            return (CursorCursorCursorCursorProd) {end_r2072_3848_3849,
                                                   endof3733, fltPrd5317,
                                                   fltPrd5318};
            break;
        }

      case 6:
        {
            CursorTy field_cur4530 = (CursorTy) tmpcur6659;
            CursorTy case3130 = (CursorTy) field_cur4530;
            CursorTy x1545 = (CursorTy) case3130;
            CursorTy loc3138 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct241 =
                                          _add_size_and_rel_offsets_LVBIND(end_r2071, end_r2072, loc3138, x1545);
            CursorTy pvrtmp6758 = tmp_struct241.field0;
            CursorTy pvrtmp6759 = tmp_struct241.field1;
            CursorTy pvrtmp6760 = tmp_struct241.field2;
            CursorTy pvrtmp6761 = tmp_struct241.field3;
            CursorTy fltPrd5319 = (CursorTy) pvrtmp6760;
            CursorTy fltPrd5320 = (CursorTy) pvrtmp6761;
            CursorTy pvrtmp6763 = (CursorTy) fltPrd5320;
            CursorTy pvrtmp6762 = (CursorTy) fltPrd5319;
            CursorTy y1547 = (CursorTy) pvrtmp6762;
            CursorTy fltPrd5321 = (CursorTy) pvrtmp6760;
            CursorTy fltPrd5322 = (CursorTy) pvrtmp6761;
            CursorTy pvrtmp6765 = (CursorTy) fltPrd5322;
            CursorTy pvrtmp6764 = (CursorTy) fltPrd5321;
            CursorTy end_y1547 = (CursorTy) pvrtmp6765;
            CursorTy end_r2072_3850 = (CursorTy) pvrtmp6758;
            CursorTy endof3735 = (CursorTy) pvrtmp6759;
            CursorTy case3131 = (CursorTy) endof3735;
            CursorTy x1546 = (CursorTy) case3131;
            CursorTy loc3139 = (CursorTy) end_y1547;
            CursorCursorCursorCursorProd tmp_struct242 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2071, end_r2072_3850, loc3139, x1546);
            CursorTy pvrtmp6766 = tmp_struct242.field0;
            CursorTy pvrtmp6767 = tmp_struct242.field1;
            CursorTy pvrtmp6768 = tmp_struct242.field2;
            CursorTy pvrtmp6769 = tmp_struct242.field3;
            CursorTy fltPrd5323 = (CursorTy) pvrtmp6768;
            CursorTy fltPrd5324 = (CursorTy) pvrtmp6769;
            CursorTy pvrtmp6771 = (CursorTy) fltPrd5324;
            CursorTy pvrtmp6770 = (CursorTy) fltPrd5323;
            CursorTy y1548 = (CursorTy) pvrtmp6770;
            CursorTy fltPrd5325 = (CursorTy) pvrtmp6768;
            CursorTy fltPrd5326 = (CursorTy) pvrtmp6769;
            CursorTy pvrtmp6773 = (CursorTy) fltPrd5326;
            CursorTy pvrtmp6772 = (CursorTy) fltPrd5325;
            CursorTy end_y1548 = (CursorTy) pvrtmp6773;
            CursorTy end_r2072_3850_3851 = (CursorTy) pvrtmp6766;
            CursorTy endof3736 = (CursorTy) pvrtmp6767;

            *(TagTyPacked *) loc2070 = 6;

            CursorTy writetag4533 = loc2070 + 1;
            CursorTy writecur4534 = (CursorTy) end_y1547;
            CursorTy writecur4535 = (CursorTy) end_y1548;
            CursorTy pvrtmp6775 = (CursorTy) writecur4535;
            CursorTy pvrtmp6774 = (CursorTy) loc2070;
            CursorTy taildc3737 = (CursorTy) pvrtmp6774;
            CursorTy end_taildc3737 = (CursorTy) pvrtmp6775;
            CursorTy pvrtmp6777 = (CursorTy) end_taildc3737;
            CursorTy pvrtmp6776 = (CursorTy) taildc3737;
            CursorTy fltPrd5327 = (CursorTy) pvrtmp6776;
            CursorTy fltPrd5328 = (CursorTy) pvrtmp6777;

            return (CursorCursorCursorCursorProd) {end_r2072_3850_3851,
                                                   endof3736, fltPrd5327,
                                                   fltPrd5328};
            break;
        }

      case 7:
        {
            CursorTy field_cur4537 = (CursorTy) tmpcur6659;
            CursorTy case3142 = (CursorTy) field_cur4537;
            CursorTy x1549 = (CursorTy) case3142;
            CursorTy loc3150 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct243 =
                                          _add_size_and_rel_offsets_LVBIND(end_r2071, end_r2072, loc3150, x1549);
            CursorTy pvrtmp6778 = tmp_struct243.field0;
            CursorTy pvrtmp6779 = tmp_struct243.field1;
            CursorTy pvrtmp6780 = tmp_struct243.field2;
            CursorTy pvrtmp6781 = tmp_struct243.field3;
            CursorTy fltPrd5329 = (CursorTy) pvrtmp6780;
            CursorTy fltPrd5330 = (CursorTy) pvrtmp6781;
            CursorTy pvrtmp6783 = (CursorTy) fltPrd5330;
            CursorTy pvrtmp6782 = (CursorTy) fltPrd5329;
            CursorTy y1551 = (CursorTy) pvrtmp6782;
            CursorTy fltPrd5331 = (CursorTy) pvrtmp6780;
            CursorTy fltPrd5332 = (CursorTy) pvrtmp6781;
            CursorTy pvrtmp6785 = (CursorTy) fltPrd5332;
            CursorTy pvrtmp6784 = (CursorTy) fltPrd5331;
            CursorTy end_y1551 = (CursorTy) pvrtmp6785;
            CursorTy end_r2072_3852 = (CursorTy) pvrtmp6778;
            CursorTy endof3738 = (CursorTy) pvrtmp6779;
            CursorTy case3143 = (CursorTy) endof3738;
            CursorTy x1550 = (CursorTy) case3143;
            CursorTy loc3151 = (CursorTy) end_y1551;
            CursorCursorCursorCursorProd tmp_struct244 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2071, end_r2072_3852, loc3151, x1550);
            CursorTy pvrtmp6786 = tmp_struct244.field0;
            CursorTy pvrtmp6787 = tmp_struct244.field1;
            CursorTy pvrtmp6788 = tmp_struct244.field2;
            CursorTy pvrtmp6789 = tmp_struct244.field3;
            CursorTy fltPrd5333 = (CursorTy) pvrtmp6788;
            CursorTy fltPrd5334 = (CursorTy) pvrtmp6789;
            CursorTy pvrtmp6791 = (CursorTy) fltPrd5334;
            CursorTy pvrtmp6790 = (CursorTy) fltPrd5333;
            CursorTy y1552 = (CursorTy) pvrtmp6790;
            CursorTy fltPrd5335 = (CursorTy) pvrtmp6788;
            CursorTy fltPrd5336 = (CursorTy) pvrtmp6789;
            CursorTy pvrtmp6793 = (CursorTy) fltPrd5336;
            CursorTy pvrtmp6792 = (CursorTy) fltPrd5335;
            CursorTy end_y1552 = (CursorTy) pvrtmp6793;
            CursorTy end_r2072_3852_3853 = (CursorTy) pvrtmp6786;
            CursorTy endof3739 = (CursorTy) pvrtmp6787;

            *(TagTyPacked *) loc2070 = 7;

            CursorTy writetag4540 = loc2070 + 1;
            CursorTy writecur4541 = (CursorTy) end_y1551;
            CursorTy writecur4542 = (CursorTy) end_y1552;
            CursorTy pvrtmp6795 = (CursorTy) writecur4542;
            CursorTy pvrtmp6794 = (CursorTy) loc2070;
            CursorTy taildc3740 = (CursorTy) pvrtmp6794;
            CursorTy end_taildc3740 = (CursorTy) pvrtmp6795;
            CursorTy pvrtmp6797 = (CursorTy) end_taildc3740;
            CursorTy pvrtmp6796 = (CursorTy) taildc3740;
            CursorTy fltPrd5337 = (CursorTy) pvrtmp6796;
            CursorTy fltPrd5338 = (CursorTy) pvrtmp6797;

            return (CursorCursorCursorCursorProd) {end_r2072_3852_3853,
                                                   endof3739, fltPrd5337,
                                                   fltPrd5338};
            break;
        }

      case 8:
        {
            CursorTy field_cur4544 = (CursorTy) tmpcur6659;
            CursorTy case3154 = (CursorTy) field_cur4544;
            SymTy tmpval6798 = *(SymTy *) case3154;
            CursorTy tmpcur6799 = case3154 + sizeof(SymTy);
            SymTy x1553 = (SymTy) tmpval6798;
            CursorTy end_x1553 = (CursorTy) tmpcur6799;
            CursorTy case3155 = (CursorTy) end_x1553;
            CursorTy x1554 = (CursorTy) case3155;
            CursorTy jump3741 = case3154 + 8;
            CursorCursorCursorCursorProd tmp_struct245 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072, loc3160, x1554);
            CursorTy pvrtmp6800 = tmp_struct245.field0;
            CursorTy pvrtmp6801 = tmp_struct245.field1;
            CursorTy pvrtmp6802 = tmp_struct245.field2;
            CursorTy pvrtmp6803 = tmp_struct245.field3;
            CursorTy fltPrd5339 = (CursorTy) pvrtmp6802;
            CursorTy fltPrd5340 = (CursorTy) pvrtmp6803;
            CursorTy pvrtmp6805 = (CursorTy) fltPrd5340;
            CursorTy pvrtmp6804 = (CursorTy) fltPrd5339;
            CursorTy y1556 = (CursorTy) pvrtmp6804;
            CursorTy fltPrd5341 = (CursorTy) pvrtmp6802;
            CursorTy fltPrd5342 = (CursorTy) pvrtmp6803;
            CursorTy pvrtmp6807 = (CursorTy) fltPrd5342;
            CursorTy pvrtmp6806 = (CursorTy) fltPrd5341;
            CursorTy end_y1556 = (CursorTy) pvrtmp6807;
            CursorTy end_r2072_3854 = (CursorTy) pvrtmp6800;
            CursorTy endof3742 = (CursorTy) pvrtmp6801;

            *(TagTyPacked *) loc2070 = 8;

            CursorTy writetag4547 = loc2070 + 1;

            *(SymTy *) writetag4547 = x1553;

            CursorTy writecur4548 = writetag4547 + sizeof(SymTy);
            CursorTy writecur4549 = (CursorTy) end_y1556;
            CursorTy pvrtmp6809 = (CursorTy) writecur4549;
            CursorTy pvrtmp6808 = (CursorTy) loc2070;
            CursorTy taildc3743 = (CursorTy) pvrtmp6808;
            CursorTy end_taildc3743 = (CursorTy) pvrtmp6809;
            CursorTy pvrtmp6811 = (CursorTy) end_taildc3743;
            CursorTy pvrtmp6810 = (CursorTy) taildc3743;
            CursorTy fltPrd5343 = (CursorTy) pvrtmp6810;
            CursorTy fltPrd5344 = (CursorTy) pvrtmp6811;

            return (CursorCursorCursorCursorProd) {end_r2072_3854, endof3742,
                                                   fltPrd5343, fltPrd5344};
            break;
        }

      case 9:
        {
            CursorTy field_cur4551 = (CursorTy) tmpcur6659;
            CursorTy case3164 = (CursorTy) field_cur4551;
            CursorTy x1557 = (CursorTy) case3164;
            CursorTy loc3168 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct246 =
                                          _add_size_and_rel_offsets_Datum(end_r2071, end_r2072, loc3168, x1557);
            CursorTy pvrtmp6812 = tmp_struct246.field0;
            CursorTy pvrtmp6813 = tmp_struct246.field1;
            CursorTy pvrtmp6814 = tmp_struct246.field2;
            CursorTy pvrtmp6815 = tmp_struct246.field3;
            CursorTy fltPrd5345 = (CursorTy) pvrtmp6814;
            CursorTy fltPrd5346 = (CursorTy) pvrtmp6815;
            CursorTy pvrtmp6817 = (CursorTy) fltPrd5346;
            CursorTy pvrtmp6816 = (CursorTy) fltPrd5345;
            CursorTy y1558 = (CursorTy) pvrtmp6816;
            CursorTy fltPrd5347 = (CursorTy) pvrtmp6814;
            CursorTy fltPrd5348 = (CursorTy) pvrtmp6815;
            CursorTy pvrtmp6819 = (CursorTy) fltPrd5348;
            CursorTy pvrtmp6818 = (CursorTy) fltPrd5347;
            CursorTy end_y1558 = (CursorTy) pvrtmp6819;
            CursorTy end_r2072_3855 = (CursorTy) pvrtmp6812;
            CursorTy endof3744 = (CursorTy) pvrtmp6813;

            *(TagTyPacked *) loc2070 = 9;

            CursorTy writetag4553 = loc2070 + 1;
            CursorTy writecur4554 = (CursorTy) end_y1558;
            CursorTy pvrtmp6821 = (CursorTy) writecur4554;
            CursorTy pvrtmp6820 = (CursorTy) loc2070;
            CursorTy taildc3745 = (CursorTy) pvrtmp6820;
            CursorTy end_taildc3745 = (CursorTy) pvrtmp6821;
            CursorTy pvrtmp6823 = (CursorTy) end_taildc3745;
            CursorTy pvrtmp6822 = (CursorTy) taildc3745;
            CursorTy fltPrd5349 = (CursorTy) pvrtmp6822;
            CursorTy fltPrd5350 = (CursorTy) pvrtmp6823;

            return (CursorCursorCursorCursorProd) {end_r2072_3855, endof3744,
                                                   fltPrd5349, fltPrd5350};
            break;
        }

      case 10:
        {
            CursorTy field_cur4556 = (CursorTy) tmpcur6659;
            CursorTy case3170 = (CursorTy) field_cur4556;
            CursorTy x1559 = (CursorTy) case3170;
            CursorTy loc3174 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct247 =
                                          _add_size_and_rel_offsets_Datum(end_r2071, end_r2072, loc3174, x1559);
            CursorTy pvrtmp6824 = tmp_struct247.field0;
            CursorTy pvrtmp6825 = tmp_struct247.field1;
            CursorTy pvrtmp6826 = tmp_struct247.field2;
            CursorTy pvrtmp6827 = tmp_struct247.field3;
            CursorTy fltPrd5351 = (CursorTy) pvrtmp6826;
            CursorTy fltPrd5352 = (CursorTy) pvrtmp6827;
            CursorTy pvrtmp6829 = (CursorTy) fltPrd5352;
            CursorTy pvrtmp6828 = (CursorTy) fltPrd5351;
            CursorTy y1560 = (CursorTy) pvrtmp6828;
            CursorTy fltPrd5353 = (CursorTy) pvrtmp6826;
            CursorTy fltPrd5354 = (CursorTy) pvrtmp6827;
            CursorTy pvrtmp6831 = (CursorTy) fltPrd5354;
            CursorTy pvrtmp6830 = (CursorTy) fltPrd5353;
            CursorTy end_y1560 = (CursorTy) pvrtmp6831;
            CursorTy end_r2072_3856 = (CursorTy) pvrtmp6824;
            CursorTy endof3746 = (CursorTy) pvrtmp6825;

            *(TagTyPacked *) loc2070 = 10;

            CursorTy writetag4558 = loc2070 + 1;
            CursorTy writecur4559 = (CursorTy) end_y1560;
            CursorTy pvrtmp6833 = (CursorTy) writecur4559;
            CursorTy pvrtmp6832 = (CursorTy) loc2070;
            CursorTy taildc3747 = (CursorTy) pvrtmp6832;
            CursorTy end_taildc3747 = (CursorTy) pvrtmp6833;
            CursorTy pvrtmp6835 = (CursorTy) end_taildc3747;
            CursorTy pvrtmp6834 = (CursorTy) taildc3747;
            CursorTy fltPrd5355 = (CursorTy) pvrtmp6834;
            CursorTy fltPrd5356 = (CursorTy) pvrtmp6835;

            return (CursorCursorCursorCursorProd) {end_r2072_3856, endof3746,
                                                   fltPrd5355, fltPrd5356};
            break;
        }

      case 11:
        {
            CursorTy field_cur4561 = (CursorTy) tmpcur6659;
            CursorTy case3176 = (CursorTy) field_cur4561;
            CursorTy x1561 = (CursorTy) case3176;
            CursorTy loc3180 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct248 =
                                          _add_size_and_rel_offsets_Datum(end_r2071, end_r2072, loc3180, x1561);
            CursorTy pvrtmp6836 = tmp_struct248.field0;
            CursorTy pvrtmp6837 = tmp_struct248.field1;
            CursorTy pvrtmp6838 = tmp_struct248.field2;
            CursorTy pvrtmp6839 = tmp_struct248.field3;
            CursorTy fltPrd5357 = (CursorTy) pvrtmp6838;
            CursorTy fltPrd5358 = (CursorTy) pvrtmp6839;
            CursorTy pvrtmp6841 = (CursorTy) fltPrd5358;
            CursorTy pvrtmp6840 = (CursorTy) fltPrd5357;
            CursorTy y1562 = (CursorTy) pvrtmp6840;
            CursorTy fltPrd5359 = (CursorTy) pvrtmp6838;
            CursorTy fltPrd5360 = (CursorTy) pvrtmp6839;
            CursorTy pvrtmp6843 = (CursorTy) fltPrd5360;
            CursorTy pvrtmp6842 = (CursorTy) fltPrd5359;
            CursorTy end_y1562 = (CursorTy) pvrtmp6843;
            CursorTy end_r2072_3857 = (CursorTy) pvrtmp6836;
            CursorTy endof3748 = (CursorTy) pvrtmp6837;

            *(TagTyPacked *) loc2070 = 11;

            CursorTy writetag4563 = loc2070 + 1;
            CursorTy writecur4564 = (CursorTy) end_y1562;
            CursorTy pvrtmp6845 = (CursorTy) writecur4564;
            CursorTy pvrtmp6844 = (CursorTy) loc2070;
            CursorTy taildc3749 = (CursorTy) pvrtmp6844;
            CursorTy end_taildc3749 = (CursorTy) pvrtmp6845;
            CursorTy pvrtmp6847 = (CursorTy) end_taildc3749;
            CursorTy pvrtmp6846 = (CursorTy) taildc3749;
            CursorTy fltPrd5361 = (CursorTy) pvrtmp6846;
            CursorTy fltPrd5362 = (CursorTy) pvrtmp6847;

            return (CursorCursorCursorCursorProd) {end_r2072_3857, endof3748,
                                                   fltPrd5361, fltPrd5362};
            break;
        }

      case 12:
        {
            CursorTy field_cur4566 = (CursorTy) tmpcur6659;
            CursorTy case3182 = (CursorTy) field_cur4566;
            CursorTy x1563 = (CursorTy) case3182;
            CursorTy loc3194 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct249 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072, loc3194, x1563);
            CursorTy pvrtmp6848 = tmp_struct249.field0;
            CursorTy pvrtmp6849 = tmp_struct249.field1;
            CursorTy pvrtmp6850 = tmp_struct249.field2;
            CursorTy pvrtmp6851 = tmp_struct249.field3;
            CursorTy fltPrd5363 = (CursorTy) pvrtmp6850;
            CursorTy fltPrd5364 = (CursorTy) pvrtmp6851;
            CursorTy pvrtmp6853 = (CursorTy) fltPrd5364;
            CursorTy pvrtmp6852 = (CursorTy) fltPrd5363;
            CursorTy y1566 = (CursorTy) pvrtmp6852;
            CursorTy fltPrd5365 = (CursorTy) pvrtmp6850;
            CursorTy fltPrd5366 = (CursorTy) pvrtmp6851;
            CursorTy pvrtmp6855 = (CursorTy) fltPrd5366;
            CursorTy pvrtmp6854 = (CursorTy) fltPrd5365;
            CursorTy end_y1566 = (CursorTy) pvrtmp6855;
            CursorTy end_r2072_3858 = (CursorTy) pvrtmp6848;
            CursorTy endof3750 = (CursorTy) pvrtmp6849;
            CursorTy case3183 = (CursorTy) endof3750;
            CursorTy x1564 = (CursorTy) case3183;
            CursorTy loc3195 = (CursorTy) end_y1566;
            CursorCursorCursorCursorProd tmp_struct250 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072_3858, loc3195, x1564);
            CursorTy pvrtmp6856 = tmp_struct250.field0;
            CursorTy pvrtmp6857 = tmp_struct250.field1;
            CursorTy pvrtmp6858 = tmp_struct250.field2;
            CursorTy pvrtmp6859 = tmp_struct250.field3;
            CursorTy fltPrd5367 = (CursorTy) pvrtmp6858;
            CursorTy fltPrd5368 = (CursorTy) pvrtmp6859;
            CursorTy pvrtmp6861 = (CursorTy) fltPrd5368;
            CursorTy pvrtmp6860 = (CursorTy) fltPrd5367;
            CursorTy y1567 = (CursorTy) pvrtmp6860;
            CursorTy fltPrd5369 = (CursorTy) pvrtmp6858;
            CursorTy fltPrd5370 = (CursorTy) pvrtmp6859;
            CursorTy pvrtmp6863 = (CursorTy) fltPrd5370;
            CursorTy pvrtmp6862 = (CursorTy) fltPrd5369;
            CursorTy end_y1567 = (CursorTy) pvrtmp6863;
            CursorTy end_r2072_3858_3859 = (CursorTy) pvrtmp6856;
            CursorTy endof3751 = (CursorTy) pvrtmp6857;
            CursorTy case3184 = (CursorTy) endof3751;
            CursorTy x1565 = (CursorTy) case3184;
            CursorTy loc3196 = (CursorTy) end_y1567;
            CursorCursorCursorCursorProd tmp_struct251 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072_3858_3859, loc3196, x1565);
            CursorTy pvrtmp6864 = tmp_struct251.field0;
            CursorTy pvrtmp6865 = tmp_struct251.field1;
            CursorTy pvrtmp6866 = tmp_struct251.field2;
            CursorTy pvrtmp6867 = tmp_struct251.field3;
            CursorTy fltPrd5371 = (CursorTy) pvrtmp6866;
            CursorTy fltPrd5372 = (CursorTy) pvrtmp6867;
            CursorTy pvrtmp6869 = (CursorTy) fltPrd5372;
            CursorTy pvrtmp6868 = (CursorTy) fltPrd5371;
            CursorTy y1568 = (CursorTy) pvrtmp6868;
            CursorTy fltPrd5373 = (CursorTy) pvrtmp6866;
            CursorTy fltPrd5374 = (CursorTy) pvrtmp6867;
            CursorTy pvrtmp6871 = (CursorTy) fltPrd5374;
            CursorTy pvrtmp6870 = (CursorTy) fltPrd5373;
            CursorTy end_y1568 = (CursorTy) pvrtmp6871;
            CursorTy end_r2072_3858_3859_3860 = (CursorTy) pvrtmp6864;
            CursorTy endof3752 = (CursorTy) pvrtmp6865;

            *(TagTyPacked *) loc2070 = 12;

            CursorTy writetag4570 = loc2070 + 1;
            CursorTy writecur4571 = (CursorTy) end_y1566;
            CursorTy writecur4572 = (CursorTy) end_y1567;
            CursorTy writecur4573 = (CursorTy) end_y1568;
            CursorTy pvrtmp6873 = (CursorTy) writecur4573;
            CursorTy pvrtmp6872 = (CursorTy) loc2070;
            CursorTy taildc3753 = (CursorTy) pvrtmp6872;
            CursorTy end_taildc3753 = (CursorTy) pvrtmp6873;
            CursorTy pvrtmp6875 = (CursorTy) end_taildc3753;
            CursorTy pvrtmp6874 = (CursorTy) taildc3753;
            CursorTy fltPrd5375 = (CursorTy) pvrtmp6874;
            CursorTy fltPrd5376 = (CursorTy) pvrtmp6875;

            return (CursorCursorCursorCursorProd) {end_r2072_3858_3859_3860,
                                                   endof3752, fltPrd5375,
                                                   fltPrd5376};
            break;
        }

      case 13:
        {
            CursorTy field_cur4575 = (CursorTy) tmpcur6659;
            CursorTy case3200 = (CursorTy) field_cur4575;
            CursorTy x1569 = (CursorTy) case3200;
            CursorTy loc3208 = loc2070 + 1;
            CursorCursorCursorCursorProd tmp_struct252 =
                                          _add_size_and_rel_offsets_Expr(end_r2071, end_r2072, loc3208, x1569);
            CursorTy pvrtmp6876 = tmp_struct252.field0;
            CursorTy pvrtmp6877 = tmp_struct252.field1;
            CursorTy pvrtmp6878 = tmp_struct252.field2;
            CursorTy pvrtmp6879 = tmp_struct252.field3;
            CursorTy fltPrd5377 = (CursorTy) pvrtmp6878;
            CursorTy fltPrd5378 = (CursorTy) pvrtmp6879;
            CursorTy pvrtmp6881 = (CursorTy) fltPrd5378;
            CursorTy pvrtmp6880 = (CursorTy) fltPrd5377;
            CursorTy y1571 = (CursorTy) pvrtmp6880;
            CursorTy fltPrd5379 = (CursorTy) pvrtmp6878;
            CursorTy fltPrd5380 = (CursorTy) pvrtmp6879;
            CursorTy pvrtmp6883 = (CursorTy) fltPrd5380;
            CursorTy pvrtmp6882 = (CursorTy) fltPrd5379;
            CursorTy end_y1571 = (CursorTy) pvrtmp6883;
            CursorTy end_r2072_3861 = (CursorTy) pvrtmp6876;
            CursorTy endof3754 = (CursorTy) pvrtmp6877;
            CursorTy case3201 = (CursorTy) endof3754;
            CursorTy x1570 = (CursorTy) case3201;
            CursorTy loc3209 = (CursorTy) end_y1571;
            CursorCursorCursorCursorProd tmp_struct253 =
                                          _add_size_and_rel_offsets_ListExpr(end_r2071, end_r2072_3861, loc3209, x1570);
            CursorTy pvrtmp6884 = tmp_struct253.field0;
            CursorTy pvrtmp6885 = tmp_struct253.field1;
            CursorTy pvrtmp6886 = tmp_struct253.field2;
            CursorTy pvrtmp6887 = tmp_struct253.field3;
            CursorTy fltPrd5381 = (CursorTy) pvrtmp6886;
            CursorTy fltPrd5382 = (CursorTy) pvrtmp6887;
            CursorTy pvrtmp6889 = (CursorTy) fltPrd5382;
            CursorTy pvrtmp6888 = (CursorTy) fltPrd5381;
            CursorTy y1572 = (CursorTy) pvrtmp6888;
            CursorTy fltPrd5383 = (CursorTy) pvrtmp6886;
            CursorTy fltPrd5384 = (CursorTy) pvrtmp6887;
            CursorTy pvrtmp6891 = (CursorTy) fltPrd5384;
            CursorTy pvrtmp6890 = (CursorTy) fltPrd5383;
            CursorTy end_y1572 = (CursorTy) pvrtmp6891;
            CursorTy end_r2072_3861_3862 = (CursorTy) pvrtmp6884;
            CursorTy endof3755 = (CursorTy) pvrtmp6885;

            *(TagTyPacked *) loc2070 = 13;

            CursorTy writetag4578 = loc2070 + 1;
            CursorTy writecur4579 = (CursorTy) end_y1571;
            CursorTy writecur4580 = (CursorTy) end_y1572;
            CursorTy pvrtmp6893 = (CursorTy) writecur4580;
            CursorTy pvrtmp6892 = (CursorTy) loc2070;
            CursorTy taildc3756 = (CursorTy) pvrtmp6892;
            CursorTy end_taildc3756 = (CursorTy) pvrtmp6893;
            CursorTy pvrtmp6895 = (CursorTy) end_taildc3756;
            CursorTy pvrtmp6894 = (CursorTy) taildc3756;
            CursorTy fltPrd5385 = (CursorTy) pvrtmp6894;
            CursorTy fltPrd5386 = (CursorTy) pvrtmp6895;

            return (CursorCursorCursorCursorProd) {end_r2072_3861_3862,
                                                   endof3755, fltPrd5385,
                                                   fltPrd5386};
            break;
        }

      case 14:
        {
            CursorTy field_cur4582 = (CursorTy) tmpcur6659;
            CursorTy case3212 = (CursorTy) field_cur4582;
            SymTy tmpval6896 = *(SymTy *) case3212;
            CursorTy tmpcur6897 = case3212 + sizeof(SymTy);
            SymTy x1573 = (SymTy) tmpval6896;
            CursorTy end_x1573 = (CursorTy) tmpcur6897;
            CursorTy jump3757 = case3212 + 8;

            *(TagTyPacked *) loc2070 = 14;

            CursorTy writetag4584 = loc2070 + 1;

            *(SymTy *) writetag4584 = x1573;

            CursorTy writecur4585 = writetag4584 + sizeof(SymTy);
            CursorTy pvrtmp6899 = (CursorTy) writecur4585;
            CursorTy pvrtmp6898 = (CursorTy) loc2070;
            CursorTy taildc3758 = (CursorTy) pvrtmp6898;
            CursorTy end_taildc3758 = (CursorTy) pvrtmp6899;
            CursorTy pvrtmp6901 = (CursorTy) end_taildc3758;
            CursorTy pvrtmp6900 = (CursorTy) taildc3758;
            CursorTy fltPrd5387 = (CursorTy) pvrtmp6900;
            CursorTy fltPrd5388 = (CursorTy) pvrtmp6901;

            return (CursorCursorCursorCursorProd) {end_r2072, jump3757,
                                                   fltPrd5387, fltPrd5388};
            break;
        }

      case 15:
        {
            CursorTy field_cur4587 = (CursorTy) tmpcur6659;
            CursorTy case3216 = (CursorTy) field_cur4587;
            SymTy tmpval6902 = *(SymTy *) case3216;
            CursorTy tmpcur6903 = case3216 + sizeof(SymTy);
            SymTy x1575 = (SymTy) tmpval6902;
            CursorTy end_x1575 = (CursorTy) tmpcur6903;
            CursorTy jump3759 = case3216 + 8;

            *(TagTyPacked *) loc2070 = 15;

            CursorTy writetag4589 = loc2070 + 1;

            *(SymTy *) writetag4589 = x1575;

            CursorTy writecur4590 = writetag4589 + sizeof(SymTy);
            CursorTy pvrtmp6905 = (CursorTy) writecur4590;
            CursorTy pvrtmp6904 = (CursorTy) loc2070;
            CursorTy taildc3760 = (CursorTy) pvrtmp6904;
            CursorTy end_taildc3760 = (CursorTy) pvrtmp6905;
            CursorTy pvrtmp6907 = (CursorTy) end_taildc3760;
            CursorTy pvrtmp6906 = (CursorTy) taildc3760;
            CursorTy fltPrd5389 = (CursorTy) pvrtmp6906;
            CursorTy fltPrd5390 = (CursorTy) pvrtmp6907;

            return (CursorCursorCursorCursorProd) {end_r2072, jump3759,
                                                   fltPrd5389, fltPrd5390};
            break;
        }

      case 16:
        {
            CursorTy field_cur4592 = (CursorTy) tmpcur6659;
            CursorTy case3220 = (CursorTy) field_cur4592;
            SymTy tmpval6908 = *(SymTy *) case3220;
            CursorTy tmpcur6909 = case3220 + sizeof(SymTy);
            SymTy x1577 = (SymTy) tmpval6908;
            CursorTy end_x1577 = (CursorTy) tmpcur6909;
            CursorTy jump3761 = case3220 + 8;

            *(TagTyPacked *) loc2070 = 16;

            CursorTy writetag4594 = loc2070 + 1;

            *(SymTy *) writetag4594 = x1577;

            CursorTy writecur4595 = writetag4594 + sizeof(SymTy);
            CursorTy pvrtmp6911 = (CursorTy) writecur4595;
            CursorTy pvrtmp6910 = (CursorTy) loc2070;
            CursorTy taildc3762 = (CursorTy) pvrtmp6910;
            CursorTy end_taildc3762 = (CursorTy) pvrtmp6911;
            CursorTy pvrtmp6913 = (CursorTy) end_taildc3762;
            CursorTy pvrtmp6912 = (CursorTy) taildc3762;
            CursorTy fltPrd5391 = (CursorTy) pvrtmp6912;
            CursorTy fltPrd5392 = (CursorTy) pvrtmp6913;

            return (CursorCursorCursorCursorProd) {end_r2072, jump3761,
                                                   fltPrd5391, fltPrd5392};
            break;
        }

      case 17:
        {
            CursorTy field_cur4597 = (CursorTy) tmpcur6659;
            CursorTy jump3763 = loc2069 + 1;

            *(TagTyPacked *) loc2070 = 17;

            CursorTy writetag4598 = loc2070 + 1;
            CursorTy pvrtmp6915 = (CursorTy) writetag4598;
            CursorTy pvrtmp6914 = (CursorTy) loc2070;
            CursorTy taildc3764 = (CursorTy) pvrtmp6914;
            CursorTy end_taildc3764 = (CursorTy) pvrtmp6915;
            CursorTy pvrtmp6917 = (CursorTy) end_taildc3764;
            CursorTy pvrtmp6916 = (CursorTy) taildc3764;
            CursorTy fltPrd5393 = (CursorTy) pvrtmp6916;
            CursorTy fltPrd5394 = (CursorTy) pvrtmp6917;

            return (CursorCursorCursorCursorProd) {end_r2072, jump3763,
                                                   fltPrd5393, fltPrd5394};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7472 = *(CursorTy *) tmpcur6659;
            CursorTy tmpaftercur7473 = tmpcur6659 + 8;
            TagTyPacked tagtmp7474 = *(TagTyPacked *) tmpcur7472;
            CursorTy tailtmp7475 = tmpcur7472 + 1;

            tmpval6658 = tagtmp7474;
            tmpcur6659 = tailtmp7475;
            goto switch6918;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7472 = *(CursorTy *) tmpcur6659;
            CursorTy tmpaftercur7473 = tmpcur6659 + 8;
            TagTyPacked tagtmp7474 = *(TagTyPacked *) tmpcur7472;
            CursorTy tailtmp7475 = tmpcur7472 + 1;

            tmpval6658 = tagtmp7474;
            tmpcur6659 = tailtmp7475;
            goto switch6918;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6658");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Toplvl(CursorTy end_r2075,
                                                              CursorTy end_r2076,
                                                              CursorTy loc2074,
                                                              CursorTy arg1579)
{
    CursorTy loc2073 = (CursorTy) arg1579;

    if (loc2074 + 26 > end_r2076) {
        ChunkTy new_chunk263 = alloc_chunk(end_r2076);
        CursorTy chunk_start264 = new_chunk263.start_ptr;
        CursorTy chunk_end265 = new_chunk263.end_ptr;

        end_r2076 = chunk_end265;
        *(TagTyPacked *) loc2074 = 255;

        CursorTy redir = loc2074 + 1;

        *(CursorTy *) redir = chunk_start264;
        loc2074 = chunk_start264;
    }

    CursorTy loc3235 = loc2074 + 1;
    CursorTy loc3236 = loc3235 + 8;
    CursorTy loc3237 = loc3236 + 8;
    CursorTy loc3253 = loc2074 + 1;
    CursorTy loc3254 = loc3253 + 8;
    CursorTy loc3255 = loc3254 + 8;
    TagTyPacked tmpval6919 = *(TagTyPacked *) arg1579;
    CursorTy tmpcur6920 = arg1579 + 1;


  switch6985:
    ;
    switch (tmpval6919) {

      case 0:
        {
            CursorTy field_cur4600 = (CursorTy) tmpcur6920;
            CursorTy case3227 = (CursorTy) field_cur4600;
            CursorTy x1580 = (CursorTy) case3227;
            CursorCursorCursorCursorProd tmp_struct257 =
                                          _add_size_and_rel_offsets_ListSym(end_r2075, end_r2076, loc3237, x1580);
            CursorTy pvrtmp6921 = tmp_struct257.field0;
            CursorTy pvrtmp6922 = tmp_struct257.field1;
            CursorTy pvrtmp6923 = tmp_struct257.field2;
            CursorTy pvrtmp6924 = tmp_struct257.field3;
            CursorTy fltPrd5395 = (CursorTy) pvrtmp6923;
            CursorTy fltPrd5396 = (CursorTy) pvrtmp6924;
            CursorTy pvrtmp6926 = (CursorTy) fltPrd5396;
            CursorTy pvrtmp6925 = (CursorTy) fltPrd5395;
            CursorTy y1582 = (CursorTy) pvrtmp6925;
            CursorTy fltPrd5397 = (CursorTy) pvrtmp6923;
            CursorTy fltPrd5398 = (CursorTy) pvrtmp6924;
            CursorTy pvrtmp6928 = (CursorTy) fltPrd5398;
            CursorTy pvrtmp6927 = (CursorTy) fltPrd5397;
            CursorTy end_y1582 = (CursorTy) pvrtmp6928;
            CursorTy end_r2076_3863 = (CursorTy) pvrtmp6921;
            CursorTy endof3765 = (CursorTy) pvrtmp6922;
            CursorTy case3228 = (CursorTy) endof3765;
            CursorTy x1581 = (CursorTy) case3228;
            CursorTy loc3238 = (CursorTy) end_y1582;
            CursorCursorCursorCursorProd tmp_struct258 =
                                          _add_size_and_rel_offsets_Expr(end_r2075, end_r2076_3863, loc3238, x1581);
            CursorTy pvrtmp6929 = tmp_struct258.field0;
            CursorTy pvrtmp6930 = tmp_struct258.field1;
            CursorTy pvrtmp6931 = tmp_struct258.field2;
            CursorTy pvrtmp6932 = tmp_struct258.field3;
            CursorTy fltPrd5399 = (CursorTy) pvrtmp6931;
            CursorTy fltPrd5400 = (CursorTy) pvrtmp6932;
            CursorTy pvrtmp6934 = (CursorTy) fltPrd5400;
            CursorTy pvrtmp6933 = (CursorTy) fltPrd5399;
            CursorTy y1583 = (CursorTy) pvrtmp6933;
            CursorTy fltPrd5401 = (CursorTy) pvrtmp6931;
            CursorTy fltPrd5402 = (CursorTy) pvrtmp6932;
            CursorTy pvrtmp6936 = (CursorTy) fltPrd5402;
            CursorTy pvrtmp6935 = (CursorTy) fltPrd5401;
            CursorTy end_y1583 = (CursorTy) pvrtmp6936;
            CursorTy end_r2076_3863_3864 = (CursorTy) pvrtmp6929;
            CursorTy endof3766 = (CursorTy) pvrtmp6930;
            IntTy sizeof_y1582_1584 = end_y1582 - y1582;
            IntTy sizeof_y1583_1585 = end_y1583 - y1583;
            IntTy fltPrm1904 = sizeof_y1582_1584 + 0;
            IntTy offset_1586 = 0 + fltPrm1904;
            IntTy fltPrm1905 = sizeof_y1582_1584 + sizeof_y1583_1585;
            IntTy size_dcon1587 = 9 + fltPrm1905;

            *(TagTyPacked *) loc2074 = 155;

            CursorTy writetag4603 = loc2074 + 1;

            *(IntTy *) writetag4603 = size_dcon1587;

            CursorTy writecur4604 = writetag4603 + sizeof(IntTy);

            *(IntTy *) writecur4604 = offset_1586;

            CursorTy writecur4605 = writecur4604 + sizeof(IntTy);
            CursorTy writecur4606 = (CursorTy) end_y1582;
            CursorTy writecur4607 = (CursorTy) end_y1583;
            CursorTy pvrtmp6938 = (CursorTy) writecur4607;
            CursorTy pvrtmp6937 = (CursorTy) loc2074;
            CursorTy taildc3767 = (CursorTy) pvrtmp6937;
            CursorTy end_taildc3767 = (CursorTy) pvrtmp6938;
            CursorTy pvrtmp6940 = (CursorTy) end_taildc3767;
            CursorTy pvrtmp6939 = (CursorTy) taildc3767;
            CursorTy fltPrd5403 = (CursorTy) pvrtmp6939;
            CursorTy fltPrd5404 = (CursorTy) pvrtmp6940;

            return (CursorCursorCursorCursorProd) {end_r2076_3863_3864,
                                                   endof3766, fltPrd5403,
                                                   fltPrd5404};
            break;
        }

      case 1:
        {
            CursorTy field_cur4609 = (CursorTy) tmpcur6920;
            CursorTy case3245 = (CursorTy) field_cur4609;
            CursorTy x1588 = (CursorTy) case3245;
            CursorCursorCursorCursorProd tmp_struct259 =
                                          _add_size_and_rel_offsets_ListSym(end_r2075, end_r2076, loc3255, x1588);
            CursorTy pvrtmp6941 = tmp_struct259.field0;
            CursorTy pvrtmp6942 = tmp_struct259.field1;
            CursorTy pvrtmp6943 = tmp_struct259.field2;
            CursorTy pvrtmp6944 = tmp_struct259.field3;
            CursorTy fltPrd5405 = (CursorTy) pvrtmp6943;
            CursorTy fltPrd5406 = (CursorTy) pvrtmp6944;
            CursorTy pvrtmp6946 = (CursorTy) fltPrd5406;
            CursorTy pvrtmp6945 = (CursorTy) fltPrd5405;
            CursorTy y1590 = (CursorTy) pvrtmp6945;
            CursorTy fltPrd5407 = (CursorTy) pvrtmp6943;
            CursorTy fltPrd5408 = (CursorTy) pvrtmp6944;
            CursorTy pvrtmp6948 = (CursorTy) fltPrd5408;
            CursorTy pvrtmp6947 = (CursorTy) fltPrd5407;
            CursorTy end_y1590 = (CursorTy) pvrtmp6948;
            CursorTy end_r2076_3865 = (CursorTy) pvrtmp6941;
            CursorTy endof3768 = (CursorTy) pvrtmp6942;
            CursorTy case3246 = (CursorTy) endof3768;
            CursorTy x1589 = (CursorTy) case3246;
            CursorTy loc3256 = (CursorTy) end_y1590;
            CursorCursorCursorCursorProd tmp_struct260 =
                                          _add_size_and_rel_offsets_Expr(end_r2075, end_r2076_3865, loc3256, x1589);
            CursorTy pvrtmp6949 = tmp_struct260.field0;
            CursorTy pvrtmp6950 = tmp_struct260.field1;
            CursorTy pvrtmp6951 = tmp_struct260.field2;
            CursorTy pvrtmp6952 = tmp_struct260.field3;
            CursorTy fltPrd5409 = (CursorTy) pvrtmp6951;
            CursorTy fltPrd5410 = (CursorTy) pvrtmp6952;
            CursorTy pvrtmp6954 = (CursorTy) fltPrd5410;
            CursorTy pvrtmp6953 = (CursorTy) fltPrd5409;
            CursorTy y1591 = (CursorTy) pvrtmp6953;
            CursorTy fltPrd5411 = (CursorTy) pvrtmp6951;
            CursorTy fltPrd5412 = (CursorTy) pvrtmp6952;
            CursorTy pvrtmp6956 = (CursorTy) fltPrd5412;
            CursorTy pvrtmp6955 = (CursorTy) fltPrd5411;
            CursorTy end_y1591 = (CursorTy) pvrtmp6956;
            CursorTy end_r2076_3865_3866 = (CursorTy) pvrtmp6949;
            CursorTy endof3769 = (CursorTy) pvrtmp6950;
            IntTy sizeof_y1590_1592 = end_y1590 - y1590;
            IntTy sizeof_y1591_1593 = end_y1591 - y1591;
            IntTy fltPrm1906 = sizeof_y1590_1592 + 0;
            IntTy offset_1594 = 0 + fltPrm1906;
            IntTy fltPrm1907 = sizeof_y1590_1592 + sizeof_y1591_1593;
            IntTy size_dcon1595 = 9 + fltPrm1907;

            *(TagTyPacked *) loc2074 = 157;

            CursorTy writetag4612 = loc2074 + 1;

            *(IntTy *) writetag4612 = size_dcon1595;

            CursorTy writecur4613 = writetag4612 + sizeof(IntTy);

            *(IntTy *) writecur4613 = offset_1594;

            CursorTy writecur4614 = writecur4613 + sizeof(IntTy);
            CursorTy writecur4615 = (CursorTy) end_y1590;
            CursorTy writecur4616 = (CursorTy) end_y1591;
            CursorTy pvrtmp6958 = (CursorTy) writecur4616;
            CursorTy pvrtmp6957 = (CursorTy) loc2074;
            CursorTy taildc3770 = (CursorTy) pvrtmp6957;
            CursorTy end_taildc3770 = (CursorTy) pvrtmp6958;
            CursorTy pvrtmp6960 = (CursorTy) end_taildc3770;
            CursorTy pvrtmp6959 = (CursorTy) taildc3770;
            CursorTy fltPrd5413 = (CursorTy) pvrtmp6959;
            CursorTy fltPrd5414 = (CursorTy) pvrtmp6960;

            return (CursorCursorCursorCursorProd) {end_r2076_3865_3866,
                                                   endof3769, fltPrd5413,
                                                   fltPrd5414};
            break;
        }

      case 2:
        {
            CursorTy field_cur4618 = (CursorTy) tmpcur6920;
            CursorTy case3263 = (CursorTy) field_cur4618;
            CursorTy x1596 = (CursorTy) case3263;
            CursorTy loc3267 = loc2074 + 1;
            CursorCursorCursorCursorProd tmp_struct261 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r2075, end_r2076, loc3267, x1596);
            CursorTy pvrtmp6961 = tmp_struct261.field0;
            CursorTy pvrtmp6962 = tmp_struct261.field1;
            CursorTy pvrtmp6963 = tmp_struct261.field2;
            CursorTy pvrtmp6964 = tmp_struct261.field3;
            CursorTy fltPrd5415 = (CursorTy) pvrtmp6963;
            CursorTy fltPrd5416 = (CursorTy) pvrtmp6964;
            CursorTy pvrtmp6966 = (CursorTy) fltPrd5416;
            CursorTy pvrtmp6965 = (CursorTy) fltPrd5415;
            CursorTy y1597 = (CursorTy) pvrtmp6965;
            CursorTy fltPrd5417 = (CursorTy) pvrtmp6963;
            CursorTy fltPrd5418 = (CursorTy) pvrtmp6964;
            CursorTy pvrtmp6968 = (CursorTy) fltPrd5418;
            CursorTy pvrtmp6967 = (CursorTy) fltPrd5417;
            CursorTy end_y1597 = (CursorTy) pvrtmp6968;
            CursorTy end_r2076_3867 = (CursorTy) pvrtmp6961;
            CursorTy endof3771 = (CursorTy) pvrtmp6962;

            *(TagTyPacked *) loc2074 = 2;

            CursorTy writetag4620 = loc2074 + 1;
            CursorTy writecur4621 = (CursorTy) end_y1597;
            CursorTy pvrtmp6970 = (CursorTy) writecur4621;
            CursorTy pvrtmp6969 = (CursorTy) loc2074;
            CursorTy taildc3772 = (CursorTy) pvrtmp6969;
            CursorTy end_taildc3772 = (CursorTy) pvrtmp6970;
            CursorTy pvrtmp6972 = (CursorTy) end_taildc3772;
            CursorTy pvrtmp6971 = (CursorTy) taildc3772;
            CursorTy fltPrd5419 = (CursorTy) pvrtmp6971;
            CursorTy fltPrd5420 = (CursorTy) pvrtmp6972;

            return (CursorCursorCursorCursorProd) {end_r2076_3867, endof3771,
                                                   fltPrd5419, fltPrd5420};
            break;
        }

      case 3:
        {
            CursorTy field_cur4623 = (CursorTy) tmpcur6920;
            CursorTy case3269 = (CursorTy) field_cur4623;
            CursorTy x1598 = (CursorTy) case3269;
            CursorTy loc3273 = loc2074 + 1;
            CursorCursorCursorCursorProd tmp_struct262 =
                                          _add_size_and_rel_offsets_Expr(end_r2075, end_r2076, loc3273, x1598);
            CursorTy pvrtmp6973 = tmp_struct262.field0;
            CursorTy pvrtmp6974 = tmp_struct262.field1;
            CursorTy pvrtmp6975 = tmp_struct262.field2;
            CursorTy pvrtmp6976 = tmp_struct262.field3;
            CursorTy fltPrd5421 = (CursorTy) pvrtmp6975;
            CursorTy fltPrd5422 = (CursorTy) pvrtmp6976;
            CursorTy pvrtmp6978 = (CursorTy) fltPrd5422;
            CursorTy pvrtmp6977 = (CursorTy) fltPrd5421;
            CursorTy y1599 = (CursorTy) pvrtmp6977;
            CursorTy fltPrd5423 = (CursorTy) pvrtmp6975;
            CursorTy fltPrd5424 = (CursorTy) pvrtmp6976;
            CursorTy pvrtmp6980 = (CursorTy) fltPrd5424;
            CursorTy pvrtmp6979 = (CursorTy) fltPrd5423;
            CursorTy end_y1599 = (CursorTy) pvrtmp6980;
            CursorTy end_r2076_3868 = (CursorTy) pvrtmp6973;
            CursorTy endof3773 = (CursorTy) pvrtmp6974;

            *(TagTyPacked *) loc2074 = 3;

            CursorTy writetag4625 = loc2074 + 1;
            CursorTy writecur4626 = (CursorTy) end_y1599;
            CursorTy pvrtmp6982 = (CursorTy) writecur4626;
            CursorTy pvrtmp6981 = (CursorTy) loc2074;
            CursorTy taildc3774 = (CursorTy) pvrtmp6981;
            CursorTy end_taildc3774 = (CursorTy) pvrtmp6982;
            CursorTy pvrtmp6984 = (CursorTy) end_taildc3774;
            CursorTy pvrtmp6983 = (CursorTy) taildc3774;
            CursorTy fltPrd5425 = (CursorTy) pvrtmp6983;
            CursorTy fltPrd5426 = (CursorTy) pvrtmp6984;

            return (CursorCursorCursorCursorProd) {end_r2076_3868, endof3773,
                                                   fltPrd5425, fltPrd5426};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7476 = *(CursorTy *) tmpcur6920;
            CursorTy tmpaftercur7477 = tmpcur6920 + 8;
            TagTyPacked tagtmp7478 = *(TagTyPacked *) tmpcur7476;
            CursorTy tailtmp7479 = tmpcur7476 + 1;

            tmpval6919 = tagtmp7478;
            tmpcur6920 = tailtmp7479;
            goto switch6985;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7476 = *(CursorTy *) tmpcur6920;
            CursorTy tmpaftercur7477 = tmpcur6920 + 8;
            TagTyPacked tagtmp7478 = *(TagTyPacked *) tmpcur7476;
            CursorTy tailtmp7479 = tmpcur7476 + 1;

            tmpval6919 = tagtmp7478;
            tmpcur6920 = tailtmp7479;
            goto switch6985;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6919");
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
