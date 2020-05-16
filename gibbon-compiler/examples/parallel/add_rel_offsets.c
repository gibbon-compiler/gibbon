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

CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListSym(CursorTy end_r1892,
                                                               CursorTy end_r1893,
                                                               CursorTy loc1891,
                                                               CursorTy arg1404)
{
    CursorTy loc1890 = (CursorTy) arg1404;

    if (loc1891 + 18 > end_r1893) {
        ChunkTy new_chunk169 = alloc_chunk(end_r1893);
        CursorTy chunk_start170 = new_chunk169.start_ptr;
        CursorTy chunk_end171 = new_chunk169.end_ptr;

        end_r1893 = chunk_end171;
        *(TagTyPacked *) loc1891 = 255;

        CursorTy redir = loc1891 + 1;

        *(CursorTy *) redir = chunk_start170;
        loc1891 = chunk_start170;
    }

    CursorTy loc2645 = loc1891 + 1;
    CursorTy loc2646 = loc2645 + 8;
    TagTyPacked tmpval5720 = *(TagTyPacked *) arg1404;
    CursorTy tmpcur5721 = arg1404 + 1;


  switch5740:
    ;
    switch (tmpval5720) {

      case 0:
        {
            CursorTy field_cur3901 = (CursorTy) tmpcur5721;
            CursorTy case2640 = (CursorTy) field_cur3901;
            SymTy tmpval5722 = *(SymTy *) case2640;
            CursorTy tmpcur5723 = case2640 + sizeof(SymTy);
            SymTy x1405 = (SymTy) tmpval5722;
            CursorTy end_x1405 = (CursorTy) tmpcur5723;
            CursorTy case2641 = (CursorTy) end_x1405;
            CursorTy x1406 = (CursorTy) case2641;
            CursorTy jump3282 = case2640 + 8;
            CursorCursorCursorCursorProd tmp_struct168 =
                                          _add_size_and_rel_offsets_ListSym(end_r1892, end_r1893, loc2646, x1406);
            CursorTy pvrtmp5724 = tmp_struct168.field0;
            CursorTy pvrtmp5725 = tmp_struct168.field1;
            CursorTy pvrtmp5726 = tmp_struct168.field2;
            CursorTy pvrtmp5727 = tmp_struct168.field3;
            CursorTy fltPrd4614 = (CursorTy) pvrtmp5726;
            CursorTy fltPrd4615 = (CursorTy) pvrtmp5727;
            CursorTy pvrtmp5729 = (CursorTy) fltPrd4615;
            CursorTy pvrtmp5728 = (CursorTy) fltPrd4614;
            CursorTy y1408 = (CursorTy) pvrtmp5728;
            CursorTy fltPrd4616 = (CursorTy) pvrtmp5726;
            CursorTy fltPrd4617 = (CursorTy) pvrtmp5727;
            CursorTy pvrtmp5731 = (CursorTy) fltPrd4617;
            CursorTy pvrtmp5730 = (CursorTy) fltPrd4616;
            CursorTy end_y1408 = (CursorTy) pvrtmp5731;
            CursorTy end_r1893_3419 = (CursorTy) pvrtmp5724;
            CursorTy endof3283 = (CursorTy) pvrtmp5725;

            *(TagTyPacked *) loc1891 = 0;

            CursorTy writetag3904 = loc1891 + 1;

            *(SymTy *) writetag3904 = x1405;

            CursorTy writecur3905 = writetag3904 + sizeof(SymTy);
            CursorTy writecur3906 = (CursorTy) end_y1408;
            CursorTy pvrtmp5733 = (CursorTy) writecur3906;
            CursorTy pvrtmp5732 = (CursorTy) loc1891;
            CursorTy taildc3284 = (CursorTy) pvrtmp5732;
            CursorTy end_taildc3284 = (CursorTy) pvrtmp5733;
            CursorTy pvrtmp5735 = (CursorTy) end_taildc3284;
            CursorTy pvrtmp5734 = (CursorTy) taildc3284;
            CursorTy fltPrd4618 = (CursorTy) pvrtmp5734;
            CursorTy fltPrd4619 = (CursorTy) pvrtmp5735;

            return (CursorCursorCursorCursorProd) {end_r1893_3419, endof3283,
                                                   fltPrd4618, fltPrd4619};
            break;
        }

      case 1:
        {
            CursorTy field_cur3908 = (CursorTy) tmpcur5721;
            CursorTy jump3285 = loc1890 + 1;

            *(TagTyPacked *) loc1891 = 1;

            CursorTy writetag3909 = loc1891 + 1;
            CursorTy pvrtmp5737 = (CursorTy) writetag3909;
            CursorTy pvrtmp5736 = (CursorTy) loc1891;
            CursorTy taildc3286 = (CursorTy) pvrtmp5736;
            CursorTy end_taildc3286 = (CursorTy) pvrtmp5737;
            CursorTy pvrtmp5739 = (CursorTy) end_taildc3286;
            CursorTy pvrtmp5738 = (CursorTy) taildc3286;
            CursorTy fltPrd4620 = (CursorTy) pvrtmp5738;
            CursorTy fltPrd4621 = (CursorTy) pvrtmp5739;

            return (CursorCursorCursorCursorProd) {end_r1893, jump3285,
                                                   fltPrd4620, fltPrd4621};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6645 = *(CursorTy *) tmpcur5721;
            CursorTy tmpaftercur6646 = tmpcur5721 + 8;
            TagTyPacked tagtmp6647 = *(TagTyPacked *) tmpcur6645;
            CursorTy tailtmp6648 = tmpcur6645 + 1;

            tmpval5720 = tagtmp6647;
            tmpcur5721 = tailtmp6648;
            goto switch5740;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6645 = *(CursorTy *) tmpcur5721;
            CursorTy tmpaftercur6646 = tmpcur5721 + 8;
            TagTyPacked tagtmp6647 = *(TagTyPacked *) tmpcur6645;
            CursorTy tailtmp6648 = tmpcur6645 + 1;

            tmpval5720 = tagtmp6647;
            tmpcur5721 = tailtmp6648;
            goto switch5740;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5720");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListExpr(CursorTy end_r1896,
                                                                CursorTy end_r1897,
                                                                CursorTy loc1895,
                                                                CursorTy arg1409)
{
    CursorTy loc1894 = (CursorTy) arg1409;

    if (loc1895 + 18 > end_r1897) {
        ChunkTy new_chunk174 = alloc_chunk(end_r1897);
        CursorTy chunk_start175 = new_chunk174.start_ptr;
        CursorTy chunk_end176 = new_chunk174.end_ptr;

        end_r1897 = chunk_end176;
        *(TagTyPacked *) loc1895 = 255;

        CursorTy redir = loc1895 + 1;

        *(CursorTy *) redir = chunk_start175;
        loc1895 = chunk_start175;
    }

    TagTyPacked tmpval5741 = *(TagTyPacked *) arg1409;
    CursorTy tmpcur5742 = arg1409 + 1;


  switch5767:
    ;
    switch (tmpval5741) {

      case 0:
        {
            CursorTy field_cur3911 = (CursorTy) tmpcur5742;
            CursorTy case2653 = (CursorTy) field_cur3911;
            CursorTy x1410 = (CursorTy) case2653;
            CursorTy loc2661 = loc1895 + 1;
            CursorCursorCursorCursorProd tmp_struct172 =
                                          _add_size_and_rel_offsets_Expr(end_r1896, end_r1897, loc2661, x1410);
            CursorTy pvrtmp5743 = tmp_struct172.field0;
            CursorTy pvrtmp5744 = tmp_struct172.field1;
            CursorTy pvrtmp5745 = tmp_struct172.field2;
            CursorTy pvrtmp5746 = tmp_struct172.field3;
            CursorTy fltPrd4622 = (CursorTy) pvrtmp5745;
            CursorTy fltPrd4623 = (CursorTy) pvrtmp5746;
            CursorTy pvrtmp5748 = (CursorTy) fltPrd4623;
            CursorTy pvrtmp5747 = (CursorTy) fltPrd4622;
            CursorTy y1412 = (CursorTy) pvrtmp5747;
            CursorTy fltPrd4624 = (CursorTy) pvrtmp5745;
            CursorTy fltPrd4625 = (CursorTy) pvrtmp5746;
            CursorTy pvrtmp5750 = (CursorTy) fltPrd4625;
            CursorTy pvrtmp5749 = (CursorTy) fltPrd4624;
            CursorTy end_y1412 = (CursorTy) pvrtmp5750;
            CursorTy end_r1897_3420 = (CursorTy) pvrtmp5743;
            CursorTy endof3287 = (CursorTy) pvrtmp5744;
            CursorTy case2654 = (CursorTy) endof3287;
            CursorTy x1411 = (CursorTy) case2654;
            CursorTy loc2662 = (CursorTy) end_y1412;
            CursorCursorCursorCursorProd tmp_struct173 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1896, end_r1897_3420, loc2662, x1411);
            CursorTy pvrtmp5751 = tmp_struct173.field0;
            CursorTy pvrtmp5752 = tmp_struct173.field1;
            CursorTy pvrtmp5753 = tmp_struct173.field2;
            CursorTy pvrtmp5754 = tmp_struct173.field3;
            CursorTy fltPrd4626 = (CursorTy) pvrtmp5753;
            CursorTy fltPrd4627 = (CursorTy) pvrtmp5754;
            CursorTy pvrtmp5756 = (CursorTy) fltPrd4627;
            CursorTy pvrtmp5755 = (CursorTy) fltPrd4626;
            CursorTy y1413 = (CursorTy) pvrtmp5755;
            CursorTy fltPrd4628 = (CursorTy) pvrtmp5753;
            CursorTy fltPrd4629 = (CursorTy) pvrtmp5754;
            CursorTy pvrtmp5758 = (CursorTy) fltPrd4629;
            CursorTy pvrtmp5757 = (CursorTy) fltPrd4628;
            CursorTy end_y1413 = (CursorTy) pvrtmp5758;
            CursorTy end_r1897_3420_3421 = (CursorTy) pvrtmp5751;
            CursorTy endof3288 = (CursorTy) pvrtmp5752;

            *(TagTyPacked *) loc1895 = 0;

            CursorTy writetag3914 = loc1895 + 1;
            CursorTy writecur3915 = (CursorTy) end_y1412;
            CursorTy writecur3916 = (CursorTy) end_y1413;
            CursorTy pvrtmp5760 = (CursorTy) writecur3916;
            CursorTy pvrtmp5759 = (CursorTy) loc1895;
            CursorTy taildc3289 = (CursorTy) pvrtmp5759;
            CursorTy end_taildc3289 = (CursorTy) pvrtmp5760;
            CursorTy pvrtmp5762 = (CursorTy) end_taildc3289;
            CursorTy pvrtmp5761 = (CursorTy) taildc3289;
            CursorTy fltPrd4630 = (CursorTy) pvrtmp5761;
            CursorTy fltPrd4631 = (CursorTy) pvrtmp5762;

            return (CursorCursorCursorCursorProd) {end_r1897_3420_3421,
                                                   endof3288, fltPrd4630,
                                                   fltPrd4631};
            break;
        }

      case 1:
        {
            CursorTy field_cur3918 = (CursorTy) tmpcur5742;
            CursorTy jump3290 = loc1894 + 1;

            *(TagTyPacked *) loc1895 = 1;

            CursorTy writetag3919 = loc1895 + 1;
            CursorTy pvrtmp5764 = (CursorTy) writetag3919;
            CursorTy pvrtmp5763 = (CursorTy) loc1895;
            CursorTy taildc3291 = (CursorTy) pvrtmp5763;
            CursorTy end_taildc3291 = (CursorTy) pvrtmp5764;
            CursorTy pvrtmp5766 = (CursorTy) end_taildc3291;
            CursorTy pvrtmp5765 = (CursorTy) taildc3291;
            CursorTy fltPrd4632 = (CursorTy) pvrtmp5765;
            CursorTy fltPrd4633 = (CursorTy) pvrtmp5766;

            return (CursorCursorCursorCursorProd) {end_r1897, jump3290,
                                                   fltPrd4632, fltPrd4633};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6649 = *(CursorTy *) tmpcur5742;
            CursorTy tmpaftercur6650 = tmpcur5742 + 8;
            TagTyPacked tagtmp6651 = *(TagTyPacked *) tmpcur6649;
            CursorTy tailtmp6652 = tmpcur6649 + 1;

            tmpval5741 = tagtmp6651;
            tmpcur5742 = tailtmp6652;
            goto switch5767;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6649 = *(CursorTy *) tmpcur5742;
            CursorTy tmpaftercur6650 = tmpcur5742 + 8;
            TagTyPacked tagtmp6651 = *(TagTyPacked *) tmpcur6649;
            CursorTy tailtmp6652 = tmpcur6649 + 1;

            tmpval5741 = tagtmp6651;
            tmpcur5742 = tailtmp6652;
            goto switch5767;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5741");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_ListToplvl(CursorTy end_r1900,
                                                                  CursorTy end_r1901,
                                                                  CursorTy loc1899,
                                                                  CursorTy arg1414)
{
    CursorTy loc1898 = (CursorTy) arg1414;

    if (loc1899 + 26 > end_r1901) {
        ChunkTy new_chunk179 = alloc_chunk(end_r1901);
        CursorTy chunk_start180 = new_chunk179.start_ptr;
        CursorTy chunk_end181 = new_chunk179.end_ptr;

        end_r1901 = chunk_end181;
        *(TagTyPacked *) loc1899 = 255;

        CursorTy redir = loc1899 + 1;

        *(CursorTy *) redir = chunk_start180;
        loc1899 = chunk_start180;
    }

    CursorTy loc2676 = loc1899 + 1;
    CursorTy loc2677 = loc2676 + 8;
    CursorTy loc2678 = loc2677 + 8;
    TagTyPacked tmpval5768 = *(TagTyPacked *) arg1414;
    CursorTy tmpcur5769 = arg1414 + 1;


  switch5794:
    ;
    switch (tmpval5768) {

      case 0:
        {
            CursorTy field_cur3921 = (CursorTy) tmpcur5769;
            CursorTy case2668 = (CursorTy) field_cur3921;
            CursorTy x1415 = (CursorTy) case2668;
            CursorCursorCursorCursorProd tmp_struct177 =
                                          _add_size_and_rel_offsets_Toplvl(end_r1900, end_r1901, loc2678, x1415);
            CursorTy pvrtmp5770 = tmp_struct177.field0;
            CursorTy pvrtmp5771 = tmp_struct177.field1;
            CursorTy pvrtmp5772 = tmp_struct177.field2;
            CursorTy pvrtmp5773 = tmp_struct177.field3;
            CursorTy fltPrd4634 = (CursorTy) pvrtmp5772;
            CursorTy fltPrd4635 = (CursorTy) pvrtmp5773;
            CursorTy pvrtmp5775 = (CursorTy) fltPrd4635;
            CursorTy pvrtmp5774 = (CursorTy) fltPrd4634;
            CursorTy y1417 = (CursorTy) pvrtmp5774;
            CursorTy fltPrd4636 = (CursorTy) pvrtmp5772;
            CursorTy fltPrd4637 = (CursorTy) pvrtmp5773;
            CursorTy pvrtmp5777 = (CursorTy) fltPrd4637;
            CursorTy pvrtmp5776 = (CursorTy) fltPrd4636;
            CursorTy end_y1417 = (CursorTy) pvrtmp5777;
            CursorTy end_r1901_3422 = (CursorTy) pvrtmp5770;
            CursorTy endof3292 = (CursorTy) pvrtmp5771;
            CursorTy case2669 = (CursorTy) endof3292;
            CursorTy x1416 = (CursorTy) case2669;
            CursorTy loc2679 = (CursorTy) end_y1417;
            CursorCursorCursorCursorProd tmp_struct178 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r1900, end_r1901_3422, loc2679, x1416);
            CursorTy pvrtmp5778 = tmp_struct178.field0;
            CursorTy pvrtmp5779 = tmp_struct178.field1;
            CursorTy pvrtmp5780 = tmp_struct178.field2;
            CursorTy pvrtmp5781 = tmp_struct178.field3;
            CursorTy fltPrd4638 = (CursorTy) pvrtmp5780;
            CursorTy fltPrd4639 = (CursorTy) pvrtmp5781;
            CursorTy pvrtmp5783 = (CursorTy) fltPrd4639;
            CursorTy pvrtmp5782 = (CursorTy) fltPrd4638;
            CursorTy y1418 = (CursorTy) pvrtmp5782;
            CursorTy fltPrd4640 = (CursorTy) pvrtmp5780;
            CursorTy fltPrd4641 = (CursorTy) pvrtmp5781;
            CursorTy pvrtmp5785 = (CursorTy) fltPrd4641;
            CursorTy pvrtmp5784 = (CursorTy) fltPrd4640;
            CursorTy end_y1418 = (CursorTy) pvrtmp5785;
            CursorTy end_r1901_3422_3423 = (CursorTy) pvrtmp5778;
            CursorTy endof3293 = (CursorTy) pvrtmp5779;
            IntTy sizeof_y1417_1419 = end_y1417 - y1417;
            IntTy sizeof_y1418_1420 = end_y1418 - y1418;
            IntTy fltPrm1763 = sizeof_y1417_1419 + 0;
            IntTy offset_1421 = 0 + fltPrm1763;
            IntTy fltPrm1764 = sizeof_y1417_1419 + sizeof_y1418_1420;
            IntTy size_dcon1422 = 9 + fltPrm1764;

            *(TagTyPacked *) loc1899 = 153;

            CursorTy writetag3924 = loc1899 + 1;

            *(IntTy *) writetag3924 = size_dcon1422;

            CursorTy writecur3925 = writetag3924 + sizeof(IntTy);

            *(IntTy *) writecur3925 = offset_1421;

            CursorTy writecur3926 = writecur3925 + sizeof(IntTy);
            CursorTy writecur3927 = (CursorTy) end_y1417;
            CursorTy writecur3928 = (CursorTy) end_y1418;
            CursorTy pvrtmp5787 = (CursorTy) writecur3928;
            CursorTy pvrtmp5786 = (CursorTy) loc1899;
            CursorTy taildc3294 = (CursorTy) pvrtmp5786;
            CursorTy end_taildc3294 = (CursorTy) pvrtmp5787;
            CursorTy pvrtmp5789 = (CursorTy) end_taildc3294;
            CursorTy pvrtmp5788 = (CursorTy) taildc3294;
            CursorTy fltPrd4642 = (CursorTy) pvrtmp5788;
            CursorTy fltPrd4643 = (CursorTy) pvrtmp5789;

            return (CursorCursorCursorCursorProd) {end_r1901_3422_3423,
                                                   endof3293, fltPrd4642,
                                                   fltPrd4643};
            break;
        }

      case 1:
        {
            CursorTy field_cur3930 = (CursorTy) tmpcur5769;
            CursorTy jump3295 = loc1898 + 1;

            *(TagTyPacked *) loc1899 = 1;

            CursorTy writetag3931 = loc1899 + 1;
            CursorTy pvrtmp5791 = (CursorTy) writetag3931;
            CursorTy pvrtmp5790 = (CursorTy) loc1899;
            CursorTy taildc3296 = (CursorTy) pvrtmp5790;
            CursorTy end_taildc3296 = (CursorTy) pvrtmp5791;
            CursorTy pvrtmp5793 = (CursorTy) end_taildc3296;
            CursorTy pvrtmp5792 = (CursorTy) taildc3296;
            CursorTy fltPrd4644 = (CursorTy) pvrtmp5792;
            CursorTy fltPrd4645 = (CursorTy) pvrtmp5793;

            return (CursorCursorCursorCursorProd) {end_r1901, jump3295,
                                                   fltPrd4644, fltPrd4645};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6653 = *(CursorTy *) tmpcur5769;
            CursorTy tmpaftercur6654 = tmpcur5769 + 8;
            TagTyPacked tagtmp6655 = *(TagTyPacked *) tmpcur6653;
            CursorTy tailtmp6656 = tmpcur6653 + 1;

            tmpval5768 = tagtmp6655;
            tmpcur5769 = tailtmp6656;
            goto switch5794;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6653 = *(CursorTy *) tmpcur5769;
            CursorTy tmpaftercur6654 = tmpcur5769 + 8;
            TagTyPacked tagtmp6655 = *(TagTyPacked *) tmpcur6653;
            CursorTy tailtmp6656 = tmpcur6653 + 1;

            tmpval5768 = tagtmp6655;
            tmpcur5769 = tailtmp6656;
            goto switch5794;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5768");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Formals(CursorTy end_r1904,
                                                               CursorTy end_r1905,
                                                               CursorTy loc1903,
                                                               CursorTy arg1423)
{
    CursorTy loc1902 = (CursorTy) arg1423;

    if (loc1903 + 18 > end_r1905) {
        ChunkTy new_chunk184 = alloc_chunk(end_r1905);
        CursorTy chunk_start185 = new_chunk184.start_ptr;
        CursorTy chunk_end186 = new_chunk184.end_ptr;

        end_r1905 = chunk_end186;
        *(TagTyPacked *) loc1903 = 255;

        CursorTy redir = loc1903 + 1;

        *(CursorTy *) redir = chunk_start185;
        loc1903 = chunk_start185;
    }

    TagTyPacked tmpval5795 = *(TagTyPacked *) arg1423;
    CursorTy tmpcur5796 = arg1423 + 1;


  switch5829:
    ;
    switch (tmpval5795) {

      case 0:
        {
            CursorTy field_cur3933 = (CursorTy) tmpcur5796;
            CursorTy case2689 = (CursorTy) field_cur3933;
            CursorTy x1424 = (CursorTy) case2689;
            CursorTy loc2693 = loc1903 + 1;
            CursorCursorCursorCursorProd tmp_struct182 =
                                          _add_size_and_rel_offsets_ListSym(end_r1904, end_r1905, loc2693, x1424);
            CursorTy pvrtmp5797 = tmp_struct182.field0;
            CursorTy pvrtmp5798 = tmp_struct182.field1;
            CursorTy pvrtmp5799 = tmp_struct182.field2;
            CursorTy pvrtmp5800 = tmp_struct182.field3;
            CursorTy fltPrd4646 = (CursorTy) pvrtmp5799;
            CursorTy fltPrd4647 = (CursorTy) pvrtmp5800;
            CursorTy pvrtmp5802 = (CursorTy) fltPrd4647;
            CursorTy pvrtmp5801 = (CursorTy) fltPrd4646;
            CursorTy y1425 = (CursorTy) pvrtmp5801;
            CursorTy fltPrd4648 = (CursorTy) pvrtmp5799;
            CursorTy fltPrd4649 = (CursorTy) pvrtmp5800;
            CursorTy pvrtmp5804 = (CursorTy) fltPrd4649;
            CursorTy pvrtmp5803 = (CursorTy) fltPrd4648;
            CursorTy end_y1425 = (CursorTy) pvrtmp5804;
            CursorTy end_r1905_3424 = (CursorTy) pvrtmp5797;
            CursorTy endof3297 = (CursorTy) pvrtmp5798;

            *(TagTyPacked *) loc1903 = 0;

            CursorTy writetag3935 = loc1903 + 1;
            CursorTy writecur3936 = (CursorTy) end_y1425;
            CursorTy pvrtmp5806 = (CursorTy) writecur3936;
            CursorTy pvrtmp5805 = (CursorTy) loc1903;
            CursorTy taildc3298 = (CursorTy) pvrtmp5805;
            CursorTy end_taildc3298 = (CursorTy) pvrtmp5806;
            CursorTy pvrtmp5808 = (CursorTy) end_taildc3298;
            CursorTy pvrtmp5807 = (CursorTy) taildc3298;
            CursorTy fltPrd4650 = (CursorTy) pvrtmp5807;
            CursorTy fltPrd4651 = (CursorTy) pvrtmp5808;

            return (CursorCursorCursorCursorProd) {end_r1905_3424, endof3297,
                                                   fltPrd4650, fltPrd4651};
            break;
        }

      case 1:
        {
            CursorTy field_cur3938 = (CursorTy) tmpcur5796;
            CursorTy case2695 = (CursorTy) field_cur3938;
            CursorTy x1426 = (CursorTy) case2695;
            CursorTy loc2700 = loc1903 + 1;
            CursorCursorCursorCursorProd tmp_struct183 =
                                          _add_size_and_rel_offsets_ListSym(end_r1904, end_r1905, loc2700, x1426);
            CursorTy pvrtmp5809 = tmp_struct183.field0;
            CursorTy pvrtmp5810 = tmp_struct183.field1;
            CursorTy pvrtmp5811 = tmp_struct183.field2;
            CursorTy pvrtmp5812 = tmp_struct183.field3;
            CursorTy fltPrd4652 = (CursorTy) pvrtmp5811;
            CursorTy fltPrd4653 = (CursorTy) pvrtmp5812;
            CursorTy pvrtmp5814 = (CursorTy) fltPrd4653;
            CursorTy pvrtmp5813 = (CursorTy) fltPrd4652;
            CursorTy y1428 = (CursorTy) pvrtmp5813;
            CursorTy fltPrd4654 = (CursorTy) pvrtmp5811;
            CursorTy fltPrd4655 = (CursorTy) pvrtmp5812;
            CursorTy pvrtmp5816 = (CursorTy) fltPrd4655;
            CursorTy pvrtmp5815 = (CursorTy) fltPrd4654;
            CursorTy end_y1428 = (CursorTy) pvrtmp5816;
            CursorTy end_r1905_3425 = (CursorTy) pvrtmp5809;
            CursorTy endof3300 = (CursorTy) pvrtmp5810;
            CursorTy case2696 = (CursorTy) endof3300;
            CursorTy jump3299 = case2696 + 8;
            SymTy tmpval5817 = *(SymTy *) case2696;
            CursorTy tmpcur5818 = case2696 + sizeof(SymTy);
            SymTy x1427 = (SymTy) tmpval5817;
            CursorTy end_x1427 = (CursorTy) tmpcur5818;

            *(TagTyPacked *) loc1903 = 1;

            CursorTy writetag3941 = loc1903 + 1;
            CursorTy writecur3942 = (CursorTy) end_y1428;

            *(SymTy *) writecur3942 = x1427;

            CursorTy writecur3943 = writecur3942 + sizeof(SymTy);
            CursorTy pvrtmp5820 = (CursorTy) writecur3943;
            CursorTy pvrtmp5819 = (CursorTy) loc1903;
            CursorTy taildc3301 = (CursorTy) pvrtmp5819;
            CursorTy end_taildc3301 = (CursorTy) pvrtmp5820;
            CursorTy pvrtmp5822 = (CursorTy) end_taildc3301;
            CursorTy pvrtmp5821 = (CursorTy) taildc3301;
            CursorTy fltPrd4656 = (CursorTy) pvrtmp5821;
            CursorTy fltPrd4657 = (CursorTy) pvrtmp5822;

            return (CursorCursorCursorCursorProd) {end_r1905_3425, jump3299,
                                                   fltPrd4656, fltPrd4657};
            break;
        }

      case 2:
        {
            CursorTy field_cur3945 = (CursorTy) tmpcur5796;
            CursorTy case2705 = (CursorTy) field_cur3945;
            SymTy tmpval5823 = *(SymTy *) case2705;
            CursorTy tmpcur5824 = case2705 + sizeof(SymTy);
            SymTy x1430 = (SymTy) tmpval5823;
            CursorTy end_x1430 = (CursorTy) tmpcur5824;
            CursorTy jump3302 = case2705 + 8;

            *(TagTyPacked *) loc1903 = 2;

            CursorTy writetag3947 = loc1903 + 1;

            *(SymTy *) writetag3947 = x1430;

            CursorTy writecur3948 = writetag3947 + sizeof(SymTy);
            CursorTy pvrtmp5826 = (CursorTy) writecur3948;
            CursorTy pvrtmp5825 = (CursorTy) loc1903;
            CursorTy taildc3303 = (CursorTy) pvrtmp5825;
            CursorTy end_taildc3303 = (CursorTy) pvrtmp5826;
            CursorTy pvrtmp5828 = (CursorTy) end_taildc3303;
            CursorTy pvrtmp5827 = (CursorTy) taildc3303;
            CursorTy fltPrd4658 = (CursorTy) pvrtmp5827;
            CursorTy fltPrd4659 = (CursorTy) pvrtmp5828;

            return (CursorCursorCursorCursorProd) {end_r1905, jump3302,
                                                   fltPrd4658, fltPrd4659};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6657 = *(CursorTy *) tmpcur5796;
            CursorTy tmpaftercur6658 = tmpcur5796 + 8;
            TagTyPacked tagtmp6659 = *(TagTyPacked *) tmpcur6657;
            CursorTy tailtmp6660 = tmpcur6657 + 1;

            tmpval5795 = tagtmp6659;
            tmpcur5796 = tailtmp6660;
            goto switch5829;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6657 = *(CursorTy *) tmpcur5796;
            CursorTy tmpaftercur6658 = tmpcur5796 + 8;
            TagTyPacked tagtmp6659 = *(TagTyPacked *) tmpcur6657;
            CursorTy tailtmp6660 = tmpcur6657 + 1;

            tmpval5795 = tagtmp6659;
            tmpcur5796 = tailtmp6660;
            goto switch5829;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5795");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Datum(CursorTy end_r1908,
                                                             CursorTy end_r1909,
                                                             CursorTy loc1907,
                                                             CursorTy arg1432)
{
    CursorTy loc1906 = (CursorTy) arg1432;

    if (loc1907 + 18 > end_r1909) {
        ChunkTy new_chunk187 = alloc_chunk(end_r1909);
        CursorTy chunk_start188 = new_chunk187.start_ptr;
        CursorTy chunk_end189 = new_chunk187.end_ptr;

        end_r1909 = chunk_end189;
        *(TagTyPacked *) loc1907 = 255;

        CursorTy redir = loc1907 + 1;

        *(CursorTy *) redir = chunk_start188;
        loc1907 = chunk_start188;
    }

    TagTyPacked tmpval5830 = *(TagTyPacked *) arg1432;
    CursorTy tmpcur5831 = arg1432 + 1;


  switch5838:
    ;
    switch (tmpval5830) {

      case 0:
        {
            CursorTy field_cur3950 = (CursorTy) tmpcur5831;
            CursorTy case2711 = (CursorTy) field_cur3950;
            IntTy tmpval5832 = *(IntTy *) case2711;
            CursorTy tmpcur5833 = case2711 + sizeof(IntTy);
            IntTy x1433 = (IntTy) tmpval5832;
            CursorTy end_x1433 = (CursorTy) tmpcur5833;
            CursorTy jump3304 = case2711 + 8;

            *(TagTyPacked *) loc1907 = 0;

            CursorTy writetag3952 = loc1907 + 1;

            *(IntTy *) writetag3952 = x1433;

            CursorTy writecur3953 = writetag3952 + sizeof(IntTy);
            CursorTy pvrtmp5835 = (CursorTy) writecur3953;
            CursorTy pvrtmp5834 = (CursorTy) loc1907;
            CursorTy taildc3305 = (CursorTy) pvrtmp5834;
            CursorTy end_taildc3305 = (CursorTy) pvrtmp5835;
            CursorTy pvrtmp5837 = (CursorTy) end_taildc3305;
            CursorTy pvrtmp5836 = (CursorTy) taildc3305;
            CursorTy fltPrd4660 = (CursorTy) pvrtmp5836;
            CursorTy fltPrd4661 = (CursorTy) pvrtmp5837;

            return (CursorCursorCursorCursorProd) {end_r1909, jump3304,
                                                   fltPrd4660, fltPrd4661};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6661 = *(CursorTy *) tmpcur5831;
            CursorTy tmpaftercur6662 = tmpcur5831 + 8;
            TagTyPacked tagtmp6663 = *(TagTyPacked *) tmpcur6661;
            CursorTy tailtmp6664 = tmpcur6661 + 1;

            tmpval5830 = tagtmp6663;
            tmpcur5831 = tailtmp6664;
            goto switch5838;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6661 = *(CursorTy *) tmpcur5831;
            CursorTy tmpaftercur6662 = tmpcur5831 + 8;
            TagTyPacked tagtmp6663 = *(TagTyPacked *) tmpcur6661;
            CursorTy tailtmp6664 = tmpcur6661 + 1;

            tmpval5830 = tagtmp6663;
            tmpcur5831 = tailtmp6664;
            goto switch5838;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5830");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LAMBDACASE(CursorTy end_r1912,
                                                                  CursorTy end_r1913,
                                                                  CursorTy loc1911,
                                                                  CursorTy arg1435)
{
    CursorTy loc1910 = (CursorTy) arg1435;

    if (loc1911 + 18 > end_r1913) {
        ChunkTy new_chunk193 = alloc_chunk(end_r1913);
        CursorTy chunk_start194 = new_chunk193.start_ptr;
        CursorTy chunk_end195 = new_chunk193.end_ptr;

        end_r1913 = chunk_end195;
        *(TagTyPacked *) loc1911 = 255;

        CursorTy redir = loc1911 + 1;

        *(CursorTy *) redir = chunk_start194;
        loc1911 = chunk_start194;
    }

    TagTyPacked tmpval5839 = *(TagTyPacked *) arg1435;
    CursorTy tmpcur5840 = arg1435 + 1;


  switch5873:
    ;
    switch (tmpval5839) {

      case 0:
        {
            CursorTy field_cur3955 = (CursorTy) tmpcur5840;
            CursorTy case2717 = (CursorTy) field_cur3955;
            CursorTy x1436 = (CursorTy) case2717;
            CursorTy loc2729 = loc1911 + 1;
            CursorCursorCursorCursorProd tmp_struct190 =
                                          _add_size_and_rel_offsets_Formals(end_r1912, end_r1913, loc2729, x1436);
            CursorTy pvrtmp5841 = tmp_struct190.field0;
            CursorTy pvrtmp5842 = tmp_struct190.field1;
            CursorTy pvrtmp5843 = tmp_struct190.field2;
            CursorTy pvrtmp5844 = tmp_struct190.field3;
            CursorTy fltPrd4662 = (CursorTy) pvrtmp5843;
            CursorTy fltPrd4663 = (CursorTy) pvrtmp5844;
            CursorTy pvrtmp5846 = (CursorTy) fltPrd4663;
            CursorTy pvrtmp5845 = (CursorTy) fltPrd4662;
            CursorTy y1439 = (CursorTy) pvrtmp5845;
            CursorTy fltPrd4664 = (CursorTy) pvrtmp5843;
            CursorTy fltPrd4665 = (CursorTy) pvrtmp5844;
            CursorTy pvrtmp5848 = (CursorTy) fltPrd4665;
            CursorTy pvrtmp5847 = (CursorTy) fltPrd4664;
            CursorTy end_y1439 = (CursorTy) pvrtmp5848;
            CursorTy end_r1913_3426 = (CursorTy) pvrtmp5841;
            CursorTy endof3306 = (CursorTy) pvrtmp5842;
            CursorTy case2718 = (CursorTy) endof3306;
            CursorTy x1437 = (CursorTy) case2718;
            CursorTy loc2730 = (CursorTy) end_y1439;
            CursorCursorCursorCursorProd tmp_struct191 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1912, end_r1913_3426, loc2730, x1437);
            CursorTy pvrtmp5849 = tmp_struct191.field0;
            CursorTy pvrtmp5850 = tmp_struct191.field1;
            CursorTy pvrtmp5851 = tmp_struct191.field2;
            CursorTy pvrtmp5852 = tmp_struct191.field3;
            CursorTy fltPrd4666 = (CursorTy) pvrtmp5851;
            CursorTy fltPrd4667 = (CursorTy) pvrtmp5852;
            CursorTy pvrtmp5854 = (CursorTy) fltPrd4667;
            CursorTy pvrtmp5853 = (CursorTy) fltPrd4666;
            CursorTy y1440 = (CursorTy) pvrtmp5853;
            CursorTy fltPrd4668 = (CursorTy) pvrtmp5851;
            CursorTy fltPrd4669 = (CursorTy) pvrtmp5852;
            CursorTy pvrtmp5856 = (CursorTy) fltPrd4669;
            CursorTy pvrtmp5855 = (CursorTy) fltPrd4668;
            CursorTy end_y1440 = (CursorTy) pvrtmp5856;
            CursorTy end_r1913_3426_3427 = (CursorTy) pvrtmp5849;
            CursorTy endof3307 = (CursorTy) pvrtmp5850;
            CursorTy case2719 = (CursorTy) endof3307;
            CursorTy x1438 = (CursorTy) case2719;
            CursorTy loc2731 = (CursorTy) end_y1440;
            CursorCursorCursorCursorProd tmp_struct192 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r1912, end_r1913_3426_3427, loc2731, x1438);
            CursorTy pvrtmp5857 = tmp_struct192.field0;
            CursorTy pvrtmp5858 = tmp_struct192.field1;
            CursorTy pvrtmp5859 = tmp_struct192.field2;
            CursorTy pvrtmp5860 = tmp_struct192.field3;
            CursorTy fltPrd4670 = (CursorTy) pvrtmp5859;
            CursorTy fltPrd4671 = (CursorTy) pvrtmp5860;
            CursorTy pvrtmp5862 = (CursorTy) fltPrd4671;
            CursorTy pvrtmp5861 = (CursorTy) fltPrd4670;
            CursorTy y1441 = (CursorTy) pvrtmp5861;
            CursorTy fltPrd4672 = (CursorTy) pvrtmp5859;
            CursorTy fltPrd4673 = (CursorTy) pvrtmp5860;
            CursorTy pvrtmp5864 = (CursorTy) fltPrd4673;
            CursorTy pvrtmp5863 = (CursorTy) fltPrd4672;
            CursorTy end_y1441 = (CursorTy) pvrtmp5864;
            CursorTy end_r1913_3426_3427_3428 = (CursorTy) pvrtmp5857;
            CursorTy endof3308 = (CursorTy) pvrtmp5858;

            *(TagTyPacked *) loc1911 = 0;

            CursorTy writetag3959 = loc1911 + 1;
            CursorTy writecur3960 = (CursorTy) end_y1439;
            CursorTy writecur3961 = (CursorTy) end_y1440;
            CursorTy writecur3962 = (CursorTy) end_y1441;
            CursorTy pvrtmp5866 = (CursorTy) writecur3962;
            CursorTy pvrtmp5865 = (CursorTy) loc1911;
            CursorTy taildc3309 = (CursorTy) pvrtmp5865;
            CursorTy end_taildc3309 = (CursorTy) pvrtmp5866;
            CursorTy pvrtmp5868 = (CursorTy) end_taildc3309;
            CursorTy pvrtmp5867 = (CursorTy) taildc3309;
            CursorTy fltPrd4674 = (CursorTy) pvrtmp5867;
            CursorTy fltPrd4675 = (CursorTy) pvrtmp5868;

            return (CursorCursorCursorCursorProd) {end_r1913_3426_3427_3428,
                                                   endof3308, fltPrd4674,
                                                   fltPrd4675};
            break;
        }

      case 1:
        {
            CursorTy field_cur3964 = (CursorTy) tmpcur5840;
            CursorTy jump3310 = loc1910 + 1;

            *(TagTyPacked *) loc1911 = 1;

            CursorTy writetag3965 = loc1911 + 1;
            CursorTy pvrtmp5870 = (CursorTy) writetag3965;
            CursorTy pvrtmp5869 = (CursorTy) loc1911;
            CursorTy taildc3311 = (CursorTy) pvrtmp5869;
            CursorTy end_taildc3311 = (CursorTy) pvrtmp5870;
            CursorTy pvrtmp5872 = (CursorTy) end_taildc3311;
            CursorTy pvrtmp5871 = (CursorTy) taildc3311;
            CursorTy fltPrd4676 = (CursorTy) pvrtmp5871;
            CursorTy fltPrd4677 = (CursorTy) pvrtmp5872;

            return (CursorCursorCursorCursorProd) {end_r1913, jump3310,
                                                   fltPrd4676, fltPrd4677};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6665 = *(CursorTy *) tmpcur5840;
            CursorTy tmpaftercur6666 = tmpcur5840 + 8;
            TagTyPacked tagtmp6667 = *(TagTyPacked *) tmpcur6665;
            CursorTy tailtmp6668 = tmpcur6665 + 1;

            tmpval5839 = tagtmp6667;
            tmpcur5840 = tailtmp6668;
            goto switch5873;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6665 = *(CursorTy *) tmpcur5840;
            CursorTy tmpaftercur6666 = tmpcur5840 + 8;
            TagTyPacked tagtmp6667 = *(TagTyPacked *) tmpcur6665;
            CursorTy tailtmp6668 = tmpcur6665 + 1;

            tmpval5839 = tagtmp6667;
            tmpcur5840 = tailtmp6668;
            goto switch5873;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5839");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_LVBIND(CursorTy end_r1916,
                                                              CursorTy end_r1917,
                                                              CursorTy loc1915,
                                                              CursorTy arg1442)
{
    CursorTy loc1914 = (CursorTy) arg1442;

    if (loc1915 + 18 > end_r1917) {
        ChunkTy new_chunk199 = alloc_chunk(end_r1917);
        CursorTy chunk_start200 = new_chunk199.start_ptr;
        CursorTy chunk_end201 = new_chunk199.end_ptr;

        end_r1917 = chunk_end201;
        *(TagTyPacked *) loc1915 = 255;

        CursorTy redir = loc1915 + 1;

        *(CursorTy *) redir = chunk_start200;
        loc1915 = chunk_start200;
    }

    TagTyPacked tmpval5874 = *(TagTyPacked *) arg1442;
    CursorTy tmpcur5875 = arg1442 + 1;


  switch5908:
    ;
    switch (tmpval5874) {

      case 0:
        {
            CursorTy field_cur3967 = (CursorTy) tmpcur5875;
            CursorTy case2738 = (CursorTy) field_cur3967;
            CursorTy x1443 = (CursorTy) case2738;
            CursorTy loc2750 = loc1915 + 1;
            CursorCursorCursorCursorProd tmp_struct196 =
                                          _add_size_and_rel_offsets_ListSym(end_r1916, end_r1917, loc2750, x1443);
            CursorTy pvrtmp5876 = tmp_struct196.field0;
            CursorTy pvrtmp5877 = tmp_struct196.field1;
            CursorTy pvrtmp5878 = tmp_struct196.field2;
            CursorTy pvrtmp5879 = tmp_struct196.field3;
            CursorTy fltPrd4678 = (CursorTy) pvrtmp5878;
            CursorTy fltPrd4679 = (CursorTy) pvrtmp5879;
            CursorTy pvrtmp5881 = (CursorTy) fltPrd4679;
            CursorTy pvrtmp5880 = (CursorTy) fltPrd4678;
            CursorTy y1446 = (CursorTy) pvrtmp5880;
            CursorTy fltPrd4680 = (CursorTy) pvrtmp5878;
            CursorTy fltPrd4681 = (CursorTy) pvrtmp5879;
            CursorTy pvrtmp5883 = (CursorTy) fltPrd4681;
            CursorTy pvrtmp5882 = (CursorTy) fltPrd4680;
            CursorTy end_y1446 = (CursorTy) pvrtmp5883;
            CursorTy end_r1917_3429 = (CursorTy) pvrtmp5876;
            CursorTy endof3312 = (CursorTy) pvrtmp5877;
            CursorTy case2739 = (CursorTy) endof3312;
            CursorTy x1444 = (CursorTy) case2739;
            CursorTy loc2751 = (CursorTy) end_y1446;
            CursorCursorCursorCursorProd tmp_struct197 =
                                          _add_size_and_rel_offsets_Expr(end_r1916, end_r1917_3429, loc2751, x1444);
            CursorTy pvrtmp5884 = tmp_struct197.field0;
            CursorTy pvrtmp5885 = tmp_struct197.field1;
            CursorTy pvrtmp5886 = tmp_struct197.field2;
            CursorTy pvrtmp5887 = tmp_struct197.field3;
            CursorTy fltPrd4682 = (CursorTy) pvrtmp5886;
            CursorTy fltPrd4683 = (CursorTy) pvrtmp5887;
            CursorTy pvrtmp5889 = (CursorTy) fltPrd4683;
            CursorTy pvrtmp5888 = (CursorTy) fltPrd4682;
            CursorTy y1447 = (CursorTy) pvrtmp5888;
            CursorTy fltPrd4684 = (CursorTy) pvrtmp5886;
            CursorTy fltPrd4685 = (CursorTy) pvrtmp5887;
            CursorTy pvrtmp5891 = (CursorTy) fltPrd4685;
            CursorTy pvrtmp5890 = (CursorTy) fltPrd4684;
            CursorTy end_y1447 = (CursorTy) pvrtmp5891;
            CursorTy end_r1917_3429_3430 = (CursorTy) pvrtmp5884;
            CursorTy endof3313 = (CursorTy) pvrtmp5885;
            CursorTy case2740 = (CursorTy) endof3313;
            CursorTy x1445 = (CursorTy) case2740;
            CursorTy loc2752 = (CursorTy) end_y1447;
            CursorCursorCursorCursorProd tmp_struct198 =
                                          _add_size_and_rel_offsets_LVBIND(end_r1916, end_r1917_3429_3430, loc2752, x1445);
            CursorTy pvrtmp5892 = tmp_struct198.field0;
            CursorTy pvrtmp5893 = tmp_struct198.field1;
            CursorTy pvrtmp5894 = tmp_struct198.field2;
            CursorTy pvrtmp5895 = tmp_struct198.field3;
            CursorTy fltPrd4686 = (CursorTy) pvrtmp5894;
            CursorTy fltPrd4687 = (CursorTy) pvrtmp5895;
            CursorTy pvrtmp5897 = (CursorTy) fltPrd4687;
            CursorTy pvrtmp5896 = (CursorTy) fltPrd4686;
            CursorTy y1448 = (CursorTy) pvrtmp5896;
            CursorTy fltPrd4688 = (CursorTy) pvrtmp5894;
            CursorTy fltPrd4689 = (CursorTy) pvrtmp5895;
            CursorTy pvrtmp5899 = (CursorTy) fltPrd4689;
            CursorTy pvrtmp5898 = (CursorTy) fltPrd4688;
            CursorTy end_y1448 = (CursorTy) pvrtmp5899;
            CursorTy end_r1917_3429_3430_3431 = (CursorTy) pvrtmp5892;
            CursorTy endof3314 = (CursorTy) pvrtmp5893;

            *(TagTyPacked *) loc1915 = 0;

            CursorTy writetag3971 = loc1915 + 1;
            CursorTy writecur3972 = (CursorTy) end_y1446;
            CursorTy writecur3973 = (CursorTy) end_y1447;
            CursorTy writecur3974 = (CursorTy) end_y1448;
            CursorTy pvrtmp5901 = (CursorTy) writecur3974;
            CursorTy pvrtmp5900 = (CursorTy) loc1915;
            CursorTy taildc3315 = (CursorTy) pvrtmp5900;
            CursorTy end_taildc3315 = (CursorTy) pvrtmp5901;
            CursorTy pvrtmp5903 = (CursorTy) end_taildc3315;
            CursorTy pvrtmp5902 = (CursorTy) taildc3315;
            CursorTy fltPrd4690 = (CursorTy) pvrtmp5902;
            CursorTy fltPrd4691 = (CursorTy) pvrtmp5903;

            return (CursorCursorCursorCursorProd) {end_r1917_3429_3430_3431,
                                                   endof3314, fltPrd4690,
                                                   fltPrd4691};
            break;
        }

      case 1:
        {
            CursorTy field_cur3976 = (CursorTy) tmpcur5875;
            CursorTy jump3316 = loc1914 + 1;

            *(TagTyPacked *) loc1915 = 1;

            CursorTy writetag3977 = loc1915 + 1;
            CursorTy pvrtmp5905 = (CursorTy) writetag3977;
            CursorTy pvrtmp5904 = (CursorTy) loc1915;
            CursorTy taildc3317 = (CursorTy) pvrtmp5904;
            CursorTy end_taildc3317 = (CursorTy) pvrtmp5905;
            CursorTy pvrtmp5907 = (CursorTy) end_taildc3317;
            CursorTy pvrtmp5906 = (CursorTy) taildc3317;
            CursorTy fltPrd4692 = (CursorTy) pvrtmp5906;
            CursorTy fltPrd4693 = (CursorTy) pvrtmp5907;

            return (CursorCursorCursorCursorProd) {end_r1917, jump3316,
                                                   fltPrd4692, fltPrd4693};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6669 = *(CursorTy *) tmpcur5875;
            CursorTy tmpaftercur6670 = tmpcur5875 + 8;
            TagTyPacked tagtmp6671 = *(TagTyPacked *) tmpcur6669;
            CursorTy tailtmp6672 = tmpcur6669 + 1;

            tmpval5874 = tagtmp6671;
            tmpcur5875 = tailtmp6672;
            goto switch5908;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6669 = *(CursorTy *) tmpcur5875;
            CursorTy tmpaftercur6670 = tmpcur5875 + 8;
            TagTyPacked tagtmp6671 = *(TagTyPacked *) tmpcur6669;
            CursorTy tailtmp6672 = tmpcur6669 + 1;

            tmpval5874 = tagtmp6671;
            tmpcur5875 = tailtmp6672;
            goto switch5908;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5874");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Expr(CursorTy end_r1920,
                                                            CursorTy end_r1921,
                                                            CursorTy loc1919,
                                                            CursorTy arg1449)
{
    CursorTy loc1918 = (CursorTy) arg1449;

    if (loc1919 + 18 > end_r1921) {
        ChunkTy new_chunk224 = alloc_chunk(end_r1921);
        CursorTy chunk_start225 = new_chunk224.start_ptr;
        CursorTy chunk_end226 = new_chunk224.end_ptr;

        end_r1921 = chunk_end226;
        *(TagTyPacked *) loc1919 = 255;

        CursorTy redir = loc1919 + 1;

        *(CursorTy *) redir = chunk_start225;
        loc1919 = chunk_start225;
    }

    CursorTy loc2846 = loc1919 + 1;
    CursorTy loc2847 = loc2846 + 8;
    TagTyPacked tmpval5909 = *(TagTyPacked *) arg1449;
    CursorTy tmpcur5910 = arg1449 + 1;


  switch6169:
    ;
    switch (tmpval5909) {

      case 0:
        {
            CursorTy field_cur3979 = (CursorTy) tmpcur5910;
            CursorTy case2759 = (CursorTy) field_cur3979;
            SymTy tmpval5911 = *(SymTy *) case2759;
            CursorTy tmpcur5912 = case2759 + sizeof(SymTy);
            SymTy x1450 = (SymTy) tmpval5911;
            CursorTy end_x1450 = (CursorTy) tmpcur5912;
            CursorTy jump3318 = case2759 + 8;

            *(TagTyPacked *) loc1919 = 0;

            CursorTy writetag3981 = loc1919 + 1;

            *(SymTy *) writetag3981 = x1450;

            CursorTy writecur3982 = writetag3981 + sizeof(SymTy);
            CursorTy pvrtmp5914 = (CursorTy) writecur3982;
            CursorTy pvrtmp5913 = (CursorTy) loc1919;
            CursorTy taildc3319 = (CursorTy) pvrtmp5913;
            CursorTy end_taildc3319 = (CursorTy) pvrtmp5914;
            CursorTy pvrtmp5916 = (CursorTy) end_taildc3319;
            CursorTy pvrtmp5915 = (CursorTy) taildc3319;
            CursorTy fltPrd4694 = (CursorTy) pvrtmp5915;
            CursorTy fltPrd4695 = (CursorTy) pvrtmp5916;

            return (CursorCursorCursorCursorProd) {end_r1921, jump3318,
                                                   fltPrd4694, fltPrd4695};
            break;
        }

      case 1:
        {
            CursorTy field_cur3984 = (CursorTy) tmpcur5910;
            CursorTy case2763 = (CursorTy) field_cur3984;
            CursorTy x1452 = (CursorTy) case2763;
            CursorTy loc2771 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct202 =
                                          _add_size_and_rel_offsets_Formals(end_r1920, end_r1921, loc2771, x1452);
            CursorTy pvrtmp5917 = tmp_struct202.field0;
            CursorTy pvrtmp5918 = tmp_struct202.field1;
            CursorTy pvrtmp5919 = tmp_struct202.field2;
            CursorTy pvrtmp5920 = tmp_struct202.field3;
            CursorTy fltPrd4696 = (CursorTy) pvrtmp5919;
            CursorTy fltPrd4697 = (CursorTy) pvrtmp5920;
            CursorTy pvrtmp5922 = (CursorTy) fltPrd4697;
            CursorTy pvrtmp5921 = (CursorTy) fltPrd4696;
            CursorTy y1454 = (CursorTy) pvrtmp5921;
            CursorTy fltPrd4698 = (CursorTy) pvrtmp5919;
            CursorTy fltPrd4699 = (CursorTy) pvrtmp5920;
            CursorTy pvrtmp5924 = (CursorTy) fltPrd4699;
            CursorTy pvrtmp5923 = (CursorTy) fltPrd4698;
            CursorTy end_y1454 = (CursorTy) pvrtmp5924;
            CursorTy end_r1921_3432 = (CursorTy) pvrtmp5917;
            CursorTy endof3320 = (CursorTy) pvrtmp5918;
            CursorTy case2764 = (CursorTy) endof3320;
            CursorTy x1453 = (CursorTy) case2764;
            CursorTy loc2772 = (CursorTy) end_y1454;
            CursorCursorCursorCursorProd tmp_struct203 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1920, end_r1921_3432, loc2772, x1453);
            CursorTy pvrtmp5925 = tmp_struct203.field0;
            CursorTy pvrtmp5926 = tmp_struct203.field1;
            CursorTy pvrtmp5927 = tmp_struct203.field2;
            CursorTy pvrtmp5928 = tmp_struct203.field3;
            CursorTy fltPrd4700 = (CursorTy) pvrtmp5927;
            CursorTy fltPrd4701 = (CursorTy) pvrtmp5928;
            CursorTy pvrtmp5930 = (CursorTy) fltPrd4701;
            CursorTy pvrtmp5929 = (CursorTy) fltPrd4700;
            CursorTy y1455 = (CursorTy) pvrtmp5929;
            CursorTy fltPrd4702 = (CursorTy) pvrtmp5927;
            CursorTy fltPrd4703 = (CursorTy) pvrtmp5928;
            CursorTy pvrtmp5932 = (CursorTy) fltPrd4703;
            CursorTy pvrtmp5931 = (CursorTy) fltPrd4702;
            CursorTy end_y1455 = (CursorTy) pvrtmp5932;
            CursorTy end_r1921_3432_3433 = (CursorTy) pvrtmp5925;
            CursorTy endof3321 = (CursorTy) pvrtmp5926;

            *(TagTyPacked *) loc1919 = 1;

            CursorTy writetag3987 = loc1919 + 1;
            CursorTy writecur3988 = (CursorTy) end_y1454;
            CursorTy writecur3989 = (CursorTy) end_y1455;
            CursorTy pvrtmp5934 = (CursorTy) writecur3989;
            CursorTy pvrtmp5933 = (CursorTy) loc1919;
            CursorTy taildc3322 = (CursorTy) pvrtmp5933;
            CursorTy end_taildc3322 = (CursorTy) pvrtmp5934;
            CursorTy pvrtmp5936 = (CursorTy) end_taildc3322;
            CursorTy pvrtmp5935 = (CursorTy) taildc3322;
            CursorTy fltPrd4704 = (CursorTy) pvrtmp5935;
            CursorTy fltPrd4705 = (CursorTy) pvrtmp5936;

            return (CursorCursorCursorCursorProd) {end_r1921_3432_3433,
                                                   endof3321, fltPrd4704,
                                                   fltPrd4705};
            break;
        }

      case 2:
        {
            CursorTy field_cur3991 = (CursorTy) tmpcur5910;
            CursorTy case2775 = (CursorTy) field_cur3991;
            CursorTy x1456 = (CursorTy) case2775;
            CursorTy loc2779 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct204 =
                                          _add_size_and_rel_offsets_LAMBDACASE(end_r1920, end_r1921, loc2779, x1456);
            CursorTy pvrtmp5937 = tmp_struct204.field0;
            CursorTy pvrtmp5938 = tmp_struct204.field1;
            CursorTy pvrtmp5939 = tmp_struct204.field2;
            CursorTy pvrtmp5940 = tmp_struct204.field3;
            CursorTy fltPrd4706 = (CursorTy) pvrtmp5939;
            CursorTy fltPrd4707 = (CursorTy) pvrtmp5940;
            CursorTy pvrtmp5942 = (CursorTy) fltPrd4707;
            CursorTy pvrtmp5941 = (CursorTy) fltPrd4706;
            CursorTy y1457 = (CursorTy) pvrtmp5941;
            CursorTy fltPrd4708 = (CursorTy) pvrtmp5939;
            CursorTy fltPrd4709 = (CursorTy) pvrtmp5940;
            CursorTy pvrtmp5944 = (CursorTy) fltPrd4709;
            CursorTy pvrtmp5943 = (CursorTy) fltPrd4708;
            CursorTy end_y1457 = (CursorTy) pvrtmp5944;
            CursorTy end_r1921_3434 = (CursorTy) pvrtmp5937;
            CursorTy endof3323 = (CursorTy) pvrtmp5938;

            *(TagTyPacked *) loc1919 = 2;

            CursorTy writetag3993 = loc1919 + 1;
            CursorTy writecur3994 = (CursorTy) end_y1457;
            CursorTy pvrtmp5946 = (CursorTy) writecur3994;
            CursorTy pvrtmp5945 = (CursorTy) loc1919;
            CursorTy taildc3324 = (CursorTy) pvrtmp5945;
            CursorTy end_taildc3324 = (CursorTy) pvrtmp5946;
            CursorTy pvrtmp5948 = (CursorTy) end_taildc3324;
            CursorTy pvrtmp5947 = (CursorTy) taildc3324;
            CursorTy fltPrd4710 = (CursorTy) pvrtmp5947;
            CursorTy fltPrd4711 = (CursorTy) pvrtmp5948;

            return (CursorCursorCursorCursorProd) {end_r1921_3434, endof3323,
                                                   fltPrd4710, fltPrd4711};
            break;
        }

      case 3:
        {
            CursorTy field_cur3996 = (CursorTy) tmpcur5910;
            CursorTy case2781 = (CursorTy) field_cur3996;
            CursorTy x1458 = (CursorTy) case2781;
            CursorTy loc2793 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct205 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921, loc2793, x1458);
            CursorTy pvrtmp5949 = tmp_struct205.field0;
            CursorTy pvrtmp5950 = tmp_struct205.field1;
            CursorTy pvrtmp5951 = tmp_struct205.field2;
            CursorTy pvrtmp5952 = tmp_struct205.field3;
            CursorTy fltPrd4712 = (CursorTy) pvrtmp5951;
            CursorTy fltPrd4713 = (CursorTy) pvrtmp5952;
            CursorTy pvrtmp5954 = (CursorTy) fltPrd4713;
            CursorTy pvrtmp5953 = (CursorTy) fltPrd4712;
            CursorTy y1461 = (CursorTy) pvrtmp5953;
            CursorTy fltPrd4714 = (CursorTy) pvrtmp5951;
            CursorTy fltPrd4715 = (CursorTy) pvrtmp5952;
            CursorTy pvrtmp5956 = (CursorTy) fltPrd4715;
            CursorTy pvrtmp5955 = (CursorTy) fltPrd4714;
            CursorTy end_y1461 = (CursorTy) pvrtmp5956;
            CursorTy end_r1921_3435 = (CursorTy) pvrtmp5949;
            CursorTy endof3325 = (CursorTy) pvrtmp5950;
            CursorTy case2782 = (CursorTy) endof3325;
            CursorTy x1459 = (CursorTy) case2782;
            CursorTy loc2794 = (CursorTy) end_y1461;
            CursorCursorCursorCursorProd tmp_struct206 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921_3435, loc2794, x1459);
            CursorTy pvrtmp5957 = tmp_struct206.field0;
            CursorTy pvrtmp5958 = tmp_struct206.field1;
            CursorTy pvrtmp5959 = tmp_struct206.field2;
            CursorTy pvrtmp5960 = tmp_struct206.field3;
            CursorTy fltPrd4716 = (CursorTy) pvrtmp5959;
            CursorTy fltPrd4717 = (CursorTy) pvrtmp5960;
            CursorTy pvrtmp5962 = (CursorTy) fltPrd4717;
            CursorTy pvrtmp5961 = (CursorTy) fltPrd4716;
            CursorTy y1462 = (CursorTy) pvrtmp5961;
            CursorTy fltPrd4718 = (CursorTy) pvrtmp5959;
            CursorTy fltPrd4719 = (CursorTy) pvrtmp5960;
            CursorTy pvrtmp5964 = (CursorTy) fltPrd4719;
            CursorTy pvrtmp5963 = (CursorTy) fltPrd4718;
            CursorTy end_y1462 = (CursorTy) pvrtmp5964;
            CursorTy end_r1921_3435_3436 = (CursorTy) pvrtmp5957;
            CursorTy endof3326 = (CursorTy) pvrtmp5958;
            CursorTy case2783 = (CursorTy) endof3326;
            CursorTy x1460 = (CursorTy) case2783;
            CursorTy loc2795 = (CursorTy) end_y1462;
            CursorCursorCursorCursorProd tmp_struct207 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921_3435_3436, loc2795, x1460);
            CursorTy pvrtmp5965 = tmp_struct207.field0;
            CursorTy pvrtmp5966 = tmp_struct207.field1;
            CursorTy pvrtmp5967 = tmp_struct207.field2;
            CursorTy pvrtmp5968 = tmp_struct207.field3;
            CursorTy fltPrd4720 = (CursorTy) pvrtmp5967;
            CursorTy fltPrd4721 = (CursorTy) pvrtmp5968;
            CursorTy pvrtmp5970 = (CursorTy) fltPrd4721;
            CursorTy pvrtmp5969 = (CursorTy) fltPrd4720;
            CursorTy y1463 = (CursorTy) pvrtmp5969;
            CursorTy fltPrd4722 = (CursorTy) pvrtmp5967;
            CursorTy fltPrd4723 = (CursorTy) pvrtmp5968;
            CursorTy pvrtmp5972 = (CursorTy) fltPrd4723;
            CursorTy pvrtmp5971 = (CursorTy) fltPrd4722;
            CursorTy end_y1463 = (CursorTy) pvrtmp5972;
            CursorTy end_r1921_3435_3436_3437 = (CursorTy) pvrtmp5965;
            CursorTy endof3327 = (CursorTy) pvrtmp5966;

            *(TagTyPacked *) loc1919 = 3;

            CursorTy writetag4000 = loc1919 + 1;
            CursorTy writecur4001 = (CursorTy) end_y1461;
            CursorTy writecur4002 = (CursorTy) end_y1462;
            CursorTy writecur4003 = (CursorTy) end_y1463;
            CursorTy pvrtmp5974 = (CursorTy) writecur4003;
            CursorTy pvrtmp5973 = (CursorTy) loc1919;
            CursorTy taildc3328 = (CursorTy) pvrtmp5973;
            CursorTy end_taildc3328 = (CursorTy) pvrtmp5974;
            CursorTy pvrtmp5976 = (CursorTy) end_taildc3328;
            CursorTy pvrtmp5975 = (CursorTy) taildc3328;
            CursorTy fltPrd4724 = (CursorTy) pvrtmp5975;
            CursorTy fltPrd4725 = (CursorTy) pvrtmp5976;

            return (CursorCursorCursorCursorProd) {end_r1921_3435_3436_3437,
                                                   endof3327, fltPrd4724,
                                                   fltPrd4725};
            break;
        }

      case 4:
        {
            CursorTy field_cur4005 = (CursorTy) tmpcur5910;
            CursorTy case2799 = (CursorTy) field_cur4005;
            CursorTy x1464 = (CursorTy) case2799;
            CursorTy loc2803 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct208 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1920, end_r1921, loc2803, x1464);
            CursorTy pvrtmp5977 = tmp_struct208.field0;
            CursorTy pvrtmp5978 = tmp_struct208.field1;
            CursorTy pvrtmp5979 = tmp_struct208.field2;
            CursorTy pvrtmp5980 = tmp_struct208.field3;
            CursorTy fltPrd4726 = (CursorTy) pvrtmp5979;
            CursorTy fltPrd4727 = (CursorTy) pvrtmp5980;
            CursorTy pvrtmp5982 = (CursorTy) fltPrd4727;
            CursorTy pvrtmp5981 = (CursorTy) fltPrd4726;
            CursorTy y1465 = (CursorTy) pvrtmp5981;
            CursorTy fltPrd4728 = (CursorTy) pvrtmp5979;
            CursorTy fltPrd4729 = (CursorTy) pvrtmp5980;
            CursorTy pvrtmp5984 = (CursorTy) fltPrd4729;
            CursorTy pvrtmp5983 = (CursorTy) fltPrd4728;
            CursorTy end_y1465 = (CursorTy) pvrtmp5984;
            CursorTy end_r1921_3438 = (CursorTy) pvrtmp5977;
            CursorTy endof3329 = (CursorTy) pvrtmp5978;

            *(TagTyPacked *) loc1919 = 4;

            CursorTy writetag4007 = loc1919 + 1;
            CursorTy writecur4008 = (CursorTy) end_y1465;
            CursorTy pvrtmp5986 = (CursorTy) writecur4008;
            CursorTy pvrtmp5985 = (CursorTy) loc1919;
            CursorTy taildc3330 = (CursorTy) pvrtmp5985;
            CursorTy end_taildc3330 = (CursorTy) pvrtmp5986;
            CursorTy pvrtmp5988 = (CursorTy) end_taildc3330;
            CursorTy pvrtmp5987 = (CursorTy) taildc3330;
            CursorTy fltPrd4730 = (CursorTy) pvrtmp5987;
            CursorTy fltPrd4731 = (CursorTy) pvrtmp5988;

            return (CursorCursorCursorCursorProd) {end_r1921_3438, endof3329,
                                                   fltPrd4730, fltPrd4731};
            break;
        }

      case 5:
        {
            CursorTy field_cur4010 = (CursorTy) tmpcur5910;
            CursorTy case2805 = (CursorTy) field_cur4010;
            CursorTy x1466 = (CursorTy) case2805;
            CursorTy loc2813 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct209 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921, loc2813, x1466);
            CursorTy pvrtmp5989 = tmp_struct209.field0;
            CursorTy pvrtmp5990 = tmp_struct209.field1;
            CursorTy pvrtmp5991 = tmp_struct209.field2;
            CursorTy pvrtmp5992 = tmp_struct209.field3;
            CursorTy fltPrd4732 = (CursorTy) pvrtmp5991;
            CursorTy fltPrd4733 = (CursorTy) pvrtmp5992;
            CursorTy pvrtmp5994 = (CursorTy) fltPrd4733;
            CursorTy pvrtmp5993 = (CursorTy) fltPrd4732;
            CursorTy y1468 = (CursorTy) pvrtmp5993;
            CursorTy fltPrd4734 = (CursorTy) pvrtmp5991;
            CursorTy fltPrd4735 = (CursorTy) pvrtmp5992;
            CursorTy pvrtmp5996 = (CursorTy) fltPrd4735;
            CursorTy pvrtmp5995 = (CursorTy) fltPrd4734;
            CursorTy end_y1468 = (CursorTy) pvrtmp5996;
            CursorTy end_r1921_3439 = (CursorTy) pvrtmp5989;
            CursorTy endof3331 = (CursorTy) pvrtmp5990;
            CursorTy case2806 = (CursorTy) endof3331;
            CursorTy x1467 = (CursorTy) case2806;
            CursorTy loc2814 = (CursorTy) end_y1468;
            CursorCursorCursorCursorProd tmp_struct210 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1920, end_r1921_3439, loc2814, x1467);
            CursorTy pvrtmp5997 = tmp_struct210.field0;
            CursorTy pvrtmp5998 = tmp_struct210.field1;
            CursorTy pvrtmp5999 = tmp_struct210.field2;
            CursorTy pvrtmp6000 = tmp_struct210.field3;
            CursorTy fltPrd4736 = (CursorTy) pvrtmp5999;
            CursorTy fltPrd4737 = (CursorTy) pvrtmp6000;
            CursorTy pvrtmp6002 = (CursorTy) fltPrd4737;
            CursorTy pvrtmp6001 = (CursorTy) fltPrd4736;
            CursorTy y1469 = (CursorTy) pvrtmp6001;
            CursorTy fltPrd4738 = (CursorTy) pvrtmp5999;
            CursorTy fltPrd4739 = (CursorTy) pvrtmp6000;
            CursorTy pvrtmp6004 = (CursorTy) fltPrd4739;
            CursorTy pvrtmp6003 = (CursorTy) fltPrd4738;
            CursorTy end_y1469 = (CursorTy) pvrtmp6004;
            CursorTy end_r1921_3439_3440 = (CursorTy) pvrtmp5997;
            CursorTy endof3332 = (CursorTy) pvrtmp5998;

            *(TagTyPacked *) loc1919 = 5;

            CursorTy writetag4013 = loc1919 + 1;
            CursorTy writecur4014 = (CursorTy) end_y1468;
            CursorTy writecur4015 = (CursorTy) end_y1469;
            CursorTy pvrtmp6006 = (CursorTy) writecur4015;
            CursorTy pvrtmp6005 = (CursorTy) loc1919;
            CursorTy taildc3333 = (CursorTy) pvrtmp6005;
            CursorTy end_taildc3333 = (CursorTy) pvrtmp6006;
            CursorTy pvrtmp6008 = (CursorTy) end_taildc3333;
            CursorTy pvrtmp6007 = (CursorTy) taildc3333;
            CursorTy fltPrd4740 = (CursorTy) pvrtmp6007;
            CursorTy fltPrd4741 = (CursorTy) pvrtmp6008;

            return (CursorCursorCursorCursorProd) {end_r1921_3439_3440,
                                                   endof3332, fltPrd4740,
                                                   fltPrd4741};
            break;
        }

      case 6:
        {
            CursorTy field_cur4017 = (CursorTy) tmpcur5910;
            CursorTy case2817 = (CursorTy) field_cur4017;
            CursorTy x1470 = (CursorTy) case2817;
            CursorTy loc2825 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct211 =
                                          _add_size_and_rel_offsets_LVBIND(end_r1920, end_r1921, loc2825, x1470);
            CursorTy pvrtmp6009 = tmp_struct211.field0;
            CursorTy pvrtmp6010 = tmp_struct211.field1;
            CursorTy pvrtmp6011 = tmp_struct211.field2;
            CursorTy pvrtmp6012 = tmp_struct211.field3;
            CursorTy fltPrd4742 = (CursorTy) pvrtmp6011;
            CursorTy fltPrd4743 = (CursorTy) pvrtmp6012;
            CursorTy pvrtmp6014 = (CursorTy) fltPrd4743;
            CursorTy pvrtmp6013 = (CursorTy) fltPrd4742;
            CursorTy y1472 = (CursorTy) pvrtmp6013;
            CursorTy fltPrd4744 = (CursorTy) pvrtmp6011;
            CursorTy fltPrd4745 = (CursorTy) pvrtmp6012;
            CursorTy pvrtmp6016 = (CursorTy) fltPrd4745;
            CursorTy pvrtmp6015 = (CursorTy) fltPrd4744;
            CursorTy end_y1472 = (CursorTy) pvrtmp6016;
            CursorTy end_r1921_3441 = (CursorTy) pvrtmp6009;
            CursorTy endof3334 = (CursorTy) pvrtmp6010;
            CursorTy case2818 = (CursorTy) endof3334;
            CursorTy x1471 = (CursorTy) case2818;
            CursorTy loc2826 = (CursorTy) end_y1472;
            CursorCursorCursorCursorProd tmp_struct212 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1920, end_r1921_3441, loc2826, x1471);
            CursorTy pvrtmp6017 = tmp_struct212.field0;
            CursorTy pvrtmp6018 = tmp_struct212.field1;
            CursorTy pvrtmp6019 = tmp_struct212.field2;
            CursorTy pvrtmp6020 = tmp_struct212.field3;
            CursorTy fltPrd4746 = (CursorTy) pvrtmp6019;
            CursorTy fltPrd4747 = (CursorTy) pvrtmp6020;
            CursorTy pvrtmp6022 = (CursorTy) fltPrd4747;
            CursorTy pvrtmp6021 = (CursorTy) fltPrd4746;
            CursorTy y1473 = (CursorTy) pvrtmp6021;
            CursorTy fltPrd4748 = (CursorTy) pvrtmp6019;
            CursorTy fltPrd4749 = (CursorTy) pvrtmp6020;
            CursorTy pvrtmp6024 = (CursorTy) fltPrd4749;
            CursorTy pvrtmp6023 = (CursorTy) fltPrd4748;
            CursorTy end_y1473 = (CursorTy) pvrtmp6024;
            CursorTy end_r1921_3441_3442 = (CursorTy) pvrtmp6017;
            CursorTy endof3335 = (CursorTy) pvrtmp6018;

            *(TagTyPacked *) loc1919 = 6;

            CursorTy writetag4020 = loc1919 + 1;
            CursorTy writecur4021 = (CursorTy) end_y1472;
            CursorTy writecur4022 = (CursorTy) end_y1473;
            CursorTy pvrtmp6026 = (CursorTy) writecur4022;
            CursorTy pvrtmp6025 = (CursorTy) loc1919;
            CursorTy taildc3336 = (CursorTy) pvrtmp6025;
            CursorTy end_taildc3336 = (CursorTy) pvrtmp6026;
            CursorTy pvrtmp6028 = (CursorTy) end_taildc3336;
            CursorTy pvrtmp6027 = (CursorTy) taildc3336;
            CursorTy fltPrd4750 = (CursorTy) pvrtmp6027;
            CursorTy fltPrd4751 = (CursorTy) pvrtmp6028;

            return (CursorCursorCursorCursorProd) {end_r1921_3441_3442,
                                                   endof3335, fltPrd4750,
                                                   fltPrd4751};
            break;
        }

      case 7:
        {
            CursorTy field_cur4024 = (CursorTy) tmpcur5910;
            CursorTy case2829 = (CursorTy) field_cur4024;
            CursorTy x1474 = (CursorTy) case2829;
            CursorTy loc2837 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct213 =
                                          _add_size_and_rel_offsets_LVBIND(end_r1920, end_r1921, loc2837, x1474);
            CursorTy pvrtmp6029 = tmp_struct213.field0;
            CursorTy pvrtmp6030 = tmp_struct213.field1;
            CursorTy pvrtmp6031 = tmp_struct213.field2;
            CursorTy pvrtmp6032 = tmp_struct213.field3;
            CursorTy fltPrd4752 = (CursorTy) pvrtmp6031;
            CursorTy fltPrd4753 = (CursorTy) pvrtmp6032;
            CursorTy pvrtmp6034 = (CursorTy) fltPrd4753;
            CursorTy pvrtmp6033 = (CursorTy) fltPrd4752;
            CursorTy y1476 = (CursorTy) pvrtmp6033;
            CursorTy fltPrd4754 = (CursorTy) pvrtmp6031;
            CursorTy fltPrd4755 = (CursorTy) pvrtmp6032;
            CursorTy pvrtmp6036 = (CursorTy) fltPrd4755;
            CursorTy pvrtmp6035 = (CursorTy) fltPrd4754;
            CursorTy end_y1476 = (CursorTy) pvrtmp6036;
            CursorTy end_r1921_3443 = (CursorTy) pvrtmp6029;
            CursorTy endof3337 = (CursorTy) pvrtmp6030;
            CursorTy case2830 = (CursorTy) endof3337;
            CursorTy x1475 = (CursorTy) case2830;
            CursorTy loc2838 = (CursorTy) end_y1476;
            CursorCursorCursorCursorProd tmp_struct214 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1920, end_r1921_3443, loc2838, x1475);
            CursorTy pvrtmp6037 = tmp_struct214.field0;
            CursorTy pvrtmp6038 = tmp_struct214.field1;
            CursorTy pvrtmp6039 = tmp_struct214.field2;
            CursorTy pvrtmp6040 = tmp_struct214.field3;
            CursorTy fltPrd4756 = (CursorTy) pvrtmp6039;
            CursorTy fltPrd4757 = (CursorTy) pvrtmp6040;
            CursorTy pvrtmp6042 = (CursorTy) fltPrd4757;
            CursorTy pvrtmp6041 = (CursorTy) fltPrd4756;
            CursorTy y1477 = (CursorTy) pvrtmp6041;
            CursorTy fltPrd4758 = (CursorTy) pvrtmp6039;
            CursorTy fltPrd4759 = (CursorTy) pvrtmp6040;
            CursorTy pvrtmp6044 = (CursorTy) fltPrd4759;
            CursorTy pvrtmp6043 = (CursorTy) fltPrd4758;
            CursorTy end_y1477 = (CursorTy) pvrtmp6044;
            CursorTy end_r1921_3443_3444 = (CursorTy) pvrtmp6037;
            CursorTy endof3338 = (CursorTy) pvrtmp6038;

            *(TagTyPacked *) loc1919 = 7;

            CursorTy writetag4027 = loc1919 + 1;
            CursorTy writecur4028 = (CursorTy) end_y1476;
            CursorTy writecur4029 = (CursorTy) end_y1477;
            CursorTy pvrtmp6046 = (CursorTy) writecur4029;
            CursorTy pvrtmp6045 = (CursorTy) loc1919;
            CursorTy taildc3339 = (CursorTy) pvrtmp6045;
            CursorTy end_taildc3339 = (CursorTy) pvrtmp6046;
            CursorTy pvrtmp6048 = (CursorTy) end_taildc3339;
            CursorTy pvrtmp6047 = (CursorTy) taildc3339;
            CursorTy fltPrd4760 = (CursorTy) pvrtmp6047;
            CursorTy fltPrd4761 = (CursorTy) pvrtmp6048;

            return (CursorCursorCursorCursorProd) {end_r1921_3443_3444,
                                                   endof3338, fltPrd4760,
                                                   fltPrd4761};
            break;
        }

      case 8:
        {
            CursorTy field_cur4031 = (CursorTy) tmpcur5910;
            CursorTy case2841 = (CursorTy) field_cur4031;
            SymTy tmpval6049 = *(SymTy *) case2841;
            CursorTy tmpcur6050 = case2841 + sizeof(SymTy);
            SymTy x1478 = (SymTy) tmpval6049;
            CursorTy end_x1478 = (CursorTy) tmpcur6050;
            CursorTy case2842 = (CursorTy) end_x1478;
            CursorTy x1479 = (CursorTy) case2842;
            CursorTy jump3340 = case2841 + 8;
            CursorCursorCursorCursorProd tmp_struct215 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921, loc2847, x1479);
            CursorTy pvrtmp6051 = tmp_struct215.field0;
            CursorTy pvrtmp6052 = tmp_struct215.field1;
            CursorTy pvrtmp6053 = tmp_struct215.field2;
            CursorTy pvrtmp6054 = tmp_struct215.field3;
            CursorTy fltPrd4762 = (CursorTy) pvrtmp6053;
            CursorTy fltPrd4763 = (CursorTy) pvrtmp6054;
            CursorTy pvrtmp6056 = (CursorTy) fltPrd4763;
            CursorTy pvrtmp6055 = (CursorTy) fltPrd4762;
            CursorTy y1481 = (CursorTy) pvrtmp6055;
            CursorTy fltPrd4764 = (CursorTy) pvrtmp6053;
            CursorTy fltPrd4765 = (CursorTy) pvrtmp6054;
            CursorTy pvrtmp6058 = (CursorTy) fltPrd4765;
            CursorTy pvrtmp6057 = (CursorTy) fltPrd4764;
            CursorTy end_y1481 = (CursorTy) pvrtmp6058;
            CursorTy end_r1921_3445 = (CursorTy) pvrtmp6051;
            CursorTy endof3341 = (CursorTy) pvrtmp6052;

            *(TagTyPacked *) loc1919 = 8;

            CursorTy writetag4034 = loc1919 + 1;

            *(SymTy *) writetag4034 = x1478;

            CursorTy writecur4035 = writetag4034 + sizeof(SymTy);
            CursorTy writecur4036 = (CursorTy) end_y1481;
            CursorTy pvrtmp6060 = (CursorTy) writecur4036;
            CursorTy pvrtmp6059 = (CursorTy) loc1919;
            CursorTy taildc3342 = (CursorTy) pvrtmp6059;
            CursorTy end_taildc3342 = (CursorTy) pvrtmp6060;
            CursorTy pvrtmp6062 = (CursorTy) end_taildc3342;
            CursorTy pvrtmp6061 = (CursorTy) taildc3342;
            CursorTy fltPrd4766 = (CursorTy) pvrtmp6061;
            CursorTy fltPrd4767 = (CursorTy) pvrtmp6062;

            return (CursorCursorCursorCursorProd) {end_r1921_3445, endof3341,
                                                   fltPrd4766, fltPrd4767};
            break;
        }

      case 9:
        {
            CursorTy field_cur4038 = (CursorTy) tmpcur5910;
            CursorTy case2851 = (CursorTy) field_cur4038;
            CursorTy x1482 = (CursorTy) case2851;
            CursorTy loc2855 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct216 =
                                          _add_size_and_rel_offsets_Datum(end_r1920, end_r1921, loc2855, x1482);
            CursorTy pvrtmp6063 = tmp_struct216.field0;
            CursorTy pvrtmp6064 = tmp_struct216.field1;
            CursorTy pvrtmp6065 = tmp_struct216.field2;
            CursorTy pvrtmp6066 = tmp_struct216.field3;
            CursorTy fltPrd4768 = (CursorTy) pvrtmp6065;
            CursorTy fltPrd4769 = (CursorTy) pvrtmp6066;
            CursorTy pvrtmp6068 = (CursorTy) fltPrd4769;
            CursorTy pvrtmp6067 = (CursorTy) fltPrd4768;
            CursorTy y1483 = (CursorTy) pvrtmp6067;
            CursorTy fltPrd4770 = (CursorTy) pvrtmp6065;
            CursorTy fltPrd4771 = (CursorTy) pvrtmp6066;
            CursorTy pvrtmp6070 = (CursorTy) fltPrd4771;
            CursorTy pvrtmp6069 = (CursorTy) fltPrd4770;
            CursorTy end_y1483 = (CursorTy) pvrtmp6070;
            CursorTy end_r1921_3446 = (CursorTy) pvrtmp6063;
            CursorTy endof3343 = (CursorTy) pvrtmp6064;

            *(TagTyPacked *) loc1919 = 9;

            CursorTy writetag4040 = loc1919 + 1;
            CursorTy writecur4041 = (CursorTy) end_y1483;
            CursorTy pvrtmp6072 = (CursorTy) writecur4041;
            CursorTy pvrtmp6071 = (CursorTy) loc1919;
            CursorTy taildc3344 = (CursorTy) pvrtmp6071;
            CursorTy end_taildc3344 = (CursorTy) pvrtmp6072;
            CursorTy pvrtmp6074 = (CursorTy) end_taildc3344;
            CursorTy pvrtmp6073 = (CursorTy) taildc3344;
            CursorTy fltPrd4772 = (CursorTy) pvrtmp6073;
            CursorTy fltPrd4773 = (CursorTy) pvrtmp6074;

            return (CursorCursorCursorCursorProd) {end_r1921_3446, endof3343,
                                                   fltPrd4772, fltPrd4773};
            break;
        }

      case 10:
        {
            CursorTy field_cur4043 = (CursorTy) tmpcur5910;
            CursorTy case2857 = (CursorTy) field_cur4043;
            CursorTy x1484 = (CursorTy) case2857;
            CursorTy loc2861 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct217 =
                                          _add_size_and_rel_offsets_Datum(end_r1920, end_r1921, loc2861, x1484);
            CursorTy pvrtmp6075 = tmp_struct217.field0;
            CursorTy pvrtmp6076 = tmp_struct217.field1;
            CursorTy pvrtmp6077 = tmp_struct217.field2;
            CursorTy pvrtmp6078 = tmp_struct217.field3;
            CursorTy fltPrd4774 = (CursorTy) pvrtmp6077;
            CursorTy fltPrd4775 = (CursorTy) pvrtmp6078;
            CursorTy pvrtmp6080 = (CursorTy) fltPrd4775;
            CursorTy pvrtmp6079 = (CursorTy) fltPrd4774;
            CursorTy y1485 = (CursorTy) pvrtmp6079;
            CursorTy fltPrd4776 = (CursorTy) pvrtmp6077;
            CursorTy fltPrd4777 = (CursorTy) pvrtmp6078;
            CursorTy pvrtmp6082 = (CursorTy) fltPrd4777;
            CursorTy pvrtmp6081 = (CursorTy) fltPrd4776;
            CursorTy end_y1485 = (CursorTy) pvrtmp6082;
            CursorTy end_r1921_3447 = (CursorTy) pvrtmp6075;
            CursorTy endof3345 = (CursorTy) pvrtmp6076;

            *(TagTyPacked *) loc1919 = 10;

            CursorTy writetag4045 = loc1919 + 1;
            CursorTy writecur4046 = (CursorTy) end_y1485;
            CursorTy pvrtmp6084 = (CursorTy) writecur4046;
            CursorTy pvrtmp6083 = (CursorTy) loc1919;
            CursorTy taildc3346 = (CursorTy) pvrtmp6083;
            CursorTy end_taildc3346 = (CursorTy) pvrtmp6084;
            CursorTy pvrtmp6086 = (CursorTy) end_taildc3346;
            CursorTy pvrtmp6085 = (CursorTy) taildc3346;
            CursorTy fltPrd4778 = (CursorTy) pvrtmp6085;
            CursorTy fltPrd4779 = (CursorTy) pvrtmp6086;

            return (CursorCursorCursorCursorProd) {end_r1921_3447, endof3345,
                                                   fltPrd4778, fltPrd4779};
            break;
        }

      case 11:
        {
            CursorTy field_cur4048 = (CursorTy) tmpcur5910;
            CursorTy case2863 = (CursorTy) field_cur4048;
            CursorTy x1486 = (CursorTy) case2863;
            CursorTy loc2867 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct218 =
                                          _add_size_and_rel_offsets_Datum(end_r1920, end_r1921, loc2867, x1486);
            CursorTy pvrtmp6087 = tmp_struct218.field0;
            CursorTy pvrtmp6088 = tmp_struct218.field1;
            CursorTy pvrtmp6089 = tmp_struct218.field2;
            CursorTy pvrtmp6090 = tmp_struct218.field3;
            CursorTy fltPrd4780 = (CursorTy) pvrtmp6089;
            CursorTy fltPrd4781 = (CursorTy) pvrtmp6090;
            CursorTy pvrtmp6092 = (CursorTy) fltPrd4781;
            CursorTy pvrtmp6091 = (CursorTy) fltPrd4780;
            CursorTy y1487 = (CursorTy) pvrtmp6091;
            CursorTy fltPrd4782 = (CursorTy) pvrtmp6089;
            CursorTy fltPrd4783 = (CursorTy) pvrtmp6090;
            CursorTy pvrtmp6094 = (CursorTy) fltPrd4783;
            CursorTy pvrtmp6093 = (CursorTy) fltPrd4782;
            CursorTy end_y1487 = (CursorTy) pvrtmp6094;
            CursorTy end_r1921_3448 = (CursorTy) pvrtmp6087;
            CursorTy endof3347 = (CursorTy) pvrtmp6088;

            *(TagTyPacked *) loc1919 = 11;

            CursorTy writetag4050 = loc1919 + 1;
            CursorTy writecur4051 = (CursorTy) end_y1487;
            CursorTy pvrtmp6096 = (CursorTy) writecur4051;
            CursorTy pvrtmp6095 = (CursorTy) loc1919;
            CursorTy taildc3348 = (CursorTy) pvrtmp6095;
            CursorTy end_taildc3348 = (CursorTy) pvrtmp6096;
            CursorTy pvrtmp6098 = (CursorTy) end_taildc3348;
            CursorTy pvrtmp6097 = (CursorTy) taildc3348;
            CursorTy fltPrd4784 = (CursorTy) pvrtmp6097;
            CursorTy fltPrd4785 = (CursorTy) pvrtmp6098;

            return (CursorCursorCursorCursorProd) {end_r1921_3448, endof3347,
                                                   fltPrd4784, fltPrd4785};
            break;
        }

      case 12:
        {
            CursorTy field_cur4053 = (CursorTy) tmpcur5910;
            CursorTy case2869 = (CursorTy) field_cur4053;
            CursorTy x1488 = (CursorTy) case2869;
            CursorTy loc2881 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct219 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921, loc2881, x1488);
            CursorTy pvrtmp6099 = tmp_struct219.field0;
            CursorTy pvrtmp6100 = tmp_struct219.field1;
            CursorTy pvrtmp6101 = tmp_struct219.field2;
            CursorTy pvrtmp6102 = tmp_struct219.field3;
            CursorTy fltPrd4786 = (CursorTy) pvrtmp6101;
            CursorTy fltPrd4787 = (CursorTy) pvrtmp6102;
            CursorTy pvrtmp6104 = (CursorTy) fltPrd4787;
            CursorTy pvrtmp6103 = (CursorTy) fltPrd4786;
            CursorTy y1491 = (CursorTy) pvrtmp6103;
            CursorTy fltPrd4788 = (CursorTy) pvrtmp6101;
            CursorTy fltPrd4789 = (CursorTy) pvrtmp6102;
            CursorTy pvrtmp6106 = (CursorTy) fltPrd4789;
            CursorTy pvrtmp6105 = (CursorTy) fltPrd4788;
            CursorTy end_y1491 = (CursorTy) pvrtmp6106;
            CursorTy end_r1921_3449 = (CursorTy) pvrtmp6099;
            CursorTy endof3349 = (CursorTy) pvrtmp6100;
            CursorTy case2870 = (CursorTy) endof3349;
            CursorTy x1489 = (CursorTy) case2870;
            CursorTy loc2882 = (CursorTy) end_y1491;
            CursorCursorCursorCursorProd tmp_struct220 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921_3449, loc2882, x1489);
            CursorTy pvrtmp6107 = tmp_struct220.field0;
            CursorTy pvrtmp6108 = tmp_struct220.field1;
            CursorTy pvrtmp6109 = tmp_struct220.field2;
            CursorTy pvrtmp6110 = tmp_struct220.field3;
            CursorTy fltPrd4790 = (CursorTy) pvrtmp6109;
            CursorTy fltPrd4791 = (CursorTy) pvrtmp6110;
            CursorTy pvrtmp6112 = (CursorTy) fltPrd4791;
            CursorTy pvrtmp6111 = (CursorTy) fltPrd4790;
            CursorTy y1492 = (CursorTy) pvrtmp6111;
            CursorTy fltPrd4792 = (CursorTy) pvrtmp6109;
            CursorTy fltPrd4793 = (CursorTy) pvrtmp6110;
            CursorTy pvrtmp6114 = (CursorTy) fltPrd4793;
            CursorTy pvrtmp6113 = (CursorTy) fltPrd4792;
            CursorTy end_y1492 = (CursorTy) pvrtmp6114;
            CursorTy end_r1921_3449_3450 = (CursorTy) pvrtmp6107;
            CursorTy endof3350 = (CursorTy) pvrtmp6108;
            CursorTy case2871 = (CursorTy) endof3350;
            CursorTy x1490 = (CursorTy) case2871;
            CursorTy loc2883 = (CursorTy) end_y1492;
            CursorCursorCursorCursorProd tmp_struct221 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921_3449_3450, loc2883, x1490);
            CursorTy pvrtmp6115 = tmp_struct221.field0;
            CursorTy pvrtmp6116 = tmp_struct221.field1;
            CursorTy pvrtmp6117 = tmp_struct221.field2;
            CursorTy pvrtmp6118 = tmp_struct221.field3;
            CursorTy fltPrd4794 = (CursorTy) pvrtmp6117;
            CursorTy fltPrd4795 = (CursorTy) pvrtmp6118;
            CursorTy pvrtmp6120 = (CursorTy) fltPrd4795;
            CursorTy pvrtmp6119 = (CursorTy) fltPrd4794;
            CursorTy y1493 = (CursorTy) pvrtmp6119;
            CursorTy fltPrd4796 = (CursorTy) pvrtmp6117;
            CursorTy fltPrd4797 = (CursorTy) pvrtmp6118;
            CursorTy pvrtmp6122 = (CursorTy) fltPrd4797;
            CursorTy pvrtmp6121 = (CursorTy) fltPrd4796;
            CursorTy end_y1493 = (CursorTy) pvrtmp6122;
            CursorTy end_r1921_3449_3450_3451 = (CursorTy) pvrtmp6115;
            CursorTy endof3351 = (CursorTy) pvrtmp6116;

            *(TagTyPacked *) loc1919 = 12;

            CursorTy writetag4057 = loc1919 + 1;
            CursorTy writecur4058 = (CursorTy) end_y1491;
            CursorTy writecur4059 = (CursorTy) end_y1492;
            CursorTy writecur4060 = (CursorTy) end_y1493;
            CursorTy pvrtmp6124 = (CursorTy) writecur4060;
            CursorTy pvrtmp6123 = (CursorTy) loc1919;
            CursorTy taildc3352 = (CursorTy) pvrtmp6123;
            CursorTy end_taildc3352 = (CursorTy) pvrtmp6124;
            CursorTy pvrtmp6126 = (CursorTy) end_taildc3352;
            CursorTy pvrtmp6125 = (CursorTy) taildc3352;
            CursorTy fltPrd4798 = (CursorTy) pvrtmp6125;
            CursorTy fltPrd4799 = (CursorTy) pvrtmp6126;

            return (CursorCursorCursorCursorProd) {end_r1921_3449_3450_3451,
                                                   endof3351, fltPrd4798,
                                                   fltPrd4799};
            break;
        }

      case 13:
        {
            CursorTy field_cur4062 = (CursorTy) tmpcur5910;
            CursorTy case2887 = (CursorTy) field_cur4062;
            CursorTy x1494 = (CursorTy) case2887;
            CursorTy loc2895 = loc1919 + 1;
            CursorCursorCursorCursorProd tmp_struct222 =
                                          _add_size_and_rel_offsets_Expr(end_r1920, end_r1921, loc2895, x1494);
            CursorTy pvrtmp6127 = tmp_struct222.field0;
            CursorTy pvrtmp6128 = tmp_struct222.field1;
            CursorTy pvrtmp6129 = tmp_struct222.field2;
            CursorTy pvrtmp6130 = tmp_struct222.field3;
            CursorTy fltPrd4800 = (CursorTy) pvrtmp6129;
            CursorTy fltPrd4801 = (CursorTy) pvrtmp6130;
            CursorTy pvrtmp6132 = (CursorTy) fltPrd4801;
            CursorTy pvrtmp6131 = (CursorTy) fltPrd4800;
            CursorTy y1496 = (CursorTy) pvrtmp6131;
            CursorTy fltPrd4802 = (CursorTy) pvrtmp6129;
            CursorTy fltPrd4803 = (CursorTy) pvrtmp6130;
            CursorTy pvrtmp6134 = (CursorTy) fltPrd4803;
            CursorTy pvrtmp6133 = (CursorTy) fltPrd4802;
            CursorTy end_y1496 = (CursorTy) pvrtmp6134;
            CursorTy end_r1921_3452 = (CursorTy) pvrtmp6127;
            CursorTy endof3353 = (CursorTy) pvrtmp6128;
            CursorTy case2888 = (CursorTy) endof3353;
            CursorTy x1495 = (CursorTy) case2888;
            CursorTy loc2896 = (CursorTy) end_y1496;
            CursorCursorCursorCursorProd tmp_struct223 =
                                          _add_size_and_rel_offsets_ListExpr(end_r1920, end_r1921_3452, loc2896, x1495);
            CursorTy pvrtmp6135 = tmp_struct223.field0;
            CursorTy pvrtmp6136 = tmp_struct223.field1;
            CursorTy pvrtmp6137 = tmp_struct223.field2;
            CursorTy pvrtmp6138 = tmp_struct223.field3;
            CursorTy fltPrd4804 = (CursorTy) pvrtmp6137;
            CursorTy fltPrd4805 = (CursorTy) pvrtmp6138;
            CursorTy pvrtmp6140 = (CursorTy) fltPrd4805;
            CursorTy pvrtmp6139 = (CursorTy) fltPrd4804;
            CursorTy y1497 = (CursorTy) pvrtmp6139;
            CursorTy fltPrd4806 = (CursorTy) pvrtmp6137;
            CursorTy fltPrd4807 = (CursorTy) pvrtmp6138;
            CursorTy pvrtmp6142 = (CursorTy) fltPrd4807;
            CursorTy pvrtmp6141 = (CursorTy) fltPrd4806;
            CursorTy end_y1497 = (CursorTy) pvrtmp6142;
            CursorTy end_r1921_3452_3453 = (CursorTy) pvrtmp6135;
            CursorTy endof3354 = (CursorTy) pvrtmp6136;

            *(TagTyPacked *) loc1919 = 13;

            CursorTy writetag4065 = loc1919 + 1;
            CursorTy writecur4066 = (CursorTy) end_y1496;
            CursorTy writecur4067 = (CursorTy) end_y1497;
            CursorTy pvrtmp6144 = (CursorTy) writecur4067;
            CursorTy pvrtmp6143 = (CursorTy) loc1919;
            CursorTy taildc3355 = (CursorTy) pvrtmp6143;
            CursorTy end_taildc3355 = (CursorTy) pvrtmp6144;
            CursorTy pvrtmp6146 = (CursorTy) end_taildc3355;
            CursorTy pvrtmp6145 = (CursorTy) taildc3355;
            CursorTy fltPrd4808 = (CursorTy) pvrtmp6145;
            CursorTy fltPrd4809 = (CursorTy) pvrtmp6146;

            return (CursorCursorCursorCursorProd) {end_r1921_3452_3453,
                                                   endof3354, fltPrd4808,
                                                   fltPrd4809};
            break;
        }

      case 14:
        {
            CursorTy field_cur4069 = (CursorTy) tmpcur5910;
            CursorTy case2899 = (CursorTy) field_cur4069;
            SymTy tmpval6147 = *(SymTy *) case2899;
            CursorTy tmpcur6148 = case2899 + sizeof(SymTy);
            SymTy x1498 = (SymTy) tmpval6147;
            CursorTy end_x1498 = (CursorTy) tmpcur6148;
            CursorTy jump3356 = case2899 + 8;

            *(TagTyPacked *) loc1919 = 14;

            CursorTy writetag4071 = loc1919 + 1;

            *(SymTy *) writetag4071 = x1498;

            CursorTy writecur4072 = writetag4071 + sizeof(SymTy);
            CursorTy pvrtmp6150 = (CursorTy) writecur4072;
            CursorTy pvrtmp6149 = (CursorTy) loc1919;
            CursorTy taildc3357 = (CursorTy) pvrtmp6149;
            CursorTy end_taildc3357 = (CursorTy) pvrtmp6150;
            CursorTy pvrtmp6152 = (CursorTy) end_taildc3357;
            CursorTy pvrtmp6151 = (CursorTy) taildc3357;
            CursorTy fltPrd4810 = (CursorTy) pvrtmp6151;
            CursorTy fltPrd4811 = (CursorTy) pvrtmp6152;

            return (CursorCursorCursorCursorProd) {end_r1921, jump3356,
                                                   fltPrd4810, fltPrd4811};
            break;
        }

      case 15:
        {
            CursorTy field_cur4074 = (CursorTy) tmpcur5910;
            CursorTy case2903 = (CursorTy) field_cur4074;
            SymTy tmpval6153 = *(SymTy *) case2903;
            CursorTy tmpcur6154 = case2903 + sizeof(SymTy);
            SymTy x1500 = (SymTy) tmpval6153;
            CursorTy end_x1500 = (CursorTy) tmpcur6154;
            CursorTy jump3358 = case2903 + 8;

            *(TagTyPacked *) loc1919 = 15;

            CursorTy writetag4076 = loc1919 + 1;

            *(SymTy *) writetag4076 = x1500;

            CursorTy writecur4077 = writetag4076 + sizeof(SymTy);
            CursorTy pvrtmp6156 = (CursorTy) writecur4077;
            CursorTy pvrtmp6155 = (CursorTy) loc1919;
            CursorTy taildc3359 = (CursorTy) pvrtmp6155;
            CursorTy end_taildc3359 = (CursorTy) pvrtmp6156;
            CursorTy pvrtmp6158 = (CursorTy) end_taildc3359;
            CursorTy pvrtmp6157 = (CursorTy) taildc3359;
            CursorTy fltPrd4812 = (CursorTy) pvrtmp6157;
            CursorTy fltPrd4813 = (CursorTy) pvrtmp6158;

            return (CursorCursorCursorCursorProd) {end_r1921, jump3358,
                                                   fltPrd4812, fltPrd4813};
            break;
        }

      case 16:
        {
            CursorTy field_cur4079 = (CursorTy) tmpcur5910;
            CursorTy case2907 = (CursorTy) field_cur4079;
            SymTy tmpval6159 = *(SymTy *) case2907;
            CursorTy tmpcur6160 = case2907 + sizeof(SymTy);
            SymTy x1502 = (SymTy) tmpval6159;
            CursorTy end_x1502 = (CursorTy) tmpcur6160;
            CursorTy jump3360 = case2907 + 8;

            *(TagTyPacked *) loc1919 = 16;

            CursorTy writetag4081 = loc1919 + 1;

            *(SymTy *) writetag4081 = x1502;

            CursorTy writecur4082 = writetag4081 + sizeof(SymTy);
            CursorTy pvrtmp6162 = (CursorTy) writecur4082;
            CursorTy pvrtmp6161 = (CursorTy) loc1919;
            CursorTy taildc3361 = (CursorTy) pvrtmp6161;
            CursorTy end_taildc3361 = (CursorTy) pvrtmp6162;
            CursorTy pvrtmp6164 = (CursorTy) end_taildc3361;
            CursorTy pvrtmp6163 = (CursorTy) taildc3361;
            CursorTy fltPrd4814 = (CursorTy) pvrtmp6163;
            CursorTy fltPrd4815 = (CursorTy) pvrtmp6164;

            return (CursorCursorCursorCursorProd) {end_r1921, jump3360,
                                                   fltPrd4814, fltPrd4815};
            break;
        }

      case 17:
        {
            CursorTy field_cur4084 = (CursorTy) tmpcur5910;
            CursorTy jump3362 = loc1918 + 1;

            *(TagTyPacked *) loc1919 = 17;

            CursorTy writetag4085 = loc1919 + 1;
            CursorTy pvrtmp6166 = (CursorTy) writetag4085;
            CursorTy pvrtmp6165 = (CursorTy) loc1919;
            CursorTy taildc3363 = (CursorTy) pvrtmp6165;
            CursorTy end_taildc3363 = (CursorTy) pvrtmp6166;
            CursorTy pvrtmp6168 = (CursorTy) end_taildc3363;
            CursorTy pvrtmp6167 = (CursorTy) taildc3363;
            CursorTy fltPrd4816 = (CursorTy) pvrtmp6167;
            CursorTy fltPrd4817 = (CursorTy) pvrtmp6168;

            return (CursorCursorCursorCursorProd) {end_r1921, jump3362,
                                                   fltPrd4816, fltPrd4817};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6673 = *(CursorTy *) tmpcur5910;
            CursorTy tmpaftercur6674 = tmpcur5910 + 8;
            TagTyPacked tagtmp6675 = *(TagTyPacked *) tmpcur6673;
            CursorTy tailtmp6676 = tmpcur6673 + 1;

            tmpval5909 = tagtmp6675;
            tmpcur5910 = tailtmp6676;
            goto switch6169;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6673 = *(CursorTy *) tmpcur5910;
            CursorTy tmpaftercur6674 = tmpcur5910 + 8;
            TagTyPacked tagtmp6675 = *(TagTyPacked *) tmpcur6673;
            CursorTy tailtmp6676 = tmpcur6673 + 1;

            tmpval5909 = tagtmp6675;
            tmpcur5910 = tailtmp6676;
            goto switch6169;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5909");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _add_size_and_rel_offsets_Toplvl(CursorTy end_r1924,
                                                              CursorTy end_r1925,
                                                              CursorTy loc1923,
                                                              CursorTy arg1504)
{
    CursorTy loc1922 = (CursorTy) arg1504;

    if (loc1923 + 18 > end_r1925) {
        ChunkTy new_chunk233 = alloc_chunk(end_r1925);
        CursorTy chunk_start234 = new_chunk233.start_ptr;
        CursorTy chunk_end235 = new_chunk233.end_ptr;

        end_r1925 = chunk_end235;
        *(TagTyPacked *) loc1923 = 255;

        CursorTy redir = loc1923 + 1;

        *(CursorTy *) redir = chunk_start234;
        loc1923 = chunk_start234;
    }

    TagTyPacked tmpval6170 = *(TagTyPacked *) arg1504;
    CursorTy tmpcur6171 = arg1504 + 1;


  switch6236:
    ;
    switch (tmpval6170) {

      case 0:
        {
            CursorTy field_cur4087 = (CursorTy) tmpcur6171;
            CursorTy case2914 = (CursorTy) field_cur4087;
            CursorTy x1505 = (CursorTy) case2914;
            CursorTy loc2922 = loc1923 + 1;
            CursorCursorCursorCursorProd tmp_struct227 =
                                          _add_size_and_rel_offsets_ListSym(end_r1924, end_r1925, loc2922, x1505);
            CursorTy pvrtmp6172 = tmp_struct227.field0;
            CursorTy pvrtmp6173 = tmp_struct227.field1;
            CursorTy pvrtmp6174 = tmp_struct227.field2;
            CursorTy pvrtmp6175 = tmp_struct227.field3;
            CursorTy fltPrd4818 = (CursorTy) pvrtmp6174;
            CursorTy fltPrd4819 = (CursorTy) pvrtmp6175;
            CursorTy pvrtmp6177 = (CursorTy) fltPrd4819;
            CursorTy pvrtmp6176 = (CursorTy) fltPrd4818;
            CursorTy y1507 = (CursorTy) pvrtmp6176;
            CursorTy fltPrd4820 = (CursorTy) pvrtmp6174;
            CursorTy fltPrd4821 = (CursorTy) pvrtmp6175;
            CursorTy pvrtmp6179 = (CursorTy) fltPrd4821;
            CursorTy pvrtmp6178 = (CursorTy) fltPrd4820;
            CursorTy end_y1507 = (CursorTy) pvrtmp6179;
            CursorTy end_r1925_3454 = (CursorTy) pvrtmp6172;
            CursorTy endof3364 = (CursorTy) pvrtmp6173;
            CursorTy case2915 = (CursorTy) endof3364;
            CursorTy x1506 = (CursorTy) case2915;
            CursorTy loc2923 = (CursorTy) end_y1507;
            CursorCursorCursorCursorProd tmp_struct228 =
                                          _add_size_and_rel_offsets_Expr(end_r1924, end_r1925_3454, loc2923, x1506);
            CursorTy pvrtmp6180 = tmp_struct228.field0;
            CursorTy pvrtmp6181 = tmp_struct228.field1;
            CursorTy pvrtmp6182 = tmp_struct228.field2;
            CursorTy pvrtmp6183 = tmp_struct228.field3;
            CursorTy fltPrd4822 = (CursorTy) pvrtmp6182;
            CursorTy fltPrd4823 = (CursorTy) pvrtmp6183;
            CursorTy pvrtmp6185 = (CursorTy) fltPrd4823;
            CursorTy pvrtmp6184 = (CursorTy) fltPrd4822;
            CursorTy y1508 = (CursorTy) pvrtmp6184;
            CursorTy fltPrd4824 = (CursorTy) pvrtmp6182;
            CursorTy fltPrd4825 = (CursorTy) pvrtmp6183;
            CursorTy pvrtmp6187 = (CursorTy) fltPrd4825;
            CursorTy pvrtmp6186 = (CursorTy) fltPrd4824;
            CursorTy end_y1508 = (CursorTy) pvrtmp6187;
            CursorTy end_r1925_3454_3455 = (CursorTy) pvrtmp6180;
            CursorTy endof3365 = (CursorTy) pvrtmp6181;

            *(TagTyPacked *) loc1923 = 0;

            CursorTy writetag4090 = loc1923 + 1;
            CursorTy writecur4091 = (CursorTy) end_y1507;
            CursorTy writecur4092 = (CursorTy) end_y1508;
            CursorTy pvrtmp6189 = (CursorTy) writecur4092;
            CursorTy pvrtmp6188 = (CursorTy) loc1923;
            CursorTy taildc3366 = (CursorTy) pvrtmp6188;
            CursorTy end_taildc3366 = (CursorTy) pvrtmp6189;
            CursorTy pvrtmp6191 = (CursorTy) end_taildc3366;
            CursorTy pvrtmp6190 = (CursorTy) taildc3366;
            CursorTy fltPrd4826 = (CursorTy) pvrtmp6190;
            CursorTy fltPrd4827 = (CursorTy) pvrtmp6191;

            return (CursorCursorCursorCursorProd) {end_r1925_3454_3455,
                                                   endof3365, fltPrd4826,
                                                   fltPrd4827};
            break;
        }

      case 1:
        {
            CursorTy field_cur4094 = (CursorTy) tmpcur6171;
            CursorTy case2926 = (CursorTy) field_cur4094;
            CursorTy x1509 = (CursorTy) case2926;
            CursorTy loc2934 = loc1923 + 1;
            CursorCursorCursorCursorProd tmp_struct229 =
                                          _add_size_and_rel_offsets_ListSym(end_r1924, end_r1925, loc2934, x1509);
            CursorTy pvrtmp6192 = tmp_struct229.field0;
            CursorTy pvrtmp6193 = tmp_struct229.field1;
            CursorTy pvrtmp6194 = tmp_struct229.field2;
            CursorTy pvrtmp6195 = tmp_struct229.field3;
            CursorTy fltPrd4828 = (CursorTy) pvrtmp6194;
            CursorTy fltPrd4829 = (CursorTy) pvrtmp6195;
            CursorTy pvrtmp6197 = (CursorTy) fltPrd4829;
            CursorTy pvrtmp6196 = (CursorTy) fltPrd4828;
            CursorTy y1511 = (CursorTy) pvrtmp6196;
            CursorTy fltPrd4830 = (CursorTy) pvrtmp6194;
            CursorTy fltPrd4831 = (CursorTy) pvrtmp6195;
            CursorTy pvrtmp6199 = (CursorTy) fltPrd4831;
            CursorTy pvrtmp6198 = (CursorTy) fltPrd4830;
            CursorTy end_y1511 = (CursorTy) pvrtmp6199;
            CursorTy end_r1925_3456 = (CursorTy) pvrtmp6192;
            CursorTy endof3367 = (CursorTy) pvrtmp6193;
            CursorTy case2927 = (CursorTy) endof3367;
            CursorTy x1510 = (CursorTy) case2927;
            CursorTy loc2935 = (CursorTy) end_y1511;
            CursorCursorCursorCursorProd tmp_struct230 =
                                          _add_size_and_rel_offsets_Expr(end_r1924, end_r1925_3456, loc2935, x1510);
            CursorTy pvrtmp6200 = tmp_struct230.field0;
            CursorTy pvrtmp6201 = tmp_struct230.field1;
            CursorTy pvrtmp6202 = tmp_struct230.field2;
            CursorTy pvrtmp6203 = tmp_struct230.field3;
            CursorTy fltPrd4832 = (CursorTy) pvrtmp6202;
            CursorTy fltPrd4833 = (CursorTy) pvrtmp6203;
            CursorTy pvrtmp6205 = (CursorTy) fltPrd4833;
            CursorTy pvrtmp6204 = (CursorTy) fltPrd4832;
            CursorTy y1512 = (CursorTy) pvrtmp6204;
            CursorTy fltPrd4834 = (CursorTy) pvrtmp6202;
            CursorTy fltPrd4835 = (CursorTy) pvrtmp6203;
            CursorTy pvrtmp6207 = (CursorTy) fltPrd4835;
            CursorTy pvrtmp6206 = (CursorTy) fltPrd4834;
            CursorTy end_y1512 = (CursorTy) pvrtmp6207;
            CursorTy end_r1925_3456_3457 = (CursorTy) pvrtmp6200;
            CursorTy endof3368 = (CursorTy) pvrtmp6201;

            *(TagTyPacked *) loc1923 = 1;

            CursorTy writetag4097 = loc1923 + 1;
            CursorTy writecur4098 = (CursorTy) end_y1511;
            CursorTy writecur4099 = (CursorTy) end_y1512;
            CursorTy pvrtmp6209 = (CursorTy) writecur4099;
            CursorTy pvrtmp6208 = (CursorTy) loc1923;
            CursorTy taildc3369 = (CursorTy) pvrtmp6208;
            CursorTy end_taildc3369 = (CursorTy) pvrtmp6209;
            CursorTy pvrtmp6211 = (CursorTy) end_taildc3369;
            CursorTy pvrtmp6210 = (CursorTy) taildc3369;
            CursorTy fltPrd4836 = (CursorTy) pvrtmp6210;
            CursorTy fltPrd4837 = (CursorTy) pvrtmp6211;

            return (CursorCursorCursorCursorProd) {end_r1925_3456_3457,
                                                   endof3368, fltPrd4836,
                                                   fltPrd4837};
            break;
        }

      case 2:
        {
            CursorTy field_cur4101 = (CursorTy) tmpcur6171;
            CursorTy case2938 = (CursorTy) field_cur4101;
            CursorTy x1513 = (CursorTy) case2938;
            CursorTy loc2942 = loc1923 + 1;
            CursorCursorCursorCursorProd tmp_struct231 =
                                          _add_size_and_rel_offsets_ListToplvl(end_r1924, end_r1925, loc2942, x1513);
            CursorTy pvrtmp6212 = tmp_struct231.field0;
            CursorTy pvrtmp6213 = tmp_struct231.field1;
            CursorTy pvrtmp6214 = tmp_struct231.field2;
            CursorTy pvrtmp6215 = tmp_struct231.field3;
            CursorTy fltPrd4838 = (CursorTy) pvrtmp6214;
            CursorTy fltPrd4839 = (CursorTy) pvrtmp6215;
            CursorTy pvrtmp6217 = (CursorTy) fltPrd4839;
            CursorTy pvrtmp6216 = (CursorTy) fltPrd4838;
            CursorTy y1514 = (CursorTy) pvrtmp6216;
            CursorTy fltPrd4840 = (CursorTy) pvrtmp6214;
            CursorTy fltPrd4841 = (CursorTy) pvrtmp6215;
            CursorTy pvrtmp6219 = (CursorTy) fltPrd4841;
            CursorTy pvrtmp6218 = (CursorTy) fltPrd4840;
            CursorTy end_y1514 = (CursorTy) pvrtmp6219;
            CursorTy end_r1925_3458 = (CursorTy) pvrtmp6212;
            CursorTy endof3370 = (CursorTy) pvrtmp6213;

            *(TagTyPacked *) loc1923 = 2;

            CursorTy writetag4103 = loc1923 + 1;
            CursorTy writecur4104 = (CursorTy) end_y1514;
            CursorTy pvrtmp6221 = (CursorTy) writecur4104;
            CursorTy pvrtmp6220 = (CursorTy) loc1923;
            CursorTy taildc3371 = (CursorTy) pvrtmp6220;
            CursorTy end_taildc3371 = (CursorTy) pvrtmp6221;
            CursorTy pvrtmp6223 = (CursorTy) end_taildc3371;
            CursorTy pvrtmp6222 = (CursorTy) taildc3371;
            CursorTy fltPrd4842 = (CursorTy) pvrtmp6222;
            CursorTy fltPrd4843 = (CursorTy) pvrtmp6223;

            return (CursorCursorCursorCursorProd) {end_r1925_3458, endof3370,
                                                   fltPrd4842, fltPrd4843};
            break;
        }

      case 3:
        {
            CursorTy field_cur4106 = (CursorTy) tmpcur6171;
            CursorTy case2944 = (CursorTy) field_cur4106;
            CursorTy x1515 = (CursorTy) case2944;
            CursorTy loc2948 = loc1923 + 1;
            CursorCursorCursorCursorProd tmp_struct232 =
                                          _add_size_and_rel_offsets_Expr(end_r1924, end_r1925, loc2948, x1515);
            CursorTy pvrtmp6224 = tmp_struct232.field0;
            CursorTy pvrtmp6225 = tmp_struct232.field1;
            CursorTy pvrtmp6226 = tmp_struct232.field2;
            CursorTy pvrtmp6227 = tmp_struct232.field3;
            CursorTy fltPrd4844 = (CursorTy) pvrtmp6226;
            CursorTy fltPrd4845 = (CursorTy) pvrtmp6227;
            CursorTy pvrtmp6229 = (CursorTy) fltPrd4845;
            CursorTy pvrtmp6228 = (CursorTy) fltPrd4844;
            CursorTy y1516 = (CursorTy) pvrtmp6228;
            CursorTy fltPrd4846 = (CursorTy) pvrtmp6226;
            CursorTy fltPrd4847 = (CursorTy) pvrtmp6227;
            CursorTy pvrtmp6231 = (CursorTy) fltPrd4847;
            CursorTy pvrtmp6230 = (CursorTy) fltPrd4846;
            CursorTy end_y1516 = (CursorTy) pvrtmp6231;
            CursorTy end_r1925_3459 = (CursorTy) pvrtmp6224;
            CursorTy endof3372 = (CursorTy) pvrtmp6225;

            *(TagTyPacked *) loc1923 = 3;

            CursorTy writetag4108 = loc1923 + 1;
            CursorTy writecur4109 = (CursorTy) end_y1516;
            CursorTy pvrtmp6233 = (CursorTy) writecur4109;
            CursorTy pvrtmp6232 = (CursorTy) loc1923;
            CursorTy taildc3373 = (CursorTy) pvrtmp6232;
            CursorTy end_taildc3373 = (CursorTy) pvrtmp6233;
            CursorTy pvrtmp6235 = (CursorTy) end_taildc3373;
            CursorTy pvrtmp6234 = (CursorTy) taildc3373;
            CursorTy fltPrd4848 = (CursorTy) pvrtmp6234;
            CursorTy fltPrd4849 = (CursorTy) pvrtmp6235;

            return (CursorCursorCursorCursorProd) {end_r1925_3459, endof3372,
                                                   fltPrd4848, fltPrd4849};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6677 = *(CursorTy *) tmpcur6171;
            CursorTy tmpaftercur6678 = tmpcur6171 + 8;
            TagTyPacked tagtmp6679 = *(TagTyPacked *) tmpcur6677;
            CursorTy tailtmp6680 = tmpcur6677 + 1;

            tmpval6170 = tagtmp6679;
            tmpcur6171 = tailtmp6680;
            goto switch6236;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6677 = *(CursorTy *) tmpcur6171;
            CursorTy tmpaftercur6678 = tmpcur6171 + 8;
            TagTyPacked tagtmp6679 = *(TagTyPacked *) tmpcur6677;
            CursorTy tailtmp6680 = tmpcur6677 + 1;

            tmpval6170 = tagtmp6679;
            tmpcur6171 = tailtmp6680;
            goto switch6236;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6170");
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
