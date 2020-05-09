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
  return 0;
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

CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r620, CursorTy end_r621,
                                           CursorTy loc619, CursorTy arg339);
CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r626,
                                            CursorTy end_r627, CursorTy loc625,
                                            CursorTy arg349);
CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r632,
                                              CursorTy end_r633,
                                              CursorTy loc631, CursorTy arg359);
CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r638, CursorTy end_r639,
                                           CursorTy loc637, CursorTy arg369);
CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r644, CursorTy end_r645,
                                         CursorTy loc643, CursorTy arg387);
CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r650,
                                              CursorTy end_r651,
                                              CursorTy loc649, CursorTy arg393);
CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r656, CursorTy end_r657,
                                          CursorTy loc655, CursorTy arg407);
CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r662, CursorTy end_r663,
                                        CursorTy loc661, CursorTy arg421);
CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r668, CursorTy end_r669,
                                          CursorTy loc667, CursorTy arg531);

CursorTy _print_ListSym(CursorTy p3299);
CursorTy _print_ListExpr(CursorTy p3306);
CursorTy _print_ListToplvl(CursorTy p3312);
CursorTy _print_Formals(CursorTy p3318);
CursorTy _print_Datum(CursorTy p3328);
CursorTy _print_LAMBDACASE(CursorTy p3334);
CursorTy _print_LVBIND(CursorTy p3341);
CursorTy _print_Expr(CursorTy p3348);
CursorTy _print_Toplvl(CursorTy p3384);

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
            printf("Unknown tag in: tmpval2511: %d", tmpval2511);
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

// sizes of things copied.
IntTy copied = 0;
IntTy copying_limit = (4 * GB);

CursorCursorCursorCursorProd enlarge_if(CursorTy end_r662, CursorTy end_r663,
                                        CursorTy loc661, CursorTy arg421) {
    CursorTy loc660 = (CursorTy) arg421;
    CursorTy loc1088 = loc661 + 1;
    CursorTy loc1089 = loc1088 + 8;
    TagTyPacked tmpval2727 = *(TagTyPacked *) arg421;
    CursorTy tmpcur2728 = arg421 + 1;

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

}

CursorCursorCursorCursorProd enlarge_app(CursorTy end_r662, CursorTy end_r663,
                                         CursorTy loc661, CursorTy arg421) {
    CursorTy loc660 = (CursorTy) arg421;
    CursorTy loc1088 = loc661 + 1;
    CursorTy loc1089 = loc1088 + 8;
    TagTyPacked tmpval2727 = *(TagTyPacked *) arg421;
    CursorTy tmpcur2728 = arg421 + 1;

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

}

CursorCursorCursorCursorProd enlarge_continuation(CursorTy end_r662, CursorTy end_r663,
                                                  CursorTy loc661, CursorTy arg421) {
    CursorTy loc660 = (CursorTy) arg421;
    CursorTy loc1088 = loc661 + 1;
    CursorTy loc1089 = loc1088 + 8;
    TagTyPacked tmpval2727 = *(TagTyPacked *) arg421;
    CursorTy tmpcur2728 = arg421 + 1;

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

        // Enlarge IF
      case 3:
        {
            // TODO
            CursorTy cur = loc661;

            if (copied > copying_limit) {
                CursorCursorCursorCursorProd tmp_struct = enlarge_if(end_r662, end_r663, cur, arg421);
                return tmp_struct;
            }

            // if
            *(TagTyPacked *) cur = 3;
            cur += 1;
            CursorTy d = cur;
            // quote
            *(TagTyPacked *) cur = 9;
            cur += 1;
            // intlit 42
            *(TagTyPacked *) cur = 0;
            cur += 1;
            *(IntTy *) cur = 42;
            cur += 8;

            CursorCursorCursorCursorProd tmp_struct = enlarge_if(end_r662, end_r663, cur, arg421);
            CursorCursorCursorCursorProd tmp_struct2 = enlarge_if(tmp_struct.field1, tmp_struct.field0, tmp_struct.field3, arg421);

            IntTy size = (IntTy) (tmp_struct2.field3 - tmp_struct2.field2);
            copied += size;

            // printf("copied: %lld\n", copied);

            return tmp_struct2;

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

        // Enlarge WithCMark
      case 12:
        {
            // TODO
            CursorTy cur = loc661;

            if (copied > copying_limit) {

                CursorCursorCursorCursorProd tmp_struct = enlarge_continuation(end_r662, end_r663, cur, arg421);
                return tmp_struct;

            }

            // if
            *(TagTyPacked *) cur = 3;
            cur += 1;
            // quote
            *(TagTyPacked *) cur = 9;
            cur += 1;
            // intlit 42
            *(TagTyPacked *) cur = 0;
            cur += 1;
            *(IntTy *) cur = 42;
            cur += 8;
            CursorCursorCursorCursorProd tmp_struct = enlarge_continuation(end_r662, end_r663, cur, arg421);
            CursorCursorCursorCursorProd tmp_struct2 = enlarge_continuation(tmp_struct.field1, tmp_struct.field0, tmp_struct.field3, arg421);

            IntTy size = (IntTy) (tmp_struct2.field3 - tmp_struct2.field2);
            copied += size;
            // printf("copied: %lld\n", copied);

            return tmp_struct2;
            break;
        }

        // Enlarge App
      case 13:
        {
            // TODO
            CursorTy cur = loc661;

            if (copied > copying_limit) {

                // printf("stopped copying...\n");
                CursorCursorCursorCursorProd tmp_struct = enlarge_app(end_r662, end_r663, cur, arg421);
                return tmp_struct;
            }

            // if
            *(TagTyPacked *) cur = 3;
            cur += 1;
            CursorTy d = cur;
            // quote
            *(TagTyPacked *) cur = 9;
            cur += 1;
            // intlit 42
            *(TagTyPacked *) cur = 0;
            cur += 1;
            *(IntTy *) cur = 42;
            cur += 8;

            CursorCursorCursorCursorProd tmp_struct = enlarge_app(end_r662, end_r663, cur, arg421);
            CursorCursorCursorCursorProd tmp_struct2 = enlarge_app(tmp_struct.field1, tmp_struct.field0, tmp_struct.field3, arg421);

            IntTy size = (IntTy) (tmp_struct2.field3 - tmp_struct2.field2);
            copied += size;
            // printf("copied: %lld\n", copied);

            // get: end-in, end-out, out, in
            // return: end-out, end-in, in, out
            // return (CursorCursorCursorCursorProd) {tmp_struct2.field};

            // _print_LVBIND(tmp_struct2.field1);
            // printf("\n");
            // exit(1);

            return tmp_struct2;

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
CursorTy _print_ListSym(CursorTy p3299)
{
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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
    fflush(stdout);
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

    // _print_Toplvl(r2565);
    // printf("\n\n");

    RegionTy *region = alloc_region(global_init_biginf_buf_size);
    CursorTy out_reg = region->start_ptr;
    CursorTy end_out_reg = out_reg + global_init_biginf_buf_size;

    CursorCursorCursorCursorProd tmp_struct =
        _copy_Toplvl(end_r2565, end_out_reg, out_reg, r2565);
    // _print_Toplvl(out_reg);
    // printf("\n");
    CursorTy val_start = tmp_struct.field2;
    CursorTy val_end = tmp_struct.field3;
    IntTy val_size = (IntTy) (val_end - val_start);

    // write output file
    size_t len = strlen(global_benchfile_param);
    char* suffix = ".big";
    size_t suffix_len = strlen(suffix);
    char *output_filename = malloc(len + suffix_len + 1);
    strcpy(output_filename, global_benchfile_param);
    strcat(output_filename, suffix);
    FILE *out_hdl = fopen(output_filename, "wb");
    const size_t wrote = fwrite(val_start, val_size, 1, out_hdl);
    fclose(out_hdl);
    printf("Wrote: %s\n", output_filename);
    printf("copied: %lld\n", copied);
}
