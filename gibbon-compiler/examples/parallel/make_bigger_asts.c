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

// --------------------------------------------------------------------------------

IntTy copied = 0;
#define COPYING_LIMIT (1.5 * GB)

CursorCursorCursorCursorProd duplicate_expr(IntTy n, CursorTy end_r2003, CursorTy end_r2004_3752, CursorTy loc2752, CursorTy x1788) {

    CursorTy cur = loc2752;
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

    if (n == 0 || copied > COPYING_LIMIT) {
        CursorCursorCursorCursorProd tmp_struct = _copy_Expr(end_r2003, end_r2004_3752, cur, x1788);
        CursorCursorCursorCursorProd tmp_struct2 = _copy_Expr(tmp_struct.field1, tmp_struct.field0, tmp_struct.field3, x1788);
        IntTy size = (IntTy) (tmp_struct2.field3 - tmp_struct2.field2);
        copied += size;
        return tmp_struct2;
    } else {
        CursorCursorCursorCursorProd tmp_struct = duplicate_expr(n-1, end_r2003, end_r2004_3752, cur, x1788);
        CursorCursorCursorCursorProd tmp_struct2 = duplicate_expr(n-1, tmp_struct.field1, tmp_struct.field0, tmp_struct.field3, x1788);
        IntTy size = (IntTy) (tmp_struct2.field3 - tmp_struct2.field2);
        copied += size;
        return tmp_struct2;
    }
}


// --------------------------------------------------------------------------------
// Copiers

CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r1838,
                                           CursorTy end_r1839, CursorTy loc1837,
                                           CursorTy arg1517)
{
    CursorTy loc1836 = (CursorTy) arg1517;

    if (loc1837 + 18 > end_r1839) {
        ChunkTy new_chunk52 = alloc_chunk(end_r1839);
        CursorTy chunk_start53 = new_chunk52.start_ptr;
        CursorTy chunk_end54 = new_chunk52.end_ptr;

        end_r1839 = chunk_end54;
        *(TagTyPacked *) loc1837 = 255;

        CursorTy redir = loc1837 + 1;

        *(CursorTy *) redir = chunk_start53;
        loc1837 = chunk_start53;
    }

    CursorTy loc2138 = loc1837 + 1;
    CursorTy loc2139 = loc2138 + 8;
    TagTyPacked tmpval5016 = *(TagTyPacked *) arg1517;
    CursorTy tmpcur5017 = arg1517 + 1;


  switch5036:
    ;
    switch (tmpval5016) {

      case 0:
        {
            CursorTy field_cur3574 = (CursorTy) tmpcur5017;
            CursorTy case2133 = (CursorTy) field_cur3574;
            SymTy tmpval5018 = *(SymTy *) case2133;
            CursorTy tmpcur5019 = case2133 + sizeof(SymTy);
            SymTy x1518 = (SymTy) tmpval5018;
            CursorTy end_x1518 = (CursorTy) tmpcur5019;
            CursorTy case2134 = (CursorTy) end_x1518;
            CursorTy x1519 = (CursorTy) case2134;
            CursorTy jump3080 = case2133 + 8;
            CursorCursorCursorCursorProd tmp_struct51 =
                                          _copy_ListSym(end_r1838, end_r1839, loc2139, x1519);
            CursorTy pvrtmp5020 = tmp_struct51.field0;
            CursorTy pvrtmp5021 = tmp_struct51.field1;
            CursorTy pvrtmp5022 = tmp_struct51.field2;
            CursorTy pvrtmp5023 = tmp_struct51.field3;
            CursorTy fltPrd4358 = (CursorTy) pvrtmp5022;
            CursorTy fltPrd4359 = (CursorTy) pvrtmp5023;
            CursorTy pvrtmp5025 = (CursorTy) fltPrd4359;
            CursorTy pvrtmp5024 = (CursorTy) fltPrd4358;
            CursorTy y1521 = (CursorTy) pvrtmp5024;
            CursorTy fltPrd4360 = (CursorTy) pvrtmp5022;
            CursorTy fltPrd4361 = (CursorTy) pvrtmp5023;
            CursorTy pvrtmp5027 = (CursorTy) fltPrd4361;
            CursorTy pvrtmp5026 = (CursorTy) fltPrd4360;
            CursorTy end_y1521 = (CursorTy) pvrtmp5027;
            CursorTy end_r1839_3374 = (CursorTy) pvrtmp5020;
            CursorTy endof3081 = (CursorTy) pvrtmp5021;

            *(TagTyPacked *) loc1837 = 0;

            CursorTy writetag3577 = loc1837 + 1;

            *(SymTy *) writetag3577 = x1518;

            CursorTy writecur3578 = writetag3577 + sizeof(SymTy);
            CursorTy writecur3579 = (CursorTy) end_y1521;
            CursorTy pvrtmp5029 = (CursorTy) writecur3579;
            CursorTy pvrtmp5028 = (CursorTy) loc1837;
            CursorTy taildc3082 = (CursorTy) pvrtmp5028;
            CursorTy end_taildc3082 = (CursorTy) pvrtmp5029;
            CursorTy pvrtmp5031 = (CursorTy) end_taildc3082;
            CursorTy pvrtmp5030 = (CursorTy) taildc3082;
            CursorTy fltPrd4362 = (CursorTy) pvrtmp5030;
            CursorTy fltPrd4363 = (CursorTy) pvrtmp5031;

            return (CursorCursorCursorCursorProd) {end_r1839_3374, endof3081,
                                                   fltPrd4362, fltPrd4363};
            break;
        }

      case 1:
        {
            CursorTy field_cur3581 = (CursorTy) tmpcur5017;
            CursorTy jump3083 = loc1836 + 1;

            *(TagTyPacked *) loc1837 = 1;

            CursorTy writetag3582 = loc1837 + 1;
            CursorTy pvrtmp5033 = (CursorTy) writetag3582;
            CursorTy pvrtmp5032 = (CursorTy) loc1837;
            CursorTy taildc3084 = (CursorTy) pvrtmp5032;
            CursorTy end_taildc3084 = (CursorTy) pvrtmp5033;
            CursorTy pvrtmp5035 = (CursorTy) end_taildc3084;
            CursorTy pvrtmp5034 = (CursorTy) taildc3084;
            CursorTy fltPrd4364 = (CursorTy) pvrtmp5034;
            CursorTy fltPrd4365 = (CursorTy) pvrtmp5035;

            return (CursorCursorCursorCursorProd) {end_r1839, jump3083,
                                                   fltPrd4364, fltPrd4365};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6573 = *(CursorTy *) tmpcur5017;
            CursorTy tmpaftercur6574 = tmpcur5017 + 8;
            TagTyPacked tagtmp6575 = *(TagTyPacked *) tmpcur6573;
            CursorTy tailtmp6576 = tmpcur6573 + 1;

            tmpval5016 = tagtmp6575;
            tmpcur5017 = tailtmp6576;
            goto switch5036;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6573 = *(CursorTy *) tmpcur5017;
            CursorTy tmpaftercur6574 = tmpcur5017 + 8;
            TagTyPacked tagtmp6575 = *(TagTyPacked *) tmpcur6573;
            CursorTy tailtmp6576 = tmpcur6573 + 1;

            tmpval5016 = tagtmp6575;
            tmpcur5017 = tailtmp6576;
            goto switch5036;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5016");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r1844,
                                            CursorTy end_r1845,
                                            CursorTy loc1843, CursorTy arg1527)
{
    CursorTy loc1842 = (CursorTy) arg1527;

    if (loc1843 + 18 > end_r1845) {
        ChunkTy new_chunk58 = alloc_chunk(end_r1845);
        CursorTy chunk_start59 = new_chunk58.start_ptr;
        CursorTy chunk_end60 = new_chunk58.end_ptr;

        end_r1845 = chunk_end60;
        *(TagTyPacked *) loc1843 = 255;

        CursorTy redir = loc1843 + 1;

        *(CursorTy *) redir = chunk_start59;
        loc1843 = chunk_start59;
    }

    TagTyPacked tmpval5044 = *(TagTyPacked *) arg1527;
    CursorTy tmpcur5045 = arg1527 + 1;


  switch5070:
    ;
    switch (tmpval5044) {

      case 0:
        {
            CursorTy field_cur3588 = (CursorTy) tmpcur5045;
            CursorTy case2152 = (CursorTy) field_cur3588;
            CursorTy x1528 = (CursorTy) case2152;
            CursorTy loc2160 = loc1843 + 1;
            CursorCursorCursorCursorProd tmp_struct56 =
                                          _copy_Expr(end_r1844, end_r1845, loc2160, x1528);
            CursorTy pvrtmp5046 = tmp_struct56.field0;
            CursorTy pvrtmp5047 = tmp_struct56.field1;
            CursorTy pvrtmp5048 = tmp_struct56.field2;
            CursorTy pvrtmp5049 = tmp_struct56.field3;
            CursorTy fltPrd4366 = (CursorTy) pvrtmp5048;
            CursorTy fltPrd4367 = (CursorTy) pvrtmp5049;
            CursorTy pvrtmp5051 = (CursorTy) fltPrd4367;
            CursorTy pvrtmp5050 = (CursorTy) fltPrd4366;
            CursorTy y1530 = (CursorTy) pvrtmp5050;
            CursorTy fltPrd4368 = (CursorTy) pvrtmp5048;
            CursorTy fltPrd4369 = (CursorTy) pvrtmp5049;
            CursorTy pvrtmp5053 = (CursorTy) fltPrd4369;
            CursorTy pvrtmp5052 = (CursorTy) fltPrd4368;
            CursorTy end_y1530 = (CursorTy) pvrtmp5053;
            CursorTy end_r1845_3375 = (CursorTy) pvrtmp5046;
            CursorTy endof3090 = (CursorTy) pvrtmp5047;
            CursorTy case2153 = (CursorTy) endof3090;
            CursorTy x1529 = (CursorTy) case2153;
            CursorTy loc2161 = (CursorTy) end_y1530;
            CursorCursorCursorCursorProd tmp_struct57 =
                                          _copy_ListExpr(end_r1844, end_r1845_3375, loc2161, x1529);
            CursorTy pvrtmp5054 = tmp_struct57.field0;
            CursorTy pvrtmp5055 = tmp_struct57.field1;
            CursorTy pvrtmp5056 = tmp_struct57.field2;
            CursorTy pvrtmp5057 = tmp_struct57.field3;
            CursorTy fltPrd4370 = (CursorTy) pvrtmp5056;
            CursorTy fltPrd4371 = (CursorTy) pvrtmp5057;
            CursorTy pvrtmp5059 = (CursorTy) fltPrd4371;
            CursorTy pvrtmp5058 = (CursorTy) fltPrd4370;
            CursorTy y1531 = (CursorTy) pvrtmp5058;
            CursorTy fltPrd4372 = (CursorTy) pvrtmp5056;
            CursorTy fltPrd4373 = (CursorTy) pvrtmp5057;
            CursorTy pvrtmp5061 = (CursorTy) fltPrd4373;
            CursorTy pvrtmp5060 = (CursorTy) fltPrd4372;
            CursorTy end_y1531 = (CursorTy) pvrtmp5061;
            CursorTy end_r1845_3375_3376 = (CursorTy) pvrtmp5054;
            CursorTy endof3091 = (CursorTy) pvrtmp5055;

            *(TagTyPacked *) loc1843 = 0;

            CursorTy writetag3591 = loc1843 + 1;
            CursorTy writecur3592 = (CursorTy) end_y1530;
            CursorTy writecur3593 = (CursorTy) end_y1531;
            CursorTy pvrtmp5063 = (CursorTy) writecur3593;
            CursorTy pvrtmp5062 = (CursorTy) loc1843;
            CursorTy taildc3092 = (CursorTy) pvrtmp5062;
            CursorTy end_taildc3092 = (CursorTy) pvrtmp5063;
            CursorTy pvrtmp5065 = (CursorTy) end_taildc3092;
            CursorTy pvrtmp5064 = (CursorTy) taildc3092;
            CursorTy fltPrd4374 = (CursorTy) pvrtmp5064;
            CursorTy fltPrd4375 = (CursorTy) pvrtmp5065;

            return (CursorCursorCursorCursorProd) {end_r1845_3375_3376,
                                                   endof3091, fltPrd4374,
                                                   fltPrd4375};
            break;
        }

      case 1:
        {
            CursorTy field_cur3595 = (CursorTy) tmpcur5045;
            CursorTy jump3093 = loc1842 + 1;

            *(TagTyPacked *) loc1843 = 1;

            CursorTy writetag3596 = loc1843 + 1;
            CursorTy pvrtmp5067 = (CursorTy) writetag3596;
            CursorTy pvrtmp5066 = (CursorTy) loc1843;
            CursorTy taildc3094 = (CursorTy) pvrtmp5066;
            CursorTy end_taildc3094 = (CursorTy) pvrtmp5067;
            CursorTy pvrtmp5069 = (CursorTy) end_taildc3094;
            CursorTy pvrtmp5068 = (CursorTy) taildc3094;
            CursorTy fltPrd4376 = (CursorTy) pvrtmp5068;
            CursorTy fltPrd4377 = (CursorTy) pvrtmp5069;

            return (CursorCursorCursorCursorProd) {end_r1845, jump3093,
                                                   fltPrd4376, fltPrd4377};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6581 = *(CursorTy *) tmpcur5045;
            CursorTy tmpaftercur6582 = tmpcur5045 + 8;
            TagTyPacked tagtmp6583 = *(TagTyPacked *) tmpcur6581;
            CursorTy tailtmp6584 = tmpcur6581 + 1;

            tmpval5044 = tagtmp6583;
            tmpcur5045 = tailtmp6584;
            goto switch5070;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6581 = *(CursorTy *) tmpcur5045;
            CursorTy tmpaftercur6582 = tmpcur5045 + 8;
            TagTyPacked tagtmp6583 = *(TagTyPacked *) tmpcur6581;
            CursorTy tailtmp6584 = tmpcur6581 + 1;

            tmpval5044 = tagtmp6583;
            tmpcur5045 = tailtmp6584;
            goto switch5070;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5044");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r1850,
                                              CursorTy end_r1851,
                                              CursorTy loc1849,
                                              CursorTy arg1537)
{
    CursorTy loc1848 = (CursorTy) arg1537;

    if (loc1849 + 26 > end_r1851) {
        ChunkTy new_chunk69 = alloc_chunk(end_r1851);
        CursorTy chunk_start70 = new_chunk69.start_ptr;
        CursorTy chunk_end71 = new_chunk69.end_ptr;

        end_r1851 = chunk_end71;
        *(TagTyPacked *) loc1849 = 255;

        CursorTy redir = loc1849 + 1;

        *(CursorTy *) redir = chunk_start70;
        loc1849 = chunk_start70;
    }

    CursorTy loc2197 = loc1849 + 1;
    CursorTy loc2198 = loc2197 + 8;
    CursorTy loc2214 = loc1849 + 1;
    CursorTy loc2215 = loc2214 + 8;
    CursorTy loc2216 = loc2215 + 8;
    TagTyPacked tmpval5078 = *(TagTyPacked *) arg1537;
    CursorTy tmpcur5079 = arg1537 + 1;


  switch5150:
    ;
    switch (tmpval5078) {

      case 0:
        {
            CursorTy field_cur3602 = (CursorTy) tmpcur5079;
            CursorTy case2175 = (CursorTy) field_cur3602;
            CursorTy x1538 = (CursorTy) case2175;
            CursorTy loc2183 = loc1849 + 1;
            CursorCursorCursorCursorProd tmp_struct63 =
                                          _copy_Toplvl(end_r1850, end_r1851, loc2183, x1538);
            CursorTy pvrtmp5080 = tmp_struct63.field0;
            CursorTy pvrtmp5081 = tmp_struct63.field1;
            CursorTy pvrtmp5082 = tmp_struct63.field2;
            CursorTy pvrtmp5083 = tmp_struct63.field3;
            CursorTy fltPrd4378 = (CursorTy) pvrtmp5082;
            CursorTy fltPrd4379 = (CursorTy) pvrtmp5083;
            CursorTy pvrtmp5085 = (CursorTy) fltPrd4379;
            CursorTy pvrtmp5084 = (CursorTy) fltPrd4378;
            CursorTy y1540 = (CursorTy) pvrtmp5084;
            CursorTy fltPrd4380 = (CursorTy) pvrtmp5082;
            CursorTy fltPrd4381 = (CursorTy) pvrtmp5083;
            CursorTy pvrtmp5087 = (CursorTy) fltPrd4381;
            CursorTy pvrtmp5086 = (CursorTy) fltPrd4380;
            CursorTy end_y1540 = (CursorTy) pvrtmp5087;
            CursorTy end_r1851_3377 = (CursorTy) pvrtmp5080;
            CursorTy endof3100 = (CursorTy) pvrtmp5081;
            CursorTy case2176 = (CursorTy) endof3100;
            CursorTy x1539 = (CursorTy) case2176;
            CursorTy loc2184 = (CursorTy) end_y1540;
            CursorCursorCursorCursorProd tmp_struct64 =
                                          _copy_ListToplvl(end_r1850, end_r1851_3377, loc2184, x1539);
            CursorTy pvrtmp5088 = tmp_struct64.field0;
            CursorTy pvrtmp5089 = tmp_struct64.field1;
            CursorTy pvrtmp5090 = tmp_struct64.field2;
            CursorTy pvrtmp5091 = tmp_struct64.field3;
            CursorTy fltPrd4382 = (CursorTy) pvrtmp5090;
            CursorTy fltPrd4383 = (CursorTy) pvrtmp5091;
            CursorTy pvrtmp5093 = (CursorTy) fltPrd4383;
            CursorTy pvrtmp5092 = (CursorTy) fltPrd4382;
            CursorTy y1541 = (CursorTy) pvrtmp5092;
            CursorTy fltPrd4384 = (CursorTy) pvrtmp5090;
            CursorTy fltPrd4385 = (CursorTy) pvrtmp5091;
            CursorTy pvrtmp5095 = (CursorTy) fltPrd4385;
            CursorTy pvrtmp5094 = (CursorTy) fltPrd4384;
            CursorTy end_y1541 = (CursorTy) pvrtmp5095;
            CursorTy end_r1851_3377_3378 = (CursorTy) pvrtmp5088;
            CursorTy endof3101 = (CursorTy) pvrtmp5089;

            *(TagTyPacked *) loc1849 = 0;

            CursorTy writetag3605 = loc1849 + 1;
            CursorTy writecur3606 = (CursorTy) end_y1540;
            CursorTy writecur3607 = (CursorTy) end_y1541;
            CursorTy pvrtmp5097 = (CursorTy) writecur3607;
            CursorTy pvrtmp5096 = (CursorTy) loc1849;
            CursorTy taildc3102 = (CursorTy) pvrtmp5096;
            CursorTy end_taildc3102 = (CursorTy) pvrtmp5097;
            CursorTy pvrtmp5099 = (CursorTy) end_taildc3102;
            CursorTy pvrtmp5098 = (CursorTy) taildc3102;
            CursorTy fltPrd4386 = (CursorTy) pvrtmp5098;
            CursorTy fltPrd4387 = (CursorTy) pvrtmp5099;

            return (CursorCursorCursorCursorProd) {end_r1851_3377_3378,
                                                   endof3101, fltPrd4386,
                                                   fltPrd4387};
            break;
        }

      case 1:
        {
            CursorTy field_cur3609 = (CursorTy) tmpcur5079;
            CursorTy jump3103 = loc1848 + 1;

            *(TagTyPacked *) loc1849 = 1;

            CursorTy writetag3610 = loc1849 + 1;
            CursorTy pvrtmp5101 = (CursorTy) writetag3610;
            CursorTy pvrtmp5100 = (CursorTy) loc1849;
            CursorTy taildc3104 = (CursorTy) pvrtmp5100;
            CursorTy end_taildc3104 = (CursorTy) pvrtmp5101;
            CursorTy pvrtmp5103 = (CursorTy) end_taildc3104;
            CursorTy pvrtmp5102 = (CursorTy) taildc3104;
            CursorTy fltPrd4388 = (CursorTy) pvrtmp5102;
            CursorTy fltPrd4389 = (CursorTy) pvrtmp5103;

            return (CursorCursorCursorCursorProd) {end_r1851, jump3103,
                                                   fltPrd4388, fltPrd4389};
            break;
        }

      case 2:
        {
            CursorTy field_cur3612 = (CursorTy) tmpcur5079;
            CursorTy tmpcur5104 = *(CursorTy *) field_cur3612;
            CursorTy tmpaftercur5105 = field_cur3612 + 8;
            CursorTy case2188 = (CursorTy) field_cur3612;
            CursorTy x1542 = (CursorTy) tmpcur5104;
            CursorTy end_x1542 = (CursorTy) tmpaftercur5105;
            CursorTy case2189 = (CursorTy) end_x1542;
            CursorTy x1543 = (CursorTy) case2189;
            CursorTy case2190 = (CursorTy) x1542;
            CursorTy x1544 = (CursorTy) case2190;
            CursorTy jump3105 = case2188 + 8;
            CursorCursorCursorCursorProd tmp_struct65 =
                                          _copy_Toplvl(end_r1850, end_r1851, loc2198, x1543);
            CursorTy pvrtmp5106 = tmp_struct65.field0;
            CursorTy pvrtmp5107 = tmp_struct65.field1;
            CursorTy pvrtmp5108 = tmp_struct65.field2;
            CursorTy pvrtmp5109 = tmp_struct65.field3;
            CursorTy fltPrd4390 = (CursorTy) pvrtmp5108;
            CursorTy fltPrd4391 = (CursorTy) pvrtmp5109;
            CursorTy pvrtmp5111 = (CursorTy) fltPrd4391;
            CursorTy pvrtmp5110 = (CursorTy) fltPrd4390;
            CursorTy y1546 = (CursorTy) pvrtmp5110;
            CursorTy fltPrd4392 = (CursorTy) pvrtmp5108;
            CursorTy fltPrd4393 = (CursorTy) pvrtmp5109;
            CursorTy pvrtmp5113 = (CursorTy) fltPrd4393;
            CursorTy pvrtmp5112 = (CursorTy) fltPrd4392;
            CursorTy end_y1546 = (CursorTy) pvrtmp5113;
            CursorTy end_r1851_3379 = (CursorTy) pvrtmp5106;
            CursorTy endof3106 = (CursorTy) pvrtmp5107;
            CursorTy loc2199 = (CursorTy) end_y1546;
            CursorCursorCursorCursorProd tmp_struct66 =
                                          _copy_ListToplvl(end_r1850, end_r1851_3379, loc2199, x1544);
            CursorTy pvrtmp5114 = tmp_struct66.field0;
            CursorTy pvrtmp5115 = tmp_struct66.field1;
            CursorTy pvrtmp5116 = tmp_struct66.field2;
            CursorTy pvrtmp5117 = tmp_struct66.field3;
            CursorTy fltPrd4394 = (CursorTy) pvrtmp5116;
            CursorTy fltPrd4395 = (CursorTy) pvrtmp5117;
            CursorTy pvrtmp5119 = (CursorTy) fltPrd4395;
            CursorTy pvrtmp5118 = (CursorTy) fltPrd4394;
            CursorTy y1547 = (CursorTy) pvrtmp5118;
            CursorTy fltPrd4396 = (CursorTy) pvrtmp5116;
            CursorTy fltPrd4397 = (CursorTy) pvrtmp5117;
            CursorTy pvrtmp5121 = (CursorTy) fltPrd4397;
            CursorTy pvrtmp5120 = (CursorTy) fltPrd4396;
            CursorTy end_y1547 = (CursorTy) pvrtmp5121;
            CursorTy end_r1851_3379_3380 = (CursorTy) pvrtmp5114;
            CursorTy endof3107 = (CursorTy) pvrtmp5115;
            CursorTy y1545 = (CursorTy) end_y1546;

            *(TagTyPacked *) loc1849 = 2;

            CursorTy writetag3616 = loc1849 + 1;

            *(CursorTy *) writetag3616 = y1545;

            CursorTy writecur3617 = writetag3616 + 8;
            CursorTy writecur3618 = (CursorTy) end_y1546;
            CursorTy writecur3619 = (CursorTy) end_y1547;
            CursorTy pvrtmp5123 = (CursorTy) writecur3619;
            CursorTy pvrtmp5122 = (CursorTy) loc1849;
            CursorTy taildc3108 = (CursorTy) pvrtmp5122;
            CursorTy end_taildc3108 = (CursorTy) pvrtmp5123;
            CursorTy pvrtmp5125 = (CursorTy) end_taildc3108;
            CursorTy pvrtmp5124 = (CursorTy) taildc3108;
            CursorTy fltPrd4398 = (CursorTy) pvrtmp5124;
            CursorTy fltPrd4399 = (CursorTy) pvrtmp5125;

            return (CursorCursorCursorCursorProd) {end_r1851_3379_3380,
                                                   endof3107, fltPrd4398,
                                                   fltPrd4399};
            break;
        }

      case 153:
        {
            CursorTy field_cur3621 = (CursorTy) tmpcur5079;
            CursorTy case2204 = (CursorTy) field_cur3621;
            IntTy tmpval5126 = *(IntTy *) case2204;
            CursorTy tmpcur5127 = case2204 + sizeof(IntTy);
            IntTy x1548 = (IntTy) tmpval5126;
            CursorTy end_x1548 = (CursorTy) tmpcur5127;
            CursorTy case2205 = (CursorTy) end_x1548;
            IntTy tmpval5128 = *(IntTy *) case2205;
            CursorTy tmpcur5129 = case2205 + sizeof(IntTy);
            IntTy x1549 = (IntTy) tmpval5128;
            CursorTy end_x1549 = (CursorTy) tmpcur5129;
            CursorTy case2206 = (CursorTy) end_x1549;
            CursorTy x1550 = (CursorTy) case2206;
            CursorTy loc3625 = case2205 + x1549;
            CursorTy case2207 = loc3625 + 8;
            CursorTy x1551 = (CursorTy) case2207;
            CursorTy jump3110 = case2205 + 8;
            CursorTy jump3109 = case2204 + 8;
            CursorCursorCursorCursorProd tmp_struct67 =
                                          _copy_Toplvl(end_r1850, end_r1851, loc2216, x1550);
            CursorTy pvrtmp5130 = tmp_struct67.field0;
            CursorTy pvrtmp5131 = tmp_struct67.field1;
            CursorTy pvrtmp5132 = tmp_struct67.field2;
            CursorTy pvrtmp5133 = tmp_struct67.field3;
            CursorTy fltPrd4400 = (CursorTy) pvrtmp5132;
            CursorTy fltPrd4401 = (CursorTy) pvrtmp5133;
            CursorTy pvrtmp5135 = (CursorTy) fltPrd4401;
            CursorTy pvrtmp5134 = (CursorTy) fltPrd4400;
            CursorTy y1554 = (CursorTy) pvrtmp5134;
            CursorTy fltPrd4402 = (CursorTy) pvrtmp5132;
            CursorTy fltPrd4403 = (CursorTy) pvrtmp5133;
            CursorTy pvrtmp5137 = (CursorTy) fltPrd4403;
            CursorTy pvrtmp5136 = (CursorTy) fltPrd4402;
            CursorTy end_y1554 = (CursorTy) pvrtmp5137;
            CursorTy end_r1851_3381 = (CursorTy) pvrtmp5130;
            CursorTy endof3111 = (CursorTy) pvrtmp5131;
            CursorTy loc2217 = (CursorTy) end_y1554;
            CursorCursorCursorCursorProd tmp_struct68 =
                                          _copy_ListToplvl(end_r1850, end_r1851_3381, loc2217, x1551);
            CursorTy pvrtmp5138 = tmp_struct68.field0;
            CursorTy pvrtmp5139 = tmp_struct68.field1;
            CursorTy pvrtmp5140 = tmp_struct68.field2;
            CursorTy pvrtmp5141 = tmp_struct68.field3;
            CursorTy fltPrd4404 = (CursorTy) pvrtmp5140;
            CursorTy fltPrd4405 = (CursorTy) pvrtmp5141;
            CursorTy pvrtmp5143 = (CursorTy) fltPrd4405;
            CursorTy pvrtmp5142 = (CursorTy) fltPrd4404;
            CursorTy y1555 = (CursorTy) pvrtmp5142;
            CursorTy fltPrd4406 = (CursorTy) pvrtmp5140;
            CursorTy fltPrd4407 = (CursorTy) pvrtmp5141;
            CursorTy pvrtmp5145 = (CursorTy) fltPrd4407;
            CursorTy pvrtmp5144 = (CursorTy) fltPrd4406;
            CursorTy end_y1555 = (CursorTy) pvrtmp5145;
            CursorTy end_r1851_3381_3382 = (CursorTy) pvrtmp5138;
            CursorTy endof3112 = (CursorTy) pvrtmp5139;

            *(TagTyPacked *) loc1849 = 153;

            CursorTy writetag3628 = loc1849 + 1;

            *(IntTy *) writetag3628 = x1548;

            CursorTy writecur3629 = writetag3628 + sizeof(IntTy);

            *(IntTy *) writecur3629 = x1549;

            CursorTy writecur3630 = writecur3629 + sizeof(IntTy);
            CursorTy writecur3631 = (CursorTy) end_y1554;
            CursorTy writecur3632 = (CursorTy) end_y1555;
            CursorTy pvrtmp5147 = (CursorTy) writecur3632;
            CursorTy pvrtmp5146 = (CursorTy) loc1849;
            CursorTy taildc3113 = (CursorTy) pvrtmp5146;
            CursorTy end_taildc3113 = (CursorTy) pvrtmp5147;
            CursorTy pvrtmp5149 = (CursorTy) end_taildc3113;
            CursorTy pvrtmp5148 = (CursorTy) taildc3113;
            CursorTy fltPrd4408 = (CursorTy) pvrtmp5148;
            CursorTy fltPrd4409 = (CursorTy) pvrtmp5149;

            return (CursorCursorCursorCursorProd) {end_r1851_3381_3382,
                                                   endof3112, fltPrd4408,
                                                   fltPrd4409};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6589 = *(CursorTy *) tmpcur5079;
            CursorTy tmpaftercur6590 = tmpcur5079 + 8;
            TagTyPacked tagtmp6591 = *(TagTyPacked *) tmpcur6589;
            CursorTy tailtmp6592 = tmpcur6589 + 1;

            tmpval5078 = tagtmp6591;
            tmpcur5079 = tailtmp6592;
            goto switch5150;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6589 = *(CursorTy *) tmpcur5079;
            CursorTy tmpaftercur6590 = tmpcur5079 + 8;
            TagTyPacked tagtmp6591 = *(TagTyPacked *) tmpcur6589;
            CursorTy tailtmp6592 = tmpcur6589 + 1;

            tmpval5078 = tagtmp6591;
            tmpcur5079 = tailtmp6592;
            goto switch5150;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5078");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r1856,
                                           CursorTy end_r1857, CursorTy loc1855,
                                           CursorTy arg1575)
{
    CursorTy loc1854 = (CursorTy) arg1575;

    if (loc1855 + 18 > end_r1857) {
        ChunkTy new_chunk80 = alloc_chunk(end_r1857);
        CursorTy chunk_start81 = new_chunk80.start_ptr;
        CursorTy chunk_end82 = new_chunk80.end_ptr;

        end_r1857 = chunk_end82;
        *(TagTyPacked *) loc1855 = 255;

        CursorTy redir = loc1855 + 1;

        *(CursorTy *) redir = chunk_start81;
        loc1855 = chunk_start81;
    }

    TagTyPacked tmpval5172 = *(TagTyPacked *) arg1575;
    CursorTy tmpcur5173 = arg1575 + 1;


  switch5206:
    ;
    switch (tmpval5172) {

      case 0:
        {
            CursorTy field_cur3649 = (CursorTy) tmpcur5173;
            CursorTy case2249 = (CursorTy) field_cur3649;
            CursorTy x1576 = (CursorTy) case2249;
            CursorTy loc2253 = loc1855 + 1;
            CursorCursorCursorCursorProd tmp_struct78 =
                                          _copy_ListSym(end_r1856, end_r1857, loc2253, x1576);
            CursorTy pvrtmp5174 = tmp_struct78.field0;
            CursorTy pvrtmp5175 = tmp_struct78.field1;
            CursorTy pvrtmp5176 = tmp_struct78.field2;
            CursorTy pvrtmp5177 = tmp_struct78.field3;
            CursorTy fltPrd4410 = (CursorTy) pvrtmp5176;
            CursorTy fltPrd4411 = (CursorTy) pvrtmp5177;
            CursorTy pvrtmp5179 = (CursorTy) fltPrd4411;
            CursorTy pvrtmp5178 = (CursorTy) fltPrd4410;
            CursorTy y1577 = (CursorTy) pvrtmp5178;
            CursorTy fltPrd4412 = (CursorTy) pvrtmp5176;
            CursorTy fltPrd4413 = (CursorTy) pvrtmp5177;
            CursorTy pvrtmp5181 = (CursorTy) fltPrd4413;
            CursorTy pvrtmp5180 = (CursorTy) fltPrd4412;
            CursorTy end_y1577 = (CursorTy) pvrtmp5181;
            CursorTy end_r1857_3383 = (CursorTy) pvrtmp5174;
            CursorTy endof3128 = (CursorTy) pvrtmp5175;

            *(TagTyPacked *) loc1855 = 0;

            CursorTy writetag3651 = loc1855 + 1;
            CursorTy writecur3652 = (CursorTy) end_y1577;
            CursorTy pvrtmp5183 = (CursorTy) writecur3652;
            CursorTy pvrtmp5182 = (CursorTy) loc1855;
            CursorTy taildc3129 = (CursorTy) pvrtmp5182;
            CursorTy end_taildc3129 = (CursorTy) pvrtmp5183;
            CursorTy pvrtmp5185 = (CursorTy) end_taildc3129;
            CursorTy pvrtmp5184 = (CursorTy) taildc3129;
            CursorTy fltPrd4414 = (CursorTy) pvrtmp5184;
            CursorTy fltPrd4415 = (CursorTy) pvrtmp5185;

            return (CursorCursorCursorCursorProd) {end_r1857_3383, endof3128,
                                                   fltPrd4414, fltPrd4415};
            break;
        }

      case 1:
        {
            CursorTy field_cur3654 = (CursorTy) tmpcur5173;
            CursorTy case2255 = (CursorTy) field_cur3654;
            CursorTy x1578 = (CursorTy) case2255;
            CursorTy loc2260 = loc1855 + 1;
            CursorCursorCursorCursorProd tmp_struct79 =
                                          _copy_ListSym(end_r1856, end_r1857, loc2260, x1578);
            CursorTy pvrtmp5186 = tmp_struct79.field0;
            CursorTy pvrtmp5187 = tmp_struct79.field1;
            CursorTy pvrtmp5188 = tmp_struct79.field2;
            CursorTy pvrtmp5189 = tmp_struct79.field3;
            CursorTy fltPrd4416 = (CursorTy) pvrtmp5188;
            CursorTy fltPrd4417 = (CursorTy) pvrtmp5189;
            CursorTy pvrtmp5191 = (CursorTy) fltPrd4417;
            CursorTy pvrtmp5190 = (CursorTy) fltPrd4416;
            CursorTy y1580 = (CursorTy) pvrtmp5190;
            CursorTy fltPrd4418 = (CursorTy) pvrtmp5188;
            CursorTy fltPrd4419 = (CursorTy) pvrtmp5189;
            CursorTy pvrtmp5193 = (CursorTy) fltPrd4419;
            CursorTy pvrtmp5192 = (CursorTy) fltPrd4418;
            CursorTy end_y1580 = (CursorTy) pvrtmp5193;
            CursorTy end_r1857_3384 = (CursorTy) pvrtmp5186;
            CursorTy endof3131 = (CursorTy) pvrtmp5187;
            CursorTy case2256 = (CursorTy) endof3131;
            CursorTy jump3130 = case2256 + 8;
            SymTy tmpval5194 = *(SymTy *) case2256;
            CursorTy tmpcur5195 = case2256 + sizeof(SymTy);
            SymTy x1579 = (SymTy) tmpval5194;
            CursorTy end_x1579 = (CursorTy) tmpcur5195;

            *(TagTyPacked *) loc1855 = 1;

            CursorTy writetag3657 = loc1855 + 1;
            CursorTy writecur3658 = (CursorTy) end_y1580;

            *(SymTy *) writecur3658 = x1579;

            CursorTy writecur3659 = writecur3658 + sizeof(SymTy);
            CursorTy pvrtmp5197 = (CursorTy) writecur3659;
            CursorTy pvrtmp5196 = (CursorTy) loc1855;
            CursorTy taildc3132 = (CursorTy) pvrtmp5196;
            CursorTy end_taildc3132 = (CursorTy) pvrtmp5197;
            CursorTy pvrtmp5199 = (CursorTy) end_taildc3132;
            CursorTy pvrtmp5198 = (CursorTy) taildc3132;
            CursorTy fltPrd4420 = (CursorTy) pvrtmp5198;
            CursorTy fltPrd4421 = (CursorTy) pvrtmp5199;

            return (CursorCursorCursorCursorProd) {end_r1857_3384, jump3130,
                                                   fltPrd4420, fltPrd4421};
            break;
        }

      case 2:
        {
            CursorTy field_cur3661 = (CursorTy) tmpcur5173;
            CursorTy case2265 = (CursorTy) field_cur3661;
            SymTy tmpval5200 = *(SymTy *) case2265;
            CursorTy tmpcur5201 = case2265 + sizeof(SymTy);
            SymTy x1582 = (SymTy) tmpval5200;
            CursorTy end_x1582 = (CursorTy) tmpcur5201;
            CursorTy jump3133 = case2265 + 8;

            *(TagTyPacked *) loc1855 = 2;

            CursorTy writetag3663 = loc1855 + 1;

            *(SymTy *) writetag3663 = x1582;

            CursorTy writecur3664 = writetag3663 + sizeof(SymTy);
            CursorTy pvrtmp5203 = (CursorTy) writecur3664;
            CursorTy pvrtmp5202 = (CursorTy) loc1855;
            CursorTy taildc3134 = (CursorTy) pvrtmp5202;
            CursorTy end_taildc3134 = (CursorTy) pvrtmp5203;
            CursorTy pvrtmp5205 = (CursorTy) end_taildc3134;
            CursorTy pvrtmp5204 = (CursorTy) taildc3134;
            CursorTy fltPrd4422 = (CursorTy) pvrtmp5204;
            CursorTy fltPrd4423 = (CursorTy) pvrtmp5205;

            return (CursorCursorCursorCursorProd) {end_r1857, jump3133,
                                                   fltPrd4422, fltPrd4423};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6597 = *(CursorTy *) tmpcur5173;
            CursorTy tmpaftercur6598 = tmpcur5173 + 8;
            TagTyPacked tagtmp6599 = *(TagTyPacked *) tmpcur6597;
            CursorTy tailtmp6600 = tmpcur6597 + 1;

            tmpval5172 = tagtmp6599;
            tmpcur5173 = tailtmp6600;
            goto switch5206;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6597 = *(CursorTy *) tmpcur5173;
            CursorTy tmpaftercur6598 = tmpcur5173 + 8;
            TagTyPacked tagtmp6599 = *(TagTyPacked *) tmpcur6597;
            CursorTy tailtmp6600 = tmpcur6597 + 1;

            tmpval5172 = tagtmp6599;
            tmpcur5173 = tailtmp6600;
            goto switch5206;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5172");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r1862, CursorTy end_r1863,
                                         CursorTy loc1861, CursorTy arg1593)
{
    CursorTy loc1860 = (CursorTy) arg1593;

    if (loc1861 + 18 > end_r1863) {
        ChunkTy new_chunk85 = alloc_chunk(end_r1863);
        CursorTy chunk_start86 = new_chunk85.start_ptr;
        CursorTy chunk_end87 = new_chunk85.end_ptr;

        end_r1863 = chunk_end87;
        *(TagTyPacked *) loc1861 = 255;

        CursorTy redir = loc1861 + 1;

        *(CursorTy *) redir = chunk_start86;
        loc1861 = chunk_start86;
    }

    TagTyPacked tmpval5218 = *(TagTyPacked *) arg1593;
    CursorTy tmpcur5219 = arg1593 + 1;


  switch5226:
    ;
    switch (tmpval5218) {

      case 0:
        {
            CursorTy field_cur3673 = (CursorTy) tmpcur5219;
            CursorTy case2281 = (CursorTy) field_cur3673;
            IntTy tmpval5220 = *(IntTy *) case2281;
            CursorTy tmpcur5221 = case2281 + sizeof(IntTy);
            IntTy x1594 = (IntTy) tmpval5220;
            CursorTy end_x1594 = (CursorTy) tmpcur5221;
            CursorTy jump3142 = case2281 + 8;

            *(TagTyPacked *) loc1861 = 0;

            CursorTy writetag3675 = loc1861 + 1;

            *(IntTy *) writetag3675 = x1594;

            CursorTy writecur3676 = writetag3675 + sizeof(IntTy);
            CursorTy pvrtmp5223 = (CursorTy) writecur3676;
            CursorTy pvrtmp5222 = (CursorTy) loc1861;
            CursorTy taildc3143 = (CursorTy) pvrtmp5222;
            CursorTy end_taildc3143 = (CursorTy) pvrtmp5223;
            CursorTy pvrtmp5225 = (CursorTy) end_taildc3143;
            CursorTy pvrtmp5224 = (CursorTy) taildc3143;
            CursorTy fltPrd4424 = (CursorTy) pvrtmp5224;
            CursorTy fltPrd4425 = (CursorTy) pvrtmp5225;

            return (CursorCursorCursorCursorProd) {end_r1863, jump3142,
                                                   fltPrd4424, fltPrd4425};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6605 = *(CursorTy *) tmpcur5219;
            CursorTy tmpaftercur6606 = tmpcur5219 + 8;
            TagTyPacked tagtmp6607 = *(TagTyPacked *) tmpcur6605;
            CursorTy tailtmp6608 = tmpcur6605 + 1;

            tmpval5218 = tagtmp6607;
            tmpcur5219 = tailtmp6608;
            goto switch5226;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6605 = *(CursorTy *) tmpcur5219;
            CursorTy tmpaftercur6606 = tmpcur5219 + 8;
            TagTyPacked tagtmp6607 = *(TagTyPacked *) tmpcur6605;
            CursorTy tailtmp6608 = tmpcur6605 + 1;

            tmpval5218 = tagtmp6607;
            tmpcur5219 = tailtmp6608;
            goto switch5226;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5218");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r1868,
                                              CursorTy end_r1869,
                                              CursorTy loc1867,
                                              CursorTy arg1599)
{
    CursorTy loc1866 = (CursorTy) arg1599;

    if (loc1867 + 18 > end_r1869) {
        ChunkTy new_chunk91 = alloc_chunk(end_r1869);
        CursorTy chunk_start92 = new_chunk91.start_ptr;
        CursorTy chunk_end93 = new_chunk91.end_ptr;

        end_r1869 = chunk_end93;
        *(TagTyPacked *) loc1867 = 255;

        CursorTy redir = loc1867 + 1;

        *(CursorTy *) redir = chunk_start92;
        loc1867 = chunk_start92;
    }

    TagTyPacked tmpval5232 = *(TagTyPacked *) arg1599;
    CursorTy tmpcur5233 = arg1599 + 1;


  switch5266:
    ;
    switch (tmpval5232) {

      case 0:
        {
            CursorTy field_cur3680 = (CursorTy) tmpcur5233;
            CursorTy case2290 = (CursorTy) field_cur3680;
            CursorTy x1600 = (CursorTy) case2290;
            CursorTy loc2302 = loc1867 + 1;
            CursorCursorCursorCursorProd tmp_struct88 =
                                          _copy_Formals(end_r1868, end_r1869, loc2302, x1600);
            CursorTy pvrtmp5234 = tmp_struct88.field0;
            CursorTy pvrtmp5235 = tmp_struct88.field1;
            CursorTy pvrtmp5236 = tmp_struct88.field2;
            CursorTy pvrtmp5237 = tmp_struct88.field3;
            CursorTy fltPrd4426 = (CursorTy) pvrtmp5236;
            CursorTy fltPrd4427 = (CursorTy) pvrtmp5237;
            CursorTy pvrtmp5239 = (CursorTy) fltPrd4427;
            CursorTy pvrtmp5238 = (CursorTy) fltPrd4426;
            CursorTy y1603 = (CursorTy) pvrtmp5238;
            CursorTy fltPrd4428 = (CursorTy) pvrtmp5236;
            CursorTy fltPrd4429 = (CursorTy) pvrtmp5237;
            CursorTy pvrtmp5241 = (CursorTy) fltPrd4429;
            CursorTy pvrtmp5240 = (CursorTy) fltPrd4428;
            CursorTy end_y1603 = (CursorTy) pvrtmp5241;
            CursorTy end_r1869_3385 = (CursorTy) pvrtmp5234;
            CursorTy endof3146 = (CursorTy) pvrtmp5235;
            CursorTy case2291 = (CursorTy) endof3146;
            CursorTy x1601 = (CursorTy) case2291;
            CursorTy loc2303 = (CursorTy) end_y1603;
            CursorCursorCursorCursorProd tmp_struct89 =
                                          _copy_ListExpr(end_r1868, end_r1869_3385, loc2303, x1601);
            CursorTy pvrtmp5242 = tmp_struct89.field0;
            CursorTy pvrtmp5243 = tmp_struct89.field1;
            CursorTy pvrtmp5244 = tmp_struct89.field2;
            CursorTy pvrtmp5245 = tmp_struct89.field3;
            CursorTy fltPrd4430 = (CursorTy) pvrtmp5244;
            CursorTy fltPrd4431 = (CursorTy) pvrtmp5245;
            CursorTy pvrtmp5247 = (CursorTy) fltPrd4431;
            CursorTy pvrtmp5246 = (CursorTy) fltPrd4430;
            CursorTy y1604 = (CursorTy) pvrtmp5246;
            CursorTy fltPrd4432 = (CursorTy) pvrtmp5244;
            CursorTy fltPrd4433 = (CursorTy) pvrtmp5245;
            CursorTy pvrtmp5249 = (CursorTy) fltPrd4433;
            CursorTy pvrtmp5248 = (CursorTy) fltPrd4432;
            CursorTy end_y1604 = (CursorTy) pvrtmp5249;
            CursorTy end_r1869_3385_3386 = (CursorTy) pvrtmp5242;
            CursorTy endof3147 = (CursorTy) pvrtmp5243;
            CursorTy case2292 = (CursorTy) endof3147;
            CursorTy x1602 = (CursorTy) case2292;
            CursorTy loc2304 = (CursorTy) end_y1604;
            CursorCursorCursorCursorProd tmp_struct90 =
                                          _copy_LAMBDACASE(end_r1868, end_r1869_3385_3386, loc2304, x1602);
            CursorTy pvrtmp5250 = tmp_struct90.field0;
            CursorTy pvrtmp5251 = tmp_struct90.field1;
            CursorTy pvrtmp5252 = tmp_struct90.field2;
            CursorTy pvrtmp5253 = tmp_struct90.field3;
            CursorTy fltPrd4434 = (CursorTy) pvrtmp5252;
            CursorTy fltPrd4435 = (CursorTy) pvrtmp5253;
            CursorTy pvrtmp5255 = (CursorTy) fltPrd4435;
            CursorTy pvrtmp5254 = (CursorTy) fltPrd4434;
            CursorTy y1605 = (CursorTy) pvrtmp5254;
            CursorTy fltPrd4436 = (CursorTy) pvrtmp5252;
            CursorTy fltPrd4437 = (CursorTy) pvrtmp5253;
            CursorTy pvrtmp5257 = (CursorTy) fltPrd4437;
            CursorTy pvrtmp5256 = (CursorTy) fltPrd4436;
            CursorTy end_y1605 = (CursorTy) pvrtmp5257;
            CursorTy end_r1869_3385_3386_3387 = (CursorTy) pvrtmp5250;
            CursorTy endof3148 = (CursorTy) pvrtmp5251;

            *(TagTyPacked *) loc1867 = 0;

            CursorTy writetag3684 = loc1867 + 1;
            CursorTy writecur3685 = (CursorTy) end_y1603;
            CursorTy writecur3686 = (CursorTy) end_y1604;
            CursorTy writecur3687 = (CursorTy) end_y1605;
            CursorTy pvrtmp5259 = (CursorTy) writecur3687;
            CursorTy pvrtmp5258 = (CursorTy) loc1867;
            CursorTy taildc3149 = (CursorTy) pvrtmp5258;
            CursorTy end_taildc3149 = (CursorTy) pvrtmp5259;
            CursorTy pvrtmp5261 = (CursorTy) end_taildc3149;
            CursorTy pvrtmp5260 = (CursorTy) taildc3149;
            CursorTy fltPrd4438 = (CursorTy) pvrtmp5260;
            CursorTy fltPrd4439 = (CursorTy) pvrtmp5261;

            return (CursorCursorCursorCursorProd) {end_r1869_3385_3386_3387,
                                                   endof3148, fltPrd4438,
                                                   fltPrd4439};
            break;
        }

      case 1:
        {
            CursorTy field_cur3689 = (CursorTy) tmpcur5233;
            CursorTy jump3150 = loc1866 + 1;

            *(TagTyPacked *) loc1867 = 1;

            CursorTy writetag3690 = loc1867 + 1;
            CursorTy pvrtmp5263 = (CursorTy) writetag3690;
            CursorTy pvrtmp5262 = (CursorTy) loc1867;
            CursorTy taildc3151 = (CursorTy) pvrtmp5262;
            CursorTy end_taildc3151 = (CursorTy) pvrtmp5263;
            CursorTy pvrtmp5265 = (CursorTy) end_taildc3151;
            CursorTy pvrtmp5264 = (CursorTy) taildc3151;
            CursorTy fltPrd4440 = (CursorTy) pvrtmp5264;
            CursorTy fltPrd4441 = (CursorTy) pvrtmp5265;

            return (CursorCursorCursorCursorProd) {end_r1869, jump3150,
                                                   fltPrd4440, fltPrd4441};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6613 = *(CursorTy *) tmpcur5233;
            CursorTy tmpaftercur6614 = tmpcur5233 + 8;
            TagTyPacked tagtmp6615 = *(TagTyPacked *) tmpcur6613;
            CursorTy tailtmp6616 = tmpcur6613 + 1;

            tmpval5232 = tagtmp6615;
            tmpcur5233 = tailtmp6616;
            goto switch5266;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6613 = *(CursorTy *) tmpcur5233;
            CursorTy tmpaftercur6614 = tmpcur5233 + 8;
            TagTyPacked tagtmp6615 = *(TagTyPacked *) tmpcur6613;
            CursorTy tailtmp6616 = tmpcur6613 + 1;

            tmpval5232 = tagtmp6615;
            tmpcur5233 = tailtmp6616;
            goto switch5266;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5232");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r1874,
                                          CursorTy end_r1875, CursorTy loc1873,
                                          CursorTy arg1613)
{
    CursorTy loc1872 = (CursorTy) arg1613;

    if (loc1873 + 18 > end_r1875) {
        ChunkTy new_chunk100 = alloc_chunk(end_r1875);
        CursorTy chunk_start101 = new_chunk100.start_ptr;
        CursorTy chunk_end102 = new_chunk100.end_ptr;

        end_r1875 = chunk_end102;
        *(TagTyPacked *) loc1873 = 255;

        CursorTy redir = loc1873 + 1;

        *(CursorTy *) redir = chunk_start101;
        loc1873 = chunk_start101;
    }

    TagTyPacked tmpval5276 = *(TagTyPacked *) arg1613;
    CursorTy tmpcur5277 = arg1613 + 1;


  switch5310:
    ;
    switch (tmpval5276) {

      case 0:
        {
            CursorTy field_cur3697 = (CursorTy) tmpcur5277;
            CursorTy case2322 = (CursorTy) field_cur3697;
            CursorTy x1614 = (CursorTy) case2322;
            CursorTy loc2334 = loc1873 + 1;
            CursorCursorCursorCursorProd tmp_struct97 =
                                          _copy_ListSym(end_r1874, end_r1875, loc2334, x1614);
            CursorTy pvrtmp5278 = tmp_struct97.field0;
            CursorTy pvrtmp5279 = tmp_struct97.field1;
            CursorTy pvrtmp5280 = tmp_struct97.field2;
            CursorTy pvrtmp5281 = tmp_struct97.field3;
            CursorTy fltPrd4442 = (CursorTy) pvrtmp5280;
            CursorTy fltPrd4443 = (CursorTy) pvrtmp5281;
            CursorTy pvrtmp5283 = (CursorTy) fltPrd4443;
            CursorTy pvrtmp5282 = (CursorTy) fltPrd4442;
            CursorTy y1617 = (CursorTy) pvrtmp5282;
            CursorTy fltPrd4444 = (CursorTy) pvrtmp5280;
            CursorTy fltPrd4445 = (CursorTy) pvrtmp5281;
            CursorTy pvrtmp5285 = (CursorTy) fltPrd4445;
            CursorTy pvrtmp5284 = (CursorTy) fltPrd4444;
            CursorTy end_y1617 = (CursorTy) pvrtmp5285;
            CursorTy end_r1875_3388 = (CursorTy) pvrtmp5278;
            CursorTy endof3158 = (CursorTy) pvrtmp5279;
            CursorTy case2323 = (CursorTy) endof3158;
            CursorTy x1615 = (CursorTy) case2323;
            CursorTy loc2335 = (CursorTy) end_y1617;
            CursorCursorCursorCursorProd tmp_struct98 =
                                          _copy_Expr(end_r1874, end_r1875_3388, loc2335, x1615);
            CursorTy pvrtmp5286 = tmp_struct98.field0;
            CursorTy pvrtmp5287 = tmp_struct98.field1;
            CursorTy pvrtmp5288 = tmp_struct98.field2;
            CursorTy pvrtmp5289 = tmp_struct98.field3;
            CursorTy fltPrd4446 = (CursorTy) pvrtmp5288;
            CursorTy fltPrd4447 = (CursorTy) pvrtmp5289;
            CursorTy pvrtmp5291 = (CursorTy) fltPrd4447;
            CursorTy pvrtmp5290 = (CursorTy) fltPrd4446;
            CursorTy y1618 = (CursorTy) pvrtmp5290;
            CursorTy fltPrd4448 = (CursorTy) pvrtmp5288;
            CursorTy fltPrd4449 = (CursorTy) pvrtmp5289;
            CursorTy pvrtmp5293 = (CursorTy) fltPrd4449;
            CursorTy pvrtmp5292 = (CursorTy) fltPrd4448;
            CursorTy end_y1618 = (CursorTy) pvrtmp5293;
            CursorTy end_r1875_3388_3389 = (CursorTy) pvrtmp5286;
            CursorTy endof3159 = (CursorTy) pvrtmp5287;
            CursorTy case2324 = (CursorTy) endof3159;
            CursorTy x1616 = (CursorTy) case2324;
            CursorTy loc2336 = (CursorTy) end_y1618;
            CursorCursorCursorCursorProd tmp_struct99 =
                                          _copy_LVBIND(end_r1874, end_r1875_3388_3389, loc2336, x1616);
            CursorTy pvrtmp5294 = tmp_struct99.field0;
            CursorTy pvrtmp5295 = tmp_struct99.field1;
            CursorTy pvrtmp5296 = tmp_struct99.field2;
            CursorTy pvrtmp5297 = tmp_struct99.field3;
            CursorTy fltPrd4450 = (CursorTy) pvrtmp5296;
            CursorTy fltPrd4451 = (CursorTy) pvrtmp5297;
            CursorTy pvrtmp5299 = (CursorTy) fltPrd4451;
            CursorTy pvrtmp5298 = (CursorTy) fltPrd4450;
            CursorTy y1619 = (CursorTy) pvrtmp5298;
            CursorTy fltPrd4452 = (CursorTy) pvrtmp5296;
            CursorTy fltPrd4453 = (CursorTy) pvrtmp5297;
            CursorTy pvrtmp5301 = (CursorTy) fltPrd4453;
            CursorTy pvrtmp5300 = (CursorTy) fltPrd4452;
            CursorTy end_y1619 = (CursorTy) pvrtmp5301;
            CursorTy end_r1875_3388_3389_3390 = (CursorTy) pvrtmp5294;
            CursorTy endof3160 = (CursorTy) pvrtmp5295;

            *(TagTyPacked *) loc1873 = 0;

            CursorTy writetag3701 = loc1873 + 1;
            CursorTy writecur3702 = (CursorTy) end_y1617;
            CursorTy writecur3703 = (CursorTy) end_y1618;
            CursorTy writecur3704 = (CursorTy) end_y1619;
            CursorTy pvrtmp5303 = (CursorTy) writecur3704;
            CursorTy pvrtmp5302 = (CursorTy) loc1873;
            CursorTy taildc3161 = (CursorTy) pvrtmp5302;
            CursorTy end_taildc3161 = (CursorTy) pvrtmp5303;
            CursorTy pvrtmp5305 = (CursorTy) end_taildc3161;
            CursorTy pvrtmp5304 = (CursorTy) taildc3161;
            CursorTy fltPrd4454 = (CursorTy) pvrtmp5304;
            CursorTy fltPrd4455 = (CursorTy) pvrtmp5305;

            return (CursorCursorCursorCursorProd) {end_r1875_3388_3389_3390,
                                                   endof3160, fltPrd4454,
                                                   fltPrd4455};
            break;
        }

      case 1:
        {
            CursorTy field_cur3706 = (CursorTy) tmpcur5277;
            CursorTy jump3162 = loc1872 + 1;

            *(TagTyPacked *) loc1873 = 1;

            CursorTy writetag3707 = loc1873 + 1;
            CursorTy pvrtmp5307 = (CursorTy) writetag3707;
            CursorTy pvrtmp5306 = (CursorTy) loc1873;
            CursorTy taildc3163 = (CursorTy) pvrtmp5306;
            CursorTy end_taildc3163 = (CursorTy) pvrtmp5307;
            CursorTy pvrtmp5309 = (CursorTy) end_taildc3163;
            CursorTy pvrtmp5308 = (CursorTy) taildc3163;
            CursorTy fltPrd4456 = (CursorTy) pvrtmp5308;
            CursorTy fltPrd4457 = (CursorTy) pvrtmp5309;

            return (CursorCursorCursorCursorProd) {end_r1875, jump3162,
                                                   fltPrd4456, fltPrd4457};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6621 = *(CursorTy *) tmpcur5277;
            CursorTy tmpaftercur6622 = tmpcur5277 + 8;
            TagTyPacked tagtmp6623 = *(TagTyPacked *) tmpcur6621;
            CursorTy tailtmp6624 = tmpcur6621 + 1;

            tmpval5276 = tagtmp6623;
            tmpcur5277 = tailtmp6624;
            goto switch5310;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6621 = *(CursorTy *) tmpcur5277;
            CursorTy tmpaftercur6622 = tmpcur5277 + 8;
            TagTyPacked tagtmp6623 = *(TagTyPacked *) tmpcur6621;
            CursorTy tailtmp6624 = tmpcur6621 + 1;

            tmpval5276 = tagtmp6623;
            tmpcur5277 = tailtmp6624;
            goto switch5310;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5276");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r1880, CursorTy end_r1881,
                                        CursorTy loc1879, CursorTy arg1627)
{
    CursorTy loc1878 = (CursorTy) arg1627;

    if (loc1879 + 18 > end_r1881) {
        ChunkTy new_chunk128 = alloc_chunk(end_r1881);
        CursorTy chunk_start129 = new_chunk128.start_ptr;
        CursorTy chunk_end130 = new_chunk128.end_ptr;

        end_r1881 = chunk_end130;
        *(TagTyPacked *) loc1879 = 255;

        CursorTy redir = loc1879 + 1;

        *(CursorTy *) redir = chunk_start129;
        loc1879 = chunk_start129;
    }

    CursorTy loc2441 = loc1879 + 1;
    CursorTy loc2442 = loc2441 + 8;
    TagTyPacked tmpval5320 = *(TagTyPacked *) arg1627;
    CursorTy tmpcur5321 = arg1627 + 1;


  switch5580:
    ;
    switch (tmpval5320) {

      case 0:
        {
            CursorTy field_cur3714 = (CursorTy) tmpcur5321;
            CursorTy case2354 = (CursorTy) field_cur3714;
            SymTy tmpval5322 = *(SymTy *) case2354;
            CursorTy tmpcur5323 = case2354 + sizeof(SymTy);
            SymTy x1628 = (SymTy) tmpval5322;
            CursorTy end_x1628 = (CursorTy) tmpcur5323;
            CursorTy jump3170 = case2354 + 8;

            *(TagTyPacked *) loc1879 = 0;

            CursorTy writetag3716 = loc1879 + 1;

            *(SymTy *) writetag3716 = x1628;

            CursorTy writecur3717 = writetag3716 + sizeof(SymTy);
            CursorTy pvrtmp5325 = (CursorTy) writecur3717;
            CursorTy pvrtmp5324 = (CursorTy) loc1879;
            CursorTy taildc3171 = (CursorTy) pvrtmp5324;
            CursorTy end_taildc3171 = (CursorTy) pvrtmp5325;
            CursorTy pvrtmp5327 = (CursorTy) end_taildc3171;
            CursorTy pvrtmp5326 = (CursorTy) taildc3171;
            CursorTy fltPrd4458 = (CursorTy) pvrtmp5326;
            CursorTy fltPrd4459 = (CursorTy) pvrtmp5327;

            return (CursorCursorCursorCursorProd) {end_r1881, jump3170,
                                                   fltPrd4458, fltPrd4459};
            break;
        }

      case 1:
        {
            CursorTy field_cur3719 = (CursorTy) tmpcur5321;
            CursorTy case2358 = (CursorTy) field_cur3719;
            CursorTy x1630 = (CursorTy) case2358;
            CursorTy loc2366 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct106 =
                                          _copy_Formals(end_r1880, end_r1881, loc2366, x1630);
            CursorTy pvrtmp5328 = tmp_struct106.field0;
            CursorTy pvrtmp5329 = tmp_struct106.field1;
            CursorTy pvrtmp5330 = tmp_struct106.field2;
            CursorTy pvrtmp5331 = tmp_struct106.field3;
            CursorTy fltPrd4460 = (CursorTy) pvrtmp5330;
            CursorTy fltPrd4461 = (CursorTy) pvrtmp5331;
            CursorTy pvrtmp5333 = (CursorTy) fltPrd4461;
            CursorTy pvrtmp5332 = (CursorTy) fltPrd4460;
            CursorTy y1632 = (CursorTy) pvrtmp5332;
            CursorTy fltPrd4462 = (CursorTy) pvrtmp5330;
            CursorTy fltPrd4463 = (CursorTy) pvrtmp5331;
            CursorTy pvrtmp5335 = (CursorTy) fltPrd4463;
            CursorTy pvrtmp5334 = (CursorTy) fltPrd4462;
            CursorTy end_y1632 = (CursorTy) pvrtmp5335;
            CursorTy end_r1881_3391 = (CursorTy) pvrtmp5328;
            CursorTy endof3172 = (CursorTy) pvrtmp5329;
            CursorTy case2359 = (CursorTy) endof3172;
            CursorTy x1631 = (CursorTy) case2359;
            CursorTy loc2367 = (CursorTy) end_y1632;
            CursorCursorCursorCursorProd tmp_struct107 =
                                          _copy_ListExpr(end_r1880, end_r1881_3391, loc2367, x1631);
            CursorTy pvrtmp5336 = tmp_struct107.field0;
            CursorTy pvrtmp5337 = tmp_struct107.field1;
            CursorTy pvrtmp5338 = tmp_struct107.field2;
            CursorTy pvrtmp5339 = tmp_struct107.field3;
            CursorTy fltPrd4464 = (CursorTy) pvrtmp5338;
            CursorTy fltPrd4465 = (CursorTy) pvrtmp5339;
            CursorTy pvrtmp5341 = (CursorTy) fltPrd4465;
            CursorTy pvrtmp5340 = (CursorTy) fltPrd4464;
            CursorTy y1633 = (CursorTy) pvrtmp5340;
            CursorTy fltPrd4466 = (CursorTy) pvrtmp5338;
            CursorTy fltPrd4467 = (CursorTy) pvrtmp5339;
            CursorTy pvrtmp5343 = (CursorTy) fltPrd4467;
            CursorTy pvrtmp5342 = (CursorTy) fltPrd4466;
            CursorTy end_y1633 = (CursorTy) pvrtmp5343;
            CursorTy end_r1881_3391_3392 = (CursorTy) pvrtmp5336;
            CursorTy endof3173 = (CursorTy) pvrtmp5337;

            *(TagTyPacked *) loc1879 = 1;

            CursorTy writetag3722 = loc1879 + 1;
            CursorTy writecur3723 = (CursorTy) end_y1632;
            CursorTy writecur3724 = (CursorTy) end_y1633;
            CursorTy pvrtmp5345 = (CursorTy) writecur3724;
            CursorTy pvrtmp5344 = (CursorTy) loc1879;
            CursorTy taildc3174 = (CursorTy) pvrtmp5344;
            CursorTy end_taildc3174 = (CursorTy) pvrtmp5345;
            CursorTy pvrtmp5347 = (CursorTy) end_taildc3174;
            CursorTy pvrtmp5346 = (CursorTy) taildc3174;
            CursorTy fltPrd4468 = (CursorTy) pvrtmp5346;
            CursorTy fltPrd4469 = (CursorTy) pvrtmp5347;

            return (CursorCursorCursorCursorProd) {end_r1881_3391_3392,
                                                   endof3173, fltPrd4468,
                                                   fltPrd4469};
            break;
        }

      case 2:
        {
            CursorTy field_cur3726 = (CursorTy) tmpcur5321;
            CursorTy case2370 = (CursorTy) field_cur3726;
            CursorTy x1634 = (CursorTy) case2370;
            CursorTy loc2374 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct108 =
                                          _copy_LAMBDACASE(end_r1880, end_r1881, loc2374, x1634);
            CursorTy pvrtmp5348 = tmp_struct108.field0;
            CursorTy pvrtmp5349 = tmp_struct108.field1;
            CursorTy pvrtmp5350 = tmp_struct108.field2;
            CursorTy pvrtmp5351 = tmp_struct108.field3;
            CursorTy fltPrd4470 = (CursorTy) pvrtmp5350;
            CursorTy fltPrd4471 = (CursorTy) pvrtmp5351;
            CursorTy pvrtmp5353 = (CursorTy) fltPrd4471;
            CursorTy pvrtmp5352 = (CursorTy) fltPrd4470;
            CursorTy y1635 = (CursorTy) pvrtmp5352;
            CursorTy fltPrd4472 = (CursorTy) pvrtmp5350;
            CursorTy fltPrd4473 = (CursorTy) pvrtmp5351;
            CursorTy pvrtmp5355 = (CursorTy) fltPrd4473;
            CursorTy pvrtmp5354 = (CursorTy) fltPrd4472;
            CursorTy end_y1635 = (CursorTy) pvrtmp5355;
            CursorTy end_r1881_3393 = (CursorTy) pvrtmp5348;
            CursorTy endof3175 = (CursorTy) pvrtmp5349;

            *(TagTyPacked *) loc1879 = 2;

            CursorTy writetag3728 = loc1879 + 1;
            CursorTy writecur3729 = (CursorTy) end_y1635;
            CursorTy pvrtmp5357 = (CursorTy) writecur3729;
            CursorTy pvrtmp5356 = (CursorTy) loc1879;
            CursorTy taildc3176 = (CursorTy) pvrtmp5356;
            CursorTy end_taildc3176 = (CursorTy) pvrtmp5357;
            CursorTy pvrtmp5359 = (CursorTy) end_taildc3176;
            CursorTy pvrtmp5358 = (CursorTy) taildc3176;
            CursorTy fltPrd4474 = (CursorTy) pvrtmp5358;
            CursorTy fltPrd4475 = (CursorTy) pvrtmp5359;

            return (CursorCursorCursorCursorProd) {end_r1881_3393, endof3175,
                                                   fltPrd4474, fltPrd4475};
            break;
        }

      case 3:
        {
            CursorTy field_cur3731 = (CursorTy) tmpcur5321;
            CursorTy case2376 = (CursorTy) field_cur3731;
            CursorTy x1636 = (CursorTy) case2376;
            CursorTy loc2388 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct109 =
                                          _copy_Expr(end_r1880, end_r1881, loc2388, x1636);
            CursorTy pvrtmp5360 = tmp_struct109.field0;
            CursorTy pvrtmp5361 = tmp_struct109.field1;
            CursorTy pvrtmp5362 = tmp_struct109.field2;
            CursorTy pvrtmp5363 = tmp_struct109.field3;
            CursorTy fltPrd4476 = (CursorTy) pvrtmp5362;
            CursorTy fltPrd4477 = (CursorTy) pvrtmp5363;
            CursorTy pvrtmp5365 = (CursorTy) fltPrd4477;
            CursorTy pvrtmp5364 = (CursorTy) fltPrd4476;
            CursorTy y1639 = (CursorTy) pvrtmp5364;
            CursorTy fltPrd4478 = (CursorTy) pvrtmp5362;
            CursorTy fltPrd4479 = (CursorTy) pvrtmp5363;
            CursorTy pvrtmp5367 = (CursorTy) fltPrd4479;
            CursorTy pvrtmp5366 = (CursorTy) fltPrd4478;
            CursorTy end_y1639 = (CursorTy) pvrtmp5367;
            CursorTy end_r1881_3394 = (CursorTy) pvrtmp5360;
            CursorTy endof3177 = (CursorTy) pvrtmp5361;
            CursorTy case2377 = (CursorTy) endof3177;
            CursorTy x1637 = (CursorTy) case2377;
            CursorTy loc2389 = (CursorTy) end_y1639;
            CursorCursorCursorCursorProd tmp_struct110 =
                                          _copy_Expr(end_r1880, end_r1881_3394, loc2389, x1637);
            CursorTy pvrtmp5368 = tmp_struct110.field0;
            CursorTy pvrtmp5369 = tmp_struct110.field1;
            CursorTy pvrtmp5370 = tmp_struct110.field2;
            CursorTy pvrtmp5371 = tmp_struct110.field3;
            CursorTy fltPrd4480 = (CursorTy) pvrtmp5370;
            CursorTy fltPrd4481 = (CursorTy) pvrtmp5371;
            CursorTy pvrtmp5373 = (CursorTy) fltPrd4481;
            CursorTy pvrtmp5372 = (CursorTy) fltPrd4480;
            CursorTy y1640 = (CursorTy) pvrtmp5372;
            CursorTy fltPrd4482 = (CursorTy) pvrtmp5370;
            CursorTy fltPrd4483 = (CursorTy) pvrtmp5371;
            CursorTy pvrtmp5375 = (CursorTy) fltPrd4483;
            CursorTy pvrtmp5374 = (CursorTy) fltPrd4482;
            CursorTy end_y1640 = (CursorTy) pvrtmp5375;
            CursorTy end_r1881_3394_3395 = (CursorTy) pvrtmp5368;
            CursorTy endof3178 = (CursorTy) pvrtmp5369;
            CursorTy case2378 = (CursorTy) endof3178;
            CursorTy x1638 = (CursorTy) case2378;
            CursorTy loc2390 = (CursorTy) end_y1640;
            CursorCursorCursorCursorProd tmp_struct111 =
                                          _copy_Expr(end_r1880, end_r1881_3394_3395, loc2390, x1638);
            CursorTy pvrtmp5376 = tmp_struct111.field0;
            CursorTy pvrtmp5377 = tmp_struct111.field1;
            CursorTy pvrtmp5378 = tmp_struct111.field2;
            CursorTy pvrtmp5379 = tmp_struct111.field3;
            CursorTy fltPrd4484 = (CursorTy) pvrtmp5378;
            CursorTy fltPrd4485 = (CursorTy) pvrtmp5379;
            CursorTy pvrtmp5381 = (CursorTy) fltPrd4485;
            CursorTy pvrtmp5380 = (CursorTy) fltPrd4484;
            CursorTy y1641 = (CursorTy) pvrtmp5380;
            CursorTy fltPrd4486 = (CursorTy) pvrtmp5378;
            CursorTy fltPrd4487 = (CursorTy) pvrtmp5379;
            CursorTy pvrtmp5383 = (CursorTy) fltPrd4487;
            CursorTy pvrtmp5382 = (CursorTy) fltPrd4486;
            CursorTy end_y1641 = (CursorTy) pvrtmp5383;
            CursorTy end_r1881_3394_3395_3396 = (CursorTy) pvrtmp5376;
            CursorTy endof3179 = (CursorTy) pvrtmp5377;

            *(TagTyPacked *) loc1879 = 3;

            CursorTy writetag3735 = loc1879 + 1;
            CursorTy writecur3736 = (CursorTy) end_y1639;
            CursorTy writecur3737 = (CursorTy) end_y1640;
            CursorTy writecur3738 = (CursorTy) end_y1641;
            CursorTy pvrtmp5385 = (CursorTy) writecur3738;
            CursorTy pvrtmp5384 = (CursorTy) loc1879;
            CursorTy taildc3180 = (CursorTy) pvrtmp5384;
            CursorTy end_taildc3180 = (CursorTy) pvrtmp5385;
            CursorTy pvrtmp5387 = (CursorTy) end_taildc3180;
            CursorTy pvrtmp5386 = (CursorTy) taildc3180;
            CursorTy fltPrd4488 = (CursorTy) pvrtmp5386;
            CursorTy fltPrd4489 = (CursorTy) pvrtmp5387;

            return (CursorCursorCursorCursorProd) {end_r1881_3394_3395_3396,
                                                   endof3179, fltPrd4488,
                                                   fltPrd4489};
            break;
        }

      case 4:
        {
            CursorTy field_cur3740 = (CursorTy) tmpcur5321;
            CursorTy case2394 = (CursorTy) field_cur3740;
            CursorTy x1642 = (CursorTy) case2394;
            CursorTy loc2398 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct112 =
                                          _copy_ListExpr(end_r1880, end_r1881, loc2398, x1642);
            CursorTy pvrtmp5388 = tmp_struct112.field0;
            CursorTy pvrtmp5389 = tmp_struct112.field1;
            CursorTy pvrtmp5390 = tmp_struct112.field2;
            CursorTy pvrtmp5391 = tmp_struct112.field3;
            CursorTy fltPrd4490 = (CursorTy) pvrtmp5390;
            CursorTy fltPrd4491 = (CursorTy) pvrtmp5391;
            CursorTy pvrtmp5393 = (CursorTy) fltPrd4491;
            CursorTy pvrtmp5392 = (CursorTy) fltPrd4490;
            CursorTy y1643 = (CursorTy) pvrtmp5392;
            CursorTy fltPrd4492 = (CursorTy) pvrtmp5390;
            CursorTy fltPrd4493 = (CursorTy) pvrtmp5391;
            CursorTy pvrtmp5395 = (CursorTy) fltPrd4493;
            CursorTy pvrtmp5394 = (CursorTy) fltPrd4492;
            CursorTy end_y1643 = (CursorTy) pvrtmp5395;
            CursorTy end_r1881_3397 = (CursorTy) pvrtmp5388;
            CursorTy endof3181 = (CursorTy) pvrtmp5389;

            *(TagTyPacked *) loc1879 = 4;

            CursorTy writetag3742 = loc1879 + 1;
            CursorTy writecur3743 = (CursorTy) end_y1643;
            CursorTy pvrtmp5397 = (CursorTy) writecur3743;
            CursorTy pvrtmp5396 = (CursorTy) loc1879;
            CursorTy taildc3182 = (CursorTy) pvrtmp5396;
            CursorTy end_taildc3182 = (CursorTy) pvrtmp5397;
            CursorTy pvrtmp5399 = (CursorTy) end_taildc3182;
            CursorTy pvrtmp5398 = (CursorTy) taildc3182;
            CursorTy fltPrd4494 = (CursorTy) pvrtmp5398;
            CursorTy fltPrd4495 = (CursorTy) pvrtmp5399;

            return (CursorCursorCursorCursorProd) {end_r1881_3397, endof3181,
                                                   fltPrd4494, fltPrd4495};
            break;
        }

      case 5:
        {
            CursorTy field_cur3745 = (CursorTy) tmpcur5321;
            CursorTy case2400 = (CursorTy) field_cur3745;
            CursorTy x1644 = (CursorTy) case2400;
            CursorTy loc2408 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct113 =
                                          _copy_Expr(end_r1880, end_r1881, loc2408, x1644);
            CursorTy pvrtmp5400 = tmp_struct113.field0;
            CursorTy pvrtmp5401 = tmp_struct113.field1;
            CursorTy pvrtmp5402 = tmp_struct113.field2;
            CursorTy pvrtmp5403 = tmp_struct113.field3;
            CursorTy fltPrd4496 = (CursorTy) pvrtmp5402;
            CursorTy fltPrd4497 = (CursorTy) pvrtmp5403;
            CursorTy pvrtmp5405 = (CursorTy) fltPrd4497;
            CursorTy pvrtmp5404 = (CursorTy) fltPrd4496;
            CursorTy y1646 = (CursorTy) pvrtmp5404;
            CursorTy fltPrd4498 = (CursorTy) pvrtmp5402;
            CursorTy fltPrd4499 = (CursorTy) pvrtmp5403;
            CursorTy pvrtmp5407 = (CursorTy) fltPrd4499;
            CursorTy pvrtmp5406 = (CursorTy) fltPrd4498;
            CursorTy end_y1646 = (CursorTy) pvrtmp5407;
            CursorTy end_r1881_3398 = (CursorTy) pvrtmp5400;
            CursorTy endof3183 = (CursorTy) pvrtmp5401;
            CursorTy case2401 = (CursorTy) endof3183;
            CursorTy x1645 = (CursorTy) case2401;
            CursorTy loc2409 = (CursorTy) end_y1646;
            CursorCursorCursorCursorProd tmp_struct114 =
                                          _copy_ListExpr(end_r1880, end_r1881_3398, loc2409, x1645);
            CursorTy pvrtmp5408 = tmp_struct114.field0;
            CursorTy pvrtmp5409 = tmp_struct114.field1;
            CursorTy pvrtmp5410 = tmp_struct114.field2;
            CursorTy pvrtmp5411 = tmp_struct114.field3;
            CursorTy fltPrd4500 = (CursorTy) pvrtmp5410;
            CursorTy fltPrd4501 = (CursorTy) pvrtmp5411;
            CursorTy pvrtmp5413 = (CursorTy) fltPrd4501;
            CursorTy pvrtmp5412 = (CursorTy) fltPrd4500;
            CursorTy y1647 = (CursorTy) pvrtmp5412;
            CursorTy fltPrd4502 = (CursorTy) pvrtmp5410;
            CursorTy fltPrd4503 = (CursorTy) pvrtmp5411;
            CursorTy pvrtmp5415 = (CursorTy) fltPrd4503;
            CursorTy pvrtmp5414 = (CursorTy) fltPrd4502;
            CursorTy end_y1647 = (CursorTy) pvrtmp5415;
            CursorTy end_r1881_3398_3399 = (CursorTy) pvrtmp5408;
            CursorTy endof3184 = (CursorTy) pvrtmp5409;

            *(TagTyPacked *) loc1879 = 5;

            CursorTy writetag3748 = loc1879 + 1;
            CursorTy writecur3749 = (CursorTy) end_y1646;
            CursorTy writecur3750 = (CursorTy) end_y1647;
            CursorTy pvrtmp5417 = (CursorTy) writecur3750;
            CursorTy pvrtmp5416 = (CursorTy) loc1879;
            CursorTy taildc3185 = (CursorTy) pvrtmp5416;
            CursorTy end_taildc3185 = (CursorTy) pvrtmp5417;
            CursorTy pvrtmp5419 = (CursorTy) end_taildc3185;
            CursorTy pvrtmp5418 = (CursorTy) taildc3185;
            CursorTy fltPrd4504 = (CursorTy) pvrtmp5418;
            CursorTy fltPrd4505 = (CursorTy) pvrtmp5419;

            return (CursorCursorCursorCursorProd) {end_r1881_3398_3399,
                                                   endof3184, fltPrd4504,
                                                   fltPrd4505};
            break;
        }

      case 6:
        {
            CursorTy field_cur3752 = (CursorTy) tmpcur5321;
            CursorTy case2412 = (CursorTy) field_cur3752;
            CursorTy x1648 = (CursorTy) case2412;
            CursorTy loc2420 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct115 =
                                          _copy_LVBIND(end_r1880, end_r1881, loc2420, x1648);
            CursorTy pvrtmp5420 = tmp_struct115.field0;
            CursorTy pvrtmp5421 = tmp_struct115.field1;
            CursorTy pvrtmp5422 = tmp_struct115.field2;
            CursorTy pvrtmp5423 = tmp_struct115.field3;
            CursorTy fltPrd4506 = (CursorTy) pvrtmp5422;
            CursorTy fltPrd4507 = (CursorTy) pvrtmp5423;
            CursorTy pvrtmp5425 = (CursorTy) fltPrd4507;
            CursorTy pvrtmp5424 = (CursorTy) fltPrd4506;
            CursorTy y1650 = (CursorTy) pvrtmp5424;
            CursorTy fltPrd4508 = (CursorTy) pvrtmp5422;
            CursorTy fltPrd4509 = (CursorTy) pvrtmp5423;
            CursorTy pvrtmp5427 = (CursorTy) fltPrd4509;
            CursorTy pvrtmp5426 = (CursorTy) fltPrd4508;
            CursorTy end_y1650 = (CursorTy) pvrtmp5427;
            CursorTy end_r1881_3400 = (CursorTy) pvrtmp5420;
            CursorTy endof3186 = (CursorTy) pvrtmp5421;
            CursorTy case2413 = (CursorTy) endof3186;
            CursorTy x1649 = (CursorTy) case2413;
            CursorTy loc2421 = (CursorTy) end_y1650;
            CursorCursorCursorCursorProd tmp_struct116 =
                                          _copy_ListExpr(end_r1880, end_r1881_3400, loc2421, x1649);
            CursorTy pvrtmp5428 = tmp_struct116.field0;
            CursorTy pvrtmp5429 = tmp_struct116.field1;
            CursorTy pvrtmp5430 = tmp_struct116.field2;
            CursorTy pvrtmp5431 = tmp_struct116.field3;
            CursorTy fltPrd4510 = (CursorTy) pvrtmp5430;
            CursorTy fltPrd4511 = (CursorTy) pvrtmp5431;
            CursorTy pvrtmp5433 = (CursorTy) fltPrd4511;
            CursorTy pvrtmp5432 = (CursorTy) fltPrd4510;
            CursorTy y1651 = (CursorTy) pvrtmp5432;
            CursorTy fltPrd4512 = (CursorTy) pvrtmp5430;
            CursorTy fltPrd4513 = (CursorTy) pvrtmp5431;
            CursorTy pvrtmp5435 = (CursorTy) fltPrd4513;
            CursorTy pvrtmp5434 = (CursorTy) fltPrd4512;
            CursorTy end_y1651 = (CursorTy) pvrtmp5435;
            CursorTy end_r1881_3400_3401 = (CursorTy) pvrtmp5428;
            CursorTy endof3187 = (CursorTy) pvrtmp5429;

            *(TagTyPacked *) loc1879 = 6;

            CursorTy writetag3755 = loc1879 + 1;
            CursorTy writecur3756 = (CursorTy) end_y1650;
            CursorTy writecur3757 = (CursorTy) end_y1651;
            CursorTy pvrtmp5437 = (CursorTy) writecur3757;
            CursorTy pvrtmp5436 = (CursorTy) loc1879;
            CursorTy taildc3188 = (CursorTy) pvrtmp5436;
            CursorTy end_taildc3188 = (CursorTy) pvrtmp5437;
            CursorTy pvrtmp5439 = (CursorTy) end_taildc3188;
            CursorTy pvrtmp5438 = (CursorTy) taildc3188;
            CursorTy fltPrd4514 = (CursorTy) pvrtmp5438;
            CursorTy fltPrd4515 = (CursorTy) pvrtmp5439;

            return (CursorCursorCursorCursorProd) {end_r1881_3400_3401,
                                                   endof3187, fltPrd4514,
                                                   fltPrd4515};
            break;
        }

      case 7:
        {
            CursorTy field_cur3759 = (CursorTy) tmpcur5321;
            CursorTy case2424 = (CursorTy) field_cur3759;
            CursorTy x1652 = (CursorTy) case2424;
            CursorTy loc2432 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct117 =
                                          _copy_LVBIND(end_r1880, end_r1881, loc2432, x1652);
            CursorTy pvrtmp5440 = tmp_struct117.field0;
            CursorTy pvrtmp5441 = tmp_struct117.field1;
            CursorTy pvrtmp5442 = tmp_struct117.field2;
            CursorTy pvrtmp5443 = tmp_struct117.field3;
            CursorTy fltPrd4516 = (CursorTy) pvrtmp5442;
            CursorTy fltPrd4517 = (CursorTy) pvrtmp5443;
            CursorTy pvrtmp5445 = (CursorTy) fltPrd4517;
            CursorTy pvrtmp5444 = (CursorTy) fltPrd4516;
            CursorTy y1654 = (CursorTy) pvrtmp5444;
            CursorTy fltPrd4518 = (CursorTy) pvrtmp5442;
            CursorTy fltPrd4519 = (CursorTy) pvrtmp5443;
            CursorTy pvrtmp5447 = (CursorTy) fltPrd4519;
            CursorTy pvrtmp5446 = (CursorTy) fltPrd4518;
            CursorTy end_y1654 = (CursorTy) pvrtmp5447;
            CursorTy end_r1881_3402 = (CursorTy) pvrtmp5440;
            CursorTy endof3189 = (CursorTy) pvrtmp5441;
            CursorTy case2425 = (CursorTy) endof3189;
            CursorTy x1653 = (CursorTy) case2425;
            CursorTy loc2433 = (CursorTy) end_y1654;
            CursorCursorCursorCursorProd tmp_struct118 =
                                          _copy_ListExpr(end_r1880, end_r1881_3402, loc2433, x1653);
            CursorTy pvrtmp5448 = tmp_struct118.field0;
            CursorTy pvrtmp5449 = tmp_struct118.field1;
            CursorTy pvrtmp5450 = tmp_struct118.field2;
            CursorTy pvrtmp5451 = tmp_struct118.field3;
            CursorTy fltPrd4520 = (CursorTy) pvrtmp5450;
            CursorTy fltPrd4521 = (CursorTy) pvrtmp5451;
            CursorTy pvrtmp5453 = (CursorTy) fltPrd4521;
            CursorTy pvrtmp5452 = (CursorTy) fltPrd4520;
            CursorTy y1655 = (CursorTy) pvrtmp5452;
            CursorTy fltPrd4522 = (CursorTy) pvrtmp5450;
            CursorTy fltPrd4523 = (CursorTy) pvrtmp5451;
            CursorTy pvrtmp5455 = (CursorTy) fltPrd4523;
            CursorTy pvrtmp5454 = (CursorTy) fltPrd4522;
            CursorTy end_y1655 = (CursorTy) pvrtmp5455;
            CursorTy end_r1881_3402_3403 = (CursorTy) pvrtmp5448;
            CursorTy endof3190 = (CursorTy) pvrtmp5449;

            *(TagTyPacked *) loc1879 = 7;

            CursorTy writetag3762 = loc1879 + 1;
            CursorTy writecur3763 = (CursorTy) end_y1654;
            CursorTy writecur3764 = (CursorTy) end_y1655;
            CursorTy pvrtmp5457 = (CursorTy) writecur3764;
            CursorTy pvrtmp5456 = (CursorTy) loc1879;
            CursorTy taildc3191 = (CursorTy) pvrtmp5456;
            CursorTy end_taildc3191 = (CursorTy) pvrtmp5457;
            CursorTy pvrtmp5459 = (CursorTy) end_taildc3191;
            CursorTy pvrtmp5458 = (CursorTy) taildc3191;
            CursorTy fltPrd4524 = (CursorTy) pvrtmp5458;
            CursorTy fltPrd4525 = (CursorTy) pvrtmp5459;

            return (CursorCursorCursorCursorProd) {end_r1881_3402_3403,
                                                   endof3190, fltPrd4524,
                                                   fltPrd4525};
            break;
        }

      case 8:
        {
            CursorTy field_cur3766 = (CursorTy) tmpcur5321;
            CursorTy case2436 = (CursorTy) field_cur3766;
            SymTy tmpval5460 = *(SymTy *) case2436;
            CursorTy tmpcur5461 = case2436 + sizeof(SymTy);
            SymTy x1656 = (SymTy) tmpval5460;
            CursorTy end_x1656 = (CursorTy) tmpcur5461;
            CursorTy case2437 = (CursorTy) end_x1656;
            CursorTy x1657 = (CursorTy) case2437;
            CursorTy jump3192 = case2436 + 8;
            CursorCursorCursorCursorProd tmp_struct119 =
                                          _copy_Expr(end_r1880, end_r1881, loc2442, x1657);
            CursorTy pvrtmp5462 = tmp_struct119.field0;
            CursorTy pvrtmp5463 = tmp_struct119.field1;
            CursorTy pvrtmp5464 = tmp_struct119.field2;
            CursorTy pvrtmp5465 = tmp_struct119.field3;
            CursorTy fltPrd4526 = (CursorTy) pvrtmp5464;
            CursorTy fltPrd4527 = (CursorTy) pvrtmp5465;
            CursorTy pvrtmp5467 = (CursorTy) fltPrd4527;
            CursorTy pvrtmp5466 = (CursorTy) fltPrd4526;
            CursorTy y1659 = (CursorTy) pvrtmp5466;
            CursorTy fltPrd4528 = (CursorTy) pvrtmp5464;
            CursorTy fltPrd4529 = (CursorTy) pvrtmp5465;
            CursorTy pvrtmp5469 = (CursorTy) fltPrd4529;
            CursorTy pvrtmp5468 = (CursorTy) fltPrd4528;
            CursorTy end_y1659 = (CursorTy) pvrtmp5469;
            CursorTy end_r1881_3404 = (CursorTy) pvrtmp5462;
            CursorTy endof3193 = (CursorTy) pvrtmp5463;

            *(TagTyPacked *) loc1879 = 8;

            CursorTy writetag3769 = loc1879 + 1;

            *(SymTy *) writetag3769 = x1656;

            CursorTy writecur3770 = writetag3769 + sizeof(SymTy);
            CursorTy writecur3771 = (CursorTy) end_y1659;
            CursorTy pvrtmp5471 = (CursorTy) writecur3771;
            CursorTy pvrtmp5470 = (CursorTy) loc1879;
            CursorTy taildc3194 = (CursorTy) pvrtmp5470;
            CursorTy end_taildc3194 = (CursorTy) pvrtmp5471;
            CursorTy pvrtmp5473 = (CursorTy) end_taildc3194;
            CursorTy pvrtmp5472 = (CursorTy) taildc3194;
            CursorTy fltPrd4530 = (CursorTy) pvrtmp5472;
            CursorTy fltPrd4531 = (CursorTy) pvrtmp5473;

            return (CursorCursorCursorCursorProd) {end_r1881_3404, endof3193,
                                                   fltPrd4530, fltPrd4531};
            break;
        }

      case 9:
        {
            CursorTy field_cur3773 = (CursorTy) tmpcur5321;
            CursorTy case2446 = (CursorTy) field_cur3773;
            CursorTy x1660 = (CursorTy) case2446;
            CursorTy loc2450 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct120 =
                                          _copy_Datum(end_r1880, end_r1881, loc2450, x1660);
            CursorTy pvrtmp5474 = tmp_struct120.field0;
            CursorTy pvrtmp5475 = tmp_struct120.field1;
            CursorTy pvrtmp5476 = tmp_struct120.field2;
            CursorTy pvrtmp5477 = tmp_struct120.field3;
            CursorTy fltPrd4532 = (CursorTy) pvrtmp5476;
            CursorTy fltPrd4533 = (CursorTy) pvrtmp5477;
            CursorTy pvrtmp5479 = (CursorTy) fltPrd4533;
            CursorTy pvrtmp5478 = (CursorTy) fltPrd4532;
            CursorTy y1661 = (CursorTy) pvrtmp5478;
            CursorTy fltPrd4534 = (CursorTy) pvrtmp5476;
            CursorTy fltPrd4535 = (CursorTy) pvrtmp5477;
            CursorTy pvrtmp5481 = (CursorTy) fltPrd4535;
            CursorTy pvrtmp5480 = (CursorTy) fltPrd4534;
            CursorTy end_y1661 = (CursorTy) pvrtmp5481;
            CursorTy end_r1881_3405 = (CursorTy) pvrtmp5474;
            CursorTy endof3195 = (CursorTy) pvrtmp5475;

            *(TagTyPacked *) loc1879 = 9;

            CursorTy writetag3775 = loc1879 + 1;
            CursorTy writecur3776 = (CursorTy) end_y1661;
            CursorTy pvrtmp5483 = (CursorTy) writecur3776;
            CursorTy pvrtmp5482 = (CursorTy) loc1879;
            CursorTy taildc3196 = (CursorTy) pvrtmp5482;
            CursorTy end_taildc3196 = (CursorTy) pvrtmp5483;
            CursorTy pvrtmp5485 = (CursorTy) end_taildc3196;
            CursorTy pvrtmp5484 = (CursorTy) taildc3196;
            CursorTy fltPrd4536 = (CursorTy) pvrtmp5484;
            CursorTy fltPrd4537 = (CursorTy) pvrtmp5485;

            return (CursorCursorCursorCursorProd) {end_r1881_3405, endof3195,
                                                   fltPrd4536, fltPrd4537};
            break;
        }

      case 10:
        {
            CursorTy field_cur3778 = (CursorTy) tmpcur5321;
            CursorTy case2452 = (CursorTy) field_cur3778;
            CursorTy x1662 = (CursorTy) case2452;
            CursorTy loc2456 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct121 =
                                          _copy_Datum(end_r1880, end_r1881, loc2456, x1662);
            CursorTy pvrtmp5486 = tmp_struct121.field0;
            CursorTy pvrtmp5487 = tmp_struct121.field1;
            CursorTy pvrtmp5488 = tmp_struct121.field2;
            CursorTy pvrtmp5489 = tmp_struct121.field3;
            CursorTy fltPrd4538 = (CursorTy) pvrtmp5488;
            CursorTy fltPrd4539 = (CursorTy) pvrtmp5489;
            CursorTy pvrtmp5491 = (CursorTy) fltPrd4539;
            CursorTy pvrtmp5490 = (CursorTy) fltPrd4538;
            CursorTy y1663 = (CursorTy) pvrtmp5490;
            CursorTy fltPrd4540 = (CursorTy) pvrtmp5488;
            CursorTy fltPrd4541 = (CursorTy) pvrtmp5489;
            CursorTy pvrtmp5493 = (CursorTy) fltPrd4541;
            CursorTy pvrtmp5492 = (CursorTy) fltPrd4540;
            CursorTy end_y1663 = (CursorTy) pvrtmp5493;
            CursorTy end_r1881_3406 = (CursorTy) pvrtmp5486;
            CursorTy endof3197 = (CursorTy) pvrtmp5487;

            *(TagTyPacked *) loc1879 = 10;

            CursorTy writetag3780 = loc1879 + 1;
            CursorTy writecur3781 = (CursorTy) end_y1663;
            CursorTy pvrtmp5495 = (CursorTy) writecur3781;
            CursorTy pvrtmp5494 = (CursorTy) loc1879;
            CursorTy taildc3198 = (CursorTy) pvrtmp5494;
            CursorTy end_taildc3198 = (CursorTy) pvrtmp5495;
            CursorTy pvrtmp5497 = (CursorTy) end_taildc3198;
            CursorTy pvrtmp5496 = (CursorTy) taildc3198;
            CursorTy fltPrd4542 = (CursorTy) pvrtmp5496;
            CursorTy fltPrd4543 = (CursorTy) pvrtmp5497;

            return (CursorCursorCursorCursorProd) {end_r1881_3406, endof3197,
                                                   fltPrd4542, fltPrd4543};
            break;
        }

      case 11:
        {
            CursorTy field_cur3783 = (CursorTy) tmpcur5321;
            CursorTy case2458 = (CursorTy) field_cur3783;
            CursorTy x1664 = (CursorTy) case2458;
            CursorTy loc2462 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct122 =
                                          _copy_Datum(end_r1880, end_r1881, loc2462, x1664);
            CursorTy pvrtmp5498 = tmp_struct122.field0;
            CursorTy pvrtmp5499 = tmp_struct122.field1;
            CursorTy pvrtmp5500 = tmp_struct122.field2;
            CursorTy pvrtmp5501 = tmp_struct122.field3;
            CursorTy fltPrd4544 = (CursorTy) pvrtmp5500;
            CursorTy fltPrd4545 = (CursorTy) pvrtmp5501;
            CursorTy pvrtmp5503 = (CursorTy) fltPrd4545;
            CursorTy pvrtmp5502 = (CursorTy) fltPrd4544;
            CursorTy y1665 = (CursorTy) pvrtmp5502;
            CursorTy fltPrd4546 = (CursorTy) pvrtmp5500;
            CursorTy fltPrd4547 = (CursorTy) pvrtmp5501;
            CursorTy pvrtmp5505 = (CursorTy) fltPrd4547;
            CursorTy pvrtmp5504 = (CursorTy) fltPrd4546;
            CursorTy end_y1665 = (CursorTy) pvrtmp5505;
            CursorTy end_r1881_3407 = (CursorTy) pvrtmp5498;
            CursorTy endof3199 = (CursorTy) pvrtmp5499;

            *(TagTyPacked *) loc1879 = 11;

            CursorTy writetag3785 = loc1879 + 1;
            CursorTy writecur3786 = (CursorTy) end_y1665;
            CursorTy pvrtmp5507 = (CursorTy) writecur3786;
            CursorTy pvrtmp5506 = (CursorTy) loc1879;
            CursorTy taildc3200 = (CursorTy) pvrtmp5506;
            CursorTy end_taildc3200 = (CursorTy) pvrtmp5507;
            CursorTy pvrtmp5509 = (CursorTy) end_taildc3200;
            CursorTy pvrtmp5508 = (CursorTy) taildc3200;
            CursorTy fltPrd4548 = (CursorTy) pvrtmp5508;
            CursorTy fltPrd4549 = (CursorTy) pvrtmp5509;

            return (CursorCursorCursorCursorProd) {end_r1881_3407, endof3199,
                                                   fltPrd4548, fltPrd4549};
            break;
        }

      case 12:
        {
            CursorTy field_cur3788 = (CursorTy) tmpcur5321;
            CursorTy case2464 = (CursorTy) field_cur3788;
            CursorTy x1666 = (CursorTy) case2464;
            CursorTy loc2476 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct123 =
                                          _copy_Expr(end_r1880, end_r1881, loc2476, x1666);
            CursorTy pvrtmp5510 = tmp_struct123.field0;
            CursorTy pvrtmp5511 = tmp_struct123.field1;
            CursorTy pvrtmp5512 = tmp_struct123.field2;
            CursorTy pvrtmp5513 = tmp_struct123.field3;
            CursorTy fltPrd4550 = (CursorTy) pvrtmp5512;
            CursorTy fltPrd4551 = (CursorTy) pvrtmp5513;
            CursorTy pvrtmp5515 = (CursorTy) fltPrd4551;
            CursorTy pvrtmp5514 = (CursorTy) fltPrd4550;
            CursorTy y1669 = (CursorTy) pvrtmp5514;
            CursorTy fltPrd4552 = (CursorTy) pvrtmp5512;
            CursorTy fltPrd4553 = (CursorTy) pvrtmp5513;
            CursorTy pvrtmp5517 = (CursorTy) fltPrd4553;
            CursorTy pvrtmp5516 = (CursorTy) fltPrd4552;
            CursorTy end_y1669 = (CursorTy) pvrtmp5517;
            CursorTy end_r1881_3408 = (CursorTy) pvrtmp5510;
            CursorTy endof3201 = (CursorTy) pvrtmp5511;
            CursorTy case2465 = (CursorTy) endof3201;
            CursorTy x1667 = (CursorTy) case2465;
            CursorTy loc2477 = (CursorTy) end_y1669;
            CursorCursorCursorCursorProd tmp_struct124 =
                                          _copy_Expr(end_r1880, end_r1881_3408, loc2477, x1667);
            CursorTy pvrtmp5518 = tmp_struct124.field0;
            CursorTy pvrtmp5519 = tmp_struct124.field1;
            CursorTy pvrtmp5520 = tmp_struct124.field2;
            CursorTy pvrtmp5521 = tmp_struct124.field3;
            CursorTy fltPrd4554 = (CursorTy) pvrtmp5520;
            CursorTy fltPrd4555 = (CursorTy) pvrtmp5521;
            CursorTy pvrtmp5523 = (CursorTy) fltPrd4555;
            CursorTy pvrtmp5522 = (CursorTy) fltPrd4554;
            CursorTy y1670 = (CursorTy) pvrtmp5522;
            CursorTy fltPrd4556 = (CursorTy) pvrtmp5520;
            CursorTy fltPrd4557 = (CursorTy) pvrtmp5521;
            CursorTy pvrtmp5525 = (CursorTy) fltPrd4557;
            CursorTy pvrtmp5524 = (CursorTy) fltPrd4556;
            CursorTy end_y1670 = (CursorTy) pvrtmp5525;
            CursorTy end_r1881_3408_3409 = (CursorTy) pvrtmp5518;
            CursorTy endof3202 = (CursorTy) pvrtmp5519;
            CursorTy case2466 = (CursorTy) endof3202;
            CursorTy x1668 = (CursorTy) case2466;
            CursorTy loc2478 = (CursorTy) end_y1670;
            CursorCursorCursorCursorProd tmp_struct125 =
                                          _copy_Expr(end_r1880, end_r1881_3408_3409, loc2478, x1668);
            CursorTy pvrtmp5526 = tmp_struct125.field0;
            CursorTy pvrtmp5527 = tmp_struct125.field1;
            CursorTy pvrtmp5528 = tmp_struct125.field2;
            CursorTy pvrtmp5529 = tmp_struct125.field3;
            CursorTy fltPrd4558 = (CursorTy) pvrtmp5528;
            CursorTy fltPrd4559 = (CursorTy) pvrtmp5529;
            CursorTy pvrtmp5531 = (CursorTy) fltPrd4559;
            CursorTy pvrtmp5530 = (CursorTy) fltPrd4558;
            CursorTy y1671 = (CursorTy) pvrtmp5530;
            CursorTy fltPrd4560 = (CursorTy) pvrtmp5528;
            CursorTy fltPrd4561 = (CursorTy) pvrtmp5529;
            CursorTy pvrtmp5533 = (CursorTy) fltPrd4561;
            CursorTy pvrtmp5532 = (CursorTy) fltPrd4560;
            CursorTy end_y1671 = (CursorTy) pvrtmp5533;
            CursorTy end_r1881_3408_3409_3410 = (CursorTy) pvrtmp5526;
            CursorTy endof3203 = (CursorTy) pvrtmp5527;

            *(TagTyPacked *) loc1879 = 12;

            CursorTy writetag3792 = loc1879 + 1;
            CursorTy writecur3793 = (CursorTy) end_y1669;
            CursorTy writecur3794 = (CursorTy) end_y1670;
            CursorTy writecur3795 = (CursorTy) end_y1671;
            CursorTy pvrtmp5535 = (CursorTy) writecur3795;
            CursorTy pvrtmp5534 = (CursorTy) loc1879;
            CursorTy taildc3204 = (CursorTy) pvrtmp5534;
            CursorTy end_taildc3204 = (CursorTy) pvrtmp5535;
            CursorTy pvrtmp5537 = (CursorTy) end_taildc3204;
            CursorTy pvrtmp5536 = (CursorTy) taildc3204;
            CursorTy fltPrd4562 = (CursorTy) pvrtmp5536;
            CursorTy fltPrd4563 = (CursorTy) pvrtmp5537;

            return (CursorCursorCursorCursorProd) {end_r1881_3408_3409_3410,
                                                   endof3203, fltPrd4562,
                                                   fltPrd4563};
            break;
        }

      case 13:
        {
            CursorTy field_cur3797 = (CursorTy) tmpcur5321;
            CursorTy case2482 = (CursorTy) field_cur3797;
            CursorTy x1672 = (CursorTy) case2482;
            CursorTy loc2490 = loc1879 + 1;
            CursorCursorCursorCursorProd tmp_struct126 =
                                          _copy_Expr(end_r1880, end_r1881, loc2490, x1672);
            CursorTy pvrtmp5538 = tmp_struct126.field0;
            CursorTy pvrtmp5539 = tmp_struct126.field1;
            CursorTy pvrtmp5540 = tmp_struct126.field2;
            CursorTy pvrtmp5541 = tmp_struct126.field3;
            CursorTy fltPrd4564 = (CursorTy) pvrtmp5540;
            CursorTy fltPrd4565 = (CursorTy) pvrtmp5541;
            CursorTy pvrtmp5543 = (CursorTy) fltPrd4565;
            CursorTy pvrtmp5542 = (CursorTy) fltPrd4564;
            CursorTy y1674 = (CursorTy) pvrtmp5542;
            CursorTy fltPrd4566 = (CursorTy) pvrtmp5540;
            CursorTy fltPrd4567 = (CursorTy) pvrtmp5541;
            CursorTy pvrtmp5545 = (CursorTy) fltPrd4567;
            CursorTy pvrtmp5544 = (CursorTy) fltPrd4566;
            CursorTy end_y1674 = (CursorTy) pvrtmp5545;
            CursorTy end_r1881_3411 = (CursorTy) pvrtmp5538;
            CursorTy endof3205 = (CursorTy) pvrtmp5539;
            CursorTy case2483 = (CursorTy) endof3205;
            CursorTy x1673 = (CursorTy) case2483;
            CursorTy loc2491 = (CursorTy) end_y1674;
            CursorCursorCursorCursorProd tmp_struct127 =
                                          _copy_ListExpr(end_r1880, end_r1881_3411, loc2491, x1673);
            CursorTy pvrtmp5546 = tmp_struct127.field0;
            CursorTy pvrtmp5547 = tmp_struct127.field1;
            CursorTy pvrtmp5548 = tmp_struct127.field2;
            CursorTy pvrtmp5549 = tmp_struct127.field3;
            CursorTy fltPrd4568 = (CursorTy) pvrtmp5548;
            CursorTy fltPrd4569 = (CursorTy) pvrtmp5549;
            CursorTy pvrtmp5551 = (CursorTy) fltPrd4569;
            CursorTy pvrtmp5550 = (CursorTy) fltPrd4568;
            CursorTy y1675 = (CursorTy) pvrtmp5550;
            CursorTy fltPrd4570 = (CursorTy) pvrtmp5548;
            CursorTy fltPrd4571 = (CursorTy) pvrtmp5549;
            CursorTy pvrtmp5553 = (CursorTy) fltPrd4571;
            CursorTy pvrtmp5552 = (CursorTy) fltPrd4570;
            CursorTy end_y1675 = (CursorTy) pvrtmp5553;
            CursorTy end_r1881_3411_3412 = (CursorTy) pvrtmp5546;
            CursorTy endof3206 = (CursorTy) pvrtmp5547;

            *(TagTyPacked *) loc1879 = 13;

            CursorTy writetag3800 = loc1879 + 1;
            CursorTy writecur3801 = (CursorTy) end_y1674;
            CursorTy writecur3802 = (CursorTy) end_y1675;
            CursorTy pvrtmp5555 = (CursorTy) writecur3802;
            CursorTy pvrtmp5554 = (CursorTy) loc1879;
            CursorTy taildc3207 = (CursorTy) pvrtmp5554;
            CursorTy end_taildc3207 = (CursorTy) pvrtmp5555;
            CursorTy pvrtmp5557 = (CursorTy) end_taildc3207;
            CursorTy pvrtmp5556 = (CursorTy) taildc3207;
            CursorTy fltPrd4572 = (CursorTy) pvrtmp5556;
            CursorTy fltPrd4573 = (CursorTy) pvrtmp5557;

            return (CursorCursorCursorCursorProd) {end_r1881_3411_3412,
                                                   endof3206, fltPrd4572,
                                                   fltPrd4573};
            break;
        }

      case 14:
        {
            CursorTy field_cur3804 = (CursorTy) tmpcur5321;
            CursorTy case2494 = (CursorTy) field_cur3804;
            SymTy tmpval5558 = *(SymTy *) case2494;
            CursorTy tmpcur5559 = case2494 + sizeof(SymTy);
            SymTy x1676 = (SymTy) tmpval5558;
            CursorTy end_x1676 = (CursorTy) tmpcur5559;
            CursorTy jump3208 = case2494 + 8;

            *(TagTyPacked *) loc1879 = 14;

            CursorTy writetag3806 = loc1879 + 1;

            *(SymTy *) writetag3806 = x1676;

            CursorTy writecur3807 = writetag3806 + sizeof(SymTy);
            CursorTy pvrtmp5561 = (CursorTy) writecur3807;
            CursorTy pvrtmp5560 = (CursorTy) loc1879;
            CursorTy taildc3209 = (CursorTy) pvrtmp5560;
            CursorTy end_taildc3209 = (CursorTy) pvrtmp5561;
            CursorTy pvrtmp5563 = (CursorTy) end_taildc3209;
            CursorTy pvrtmp5562 = (CursorTy) taildc3209;
            CursorTy fltPrd4574 = (CursorTy) pvrtmp5562;
            CursorTy fltPrd4575 = (CursorTy) pvrtmp5563;

            return (CursorCursorCursorCursorProd) {end_r1881, jump3208,
                                                   fltPrd4574, fltPrd4575};
            break;
        }

      case 15:
        {
            CursorTy field_cur3809 = (CursorTy) tmpcur5321;
            CursorTy case2498 = (CursorTy) field_cur3809;
            SymTy tmpval5564 = *(SymTy *) case2498;
            CursorTy tmpcur5565 = case2498 + sizeof(SymTy);
            SymTy x1678 = (SymTy) tmpval5564;
            CursorTy end_x1678 = (CursorTy) tmpcur5565;
            CursorTy jump3210 = case2498 + 8;

            *(TagTyPacked *) loc1879 = 15;

            CursorTy writetag3811 = loc1879 + 1;

            *(SymTy *) writetag3811 = x1678;

            CursorTy writecur3812 = writetag3811 + sizeof(SymTy);
            CursorTy pvrtmp5567 = (CursorTy) writecur3812;
            CursorTy pvrtmp5566 = (CursorTy) loc1879;
            CursorTy taildc3211 = (CursorTy) pvrtmp5566;
            CursorTy end_taildc3211 = (CursorTy) pvrtmp5567;
            CursorTy pvrtmp5569 = (CursorTy) end_taildc3211;
            CursorTy pvrtmp5568 = (CursorTy) taildc3211;
            CursorTy fltPrd4576 = (CursorTy) pvrtmp5568;
            CursorTy fltPrd4577 = (CursorTy) pvrtmp5569;

            return (CursorCursorCursorCursorProd) {end_r1881, jump3210,
                                                   fltPrd4576, fltPrd4577};
            break;
        }

      case 16:
        {
            CursorTy field_cur3814 = (CursorTy) tmpcur5321;
            CursorTy case2502 = (CursorTy) field_cur3814;
            SymTy tmpval5570 = *(SymTy *) case2502;
            CursorTy tmpcur5571 = case2502 + sizeof(SymTy);
            SymTy x1680 = (SymTy) tmpval5570;
            CursorTy end_x1680 = (CursorTy) tmpcur5571;
            CursorTy jump3212 = case2502 + 8;

            *(TagTyPacked *) loc1879 = 16;

            CursorTy writetag3816 = loc1879 + 1;

            *(SymTy *) writetag3816 = x1680;

            CursorTy writecur3817 = writetag3816 + sizeof(SymTy);
            CursorTy pvrtmp5573 = (CursorTy) writecur3817;
            CursorTy pvrtmp5572 = (CursorTy) loc1879;
            CursorTy taildc3213 = (CursorTy) pvrtmp5572;
            CursorTy end_taildc3213 = (CursorTy) pvrtmp5573;
            CursorTy pvrtmp5575 = (CursorTy) end_taildc3213;
            CursorTy pvrtmp5574 = (CursorTy) taildc3213;
            CursorTy fltPrd4578 = (CursorTy) pvrtmp5574;
            CursorTy fltPrd4579 = (CursorTy) pvrtmp5575;

            return (CursorCursorCursorCursorProd) {end_r1881, jump3212,
                                                   fltPrd4578, fltPrd4579};
            break;
        }

      case 17:
        {
            CursorTy field_cur3819 = (CursorTy) tmpcur5321;
            CursorTy jump3214 = loc1878 + 1;

            *(TagTyPacked *) loc1879 = 17;

            CursorTy writetag3820 = loc1879 + 1;
            CursorTy pvrtmp5577 = (CursorTy) writetag3820;
            CursorTy pvrtmp5576 = (CursorTy) loc1879;
            CursorTy taildc3215 = (CursorTy) pvrtmp5576;
            CursorTy end_taildc3215 = (CursorTy) pvrtmp5577;
            CursorTy pvrtmp5579 = (CursorTy) end_taildc3215;
            CursorTy pvrtmp5578 = (CursorTy) taildc3215;
            CursorTy fltPrd4580 = (CursorTy) pvrtmp5578;
            CursorTy fltPrd4581 = (CursorTy) pvrtmp5579;

            return (CursorCursorCursorCursorProd) {end_r1881, jump3214,
                                                   fltPrd4580, fltPrd4581};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6629 = *(CursorTy *) tmpcur5321;
            CursorTy tmpaftercur6630 = tmpcur5321 + 8;
            TagTyPacked tagtmp6631 = *(TagTyPacked *) tmpcur6629;
            CursorTy tailtmp6632 = tmpcur6629 + 1;

            tmpval5320 = tagtmp6631;
            tmpcur5321 = tailtmp6632;
            goto switch5580;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6629 = *(CursorTy *) tmpcur5321;
            CursorTy tmpaftercur6630 = tmpcur5321 + 8;
            TagTyPacked tagtmp6631 = *(TagTyPacked *) tmpcur6629;
            CursorTy tailtmp6632 = tmpcur6629 + 1;

            tmpval5320 = tagtmp6631;
            tmpcur5321 = tailtmp6632;
            goto switch5580;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5320");
            exit(1);
        }
    }
}
CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r1886,
                                          CursorTy end_r1887, CursorTy loc1885,
                                          CursorTy arg1737)
{
    CursorTy loc1884 = (CursorTy) arg1737;

    if (loc1885 + 18 > end_r1887) {
        ChunkTy new_chunk159 = alloc_chunk(end_r1887);
        CursorTy chunk_start160 = new_chunk159.start_ptr;
        CursorTy chunk_end161 = new_chunk159.end_ptr;

        end_r1887 = chunk_end161;
        *(TagTyPacked *) loc1885 = 255;

        CursorTy redir = loc1885 + 1;

        *(CursorTy *) redir = chunk_start160;
        loc1885 = chunk_start160;
    }

    TagTyPacked tmpval5638 = *(TagTyPacked *) arg1737;
    CursorTy tmpcur5639 = arg1737 + 1;


  switch5704:
    ;
    switch (tmpval5638) {

      case 0:
        {
            CursorTy field_cur3867 = (CursorTy) tmpcur5639;
            CursorTy case2582 = (CursorTy) field_cur3867;
            CursorTy x1738 = (CursorTy) case2582;
            CursorTy loc2590 = loc1885 + 1;
            CursorCursorCursorCursorProd tmp_struct153 =
                                          _copy_ListSym(end_r1886, end_r1887, loc2590, x1738);
            CursorTy pvrtmp5640 = tmp_struct153.field0;
            CursorTy pvrtmp5641 = tmp_struct153.field1;
            CursorTy pvrtmp5642 = tmp_struct153.field2;
            CursorTy pvrtmp5643 = tmp_struct153.field3;
            CursorTy fltPrd4582 = (CursorTy) pvrtmp5642;
            CursorTy fltPrd4583 = (CursorTy) pvrtmp5643;
            CursorTy pvrtmp5645 = (CursorTy) fltPrd4583;
            CursorTy pvrtmp5644 = (CursorTy) fltPrd4582;
            CursorTy y1740 = (CursorTy) pvrtmp5644;
            CursorTy fltPrd4584 = (CursorTy) pvrtmp5642;
            CursorTy fltPrd4585 = (CursorTy) pvrtmp5643;
            CursorTy pvrtmp5647 = (CursorTy) fltPrd4585;
            CursorTy pvrtmp5646 = (CursorTy) fltPrd4584;
            CursorTy end_y1740 = (CursorTy) pvrtmp5647;
            CursorTy end_r1887_3413 = (CursorTy) pvrtmp5640;
            CursorTy endof3262 = (CursorTy) pvrtmp5641;
            CursorTy case2583 = (CursorTy) endof3262;
            CursorTy x1739 = (CursorTy) case2583;
            CursorTy loc2591 = (CursorTy) end_y1740;
            CursorCursorCursorCursorProd tmp_struct154 =
                                          _copy_Expr(end_r1886, end_r1887_3413, loc2591, x1739);
            CursorTy pvrtmp5648 = tmp_struct154.field0;
            CursorTy pvrtmp5649 = tmp_struct154.field1;
            CursorTy pvrtmp5650 = tmp_struct154.field2;
            CursorTy pvrtmp5651 = tmp_struct154.field3;
            CursorTy fltPrd4586 = (CursorTy) pvrtmp5650;
            CursorTy fltPrd4587 = (CursorTy) pvrtmp5651;
            CursorTy pvrtmp5653 = (CursorTy) fltPrd4587;
            CursorTy pvrtmp5652 = (CursorTy) fltPrd4586;
            CursorTy y1741 = (CursorTy) pvrtmp5652;
            CursorTy fltPrd4588 = (CursorTy) pvrtmp5650;
            CursorTy fltPrd4589 = (CursorTy) pvrtmp5651;
            CursorTy pvrtmp5655 = (CursorTy) fltPrd4589;
            CursorTy pvrtmp5654 = (CursorTy) fltPrd4588;
            CursorTy end_y1741 = (CursorTy) pvrtmp5655;
            CursorTy end_r1887_3413_3414 = (CursorTy) pvrtmp5648;
            CursorTy endof3263 = (CursorTy) pvrtmp5649;

            *(TagTyPacked *) loc1885 = 0;

            CursorTy writetag3870 = loc1885 + 1;
            CursorTy writecur3871 = (CursorTy) end_y1740;
            CursorTy writecur3872 = (CursorTy) end_y1741;
            CursorTy pvrtmp5657 = (CursorTy) writecur3872;
            CursorTy pvrtmp5656 = (CursorTy) loc1885;
            CursorTy taildc3264 = (CursorTy) pvrtmp5656;
            CursorTy end_taildc3264 = (CursorTy) pvrtmp5657;
            CursorTy pvrtmp5659 = (CursorTy) end_taildc3264;
            CursorTy pvrtmp5658 = (CursorTy) taildc3264;
            CursorTy fltPrd4590 = (CursorTy) pvrtmp5658;
            CursorTy fltPrd4591 = (CursorTy) pvrtmp5659;

            return (CursorCursorCursorCursorProd) {end_r1887_3413_3414,
                                                   endof3263, fltPrd4590,
                                                   fltPrd4591};
            break;
        }

      case 1:
        {
            CursorTy field_cur3874 = (CursorTy) tmpcur5639;
            CursorTy case2594 = (CursorTy) field_cur3874;
            CursorTy x1742 = (CursorTy) case2594;
            CursorTy loc2602 = loc1885 + 1;
            CursorCursorCursorCursorProd tmp_struct155 =
                                          _copy_ListSym(end_r1886, end_r1887, loc2602, x1742);
            CursorTy pvrtmp5660 = tmp_struct155.field0;
            CursorTy pvrtmp5661 = tmp_struct155.field1;
            CursorTy pvrtmp5662 = tmp_struct155.field2;
            CursorTy pvrtmp5663 = tmp_struct155.field3;
            CursorTy fltPrd4592 = (CursorTy) pvrtmp5662;
            CursorTy fltPrd4593 = (CursorTy) pvrtmp5663;
            CursorTy pvrtmp5665 = (CursorTy) fltPrd4593;
            CursorTy pvrtmp5664 = (CursorTy) fltPrd4592;
            CursorTy y1744 = (CursorTy) pvrtmp5664;
            CursorTy fltPrd4594 = (CursorTy) pvrtmp5662;
            CursorTy fltPrd4595 = (CursorTy) pvrtmp5663;
            CursorTy pvrtmp5667 = (CursorTy) fltPrd4595;
            CursorTy pvrtmp5666 = (CursorTy) fltPrd4594;
            CursorTy end_y1744 = (CursorTy) pvrtmp5667;
            CursorTy end_r1887_3415 = (CursorTy) pvrtmp5660;
            CursorTy endof3265 = (CursorTy) pvrtmp5661;
            CursorTy case2595 = (CursorTy) endof3265;
            CursorTy x1743 = (CursorTy) case2595;
            CursorTy loc2603 = (CursorTy) end_y1744;
            CursorCursorCursorCursorProd tmp_struct156 =
                                          _copy_Expr(end_r1886, end_r1887_3415, loc2603, x1743);
            CursorTy pvrtmp5668 = tmp_struct156.field0;
            CursorTy pvrtmp5669 = tmp_struct156.field1;
            CursorTy pvrtmp5670 = tmp_struct156.field2;
            CursorTy pvrtmp5671 = tmp_struct156.field3;
            CursorTy fltPrd4596 = (CursorTy) pvrtmp5670;
            CursorTy fltPrd4597 = (CursorTy) pvrtmp5671;
            CursorTy pvrtmp5673 = (CursorTy) fltPrd4597;
            CursorTy pvrtmp5672 = (CursorTy) fltPrd4596;
            CursorTy y1745 = (CursorTy) pvrtmp5672;
            CursorTy fltPrd4598 = (CursorTy) pvrtmp5670;
            CursorTy fltPrd4599 = (CursorTy) pvrtmp5671;
            CursorTy pvrtmp5675 = (CursorTy) fltPrd4599;
            CursorTy pvrtmp5674 = (CursorTy) fltPrd4598;
            CursorTy end_y1745 = (CursorTy) pvrtmp5675;
            CursorTy end_r1887_3415_3416 = (CursorTy) pvrtmp5668;
            CursorTy endof3266 = (CursorTy) pvrtmp5669;

            *(TagTyPacked *) loc1885 = 1;

            CursorTy writetag3877 = loc1885 + 1;
            CursorTy writecur3878 = (CursorTy) end_y1744;
            CursorTy writecur3879 = (CursorTy) end_y1745;
            CursorTy pvrtmp5677 = (CursorTy) writecur3879;
            CursorTy pvrtmp5676 = (CursorTy) loc1885;
            CursorTy taildc3267 = (CursorTy) pvrtmp5676;
            CursorTy end_taildc3267 = (CursorTy) pvrtmp5677;
            CursorTy pvrtmp5679 = (CursorTy) end_taildc3267;
            CursorTy pvrtmp5678 = (CursorTy) taildc3267;
            CursorTy fltPrd4600 = (CursorTy) pvrtmp5678;
            CursorTy fltPrd4601 = (CursorTy) pvrtmp5679;

            return (CursorCursorCursorCursorProd) {end_r1887_3415_3416,
                                                   endof3266, fltPrd4600,
                                                   fltPrd4601};
            break;
        }

      case 2:
        {
            CursorTy field_cur3881 = (CursorTy) tmpcur5639;
            CursorTy case2606 = (CursorTy) field_cur3881;
            CursorTy x1746 = (CursorTy) case2606;
            CursorTy loc2610 = loc1885 + 1;
            CursorCursorCursorCursorProd tmp_struct157 =
                                          _copy_ListToplvl(end_r1886, end_r1887, loc2610, x1746);
            CursorTy pvrtmp5680 = tmp_struct157.field0;
            CursorTy pvrtmp5681 = tmp_struct157.field1;
            CursorTy pvrtmp5682 = tmp_struct157.field2;
            CursorTy pvrtmp5683 = tmp_struct157.field3;
            CursorTy fltPrd4602 = (CursorTy) pvrtmp5682;
            CursorTy fltPrd4603 = (CursorTy) pvrtmp5683;
            CursorTy pvrtmp5685 = (CursorTy) fltPrd4603;
            CursorTy pvrtmp5684 = (CursorTy) fltPrd4602;
            CursorTy y1747 = (CursorTy) pvrtmp5684;
            CursorTy fltPrd4604 = (CursorTy) pvrtmp5682;
            CursorTy fltPrd4605 = (CursorTy) pvrtmp5683;
            CursorTy pvrtmp5687 = (CursorTy) fltPrd4605;
            CursorTy pvrtmp5686 = (CursorTy) fltPrd4604;
            CursorTy end_y1747 = (CursorTy) pvrtmp5687;
            CursorTy end_r1887_3417 = (CursorTy) pvrtmp5680;
            CursorTy endof3268 = (CursorTy) pvrtmp5681;

            *(TagTyPacked *) loc1885 = 2;

            CursorTy writetag3883 = loc1885 + 1;
            CursorTy writecur3884 = (CursorTy) end_y1747;
            CursorTy pvrtmp5689 = (CursorTy) writecur3884;
            CursorTy pvrtmp5688 = (CursorTy) loc1885;
            CursorTy taildc3269 = (CursorTy) pvrtmp5688;
            CursorTy end_taildc3269 = (CursorTy) pvrtmp5689;
            CursorTy pvrtmp5691 = (CursorTy) end_taildc3269;
            CursorTy pvrtmp5690 = (CursorTy) taildc3269;
            CursorTy fltPrd4606 = (CursorTy) pvrtmp5690;
            CursorTy fltPrd4607 = (CursorTy) pvrtmp5691;

            return (CursorCursorCursorCursorProd) {end_r1887_3417, endof3268,
                                                   fltPrd4606, fltPrd4607};
            break;
        }

      case 3:
        {
            CursorTy field_cur3886 = (CursorTy) tmpcur5639;
            CursorTy case2612 = (CursorTy) field_cur3886;
            CursorTy x1748 = (CursorTy) case2612;
            CursorTy loc2616 = loc1885 + 1;
            // CursorCursorCursorCursorProd tmp_struct158 =
            //                               _copy_Expr(end_r1886, end_r1887, loc2616, x1748);
            CursorCursorCursorCursorProd tmp_struct158 =
                duplicate_expr(3, end_r1886, end_r1887, loc2616, x1748);
            CursorTy pvrtmp5692 = tmp_struct158.field0;
            CursorTy pvrtmp5693 = tmp_struct158.field1;
            CursorTy pvrtmp5694 = tmp_struct158.field2;
            CursorTy pvrtmp5695 = tmp_struct158.field3;
            CursorTy fltPrd4608 = (CursorTy) pvrtmp5694;
            CursorTy fltPrd4609 = (CursorTy) pvrtmp5695;
            CursorTy pvrtmp5697 = (CursorTy) fltPrd4609;
            CursorTy pvrtmp5696 = (CursorTy) fltPrd4608;
            CursorTy y1749 = (CursorTy) pvrtmp5696;
            CursorTy fltPrd4610 = (CursorTy) pvrtmp5694;
            CursorTy fltPrd4611 = (CursorTy) pvrtmp5695;
            CursorTy pvrtmp5699 = (CursorTy) fltPrd4611;
            CursorTy pvrtmp5698 = (CursorTy) fltPrd4610;
            CursorTy end_y1749 = (CursorTy) pvrtmp5699;
            CursorTy end_r1887_3418 = (CursorTy) pvrtmp5692;
            CursorTy endof3270 = (CursorTy) pvrtmp5693;

            *(TagTyPacked *) loc1885 = 3;

            CursorTy writetag3888 = loc1885 + 1;
            CursorTy writecur3889 = (CursorTy) end_y1749;
            CursorTy pvrtmp5701 = (CursorTy) writecur3889;
            CursorTy pvrtmp5700 = (CursorTy) loc1885;
            CursorTy taildc3271 = (CursorTy) pvrtmp5700;
            CursorTy end_taildc3271 = (CursorTy) pvrtmp5701;
            CursorTy pvrtmp5703 = (CursorTy) end_taildc3271;
            CursorTy pvrtmp5702 = (CursorTy) taildc3271;
            CursorTy fltPrd4612 = (CursorTy) pvrtmp5702;
            CursorTy fltPrd4613 = (CursorTy) pvrtmp5703;

            return (CursorCursorCursorCursorProd) {end_r1887_3418, endof3270,
                                                   fltPrd4612, fltPrd4613};
            break;
        }

      case 255:
        {
            CursorTy tmpcur6637 = *(CursorTy *) tmpcur5639;
            CursorTy tmpaftercur6638 = tmpcur5639 + 8;
            TagTyPacked tagtmp6639 = *(TagTyPacked *) tmpcur6637;
            CursorTy tailtmp6640 = tmpcur6637 + 1;

            tmpval5638 = tagtmp6639;
            tmpcur5639 = tailtmp6640;
            goto switch5704;
            break;
        }

      case 254:
        {
            CursorTy tmpcur6637 = *(CursorTy *) tmpcur5639;
            CursorTy tmpaftercur6638 = tmpcur5639 + 8;
            TagTyPacked tagtmp6639 = *(TagTyPacked *) tmpcur6637;
            CursorTy tailtmp6640 = tmpcur6637 + 1;

            tmpval5638 = tagtmp6639;
            tmpcur5639 = tailtmp6640;
            goto switch5704;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5638");
            exit(1);
        }
    }
}


// --------------------------------------------------------------------------------
// Printers

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
    // printf("copied: %lld\n", copied);
}
