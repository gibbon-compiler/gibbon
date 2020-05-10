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

CursorCursorCursorCursorProd _copy_ListSym(CursorTy end_r1955,
                                           CursorTy end_r1956, CursorTy loc1954,
                                           CursorTy arg1566)
{
    CursorTy loc1953 = (CursorTy) arg1566;

    if (loc1954 + 18 > end_r1956) {
        ChunkTy new_chunk58 = alloc_chunk(end_r1956);
        CursorTy chunk_start59 = new_chunk58.start_ptr;
        CursorTy chunk_end60 = new_chunk58.end_ptr;

        end_r1956 = chunk_end60;
        *(TagTyPacked *) loc1954 = 255;

        CursorTy redir = loc1954 + 1;

        *(CursorTy *) redir = chunk_start59;
        loc1954 = chunk_start59;
    }

    CursorTy loc2299 = loc1954 + 1;
    CursorTy loc2300 = loc2299 + 8;
    TagTyPacked tmpval5559 = *(TagTyPacked *) arg1566;
    CursorTy tmpcur5560 = arg1566 + 1;


  switch5579:
    ;
    switch (tmpval5559) {

      case 0:
        {
            CursorTy field_cur3951 = (CursorTy) tmpcur5560;
            CursorTy case2294 = (CursorTy) field_cur3951;
            SymTy tmpval5561 = *(SymTy *) case2294;
            CursorTy tmpcur5562 = case2294 + sizeof(SymTy);
            SymTy x1567 = (SymTy) tmpval5561;
            CursorTy end_x1567 = (CursorTy) tmpcur5562;
            CursorTy case2295 = (CursorTy) end_x1567;
            CursorTy x1568 = (CursorTy) case2295;
            CursorTy jump3383 = case2294 + 8;
            CursorCursorCursorCursorProd tmp_struct57 =
                                          _copy_ListSym(end_r1955, end_r1956, loc2300, x1568);
            CursorTy pvrtmp5563 = tmp_struct57.field0;
            CursorTy pvrtmp5564 = tmp_struct57.field1;
            CursorTy pvrtmp5565 = tmp_struct57.field2;
            CursorTy pvrtmp5566 = tmp_struct57.field3;
            CursorTy fltPrd4825 = (CursorTy) pvrtmp5565;
            CursorTy fltPrd4826 = (CursorTy) pvrtmp5566;
            CursorTy pvrtmp5568 = (CursorTy) fltPrd4826;
            CursorTy pvrtmp5567 = (CursorTy) fltPrd4825;
            CursorTy y1570 = (CursorTy) pvrtmp5567;
            CursorTy fltPrd4827 = (CursorTy) pvrtmp5565;
            CursorTy fltPrd4828 = (CursorTy) pvrtmp5566;
            CursorTy pvrtmp5570 = (CursorTy) fltPrd4828;
            CursorTy pvrtmp5569 = (CursorTy) fltPrd4827;
            CursorTy end_y1570 = (CursorTy) pvrtmp5570;
            CursorTy end_r1956_3713 = (CursorTy) pvrtmp5563;
            CursorTy endof3384 = (CursorTy) pvrtmp5564;

            *(TagTyPacked *) loc1954 = 0;

            CursorTy writetag3954 = loc1954 + 1;

            *(SymTy *) writetag3954 = x1567;

            CursorTy writecur3955 = writetag3954 + sizeof(SymTy);
            CursorTy writecur3956 = (CursorTy) end_y1570;
            CursorTy pvrtmp5572 = (CursorTy) writecur3956;
            CursorTy pvrtmp5571 = (CursorTy) loc1954;
            CursorTy taildc3385 = (CursorTy) pvrtmp5571;
            CursorTy end_taildc3385 = (CursorTy) pvrtmp5572;
            CursorTy pvrtmp5574 = (CursorTy) end_taildc3385;
            CursorTy pvrtmp5573 = (CursorTy) taildc3385;
            CursorTy fltPrd4829 = (CursorTy) pvrtmp5573;
            CursorTy fltPrd4830 = (CursorTy) pvrtmp5574;

            return (CursorCursorCursorCursorProd) {end_r1956_3713, endof3384,
                                                   fltPrd4829, fltPrd4830};
            break;
        }

      case 1:
        {
            CursorTy field_cur3958 = (CursorTy) tmpcur5560;
            CursorTy jump3386 = loc1953 + 1;

            *(TagTyPacked *) loc1954 = 1;

            CursorTy writetag3959 = loc1954 + 1;
            CursorTy pvrtmp5576 = (CursorTy) writetag3959;
            CursorTy pvrtmp5575 = (CursorTy) loc1954;
            CursorTy taildc3387 = (CursorTy) pvrtmp5575;
            CursorTy end_taildc3387 = (CursorTy) pvrtmp5576;
            CursorTy pvrtmp5578 = (CursorTy) end_taildc3387;
            CursorTy pvrtmp5577 = (CursorTy) taildc3387;
            CursorTy fltPrd4831 = (CursorTy) pvrtmp5577;
            CursorTy fltPrd4832 = (CursorTy) pvrtmp5578;

            return (CursorCursorCursorCursorProd) {end_r1956, jump3386,
                                                   fltPrd4831, fltPrd4832};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7286 = *(CursorTy *) tmpcur5560;
            CursorTy tmpaftercur7287 = tmpcur5560 + 8;
            TagTyPacked tagtmp7288 = *(TagTyPacked *) tmpcur7286;
            CursorTy tailtmp7289 = tmpcur7286 + 1;

            tmpval5559 = tagtmp7288;
            tmpcur5560 = tailtmp7289;
            goto switch5579;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7286 = *(CursorTy *) tmpcur5560;
            CursorTy tmpaftercur7287 = tmpcur5560 + 8;
            TagTyPacked tagtmp7288 = *(TagTyPacked *) tmpcur7286;
            CursorTy tailtmp7289 = tmpcur7286 + 1;

            tmpval5559 = tagtmp7288;
            tmpcur5560 = tailtmp7289;
            goto switch5579;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5559");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_ListExpr(CursorTy end_r1961,
                                            CursorTy end_r1962,
                                            CursorTy loc1960, CursorTy arg1576)
{
    CursorTy loc1959 = (CursorTy) arg1576;

    if (loc1960 + 18 > end_r1962) {
        ChunkTy new_chunk64 = alloc_chunk(end_r1962);
        CursorTy chunk_start65 = new_chunk64.start_ptr;
        CursorTy chunk_end66 = new_chunk64.end_ptr;

        end_r1962 = chunk_end66;
        *(TagTyPacked *) loc1960 = 255;

        CursorTy redir = loc1960 + 1;

        *(CursorTy *) redir = chunk_start65;
        loc1960 = chunk_start65;
    }

    TagTyPacked tmpval5587 = *(TagTyPacked *) arg1576;
    CursorTy tmpcur5588 = arg1576 + 1;


  switch5613:
    ;
    switch (tmpval5587) {

      case 0:
        {
            CursorTy field_cur3965 = (CursorTy) tmpcur5588;
            CursorTy case2313 = (CursorTy) field_cur3965;
            CursorTy x1577 = (CursorTy) case2313;
            CursorTy loc2321 = loc1960 + 1;
            CursorCursorCursorCursorProd tmp_struct62 =
                                          _copy_Expr(end_r1961, end_r1962, loc2321, x1577);
            CursorTy pvrtmp5589 = tmp_struct62.field0;
            CursorTy pvrtmp5590 = tmp_struct62.field1;
            CursorTy pvrtmp5591 = tmp_struct62.field2;
            CursorTy pvrtmp5592 = tmp_struct62.field3;
            CursorTy fltPrd4833 = (CursorTy) pvrtmp5591;
            CursorTy fltPrd4834 = (CursorTy) pvrtmp5592;
            CursorTy pvrtmp5594 = (CursorTy) fltPrd4834;
            CursorTy pvrtmp5593 = (CursorTy) fltPrd4833;
            CursorTy y1579 = (CursorTy) pvrtmp5593;
            CursorTy fltPrd4835 = (CursorTy) pvrtmp5591;
            CursorTy fltPrd4836 = (CursorTy) pvrtmp5592;
            CursorTy pvrtmp5596 = (CursorTy) fltPrd4836;
            CursorTy pvrtmp5595 = (CursorTy) fltPrd4835;
            CursorTy end_y1579 = (CursorTy) pvrtmp5596;
            CursorTy end_r1962_3714 = (CursorTy) pvrtmp5589;
            CursorTy endof3393 = (CursorTy) pvrtmp5590;
            CursorTy case2314 = (CursorTy) endof3393;
            CursorTy x1578 = (CursorTy) case2314;
            CursorTy loc2322 = (CursorTy) end_y1579;
            CursorCursorCursorCursorProd tmp_struct63 =
                                          _copy_ListExpr(end_r1961, end_r1962_3714, loc2322, x1578);
            CursorTy pvrtmp5597 = tmp_struct63.field0;
            CursorTy pvrtmp5598 = tmp_struct63.field1;
            CursorTy pvrtmp5599 = tmp_struct63.field2;
            CursorTy pvrtmp5600 = tmp_struct63.field3;
            CursorTy fltPrd4837 = (CursorTy) pvrtmp5599;
            CursorTy fltPrd4838 = (CursorTy) pvrtmp5600;
            CursorTy pvrtmp5602 = (CursorTy) fltPrd4838;
            CursorTy pvrtmp5601 = (CursorTy) fltPrd4837;
            CursorTy y1580 = (CursorTy) pvrtmp5601;
            CursorTy fltPrd4839 = (CursorTy) pvrtmp5599;
            CursorTy fltPrd4840 = (CursorTy) pvrtmp5600;
            CursorTy pvrtmp5604 = (CursorTy) fltPrd4840;
            CursorTy pvrtmp5603 = (CursorTy) fltPrd4839;
            CursorTy end_y1580 = (CursorTy) pvrtmp5604;
            CursorTy end_r1962_3714_3715 = (CursorTy) pvrtmp5597;
            CursorTy endof3394 = (CursorTy) pvrtmp5598;

            *(TagTyPacked *) loc1960 = 0;

            CursorTy writetag3968 = loc1960 + 1;
            CursorTy writecur3969 = (CursorTy) end_y1579;
            CursorTy writecur3970 = (CursorTy) end_y1580;
            CursorTy pvrtmp5606 = (CursorTy) writecur3970;
            CursorTy pvrtmp5605 = (CursorTy) loc1960;
            CursorTy taildc3395 = (CursorTy) pvrtmp5605;
            CursorTy end_taildc3395 = (CursorTy) pvrtmp5606;
            CursorTy pvrtmp5608 = (CursorTy) end_taildc3395;
            CursorTy pvrtmp5607 = (CursorTy) taildc3395;
            CursorTy fltPrd4841 = (CursorTy) pvrtmp5607;
            CursorTy fltPrd4842 = (CursorTy) pvrtmp5608;

            return (CursorCursorCursorCursorProd) {end_r1962_3714_3715,
                                                   endof3394, fltPrd4841,
                                                   fltPrd4842};
            break;
        }

      case 1:
        {
            CursorTy field_cur3972 = (CursorTy) tmpcur5588;
            CursorTy jump3396 = loc1959 + 1;

            *(TagTyPacked *) loc1960 = 1;

            CursorTy writetag3973 = loc1960 + 1;
            CursorTy pvrtmp5610 = (CursorTy) writetag3973;
            CursorTy pvrtmp5609 = (CursorTy) loc1960;
            CursorTy taildc3397 = (CursorTy) pvrtmp5609;
            CursorTy end_taildc3397 = (CursorTy) pvrtmp5610;
            CursorTy pvrtmp5612 = (CursorTy) end_taildc3397;
            CursorTy pvrtmp5611 = (CursorTy) taildc3397;
            CursorTy fltPrd4843 = (CursorTy) pvrtmp5611;
            CursorTy fltPrd4844 = (CursorTy) pvrtmp5612;

            return (CursorCursorCursorCursorProd) {end_r1962, jump3396,
                                                   fltPrd4843, fltPrd4844};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7294 = *(CursorTy *) tmpcur5588;
            CursorTy tmpaftercur7295 = tmpcur5588 + 8;
            TagTyPacked tagtmp7296 = *(TagTyPacked *) tmpcur7294;
            CursorTy tailtmp7297 = tmpcur7294 + 1;

            tmpval5587 = tagtmp7296;
            tmpcur5588 = tailtmp7297;
            goto switch5613;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7294 = *(CursorTy *) tmpcur5588;
            CursorTy tmpaftercur7295 = tmpcur5588 + 8;
            TagTyPacked tagtmp7296 = *(TagTyPacked *) tmpcur7294;
            CursorTy tailtmp7297 = tmpcur7294 + 1;

            tmpval5587 = tagtmp7296;
            tmpcur5588 = tailtmp7297;
            goto switch5613;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5587");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_ListToplvl(CursorTy end_r1967,
                                              CursorTy end_r1968,
                                              CursorTy loc1966,
                                              CursorTy arg1586)
{
    CursorTy loc1965 = (CursorTy) arg1586;

    if (loc1966 + 26 > end_r1968) {
        ChunkTy new_chunk75 = alloc_chunk(end_r1968);
        CursorTy chunk_start76 = new_chunk75.start_ptr;
        CursorTy chunk_end77 = new_chunk75.end_ptr;

        end_r1968 = chunk_end77;
        *(TagTyPacked *) loc1966 = 255;

        CursorTy redir = loc1966 + 1;

        *(CursorTy *) redir = chunk_start76;
        loc1966 = chunk_start76;
    }

    CursorTy loc2358 = loc1966 + 1;
    CursorTy loc2359 = loc2358 + 8;
    CursorTy loc2375 = loc1966 + 1;
    CursorTy loc2376 = loc2375 + 8;
    CursorTy loc2377 = loc2376 + 8;
    TagTyPacked tmpval5621 = *(TagTyPacked *) arg1586;
    CursorTy tmpcur5622 = arg1586 + 1;


  switch5693:
    ;
    switch (tmpval5621) {

      case 0:
        {
            CursorTy field_cur3979 = (CursorTy) tmpcur5622;
            CursorTy case2336 = (CursorTy) field_cur3979;
            CursorTy x1587 = (CursorTy) case2336;
            CursorTy loc2344 = loc1966 + 1;
            CursorCursorCursorCursorProd tmp_struct69 =
                                          _copy_Toplvl(end_r1967, end_r1968, loc2344, x1587);
            CursorTy pvrtmp5623 = tmp_struct69.field0;
            CursorTy pvrtmp5624 = tmp_struct69.field1;
            CursorTy pvrtmp5625 = tmp_struct69.field2;
            CursorTy pvrtmp5626 = tmp_struct69.field3;
            CursorTy fltPrd4845 = (CursorTy) pvrtmp5625;
            CursorTy fltPrd4846 = (CursorTy) pvrtmp5626;
            CursorTy pvrtmp5628 = (CursorTy) fltPrd4846;
            CursorTy pvrtmp5627 = (CursorTy) fltPrd4845;
            CursorTy y1589 = (CursorTy) pvrtmp5627;
            CursorTy fltPrd4847 = (CursorTy) pvrtmp5625;
            CursorTy fltPrd4848 = (CursorTy) pvrtmp5626;
            CursorTy pvrtmp5630 = (CursorTy) fltPrd4848;
            CursorTy pvrtmp5629 = (CursorTy) fltPrd4847;
            CursorTy end_y1589 = (CursorTy) pvrtmp5630;
            CursorTy end_r1968_3716 = (CursorTy) pvrtmp5623;
            CursorTy endof3403 = (CursorTy) pvrtmp5624;
            CursorTy case2337 = (CursorTy) endof3403;
            CursorTy x1588 = (CursorTy) case2337;
            CursorTy loc2345 = (CursorTy) end_y1589;
            CursorCursorCursorCursorProd tmp_struct70 =
                                          _copy_ListToplvl(end_r1967, end_r1968_3716, loc2345, x1588);
            CursorTy pvrtmp5631 = tmp_struct70.field0;
            CursorTy pvrtmp5632 = tmp_struct70.field1;
            CursorTy pvrtmp5633 = tmp_struct70.field2;
            CursorTy pvrtmp5634 = tmp_struct70.field3;
            CursorTy fltPrd4849 = (CursorTy) pvrtmp5633;
            CursorTy fltPrd4850 = (CursorTy) pvrtmp5634;
            CursorTy pvrtmp5636 = (CursorTy) fltPrd4850;
            CursorTy pvrtmp5635 = (CursorTy) fltPrd4849;
            CursorTy y1590 = (CursorTy) pvrtmp5635;
            CursorTy fltPrd4851 = (CursorTy) pvrtmp5633;
            CursorTy fltPrd4852 = (CursorTy) pvrtmp5634;
            CursorTy pvrtmp5638 = (CursorTy) fltPrd4852;
            CursorTy pvrtmp5637 = (CursorTy) fltPrd4851;
            CursorTy end_y1590 = (CursorTy) pvrtmp5638;
            CursorTy end_r1968_3716_3717 = (CursorTy) pvrtmp5631;
            CursorTy endof3404 = (CursorTy) pvrtmp5632;

            *(TagTyPacked *) loc1966 = 0;

            CursorTy writetag3982 = loc1966 + 1;
            CursorTy writecur3983 = (CursorTy) end_y1589;
            CursorTy writecur3984 = (CursorTy) end_y1590;
            CursorTy pvrtmp5640 = (CursorTy) writecur3984;
            CursorTy pvrtmp5639 = (CursorTy) loc1966;
            CursorTy taildc3405 = (CursorTy) pvrtmp5639;
            CursorTy end_taildc3405 = (CursorTy) pvrtmp5640;
            CursorTy pvrtmp5642 = (CursorTy) end_taildc3405;
            CursorTy pvrtmp5641 = (CursorTy) taildc3405;
            CursorTy fltPrd4853 = (CursorTy) pvrtmp5641;
            CursorTy fltPrd4854 = (CursorTy) pvrtmp5642;

            return (CursorCursorCursorCursorProd) {end_r1968_3716_3717,
                                                   endof3404, fltPrd4853,
                                                   fltPrd4854};
            break;
        }

      case 1:
        {
            CursorTy field_cur3986 = (CursorTy) tmpcur5622;
            CursorTy jump3406 = loc1965 + 1;

            *(TagTyPacked *) loc1966 = 1;

            CursorTy writetag3987 = loc1966 + 1;
            CursorTy pvrtmp5644 = (CursorTy) writetag3987;
            CursorTy pvrtmp5643 = (CursorTy) loc1966;
            CursorTy taildc3407 = (CursorTy) pvrtmp5643;
            CursorTy end_taildc3407 = (CursorTy) pvrtmp5644;
            CursorTy pvrtmp5646 = (CursorTy) end_taildc3407;
            CursorTy pvrtmp5645 = (CursorTy) taildc3407;
            CursorTy fltPrd4855 = (CursorTy) pvrtmp5645;
            CursorTy fltPrd4856 = (CursorTy) pvrtmp5646;

            return (CursorCursorCursorCursorProd) {end_r1968, jump3406,
                                                   fltPrd4855, fltPrd4856};
            break;
        }

      case 2:
        {
            CursorTy field_cur3989 = (CursorTy) tmpcur5622;
            CursorTy tmpcur5647 = *(CursorTy *) field_cur3989;
            CursorTy tmpaftercur5648 = field_cur3989 + 8;
            CursorTy case2349 = (CursorTy) field_cur3989;
            CursorTy x1591 = (CursorTy) tmpcur5647;
            CursorTy end_x1591 = (CursorTy) tmpaftercur5648;
            CursorTy case2350 = (CursorTy) end_x1591;
            CursorTy x1592 = (CursorTy) case2350;
            CursorTy case2351 = (CursorTy) x1591;
            CursorTy x1593 = (CursorTy) case2351;
            CursorTy jump3408 = case2349 + 8;
            CursorCursorCursorCursorProd tmp_struct71 =
                                          _copy_Toplvl(end_r1967, end_r1968, loc2359, x1592);
            CursorTy pvrtmp5649 = tmp_struct71.field0;
            CursorTy pvrtmp5650 = tmp_struct71.field1;
            CursorTy pvrtmp5651 = tmp_struct71.field2;
            CursorTy pvrtmp5652 = tmp_struct71.field3;
            CursorTy fltPrd4857 = (CursorTy) pvrtmp5651;
            CursorTy fltPrd4858 = (CursorTy) pvrtmp5652;
            CursorTy pvrtmp5654 = (CursorTy) fltPrd4858;
            CursorTy pvrtmp5653 = (CursorTy) fltPrd4857;
            CursorTy y1595 = (CursorTy) pvrtmp5653;
            CursorTy fltPrd4859 = (CursorTy) pvrtmp5651;
            CursorTy fltPrd4860 = (CursorTy) pvrtmp5652;
            CursorTy pvrtmp5656 = (CursorTy) fltPrd4860;
            CursorTy pvrtmp5655 = (CursorTy) fltPrd4859;
            CursorTy end_y1595 = (CursorTy) pvrtmp5656;
            CursorTy end_r1968_3718 = (CursorTy) pvrtmp5649;
            CursorTy endof3409 = (CursorTy) pvrtmp5650;
            CursorTy loc2360 = (CursorTy) end_y1595;
            CursorCursorCursorCursorProd tmp_struct72 =
                                          _copy_ListToplvl(end_r1967, end_r1968_3718, loc2360, x1593);
            CursorTy pvrtmp5657 = tmp_struct72.field0;
            CursorTy pvrtmp5658 = tmp_struct72.field1;
            CursorTy pvrtmp5659 = tmp_struct72.field2;
            CursorTy pvrtmp5660 = tmp_struct72.field3;
            CursorTy fltPrd4861 = (CursorTy) pvrtmp5659;
            CursorTy fltPrd4862 = (CursorTy) pvrtmp5660;
            CursorTy pvrtmp5662 = (CursorTy) fltPrd4862;
            CursorTy pvrtmp5661 = (CursorTy) fltPrd4861;
            CursorTy y1596 = (CursorTy) pvrtmp5661;
            CursorTy fltPrd4863 = (CursorTy) pvrtmp5659;
            CursorTy fltPrd4864 = (CursorTy) pvrtmp5660;
            CursorTy pvrtmp5664 = (CursorTy) fltPrd4864;
            CursorTy pvrtmp5663 = (CursorTy) fltPrd4863;
            CursorTy end_y1596 = (CursorTy) pvrtmp5664;
            CursorTy end_r1968_3718_3719 = (CursorTy) pvrtmp5657;
            CursorTy endof3410 = (CursorTy) pvrtmp5658;
            CursorTy y1594 = (CursorTy) end_y1595;

            *(TagTyPacked *) loc1966 = 2;

            CursorTy writetag3993 = loc1966 + 1;

            *(CursorTy *) writetag3993 = y1594;

            CursorTy writecur3994 = writetag3993 + 8;
            CursorTy writecur3995 = (CursorTy) end_y1595;
            CursorTy writecur3996 = (CursorTy) end_y1596;
            CursorTy pvrtmp5666 = (CursorTy) writecur3996;
            CursorTy pvrtmp5665 = (CursorTy) loc1966;
            CursorTy taildc3411 = (CursorTy) pvrtmp5665;
            CursorTy end_taildc3411 = (CursorTy) pvrtmp5666;
            CursorTy pvrtmp5668 = (CursorTy) end_taildc3411;
            CursorTy pvrtmp5667 = (CursorTy) taildc3411;
            CursorTy fltPrd4865 = (CursorTy) pvrtmp5667;
            CursorTy fltPrd4866 = (CursorTy) pvrtmp5668;

            return (CursorCursorCursorCursorProd) {end_r1968_3718_3719,
                                                   endof3410, fltPrd4865,
                                                   fltPrd4866};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7302 = *(CursorTy *) tmpcur5622;
            CursorTy tmpaftercur7303 = tmpcur5622 + 8;
            TagTyPacked tagtmp7304 = *(TagTyPacked *) tmpcur7302;
            CursorTy tailtmp7305 = tmpcur7302 + 1;

            tmpval5621 = tagtmp7304;
            tmpcur5622 = tailtmp7305;
            goto switch5693;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7302 = *(CursorTy *) tmpcur5622;
            CursorTy tmpaftercur7303 = tmpcur5622 + 8;
            TagTyPacked tagtmp7304 = *(TagTyPacked *) tmpcur7302;
            CursorTy tailtmp7305 = tmpcur7302 + 1;

            tmpval5621 = tagtmp7304;
            tmpcur5622 = tailtmp7305;
            goto switch5693;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5621");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_Formals(CursorTy end_r1973,
                                           CursorTy end_r1974, CursorTy loc1972,
                                           CursorTy arg1624)
{
    CursorTy loc1971 = (CursorTy) arg1624;

    if (loc1972 + 18 > end_r1974) {
        ChunkTy new_chunk86 = alloc_chunk(end_r1974);
        CursorTy chunk_start87 = new_chunk86.start_ptr;
        CursorTy chunk_end88 = new_chunk86.end_ptr;

        end_r1974 = chunk_end88;
        *(TagTyPacked *) loc1972 = 255;

        CursorTy redir = loc1972 + 1;

        *(CursorTy *) redir = chunk_start87;
        loc1972 = chunk_start87;
    }

    TagTyPacked tmpval5715 = *(TagTyPacked *) arg1624;
    CursorTy tmpcur5716 = arg1624 + 1;


  switch5749:
    ;
    switch (tmpval5715) {

      case 0:
        {
            CursorTy field_cur4026 = (CursorTy) tmpcur5716;
            CursorTy case2410 = (CursorTy) field_cur4026;
            CursorTy x1625 = (CursorTy) case2410;
            CursorTy loc2414 = loc1972 + 1;
            CursorCursorCursorCursorProd tmp_struct84 =
                                          _copy_ListSym(end_r1973, end_r1974, loc2414, x1625);
            CursorTy pvrtmp5717 = tmp_struct84.field0;
            CursorTy pvrtmp5718 = tmp_struct84.field1;
            CursorTy pvrtmp5719 = tmp_struct84.field2;
            CursorTy pvrtmp5720 = tmp_struct84.field3;
            CursorTy fltPrd4877 = (CursorTy) pvrtmp5719;
            CursorTy fltPrd4878 = (CursorTy) pvrtmp5720;
            CursorTy pvrtmp5722 = (CursorTy) fltPrd4878;
            CursorTy pvrtmp5721 = (CursorTy) fltPrd4877;
            CursorTy y1626 = (CursorTy) pvrtmp5721;
            CursorTy fltPrd4879 = (CursorTy) pvrtmp5719;
            CursorTy fltPrd4880 = (CursorTy) pvrtmp5720;
            CursorTy pvrtmp5724 = (CursorTy) fltPrd4880;
            CursorTy pvrtmp5723 = (CursorTy) fltPrd4879;
            CursorTy end_y1626 = (CursorTy) pvrtmp5724;
            CursorTy end_r1974_3722 = (CursorTy) pvrtmp5717;
            CursorTy endof3431 = (CursorTy) pvrtmp5718;

            *(TagTyPacked *) loc1972 = 0;

            CursorTy writetag4028 = loc1972 + 1;
            CursorTy writecur4029 = (CursorTy) end_y1626;
            CursorTy pvrtmp5726 = (CursorTy) writecur4029;
            CursorTy pvrtmp5725 = (CursorTy) loc1972;
            CursorTy taildc3432 = (CursorTy) pvrtmp5725;
            CursorTy end_taildc3432 = (CursorTy) pvrtmp5726;
            CursorTy pvrtmp5728 = (CursorTy) end_taildc3432;
            CursorTy pvrtmp5727 = (CursorTy) taildc3432;
            CursorTy fltPrd4881 = (CursorTy) pvrtmp5727;
            CursorTy fltPrd4882 = (CursorTy) pvrtmp5728;

            return (CursorCursorCursorCursorProd) {end_r1974_3722, endof3431,
                                                   fltPrd4881, fltPrd4882};
            break;
        }

      case 1:
        {
            CursorTy field_cur4031 = (CursorTy) tmpcur5716;
            CursorTy case2416 = (CursorTy) field_cur4031;
            CursorTy x1627 = (CursorTy) case2416;
            CursorTy loc2421 = loc1972 + 1;
            CursorCursorCursorCursorProd tmp_struct85 =
                                          _copy_ListSym(end_r1973, end_r1974, loc2421, x1627);
            CursorTy pvrtmp5729 = tmp_struct85.field0;
            CursorTy pvrtmp5730 = tmp_struct85.field1;
            CursorTy pvrtmp5731 = tmp_struct85.field2;
            CursorTy pvrtmp5732 = tmp_struct85.field3;
            CursorTy fltPrd4883 = (CursorTy) pvrtmp5731;
            CursorTy fltPrd4884 = (CursorTy) pvrtmp5732;
            CursorTy pvrtmp5734 = (CursorTy) fltPrd4884;
            CursorTy pvrtmp5733 = (CursorTy) fltPrd4883;
            CursorTy y1629 = (CursorTy) pvrtmp5733;
            CursorTy fltPrd4885 = (CursorTy) pvrtmp5731;
            CursorTy fltPrd4886 = (CursorTy) pvrtmp5732;
            CursorTy pvrtmp5736 = (CursorTy) fltPrd4886;
            CursorTy pvrtmp5735 = (CursorTy) fltPrd4885;
            CursorTy end_y1629 = (CursorTy) pvrtmp5736;
            CursorTy end_r1974_3723 = (CursorTy) pvrtmp5729;
            CursorTy endof3434 = (CursorTy) pvrtmp5730;
            CursorTy case2417 = (CursorTy) endof3434;
            CursorTy jump3433 = case2417 + 8;
            SymTy tmpval5737 = *(SymTy *) case2417;
            CursorTy tmpcur5738 = case2417 + sizeof(SymTy);
            SymTy x1628 = (SymTy) tmpval5737;
            CursorTy end_x1628 = (CursorTy) tmpcur5738;

            *(TagTyPacked *) loc1972 = 1;

            CursorTy writetag4034 = loc1972 + 1;
            CursorTy writecur4035 = (CursorTy) end_y1629;

            *(SymTy *) writecur4035 = x1628;

            CursorTy writecur4036 = writecur4035 + sizeof(SymTy);
            CursorTy pvrtmp5740 = (CursorTy) writecur4036;
            CursorTy pvrtmp5739 = (CursorTy) loc1972;
            CursorTy taildc3435 = (CursorTy) pvrtmp5739;
            CursorTy end_taildc3435 = (CursorTy) pvrtmp5740;
            CursorTy pvrtmp5742 = (CursorTy) end_taildc3435;
            CursorTy pvrtmp5741 = (CursorTy) taildc3435;
            CursorTy fltPrd4887 = (CursorTy) pvrtmp5741;
            CursorTy fltPrd4888 = (CursorTy) pvrtmp5742;

            return (CursorCursorCursorCursorProd) {end_r1974_3723, jump3433,
                                                   fltPrd4887, fltPrd4888};
            break;
        }

      case 2:
        {
            CursorTy field_cur4038 = (CursorTy) tmpcur5716;
            CursorTy case2426 = (CursorTy) field_cur4038;
            SymTy tmpval5743 = *(SymTy *) case2426;
            CursorTy tmpcur5744 = case2426 + sizeof(SymTy);
            SymTy x1631 = (SymTy) tmpval5743;
            CursorTy end_x1631 = (CursorTy) tmpcur5744;
            CursorTy jump3436 = case2426 + 8;

            *(TagTyPacked *) loc1972 = 2;

            CursorTy writetag4040 = loc1972 + 1;

            *(SymTy *) writetag4040 = x1631;

            CursorTy writecur4041 = writetag4040 + sizeof(SymTy);
            CursorTy pvrtmp5746 = (CursorTy) writecur4041;
            CursorTy pvrtmp5745 = (CursorTy) loc1972;
            CursorTy taildc3437 = (CursorTy) pvrtmp5745;
            CursorTy end_taildc3437 = (CursorTy) pvrtmp5746;
            CursorTy pvrtmp5748 = (CursorTy) end_taildc3437;
            CursorTy pvrtmp5747 = (CursorTy) taildc3437;
            CursorTy fltPrd4889 = (CursorTy) pvrtmp5747;
            CursorTy fltPrd4890 = (CursorTy) pvrtmp5748;

            return (CursorCursorCursorCursorProd) {end_r1974, jump3436,
                                                   fltPrd4889, fltPrd4890};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7310 = *(CursorTy *) tmpcur5716;
            CursorTy tmpaftercur7311 = tmpcur5716 + 8;
            TagTyPacked tagtmp7312 = *(TagTyPacked *) tmpcur7310;
            CursorTy tailtmp7313 = tmpcur7310 + 1;

            tmpval5715 = tagtmp7312;
            tmpcur5716 = tailtmp7313;
            goto switch5749;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7310 = *(CursorTy *) tmpcur5716;
            CursorTy tmpaftercur7311 = tmpcur5716 + 8;
            TagTyPacked tagtmp7312 = *(TagTyPacked *) tmpcur7310;
            CursorTy tailtmp7313 = tmpcur7310 + 1;

            tmpval5715 = tagtmp7312;
            tmpcur5716 = tailtmp7313;
            goto switch5749;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5715");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_Datum(CursorTy end_r1979, CursorTy end_r1980,
                                         CursorTy loc1978, CursorTy arg1642)
{
    CursorTy loc1977 = (CursorTy) arg1642;

    if (loc1978 + 18 > end_r1980) {
        ChunkTy new_chunk91 = alloc_chunk(end_r1980);
        CursorTy chunk_start92 = new_chunk91.start_ptr;
        CursorTy chunk_end93 = new_chunk91.end_ptr;

        end_r1980 = chunk_end93;
        *(TagTyPacked *) loc1978 = 255;

        CursorTy redir = loc1978 + 1;

        *(CursorTy *) redir = chunk_start92;
        loc1978 = chunk_start92;
    }

    TagTyPacked tmpval5761 = *(TagTyPacked *) arg1642;
    CursorTy tmpcur5762 = arg1642 + 1;


  switch5769:
    ;
    switch (tmpval5761) {

      case 0:
        {
            CursorTy field_cur4050 = (CursorTy) tmpcur5762;
            CursorTy case2442 = (CursorTy) field_cur4050;
            IntTy tmpval5763 = *(IntTy *) case2442;
            CursorTy tmpcur5764 = case2442 + sizeof(IntTy);
            IntTy x1643 = (IntTy) tmpval5763;
            CursorTy end_x1643 = (CursorTy) tmpcur5764;
            CursorTy jump3445 = case2442 + 8;

            *(TagTyPacked *) loc1978 = 0;

            CursorTy writetag4052 = loc1978 + 1;

            *(IntTy *) writetag4052 = x1643;

            CursorTy writecur4053 = writetag4052 + sizeof(IntTy);
            CursorTy pvrtmp5766 = (CursorTy) writecur4053;
            CursorTy pvrtmp5765 = (CursorTy) loc1978;
            CursorTy taildc3446 = (CursorTy) pvrtmp5765;
            CursorTy end_taildc3446 = (CursorTy) pvrtmp5766;
            CursorTy pvrtmp5768 = (CursorTy) end_taildc3446;
            CursorTy pvrtmp5767 = (CursorTy) taildc3446;
            CursorTy fltPrd4891 = (CursorTy) pvrtmp5767;
            CursorTy fltPrd4892 = (CursorTy) pvrtmp5768;

            return (CursorCursorCursorCursorProd) {end_r1980, jump3445,
                                                   fltPrd4891, fltPrd4892};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7318 = *(CursorTy *) tmpcur5762;
            CursorTy tmpaftercur7319 = tmpcur5762 + 8;
            TagTyPacked tagtmp7320 = *(TagTyPacked *) tmpcur7318;
            CursorTy tailtmp7321 = tmpcur7318 + 1;

            tmpval5761 = tagtmp7320;
            tmpcur5762 = tailtmp7321;
            goto switch5769;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7318 = *(CursorTy *) tmpcur5762;
            CursorTy tmpaftercur7319 = tmpcur5762 + 8;
            TagTyPacked tagtmp7320 = *(TagTyPacked *) tmpcur7318;
            CursorTy tailtmp7321 = tmpcur7318 + 1;

            tmpval5761 = tagtmp7320;
            tmpcur5762 = tailtmp7321;
            goto switch5769;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5761");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_LAMBDACASE(CursorTy end_r1985,
                                              CursorTy end_r1986,
                                              CursorTy loc1984,
                                              CursorTy arg1648)
{
    CursorTy loc1983 = (CursorTy) arg1648;

    if (loc1984 + 18 > end_r1986) {
        ChunkTy new_chunk97 = alloc_chunk(end_r1986);
        CursorTy chunk_start98 = new_chunk97.start_ptr;
        CursorTy chunk_end99 = new_chunk97.end_ptr;

        end_r1986 = chunk_end99;
        *(TagTyPacked *) loc1984 = 255;

        CursorTy redir = loc1984 + 1;

        *(CursorTy *) redir = chunk_start98;
        loc1984 = chunk_start98;
    }

    TagTyPacked tmpval5775 = *(TagTyPacked *) arg1648;
    CursorTy tmpcur5776 = arg1648 + 1;


  switch5809:
    ;
    switch (tmpval5775) {

      case 0:
        {
            CursorTy field_cur4057 = (CursorTy) tmpcur5776;
            CursorTy case2451 = (CursorTy) field_cur4057;
            CursorTy x1649 = (CursorTy) case2451;
            CursorTy loc2463 = loc1984 + 1;
            CursorCursorCursorCursorProd tmp_struct94 =
                                          _copy_Formals(end_r1985, end_r1986, loc2463, x1649);
            CursorTy pvrtmp5777 = tmp_struct94.field0;
            CursorTy pvrtmp5778 = tmp_struct94.field1;
            CursorTy pvrtmp5779 = tmp_struct94.field2;
            CursorTy pvrtmp5780 = tmp_struct94.field3;
            CursorTy fltPrd4893 = (CursorTy) pvrtmp5779;
            CursorTy fltPrd4894 = (CursorTy) pvrtmp5780;
            CursorTy pvrtmp5782 = (CursorTy) fltPrd4894;
            CursorTy pvrtmp5781 = (CursorTy) fltPrd4893;
            CursorTy y1652 = (CursorTy) pvrtmp5781;
            CursorTy fltPrd4895 = (CursorTy) pvrtmp5779;
            CursorTy fltPrd4896 = (CursorTy) pvrtmp5780;
            CursorTy pvrtmp5784 = (CursorTy) fltPrd4896;
            CursorTy pvrtmp5783 = (CursorTy) fltPrd4895;
            CursorTy end_y1652 = (CursorTy) pvrtmp5784;
            CursorTy end_r1986_3724 = (CursorTy) pvrtmp5777;
            CursorTy endof3449 = (CursorTy) pvrtmp5778;
            CursorTy case2452 = (CursorTy) endof3449;
            CursorTy x1650 = (CursorTy) case2452;
            CursorTy loc2464 = (CursorTy) end_y1652;
            CursorCursorCursorCursorProd tmp_struct95 =
                                          _copy_ListExpr(end_r1985, end_r1986_3724, loc2464, x1650);
            CursorTy pvrtmp5785 = tmp_struct95.field0;
            CursorTy pvrtmp5786 = tmp_struct95.field1;
            CursorTy pvrtmp5787 = tmp_struct95.field2;
            CursorTy pvrtmp5788 = tmp_struct95.field3;
            CursorTy fltPrd4897 = (CursorTy) pvrtmp5787;
            CursorTy fltPrd4898 = (CursorTy) pvrtmp5788;
            CursorTy pvrtmp5790 = (CursorTy) fltPrd4898;
            CursorTy pvrtmp5789 = (CursorTy) fltPrd4897;
            CursorTy y1653 = (CursorTy) pvrtmp5789;
            CursorTy fltPrd4899 = (CursorTy) pvrtmp5787;
            CursorTy fltPrd4900 = (CursorTy) pvrtmp5788;
            CursorTy pvrtmp5792 = (CursorTy) fltPrd4900;
            CursorTy pvrtmp5791 = (CursorTy) fltPrd4899;
            CursorTy end_y1653 = (CursorTy) pvrtmp5792;
            CursorTy end_r1986_3724_3725 = (CursorTy) pvrtmp5785;
            CursorTy endof3450 = (CursorTy) pvrtmp5786;
            CursorTy case2453 = (CursorTy) endof3450;
            CursorTy x1651 = (CursorTy) case2453;
            CursorTy loc2465 = (CursorTy) end_y1653;
            CursorCursorCursorCursorProd tmp_struct96 =
                                          _copy_LAMBDACASE(end_r1985, end_r1986_3724_3725, loc2465, x1651);
            CursorTy pvrtmp5793 = tmp_struct96.field0;
            CursorTy pvrtmp5794 = tmp_struct96.field1;
            CursorTy pvrtmp5795 = tmp_struct96.field2;
            CursorTy pvrtmp5796 = tmp_struct96.field3;
            CursorTy fltPrd4901 = (CursorTy) pvrtmp5795;
            CursorTy fltPrd4902 = (CursorTy) pvrtmp5796;
            CursorTy pvrtmp5798 = (CursorTy) fltPrd4902;
            CursorTy pvrtmp5797 = (CursorTy) fltPrd4901;
            CursorTy y1654 = (CursorTy) pvrtmp5797;
            CursorTy fltPrd4903 = (CursorTy) pvrtmp5795;
            CursorTy fltPrd4904 = (CursorTy) pvrtmp5796;
            CursorTy pvrtmp5800 = (CursorTy) fltPrd4904;
            CursorTy pvrtmp5799 = (CursorTy) fltPrd4903;
            CursorTy end_y1654 = (CursorTy) pvrtmp5800;
            CursorTy end_r1986_3724_3725_3726 = (CursorTy) pvrtmp5793;
            CursorTy endof3451 = (CursorTy) pvrtmp5794;

            *(TagTyPacked *) loc1984 = 0;

            CursorTy writetag4061 = loc1984 + 1;
            CursorTy writecur4062 = (CursorTy) end_y1652;
            CursorTy writecur4063 = (CursorTy) end_y1653;
            CursorTy writecur4064 = (CursorTy) end_y1654;
            CursorTy pvrtmp5802 = (CursorTy) writecur4064;
            CursorTy pvrtmp5801 = (CursorTy) loc1984;
            CursorTy taildc3452 = (CursorTy) pvrtmp5801;
            CursorTy end_taildc3452 = (CursorTy) pvrtmp5802;
            CursorTy pvrtmp5804 = (CursorTy) end_taildc3452;
            CursorTy pvrtmp5803 = (CursorTy) taildc3452;
            CursorTy fltPrd4905 = (CursorTy) pvrtmp5803;
            CursorTy fltPrd4906 = (CursorTy) pvrtmp5804;

            return (CursorCursorCursorCursorProd) {end_r1986_3724_3725_3726,
                                                   endof3451, fltPrd4905,
                                                   fltPrd4906};
            break;
        }

      case 1:
        {
            CursorTy field_cur4066 = (CursorTy) tmpcur5776;
            CursorTy jump3453 = loc1983 + 1;

            *(TagTyPacked *) loc1984 = 1;

            CursorTy writetag4067 = loc1984 + 1;
            CursorTy pvrtmp5806 = (CursorTy) writetag4067;
            CursorTy pvrtmp5805 = (CursorTy) loc1984;
            CursorTy taildc3454 = (CursorTy) pvrtmp5805;
            CursorTy end_taildc3454 = (CursorTy) pvrtmp5806;
            CursorTy pvrtmp5808 = (CursorTy) end_taildc3454;
            CursorTy pvrtmp5807 = (CursorTy) taildc3454;
            CursorTy fltPrd4907 = (CursorTy) pvrtmp5807;
            CursorTy fltPrd4908 = (CursorTy) pvrtmp5808;

            return (CursorCursorCursorCursorProd) {end_r1986, jump3453,
                                                   fltPrd4907, fltPrd4908};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7326 = *(CursorTy *) tmpcur5776;
            CursorTy tmpaftercur7327 = tmpcur5776 + 8;
            TagTyPacked tagtmp7328 = *(TagTyPacked *) tmpcur7326;
            CursorTy tailtmp7329 = tmpcur7326 + 1;

            tmpval5775 = tagtmp7328;
            tmpcur5776 = tailtmp7329;
            goto switch5809;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7326 = *(CursorTy *) tmpcur5776;
            CursorTy tmpaftercur7327 = tmpcur5776 + 8;
            TagTyPacked tagtmp7328 = *(TagTyPacked *) tmpcur7326;
            CursorTy tailtmp7329 = tmpcur7326 + 1;

            tmpval5775 = tagtmp7328;
            tmpcur5776 = tailtmp7329;
            goto switch5809;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5775");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_LVBIND(CursorTy end_r1991,
                                          CursorTy end_r1992, CursorTy loc1990,
                                          CursorTy arg1662)
{
    CursorTy loc1989 = (CursorTy) arg1662;

    if (loc1990 + 18 > end_r1992) {
        ChunkTy new_chunk106 = alloc_chunk(end_r1992);
        CursorTy chunk_start107 = new_chunk106.start_ptr;
        CursorTy chunk_end108 = new_chunk106.end_ptr;

        end_r1992 = chunk_end108;
        *(TagTyPacked *) loc1990 = 255;

        CursorTy redir = loc1990 + 1;

        *(CursorTy *) redir = chunk_start107;
        loc1990 = chunk_start107;
    }

    TagTyPacked tmpval5819 = *(TagTyPacked *) arg1662;
    CursorTy tmpcur5820 = arg1662 + 1;


  switch5853:
    ;
    switch (tmpval5819) {

      case 0:
        {
            CursorTy field_cur4074 = (CursorTy) tmpcur5820;
            CursorTy case2483 = (CursorTy) field_cur4074;
            CursorTy x1663 = (CursorTy) case2483;
            CursorTy loc2495 = loc1990 + 1;
            CursorCursorCursorCursorProd tmp_struct103 =
                                          _copy_ListSym(end_r1991, end_r1992, loc2495, x1663);
            CursorTy pvrtmp5821 = tmp_struct103.field0;
            CursorTy pvrtmp5822 = tmp_struct103.field1;
            CursorTy pvrtmp5823 = tmp_struct103.field2;
            CursorTy pvrtmp5824 = tmp_struct103.field3;
            CursorTy fltPrd4909 = (CursorTy) pvrtmp5823;
            CursorTy fltPrd4910 = (CursorTy) pvrtmp5824;
            CursorTy pvrtmp5826 = (CursorTy) fltPrd4910;
            CursorTy pvrtmp5825 = (CursorTy) fltPrd4909;
            CursorTy y1666 = (CursorTy) pvrtmp5825;
            CursorTy fltPrd4911 = (CursorTy) pvrtmp5823;
            CursorTy fltPrd4912 = (CursorTy) pvrtmp5824;
            CursorTy pvrtmp5828 = (CursorTy) fltPrd4912;
            CursorTy pvrtmp5827 = (CursorTy) fltPrd4911;
            CursorTy end_y1666 = (CursorTy) pvrtmp5828;
            CursorTy end_r1992_3727 = (CursorTy) pvrtmp5821;
            CursorTy endof3461 = (CursorTy) pvrtmp5822;
            CursorTy case2484 = (CursorTy) endof3461;
            CursorTy x1664 = (CursorTy) case2484;
            CursorTy loc2496 = (CursorTy) end_y1666;
            CursorCursorCursorCursorProd tmp_struct104 =
                                          _copy_Expr(end_r1991, end_r1992_3727, loc2496, x1664);
            CursorTy pvrtmp5829 = tmp_struct104.field0;
            CursorTy pvrtmp5830 = tmp_struct104.field1;
            CursorTy pvrtmp5831 = tmp_struct104.field2;
            CursorTy pvrtmp5832 = tmp_struct104.field3;
            CursorTy fltPrd4913 = (CursorTy) pvrtmp5831;
            CursorTy fltPrd4914 = (CursorTy) pvrtmp5832;
            CursorTy pvrtmp5834 = (CursorTy) fltPrd4914;
            CursorTy pvrtmp5833 = (CursorTy) fltPrd4913;
            CursorTy y1667 = (CursorTy) pvrtmp5833;
            CursorTy fltPrd4915 = (CursorTy) pvrtmp5831;
            CursorTy fltPrd4916 = (CursorTy) pvrtmp5832;
            CursorTy pvrtmp5836 = (CursorTy) fltPrd4916;
            CursorTy pvrtmp5835 = (CursorTy) fltPrd4915;
            CursorTy end_y1667 = (CursorTy) pvrtmp5836;
            CursorTy end_r1992_3727_3728 = (CursorTy) pvrtmp5829;
            CursorTy endof3462 = (CursorTy) pvrtmp5830;
            CursorTy case2485 = (CursorTy) endof3462;
            CursorTy x1665 = (CursorTy) case2485;
            CursorTy loc2497 = (CursorTy) end_y1667;
            CursorCursorCursorCursorProd tmp_struct105 =
                                          _copy_LVBIND(end_r1991, end_r1992_3727_3728, loc2497, x1665);
            CursorTy pvrtmp5837 = tmp_struct105.field0;
            CursorTy pvrtmp5838 = tmp_struct105.field1;
            CursorTy pvrtmp5839 = tmp_struct105.field2;
            CursorTy pvrtmp5840 = tmp_struct105.field3;
            CursorTy fltPrd4917 = (CursorTy) pvrtmp5839;
            CursorTy fltPrd4918 = (CursorTy) pvrtmp5840;
            CursorTy pvrtmp5842 = (CursorTy) fltPrd4918;
            CursorTy pvrtmp5841 = (CursorTy) fltPrd4917;
            CursorTy y1668 = (CursorTy) pvrtmp5841;
            CursorTy fltPrd4919 = (CursorTy) pvrtmp5839;
            CursorTy fltPrd4920 = (CursorTy) pvrtmp5840;
            CursorTy pvrtmp5844 = (CursorTy) fltPrd4920;
            CursorTy pvrtmp5843 = (CursorTy) fltPrd4919;
            CursorTy end_y1668 = (CursorTy) pvrtmp5844;
            CursorTy end_r1992_3727_3728_3729 = (CursorTy) pvrtmp5837;
            CursorTy endof3463 = (CursorTy) pvrtmp5838;

            *(TagTyPacked *) loc1990 = 0;

            CursorTy writetag4078 = loc1990 + 1;
            CursorTy writecur4079 = (CursorTy) end_y1666;
            CursorTy writecur4080 = (CursorTy) end_y1667;
            CursorTy writecur4081 = (CursorTy) end_y1668;
            CursorTy pvrtmp5846 = (CursorTy) writecur4081;
            CursorTy pvrtmp5845 = (CursorTy) loc1990;
            CursorTy taildc3464 = (CursorTy) pvrtmp5845;
            CursorTy end_taildc3464 = (CursorTy) pvrtmp5846;
            CursorTy pvrtmp5848 = (CursorTy) end_taildc3464;
            CursorTy pvrtmp5847 = (CursorTy) taildc3464;
            CursorTy fltPrd4921 = (CursorTy) pvrtmp5847;
            CursorTy fltPrd4922 = (CursorTy) pvrtmp5848;

            return (CursorCursorCursorCursorProd) {end_r1992_3727_3728_3729,
                                                   endof3463, fltPrd4921,
                                                   fltPrd4922};
            break;
        }

      case 1:
        {
            CursorTy field_cur4083 = (CursorTy) tmpcur5820;
            CursorTy jump3465 = loc1989 + 1;

            *(TagTyPacked *) loc1990 = 1;

            CursorTy writetag4084 = loc1990 + 1;
            CursorTy pvrtmp5850 = (CursorTy) writetag4084;
            CursorTy pvrtmp5849 = (CursorTy) loc1990;
            CursorTy taildc3466 = (CursorTy) pvrtmp5849;
            CursorTy end_taildc3466 = (CursorTy) pvrtmp5850;
            CursorTy pvrtmp5852 = (CursorTy) end_taildc3466;
            CursorTy pvrtmp5851 = (CursorTy) taildc3466;
            CursorTy fltPrd4923 = (CursorTy) pvrtmp5851;
            CursorTy fltPrd4924 = (CursorTy) pvrtmp5852;

            return (CursorCursorCursorCursorProd) {end_r1992, jump3465,
                                                   fltPrd4923, fltPrd4924};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7334 = *(CursorTy *) tmpcur5820;
            CursorTy tmpaftercur7335 = tmpcur5820 + 8;
            TagTyPacked tagtmp7336 = *(TagTyPacked *) tmpcur7334;
            CursorTy tailtmp7337 = tmpcur7334 + 1;

            tmpval5819 = tagtmp7336;
            tmpcur5820 = tailtmp7337;
            goto switch5853;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7334 = *(CursorTy *) tmpcur5820;
            CursorTy tmpaftercur7335 = tmpcur5820 + 8;
            TagTyPacked tagtmp7336 = *(TagTyPacked *) tmpcur7334;
            CursorTy tailtmp7337 = tmpcur7334 + 1;

            tmpval5819 = tagtmp7336;
            tmpcur5820 = tailtmp7337;
            goto switch5853;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5819");
            exit(1);
        }
    }
}

CursorCursorCursorCursorProd _copy_Expr(CursorTy end_r1997, CursorTy end_r1998,
                                        CursorTy loc1996, CursorTy arg1676)
{
    CursorTy loc1995 = (CursorTy) arg1676;

    if (loc1996 + 18 > end_r1998) {
        ChunkTy new_chunk134 = alloc_chunk(end_r1998);
        CursorTy chunk_start135 = new_chunk134.start_ptr;
        CursorTy chunk_end136 = new_chunk134.end_ptr;

        end_r1998 = chunk_end136;
        *(TagTyPacked *) loc1996 = 255;

        CursorTy redir = loc1996 + 1;

        *(CursorTy *) redir = chunk_start135;
        loc1996 = chunk_start135;
    }

    CursorTy loc2602 = loc1996 + 1;
    CursorTy loc2603 = loc2602 + 8;
    TagTyPacked tmpval5863 = *(TagTyPacked *) arg1676;
    CursorTy tmpcur5864 = arg1676 + 1;


  switch6123:
    ;
    switch (tmpval5863) {

      case 0:
        {
            CursorTy field_cur4091 = (CursorTy) tmpcur5864;
            CursorTy case2515 = (CursorTy) field_cur4091;
            SymTy tmpval5865 = *(SymTy *) case2515;
            CursorTy tmpcur5866 = case2515 + sizeof(SymTy);
            SymTy x1677 = (SymTy) tmpval5865;
            CursorTy end_x1677 = (CursorTy) tmpcur5866;
            CursorTy jump3473 = case2515 + 8;

            *(TagTyPacked *) loc1996 = 0;

            CursorTy writetag4093 = loc1996 + 1;

            *(SymTy *) writetag4093 = x1677;

            CursorTy writecur4094 = writetag4093 + sizeof(SymTy);
            CursorTy pvrtmp5868 = (CursorTy) writecur4094;
            CursorTy pvrtmp5867 = (CursorTy) loc1996;
            CursorTy taildc3474 = (CursorTy) pvrtmp5867;
            CursorTy end_taildc3474 = (CursorTy) pvrtmp5868;
            CursorTy pvrtmp5870 = (CursorTy) end_taildc3474;
            CursorTy pvrtmp5869 = (CursorTy) taildc3474;
            CursorTy fltPrd4925 = (CursorTy) pvrtmp5869;
            CursorTy fltPrd4926 = (CursorTy) pvrtmp5870;

            return (CursorCursorCursorCursorProd) {end_r1998, jump3473,
                                                   fltPrd4925, fltPrd4926};
            break;
        }

      case 1:
        {
            CursorTy field_cur4096 = (CursorTy) tmpcur5864;
            CursorTy case2519 = (CursorTy) field_cur4096;
            CursorTy x1679 = (CursorTy) case2519;
            CursorTy loc2527 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct112 =
                                          _copy_Formals(end_r1997, end_r1998, loc2527, x1679);
            CursorTy pvrtmp5871 = tmp_struct112.field0;
            CursorTy pvrtmp5872 = tmp_struct112.field1;
            CursorTy pvrtmp5873 = tmp_struct112.field2;
            CursorTy pvrtmp5874 = tmp_struct112.field3;
            CursorTy fltPrd4927 = (CursorTy) pvrtmp5873;
            CursorTy fltPrd4928 = (CursorTy) pvrtmp5874;
            CursorTy pvrtmp5876 = (CursorTy) fltPrd4928;
            CursorTy pvrtmp5875 = (CursorTy) fltPrd4927;
            CursorTy y1681 = (CursorTy) pvrtmp5875;
            CursorTy fltPrd4929 = (CursorTy) pvrtmp5873;
            CursorTy fltPrd4930 = (CursorTy) pvrtmp5874;
            CursorTy pvrtmp5878 = (CursorTy) fltPrd4930;
            CursorTy pvrtmp5877 = (CursorTy) fltPrd4929;
            CursorTy end_y1681 = (CursorTy) pvrtmp5878;
            CursorTy end_r1998_3730 = (CursorTy) pvrtmp5871;
            CursorTy endof3475 = (CursorTy) pvrtmp5872;
            CursorTy case2520 = (CursorTy) endof3475;
            CursorTy x1680 = (CursorTy) case2520;
            CursorTy loc2528 = (CursorTy) end_y1681;
            CursorCursorCursorCursorProd tmp_struct113 =
                                          _copy_ListExpr(end_r1997, end_r1998_3730, loc2528, x1680);
            CursorTy pvrtmp5879 = tmp_struct113.field0;
            CursorTy pvrtmp5880 = tmp_struct113.field1;
            CursorTy pvrtmp5881 = tmp_struct113.field2;
            CursorTy pvrtmp5882 = tmp_struct113.field3;
            CursorTy fltPrd4931 = (CursorTy) pvrtmp5881;
            CursorTy fltPrd4932 = (CursorTy) pvrtmp5882;
            CursorTy pvrtmp5884 = (CursorTy) fltPrd4932;
            CursorTy pvrtmp5883 = (CursorTy) fltPrd4931;
            CursorTy y1682 = (CursorTy) pvrtmp5883;
            CursorTy fltPrd4933 = (CursorTy) pvrtmp5881;
            CursorTy fltPrd4934 = (CursorTy) pvrtmp5882;
            CursorTy pvrtmp5886 = (CursorTy) fltPrd4934;
            CursorTy pvrtmp5885 = (CursorTy) fltPrd4933;
            CursorTy end_y1682 = (CursorTy) pvrtmp5886;
            CursorTy end_r1998_3730_3731 = (CursorTy) pvrtmp5879;
            CursorTy endof3476 = (CursorTy) pvrtmp5880;

            *(TagTyPacked *) loc1996 = 1;

            CursorTy writetag4099 = loc1996 + 1;
            CursorTy writecur4100 = (CursorTy) end_y1681;
            CursorTy writecur4101 = (CursorTy) end_y1682;
            CursorTy pvrtmp5888 = (CursorTy) writecur4101;
            CursorTy pvrtmp5887 = (CursorTy) loc1996;
            CursorTy taildc3477 = (CursorTy) pvrtmp5887;
            CursorTy end_taildc3477 = (CursorTy) pvrtmp5888;
            CursorTy pvrtmp5890 = (CursorTy) end_taildc3477;
            CursorTy pvrtmp5889 = (CursorTy) taildc3477;
            CursorTy fltPrd4935 = (CursorTy) pvrtmp5889;
            CursorTy fltPrd4936 = (CursorTy) pvrtmp5890;

            return (CursorCursorCursorCursorProd) {end_r1998_3730_3731,
                                                   endof3476, fltPrd4935,
                                                   fltPrd4936};
            break;
        }

      case 2:
        {
            CursorTy field_cur4103 = (CursorTy) tmpcur5864;
            CursorTy case2531 = (CursorTy) field_cur4103;
            CursorTy x1683 = (CursorTy) case2531;
            CursorTy loc2535 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct114 =
                                          _copy_LAMBDACASE(end_r1997, end_r1998, loc2535, x1683);
            CursorTy pvrtmp5891 = tmp_struct114.field0;
            CursorTy pvrtmp5892 = tmp_struct114.field1;
            CursorTy pvrtmp5893 = tmp_struct114.field2;
            CursorTy pvrtmp5894 = tmp_struct114.field3;
            CursorTy fltPrd4937 = (CursorTy) pvrtmp5893;
            CursorTy fltPrd4938 = (CursorTy) pvrtmp5894;
            CursorTy pvrtmp5896 = (CursorTy) fltPrd4938;
            CursorTy pvrtmp5895 = (CursorTy) fltPrd4937;
            CursorTy y1684 = (CursorTy) pvrtmp5895;
            CursorTy fltPrd4939 = (CursorTy) pvrtmp5893;
            CursorTy fltPrd4940 = (CursorTy) pvrtmp5894;
            CursorTy pvrtmp5898 = (CursorTy) fltPrd4940;
            CursorTy pvrtmp5897 = (CursorTy) fltPrd4939;
            CursorTy end_y1684 = (CursorTy) pvrtmp5898;
            CursorTy end_r1998_3732 = (CursorTy) pvrtmp5891;
            CursorTy endof3478 = (CursorTy) pvrtmp5892;

            *(TagTyPacked *) loc1996 = 2;

            CursorTy writetag4105 = loc1996 + 1;
            CursorTy writecur4106 = (CursorTy) end_y1684;
            CursorTy pvrtmp5900 = (CursorTy) writecur4106;
            CursorTy pvrtmp5899 = (CursorTy) loc1996;
            CursorTy taildc3479 = (CursorTy) pvrtmp5899;
            CursorTy end_taildc3479 = (CursorTy) pvrtmp5900;
            CursorTy pvrtmp5902 = (CursorTy) end_taildc3479;
            CursorTy pvrtmp5901 = (CursorTy) taildc3479;
            CursorTy fltPrd4941 = (CursorTy) pvrtmp5901;
            CursorTy fltPrd4942 = (CursorTy) pvrtmp5902;

            return (CursorCursorCursorCursorProd) {end_r1998_3732, endof3478,
                                                   fltPrd4941, fltPrd4942};
            break;
        }

      case 3:
        {
            CursorTy field_cur4108 = (CursorTy) tmpcur5864;
            CursorTy case2537 = (CursorTy) field_cur4108;
            CursorTy x1685 = (CursorTy) case2537;
            CursorTy loc2549 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct115 =
                                          _copy_Expr(end_r1997, end_r1998, loc2549, x1685);
            CursorTy pvrtmp5903 = tmp_struct115.field0;
            CursorTy pvrtmp5904 = tmp_struct115.field1;
            CursorTy pvrtmp5905 = tmp_struct115.field2;
            CursorTy pvrtmp5906 = tmp_struct115.field3;
            CursorTy fltPrd4943 = (CursorTy) pvrtmp5905;
            CursorTy fltPrd4944 = (CursorTy) pvrtmp5906;
            CursorTy pvrtmp5908 = (CursorTy) fltPrd4944;
            CursorTy pvrtmp5907 = (CursorTy) fltPrd4943;
            CursorTy y1688 = (CursorTy) pvrtmp5907;
            CursorTy fltPrd4945 = (CursorTy) pvrtmp5905;
            CursorTy fltPrd4946 = (CursorTy) pvrtmp5906;
            CursorTy pvrtmp5910 = (CursorTy) fltPrd4946;
            CursorTy pvrtmp5909 = (CursorTy) fltPrd4945;
            CursorTy end_y1688 = (CursorTy) pvrtmp5910;
            CursorTy end_r1998_3733 = (CursorTy) pvrtmp5903;
            CursorTy endof3480 = (CursorTy) pvrtmp5904;
            CursorTy case2538 = (CursorTy) endof3480;
            CursorTy x1686 = (CursorTy) case2538;
            CursorTy loc2550 = (CursorTy) end_y1688;
            CursorCursorCursorCursorProd tmp_struct116 =
                                          _copy_Expr(end_r1997, end_r1998_3733, loc2550, x1686);
            CursorTy pvrtmp5911 = tmp_struct116.field0;
            CursorTy pvrtmp5912 = tmp_struct116.field1;
            CursorTy pvrtmp5913 = tmp_struct116.field2;
            CursorTy pvrtmp5914 = tmp_struct116.field3;
            CursorTy fltPrd4947 = (CursorTy) pvrtmp5913;
            CursorTy fltPrd4948 = (CursorTy) pvrtmp5914;
            CursorTy pvrtmp5916 = (CursorTy) fltPrd4948;
            CursorTy pvrtmp5915 = (CursorTy) fltPrd4947;
            CursorTy y1689 = (CursorTy) pvrtmp5915;
            CursorTy fltPrd4949 = (CursorTy) pvrtmp5913;
            CursorTy fltPrd4950 = (CursorTy) pvrtmp5914;
            CursorTy pvrtmp5918 = (CursorTy) fltPrd4950;
            CursorTy pvrtmp5917 = (CursorTy) fltPrd4949;
            CursorTy end_y1689 = (CursorTy) pvrtmp5918;
            CursorTy end_r1998_3733_3734 = (CursorTy) pvrtmp5911;
            CursorTy endof3481 = (CursorTy) pvrtmp5912;
            CursorTy case2539 = (CursorTy) endof3481;
            CursorTy x1687 = (CursorTy) case2539;
            CursorTy loc2551 = (CursorTy) end_y1689;
            CursorCursorCursorCursorProd tmp_struct117 =
                                          _copy_Expr(end_r1997, end_r1998_3733_3734, loc2551, x1687);
            CursorTy pvrtmp5919 = tmp_struct117.field0;
            CursorTy pvrtmp5920 = tmp_struct117.field1;
            CursorTy pvrtmp5921 = tmp_struct117.field2;
            CursorTy pvrtmp5922 = tmp_struct117.field3;
            CursorTy fltPrd4951 = (CursorTy) pvrtmp5921;
            CursorTy fltPrd4952 = (CursorTy) pvrtmp5922;
            CursorTy pvrtmp5924 = (CursorTy) fltPrd4952;
            CursorTy pvrtmp5923 = (CursorTy) fltPrd4951;
            CursorTy y1690 = (CursorTy) pvrtmp5923;
            CursorTy fltPrd4953 = (CursorTy) pvrtmp5921;
            CursorTy fltPrd4954 = (CursorTy) pvrtmp5922;
            CursorTy pvrtmp5926 = (CursorTy) fltPrd4954;
            CursorTy pvrtmp5925 = (CursorTy) fltPrd4953;
            CursorTy end_y1690 = (CursorTy) pvrtmp5926;
            CursorTy end_r1998_3733_3734_3735 = (CursorTy) pvrtmp5919;
            CursorTy endof3482 = (CursorTy) pvrtmp5920;

            *(TagTyPacked *) loc1996 = 3;

            CursorTy writetag4112 = loc1996 + 1;
            CursorTy writecur4113 = (CursorTy) end_y1688;
            CursorTy writecur4114 = (CursorTy) end_y1689;
            CursorTy writecur4115 = (CursorTy) end_y1690;
            CursorTy pvrtmp5928 = (CursorTy) writecur4115;
            CursorTy pvrtmp5927 = (CursorTy) loc1996;
            CursorTy taildc3483 = (CursorTy) pvrtmp5927;
            CursorTy end_taildc3483 = (CursorTy) pvrtmp5928;
            CursorTy pvrtmp5930 = (CursorTy) end_taildc3483;
            CursorTy pvrtmp5929 = (CursorTy) taildc3483;
            CursorTy fltPrd4955 = (CursorTy) pvrtmp5929;
            CursorTy fltPrd4956 = (CursorTy) pvrtmp5930;

            return (CursorCursorCursorCursorProd) {end_r1998_3733_3734_3735,
                                                   endof3482, fltPrd4955,
                                                   fltPrd4956};
            break;
        }

      case 4:
        {
            CursorTy field_cur4117 = (CursorTy) tmpcur5864;
            CursorTy case2555 = (CursorTy) field_cur4117;
            CursorTy x1691 = (CursorTy) case2555;
            CursorTy loc2559 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct118 =
                                          _copy_ListExpr(end_r1997, end_r1998, loc2559, x1691);
            CursorTy pvrtmp5931 = tmp_struct118.field0;
            CursorTy pvrtmp5932 = tmp_struct118.field1;
            CursorTy pvrtmp5933 = tmp_struct118.field2;
            CursorTy pvrtmp5934 = tmp_struct118.field3;
            CursorTy fltPrd4957 = (CursorTy) pvrtmp5933;
            CursorTy fltPrd4958 = (CursorTy) pvrtmp5934;
            CursorTy pvrtmp5936 = (CursorTy) fltPrd4958;
            CursorTy pvrtmp5935 = (CursorTy) fltPrd4957;
            CursorTy y1692 = (CursorTy) pvrtmp5935;
            CursorTy fltPrd4959 = (CursorTy) pvrtmp5933;
            CursorTy fltPrd4960 = (CursorTy) pvrtmp5934;
            CursorTy pvrtmp5938 = (CursorTy) fltPrd4960;
            CursorTy pvrtmp5937 = (CursorTy) fltPrd4959;
            CursorTy end_y1692 = (CursorTy) pvrtmp5938;
            CursorTy end_r1998_3736 = (CursorTy) pvrtmp5931;
            CursorTy endof3484 = (CursorTy) pvrtmp5932;

            *(TagTyPacked *) loc1996 = 4;

            CursorTy writetag4119 = loc1996 + 1;
            CursorTy writecur4120 = (CursorTy) end_y1692;
            CursorTy pvrtmp5940 = (CursorTy) writecur4120;
            CursorTy pvrtmp5939 = (CursorTy) loc1996;
            CursorTy taildc3485 = (CursorTy) pvrtmp5939;
            CursorTy end_taildc3485 = (CursorTy) pvrtmp5940;
            CursorTy pvrtmp5942 = (CursorTy) end_taildc3485;
            CursorTy pvrtmp5941 = (CursorTy) taildc3485;
            CursorTy fltPrd4961 = (CursorTy) pvrtmp5941;
            CursorTy fltPrd4962 = (CursorTy) pvrtmp5942;

            return (CursorCursorCursorCursorProd) {end_r1998_3736, endof3484,
                                                   fltPrd4961, fltPrd4962};
            break;
        }

      case 5:
        {
            CursorTy field_cur4122 = (CursorTy) tmpcur5864;
            CursorTy case2561 = (CursorTy) field_cur4122;
            CursorTy x1693 = (CursorTy) case2561;
            CursorTy loc2569 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct119 =
                                          _copy_Expr(end_r1997, end_r1998, loc2569, x1693);
            CursorTy pvrtmp5943 = tmp_struct119.field0;
            CursorTy pvrtmp5944 = tmp_struct119.field1;
            CursorTy pvrtmp5945 = tmp_struct119.field2;
            CursorTy pvrtmp5946 = tmp_struct119.field3;
            CursorTy fltPrd4963 = (CursorTy) pvrtmp5945;
            CursorTy fltPrd4964 = (CursorTy) pvrtmp5946;
            CursorTy pvrtmp5948 = (CursorTy) fltPrd4964;
            CursorTy pvrtmp5947 = (CursorTy) fltPrd4963;
            CursorTy y1695 = (CursorTy) pvrtmp5947;
            CursorTy fltPrd4965 = (CursorTy) pvrtmp5945;
            CursorTy fltPrd4966 = (CursorTy) pvrtmp5946;
            CursorTy pvrtmp5950 = (CursorTy) fltPrd4966;
            CursorTy pvrtmp5949 = (CursorTy) fltPrd4965;
            CursorTy end_y1695 = (CursorTy) pvrtmp5950;
            CursorTy end_r1998_3737 = (CursorTy) pvrtmp5943;
            CursorTy endof3486 = (CursorTy) pvrtmp5944;
            CursorTy case2562 = (CursorTy) endof3486;
            CursorTy x1694 = (CursorTy) case2562;
            CursorTy loc2570 = (CursorTy) end_y1695;
            CursorCursorCursorCursorProd tmp_struct120 =
                                          _copy_ListExpr(end_r1997, end_r1998_3737, loc2570, x1694);
            CursorTy pvrtmp5951 = tmp_struct120.field0;
            CursorTy pvrtmp5952 = tmp_struct120.field1;
            CursorTy pvrtmp5953 = tmp_struct120.field2;
            CursorTy pvrtmp5954 = tmp_struct120.field3;
            CursorTy fltPrd4967 = (CursorTy) pvrtmp5953;
            CursorTy fltPrd4968 = (CursorTy) pvrtmp5954;
            CursorTy pvrtmp5956 = (CursorTy) fltPrd4968;
            CursorTy pvrtmp5955 = (CursorTy) fltPrd4967;
            CursorTy y1696 = (CursorTy) pvrtmp5955;
            CursorTy fltPrd4969 = (CursorTy) pvrtmp5953;
            CursorTy fltPrd4970 = (CursorTy) pvrtmp5954;
            CursorTy pvrtmp5958 = (CursorTy) fltPrd4970;
            CursorTy pvrtmp5957 = (CursorTy) fltPrd4969;
            CursorTy end_y1696 = (CursorTy) pvrtmp5958;
            CursorTy end_r1998_3737_3738 = (CursorTy) pvrtmp5951;
            CursorTy endof3487 = (CursorTy) pvrtmp5952;

            *(TagTyPacked *) loc1996 = 5;

            CursorTy writetag4125 = loc1996 + 1;
            CursorTy writecur4126 = (CursorTy) end_y1695;
            CursorTy writecur4127 = (CursorTy) end_y1696;
            CursorTy pvrtmp5960 = (CursorTy) writecur4127;
            CursorTy pvrtmp5959 = (CursorTy) loc1996;
            CursorTy taildc3488 = (CursorTy) pvrtmp5959;
            CursorTy end_taildc3488 = (CursorTy) pvrtmp5960;
            CursorTy pvrtmp5962 = (CursorTy) end_taildc3488;
            CursorTy pvrtmp5961 = (CursorTy) taildc3488;
            CursorTy fltPrd4971 = (CursorTy) pvrtmp5961;
            CursorTy fltPrd4972 = (CursorTy) pvrtmp5962;

            return (CursorCursorCursorCursorProd) {end_r1998_3737_3738,
                                                   endof3487, fltPrd4971,
                                                   fltPrd4972};
            break;
        }

      case 6:
        {
            CursorTy field_cur4129 = (CursorTy) tmpcur5864;
            CursorTy case2573 = (CursorTy) field_cur4129;
            CursorTy x1697 = (CursorTy) case2573;
            CursorTy loc2581 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct121 =
                                          _copy_LVBIND(end_r1997, end_r1998, loc2581, x1697);
            CursorTy pvrtmp5963 = tmp_struct121.field0;
            CursorTy pvrtmp5964 = tmp_struct121.field1;
            CursorTy pvrtmp5965 = tmp_struct121.field2;
            CursorTy pvrtmp5966 = tmp_struct121.field3;
            CursorTy fltPrd4973 = (CursorTy) pvrtmp5965;
            CursorTy fltPrd4974 = (CursorTy) pvrtmp5966;
            CursorTy pvrtmp5968 = (CursorTy) fltPrd4974;
            CursorTy pvrtmp5967 = (CursorTy) fltPrd4973;
            CursorTy y1699 = (CursorTy) pvrtmp5967;
            CursorTy fltPrd4975 = (CursorTy) pvrtmp5965;
            CursorTy fltPrd4976 = (CursorTy) pvrtmp5966;
            CursorTy pvrtmp5970 = (CursorTy) fltPrd4976;
            CursorTy pvrtmp5969 = (CursorTy) fltPrd4975;
            CursorTy end_y1699 = (CursorTy) pvrtmp5970;
            CursorTy end_r1998_3739 = (CursorTy) pvrtmp5963;
            CursorTy endof3489 = (CursorTy) pvrtmp5964;
            CursorTy case2574 = (CursorTy) endof3489;
            CursorTy x1698 = (CursorTy) case2574;
            CursorTy loc2582 = (CursorTy) end_y1699;
            CursorCursorCursorCursorProd tmp_struct122 =
                                          _copy_ListExpr(end_r1997, end_r1998_3739, loc2582, x1698);
            CursorTy pvrtmp5971 = tmp_struct122.field0;
            CursorTy pvrtmp5972 = tmp_struct122.field1;
            CursorTy pvrtmp5973 = tmp_struct122.field2;
            CursorTy pvrtmp5974 = tmp_struct122.field3;
            CursorTy fltPrd4977 = (CursorTy) pvrtmp5973;
            CursorTy fltPrd4978 = (CursorTy) pvrtmp5974;
            CursorTy pvrtmp5976 = (CursorTy) fltPrd4978;
            CursorTy pvrtmp5975 = (CursorTy) fltPrd4977;
            CursorTy y1700 = (CursorTy) pvrtmp5975;
            CursorTy fltPrd4979 = (CursorTy) pvrtmp5973;
            CursorTy fltPrd4980 = (CursorTy) pvrtmp5974;
            CursorTy pvrtmp5978 = (CursorTy) fltPrd4980;
            CursorTy pvrtmp5977 = (CursorTy) fltPrd4979;
            CursorTy end_y1700 = (CursorTy) pvrtmp5978;
            CursorTy end_r1998_3739_3740 = (CursorTy) pvrtmp5971;
            CursorTy endof3490 = (CursorTy) pvrtmp5972;

            *(TagTyPacked *) loc1996 = 6;

            CursorTy writetag4132 = loc1996 + 1;
            CursorTy writecur4133 = (CursorTy) end_y1699;
            CursorTy writecur4134 = (CursorTy) end_y1700;
            CursorTy pvrtmp5980 = (CursorTy) writecur4134;
            CursorTy pvrtmp5979 = (CursorTy) loc1996;
            CursorTy taildc3491 = (CursorTy) pvrtmp5979;
            CursorTy end_taildc3491 = (CursorTy) pvrtmp5980;
            CursorTy pvrtmp5982 = (CursorTy) end_taildc3491;
            CursorTy pvrtmp5981 = (CursorTy) taildc3491;
            CursorTy fltPrd4981 = (CursorTy) pvrtmp5981;
            CursorTy fltPrd4982 = (CursorTy) pvrtmp5982;

            return (CursorCursorCursorCursorProd) {end_r1998_3739_3740,
                                                   endof3490, fltPrd4981,
                                                   fltPrd4982};
            break;
        }

      case 7:
        {
            CursorTy field_cur4136 = (CursorTy) tmpcur5864;
            CursorTy case2585 = (CursorTy) field_cur4136;
            CursorTy x1701 = (CursorTy) case2585;
            CursorTy loc2593 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct123 =
                                          _copy_LVBIND(end_r1997, end_r1998, loc2593, x1701);
            CursorTy pvrtmp5983 = tmp_struct123.field0;
            CursorTy pvrtmp5984 = tmp_struct123.field1;
            CursorTy pvrtmp5985 = tmp_struct123.field2;
            CursorTy pvrtmp5986 = tmp_struct123.field3;
            CursorTy fltPrd4983 = (CursorTy) pvrtmp5985;
            CursorTy fltPrd4984 = (CursorTy) pvrtmp5986;
            CursorTy pvrtmp5988 = (CursorTy) fltPrd4984;
            CursorTy pvrtmp5987 = (CursorTy) fltPrd4983;
            CursorTy y1703 = (CursorTy) pvrtmp5987;
            CursorTy fltPrd4985 = (CursorTy) pvrtmp5985;
            CursorTy fltPrd4986 = (CursorTy) pvrtmp5986;
            CursorTy pvrtmp5990 = (CursorTy) fltPrd4986;
            CursorTy pvrtmp5989 = (CursorTy) fltPrd4985;
            CursorTy end_y1703 = (CursorTy) pvrtmp5990;
            CursorTy end_r1998_3741 = (CursorTy) pvrtmp5983;
            CursorTy endof3492 = (CursorTy) pvrtmp5984;
            CursorTy case2586 = (CursorTy) endof3492;
            CursorTy x1702 = (CursorTy) case2586;
            CursorTy loc2594 = (CursorTy) end_y1703;
            CursorCursorCursorCursorProd tmp_struct124 =
                                          _copy_ListExpr(end_r1997, end_r1998_3741, loc2594, x1702);
            CursorTy pvrtmp5991 = tmp_struct124.field0;
            CursorTy pvrtmp5992 = tmp_struct124.field1;
            CursorTy pvrtmp5993 = tmp_struct124.field2;
            CursorTy pvrtmp5994 = tmp_struct124.field3;
            CursorTy fltPrd4987 = (CursorTy) pvrtmp5993;
            CursorTy fltPrd4988 = (CursorTy) pvrtmp5994;
            CursorTy pvrtmp5996 = (CursorTy) fltPrd4988;
            CursorTy pvrtmp5995 = (CursorTy) fltPrd4987;
            CursorTy y1704 = (CursorTy) pvrtmp5995;
            CursorTy fltPrd4989 = (CursorTy) pvrtmp5993;
            CursorTy fltPrd4990 = (CursorTy) pvrtmp5994;
            CursorTy pvrtmp5998 = (CursorTy) fltPrd4990;
            CursorTy pvrtmp5997 = (CursorTy) fltPrd4989;
            CursorTy end_y1704 = (CursorTy) pvrtmp5998;
            CursorTy end_r1998_3741_3742 = (CursorTy) pvrtmp5991;
            CursorTy endof3493 = (CursorTy) pvrtmp5992;

            *(TagTyPacked *) loc1996 = 7;

            CursorTy writetag4139 = loc1996 + 1;
            CursorTy writecur4140 = (CursorTy) end_y1703;
            CursorTy writecur4141 = (CursorTy) end_y1704;
            CursorTy pvrtmp6000 = (CursorTy) writecur4141;
            CursorTy pvrtmp5999 = (CursorTy) loc1996;
            CursorTy taildc3494 = (CursorTy) pvrtmp5999;
            CursorTy end_taildc3494 = (CursorTy) pvrtmp6000;
            CursorTy pvrtmp6002 = (CursorTy) end_taildc3494;
            CursorTy pvrtmp6001 = (CursorTy) taildc3494;
            CursorTy fltPrd4991 = (CursorTy) pvrtmp6001;
            CursorTy fltPrd4992 = (CursorTy) pvrtmp6002;

            return (CursorCursorCursorCursorProd) {end_r1998_3741_3742,
                                                   endof3493, fltPrd4991,
                                                   fltPrd4992};
            break;
        }

      case 8:
        {
            CursorTy field_cur4143 = (CursorTy) tmpcur5864;
            CursorTy case2597 = (CursorTy) field_cur4143;
            SymTy tmpval6003 = *(SymTy *) case2597;
            CursorTy tmpcur6004 = case2597 + sizeof(SymTy);
            SymTy x1705 = (SymTy) tmpval6003;
            CursorTy end_x1705 = (CursorTy) tmpcur6004;
            CursorTy case2598 = (CursorTy) end_x1705;
            CursorTy x1706 = (CursorTy) case2598;
            CursorTy jump3495 = case2597 + 8;
            CursorCursorCursorCursorProd tmp_struct125 =
                                          _copy_Expr(end_r1997, end_r1998, loc2603, x1706);
            CursorTy pvrtmp6005 = tmp_struct125.field0;
            CursorTy pvrtmp6006 = tmp_struct125.field1;
            CursorTy pvrtmp6007 = tmp_struct125.field2;
            CursorTy pvrtmp6008 = tmp_struct125.field3;
            CursorTy fltPrd4993 = (CursorTy) pvrtmp6007;
            CursorTy fltPrd4994 = (CursorTy) pvrtmp6008;
            CursorTy pvrtmp6010 = (CursorTy) fltPrd4994;
            CursorTy pvrtmp6009 = (CursorTy) fltPrd4993;
            CursorTy y1708 = (CursorTy) pvrtmp6009;
            CursorTy fltPrd4995 = (CursorTy) pvrtmp6007;
            CursorTy fltPrd4996 = (CursorTy) pvrtmp6008;
            CursorTy pvrtmp6012 = (CursorTy) fltPrd4996;
            CursorTy pvrtmp6011 = (CursorTy) fltPrd4995;
            CursorTy end_y1708 = (CursorTy) pvrtmp6012;
            CursorTy end_r1998_3743 = (CursorTy) pvrtmp6005;
            CursorTy endof3496 = (CursorTy) pvrtmp6006;

            *(TagTyPacked *) loc1996 = 8;

            CursorTy writetag4146 = loc1996 + 1;

            *(SymTy *) writetag4146 = x1705;

            CursorTy writecur4147 = writetag4146 + sizeof(SymTy);
            CursorTy writecur4148 = (CursorTy) end_y1708;
            CursorTy pvrtmp6014 = (CursorTy) writecur4148;
            CursorTy pvrtmp6013 = (CursorTy) loc1996;
            CursorTy taildc3497 = (CursorTy) pvrtmp6013;
            CursorTy end_taildc3497 = (CursorTy) pvrtmp6014;
            CursorTy pvrtmp6016 = (CursorTy) end_taildc3497;
            CursorTy pvrtmp6015 = (CursorTy) taildc3497;
            CursorTy fltPrd4997 = (CursorTy) pvrtmp6015;
            CursorTy fltPrd4998 = (CursorTy) pvrtmp6016;

            return (CursorCursorCursorCursorProd) {end_r1998_3743, endof3496,
                                                   fltPrd4997, fltPrd4998};
            break;
        }

      case 9:
        {
            CursorTy field_cur4150 = (CursorTy) tmpcur5864;
            CursorTy case2607 = (CursorTy) field_cur4150;
            CursorTy x1709 = (CursorTy) case2607;
            CursorTy loc2611 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct126 =
                                          _copy_Datum(end_r1997, end_r1998, loc2611, x1709);
            CursorTy pvrtmp6017 = tmp_struct126.field0;
            CursorTy pvrtmp6018 = tmp_struct126.field1;
            CursorTy pvrtmp6019 = tmp_struct126.field2;
            CursorTy pvrtmp6020 = tmp_struct126.field3;
            CursorTy fltPrd4999 = (CursorTy) pvrtmp6019;
            CursorTy fltPrd5000 = (CursorTy) pvrtmp6020;
            CursorTy pvrtmp6022 = (CursorTy) fltPrd5000;
            CursorTy pvrtmp6021 = (CursorTy) fltPrd4999;
            CursorTy y1710 = (CursorTy) pvrtmp6021;
            CursorTy fltPrd5001 = (CursorTy) pvrtmp6019;
            CursorTy fltPrd5002 = (CursorTy) pvrtmp6020;
            CursorTy pvrtmp6024 = (CursorTy) fltPrd5002;
            CursorTy pvrtmp6023 = (CursorTy) fltPrd5001;
            CursorTy end_y1710 = (CursorTy) pvrtmp6024;
            CursorTy end_r1998_3744 = (CursorTy) pvrtmp6017;
            CursorTy endof3498 = (CursorTy) pvrtmp6018;

            *(TagTyPacked *) loc1996 = 9;

            CursorTy writetag4152 = loc1996 + 1;
            CursorTy writecur4153 = (CursorTy) end_y1710;
            CursorTy pvrtmp6026 = (CursorTy) writecur4153;
            CursorTy pvrtmp6025 = (CursorTy) loc1996;
            CursorTy taildc3499 = (CursorTy) pvrtmp6025;
            CursorTy end_taildc3499 = (CursorTy) pvrtmp6026;
            CursorTy pvrtmp6028 = (CursorTy) end_taildc3499;
            CursorTy pvrtmp6027 = (CursorTy) taildc3499;
            CursorTy fltPrd5003 = (CursorTy) pvrtmp6027;
            CursorTy fltPrd5004 = (CursorTy) pvrtmp6028;

            return (CursorCursorCursorCursorProd) {end_r1998_3744, endof3498,
                                                   fltPrd5003, fltPrd5004};
            break;
        }

      case 10:
        {
            CursorTy field_cur4155 = (CursorTy) tmpcur5864;
            CursorTy case2613 = (CursorTy) field_cur4155;
            CursorTy x1711 = (CursorTy) case2613;
            CursorTy loc2617 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct127 =
                                          _copy_Datum(end_r1997, end_r1998, loc2617, x1711);
            CursorTy pvrtmp6029 = tmp_struct127.field0;
            CursorTy pvrtmp6030 = tmp_struct127.field1;
            CursorTy pvrtmp6031 = tmp_struct127.field2;
            CursorTy pvrtmp6032 = tmp_struct127.field3;
            CursorTy fltPrd5005 = (CursorTy) pvrtmp6031;
            CursorTy fltPrd5006 = (CursorTy) pvrtmp6032;
            CursorTy pvrtmp6034 = (CursorTy) fltPrd5006;
            CursorTy pvrtmp6033 = (CursorTy) fltPrd5005;
            CursorTy y1712 = (CursorTy) pvrtmp6033;
            CursorTy fltPrd5007 = (CursorTy) pvrtmp6031;
            CursorTy fltPrd5008 = (CursorTy) pvrtmp6032;
            CursorTy pvrtmp6036 = (CursorTy) fltPrd5008;
            CursorTy pvrtmp6035 = (CursorTy) fltPrd5007;
            CursorTy end_y1712 = (CursorTy) pvrtmp6036;
            CursorTy end_r1998_3745 = (CursorTy) pvrtmp6029;
            CursorTy endof3500 = (CursorTy) pvrtmp6030;

            *(TagTyPacked *) loc1996 = 10;

            CursorTy writetag4157 = loc1996 + 1;
            CursorTy writecur4158 = (CursorTy) end_y1712;
            CursorTy pvrtmp6038 = (CursorTy) writecur4158;
            CursorTy pvrtmp6037 = (CursorTy) loc1996;
            CursorTy taildc3501 = (CursorTy) pvrtmp6037;
            CursorTy end_taildc3501 = (CursorTy) pvrtmp6038;
            CursorTy pvrtmp6040 = (CursorTy) end_taildc3501;
            CursorTy pvrtmp6039 = (CursorTy) taildc3501;
            CursorTy fltPrd5009 = (CursorTy) pvrtmp6039;
            CursorTy fltPrd5010 = (CursorTy) pvrtmp6040;

            return (CursorCursorCursorCursorProd) {end_r1998_3745, endof3500,
                                                   fltPrd5009, fltPrd5010};
            break;
        }

      case 11:
        {
            CursorTy field_cur4160 = (CursorTy) tmpcur5864;
            CursorTy case2619 = (CursorTy) field_cur4160;
            CursorTy x1713 = (CursorTy) case2619;
            CursorTy loc2623 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct128 =
                                          _copy_Datum(end_r1997, end_r1998, loc2623, x1713);
            CursorTy pvrtmp6041 = tmp_struct128.field0;
            CursorTy pvrtmp6042 = tmp_struct128.field1;
            CursorTy pvrtmp6043 = tmp_struct128.field2;
            CursorTy pvrtmp6044 = tmp_struct128.field3;
            CursorTy fltPrd5011 = (CursorTy) pvrtmp6043;
            CursorTy fltPrd5012 = (CursorTy) pvrtmp6044;
            CursorTy pvrtmp6046 = (CursorTy) fltPrd5012;
            CursorTy pvrtmp6045 = (CursorTy) fltPrd5011;
            CursorTy y1714 = (CursorTy) pvrtmp6045;
            CursorTy fltPrd5013 = (CursorTy) pvrtmp6043;
            CursorTy fltPrd5014 = (CursorTy) pvrtmp6044;
            CursorTy pvrtmp6048 = (CursorTy) fltPrd5014;
            CursorTy pvrtmp6047 = (CursorTy) fltPrd5013;
            CursorTy end_y1714 = (CursorTy) pvrtmp6048;
            CursorTy end_r1998_3746 = (CursorTy) pvrtmp6041;
            CursorTy endof3502 = (CursorTy) pvrtmp6042;

            *(TagTyPacked *) loc1996 = 11;

            CursorTy writetag4162 = loc1996 + 1;
            CursorTy writecur4163 = (CursorTy) end_y1714;
            CursorTy pvrtmp6050 = (CursorTy) writecur4163;
            CursorTy pvrtmp6049 = (CursorTy) loc1996;
            CursorTy taildc3503 = (CursorTy) pvrtmp6049;
            CursorTy end_taildc3503 = (CursorTy) pvrtmp6050;
            CursorTy pvrtmp6052 = (CursorTy) end_taildc3503;
            CursorTy pvrtmp6051 = (CursorTy) taildc3503;
            CursorTy fltPrd5015 = (CursorTy) pvrtmp6051;
            CursorTy fltPrd5016 = (CursorTy) pvrtmp6052;

            return (CursorCursorCursorCursorProd) {end_r1998_3746, endof3502,
                                                   fltPrd5015, fltPrd5016};
            break;
        }

      case 12:
        {
            CursorTy field_cur4165 = (CursorTy) tmpcur5864;
            CursorTy case2625 = (CursorTy) field_cur4165;
            CursorTy x1715 = (CursorTy) case2625;
            CursorTy loc2637 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct129 =
                                          _copy_Expr(end_r1997, end_r1998, loc2637, x1715);
            CursorTy pvrtmp6053 = tmp_struct129.field0;
            CursorTy pvrtmp6054 = tmp_struct129.field1;
            CursorTy pvrtmp6055 = tmp_struct129.field2;
            CursorTy pvrtmp6056 = tmp_struct129.field3;
            CursorTy fltPrd5017 = (CursorTy) pvrtmp6055;
            CursorTy fltPrd5018 = (CursorTy) pvrtmp6056;
            CursorTy pvrtmp6058 = (CursorTy) fltPrd5018;
            CursorTy pvrtmp6057 = (CursorTy) fltPrd5017;
            CursorTy y1718 = (CursorTy) pvrtmp6057;
            CursorTy fltPrd5019 = (CursorTy) pvrtmp6055;
            CursorTy fltPrd5020 = (CursorTy) pvrtmp6056;
            CursorTy pvrtmp6060 = (CursorTy) fltPrd5020;
            CursorTy pvrtmp6059 = (CursorTy) fltPrd5019;
            CursorTy end_y1718 = (CursorTy) pvrtmp6060;
            CursorTy end_r1998_3747 = (CursorTy) pvrtmp6053;
            CursorTy endof3504 = (CursorTy) pvrtmp6054;
            CursorTy case2626 = (CursorTy) endof3504;
            CursorTy x1716 = (CursorTy) case2626;
            CursorTy loc2638 = (CursorTy) end_y1718;
            CursorCursorCursorCursorProd tmp_struct130 =
                                          _copy_Expr(end_r1997, end_r1998_3747, loc2638, x1716);
            CursorTy pvrtmp6061 = tmp_struct130.field0;
            CursorTy pvrtmp6062 = tmp_struct130.field1;
            CursorTy pvrtmp6063 = tmp_struct130.field2;
            CursorTy pvrtmp6064 = tmp_struct130.field3;
            CursorTy fltPrd5021 = (CursorTy) pvrtmp6063;
            CursorTy fltPrd5022 = (CursorTy) pvrtmp6064;
            CursorTy pvrtmp6066 = (CursorTy) fltPrd5022;
            CursorTy pvrtmp6065 = (CursorTy) fltPrd5021;
            CursorTy y1719 = (CursorTy) pvrtmp6065;
            CursorTy fltPrd5023 = (CursorTy) pvrtmp6063;
            CursorTy fltPrd5024 = (CursorTy) pvrtmp6064;
            CursorTy pvrtmp6068 = (CursorTy) fltPrd5024;
            CursorTy pvrtmp6067 = (CursorTy) fltPrd5023;
            CursorTy end_y1719 = (CursorTy) pvrtmp6068;
            CursorTy end_r1998_3747_3748 = (CursorTy) pvrtmp6061;
            CursorTy endof3505 = (CursorTy) pvrtmp6062;
            CursorTy case2627 = (CursorTy) endof3505;
            CursorTy x1717 = (CursorTy) case2627;
            CursorTy loc2639 = (CursorTy) end_y1719;
            CursorCursorCursorCursorProd tmp_struct131 =
                                          _copy_Expr(end_r1997, end_r1998_3747_3748, loc2639, x1717);
            CursorTy pvrtmp6069 = tmp_struct131.field0;
            CursorTy pvrtmp6070 = tmp_struct131.field1;
            CursorTy pvrtmp6071 = tmp_struct131.field2;
            CursorTy pvrtmp6072 = tmp_struct131.field3;
            CursorTy fltPrd5025 = (CursorTy) pvrtmp6071;
            CursorTy fltPrd5026 = (CursorTy) pvrtmp6072;
            CursorTy pvrtmp6074 = (CursorTy) fltPrd5026;
            CursorTy pvrtmp6073 = (CursorTy) fltPrd5025;
            CursorTy y1720 = (CursorTy) pvrtmp6073;
            CursorTy fltPrd5027 = (CursorTy) pvrtmp6071;
            CursorTy fltPrd5028 = (CursorTy) pvrtmp6072;
            CursorTy pvrtmp6076 = (CursorTy) fltPrd5028;
            CursorTy pvrtmp6075 = (CursorTy) fltPrd5027;
            CursorTy end_y1720 = (CursorTy) pvrtmp6076;
            CursorTy end_r1998_3747_3748_3749 = (CursorTy) pvrtmp6069;
            CursorTy endof3506 = (CursorTy) pvrtmp6070;

            *(TagTyPacked *) loc1996 = 12;

            CursorTy writetag4169 = loc1996 + 1;
            CursorTy writecur4170 = (CursorTy) end_y1718;
            CursorTy writecur4171 = (CursorTy) end_y1719;
            CursorTy writecur4172 = (CursorTy) end_y1720;
            CursorTy pvrtmp6078 = (CursorTy) writecur4172;
            CursorTy pvrtmp6077 = (CursorTy) loc1996;
            CursorTy taildc3507 = (CursorTy) pvrtmp6077;
            CursorTy end_taildc3507 = (CursorTy) pvrtmp6078;
            CursorTy pvrtmp6080 = (CursorTy) end_taildc3507;
            CursorTy pvrtmp6079 = (CursorTy) taildc3507;
            CursorTy fltPrd5029 = (CursorTy) pvrtmp6079;
            CursorTy fltPrd5030 = (CursorTy) pvrtmp6080;

            return (CursorCursorCursorCursorProd) {end_r1998_3747_3748_3749,
                                                   endof3506, fltPrd5029,
                                                   fltPrd5030};
            break;
        }

      case 13:
        {
            CursorTy field_cur4174 = (CursorTy) tmpcur5864;
            CursorTy case2643 = (CursorTy) field_cur4174;
            CursorTy x1721 = (CursorTy) case2643;
            CursorTy loc2651 = loc1996 + 1;
            CursorCursorCursorCursorProd tmp_struct132 =
                                          _copy_Expr(end_r1997, end_r1998, loc2651, x1721);
            CursorTy pvrtmp6081 = tmp_struct132.field0;
            CursorTy pvrtmp6082 = tmp_struct132.field1;
            CursorTy pvrtmp6083 = tmp_struct132.field2;
            CursorTy pvrtmp6084 = tmp_struct132.field3;
            CursorTy fltPrd5031 = (CursorTy) pvrtmp6083;
            CursorTy fltPrd5032 = (CursorTy) pvrtmp6084;
            CursorTy pvrtmp6086 = (CursorTy) fltPrd5032;
            CursorTy pvrtmp6085 = (CursorTy) fltPrd5031;
            CursorTy y1723 = (CursorTy) pvrtmp6085;
            CursorTy fltPrd5033 = (CursorTy) pvrtmp6083;
            CursorTy fltPrd5034 = (CursorTy) pvrtmp6084;
            CursorTy pvrtmp6088 = (CursorTy) fltPrd5034;
            CursorTy pvrtmp6087 = (CursorTy) fltPrd5033;
            CursorTy end_y1723 = (CursorTy) pvrtmp6088;
            CursorTy end_r1998_3750 = (CursorTy) pvrtmp6081;
            CursorTy endof3508 = (CursorTy) pvrtmp6082;
            CursorTy case2644 = (CursorTy) endof3508;
            CursorTy x1722 = (CursorTy) case2644;
            CursorTy loc2652 = (CursorTy) end_y1723;
            CursorCursorCursorCursorProd tmp_struct133 =
                                          _copy_ListExpr(end_r1997, end_r1998_3750, loc2652, x1722);
            CursorTy pvrtmp6089 = tmp_struct133.field0;
            CursorTy pvrtmp6090 = tmp_struct133.field1;
            CursorTy pvrtmp6091 = tmp_struct133.field2;
            CursorTy pvrtmp6092 = tmp_struct133.field3;
            CursorTy fltPrd5035 = (CursorTy) pvrtmp6091;
            CursorTy fltPrd5036 = (CursorTy) pvrtmp6092;
            CursorTy pvrtmp6094 = (CursorTy) fltPrd5036;
            CursorTy pvrtmp6093 = (CursorTy) fltPrd5035;
            CursorTy y1724 = (CursorTy) pvrtmp6093;
            CursorTy fltPrd5037 = (CursorTy) pvrtmp6091;
            CursorTy fltPrd5038 = (CursorTy) pvrtmp6092;
            CursorTy pvrtmp6096 = (CursorTy) fltPrd5038;
            CursorTy pvrtmp6095 = (CursorTy) fltPrd5037;
            CursorTy end_y1724 = (CursorTy) pvrtmp6096;
            CursorTy end_r1998_3750_3751 = (CursorTy) pvrtmp6089;
            CursorTy endof3509 = (CursorTy) pvrtmp6090;

            *(TagTyPacked *) loc1996 = 13;

            CursorTy writetag4177 = loc1996 + 1;
            CursorTy writecur4178 = (CursorTy) end_y1723;
            CursorTy writecur4179 = (CursorTy) end_y1724;
            CursorTy pvrtmp6098 = (CursorTy) writecur4179;
            CursorTy pvrtmp6097 = (CursorTy) loc1996;
            CursorTy taildc3510 = (CursorTy) pvrtmp6097;
            CursorTy end_taildc3510 = (CursorTy) pvrtmp6098;
            CursorTy pvrtmp6100 = (CursorTy) end_taildc3510;
            CursorTy pvrtmp6099 = (CursorTy) taildc3510;
            CursorTy fltPrd5039 = (CursorTy) pvrtmp6099;
            CursorTy fltPrd5040 = (CursorTy) pvrtmp6100;

            return (CursorCursorCursorCursorProd) {end_r1998_3750_3751,
                                                   endof3509, fltPrd5039,
                                                   fltPrd5040};
            break;
        }

      case 14:
        {
            CursorTy field_cur4181 = (CursorTy) tmpcur5864;
            CursorTy case2655 = (CursorTy) field_cur4181;
            SymTy tmpval6101 = *(SymTy *) case2655;
            CursorTy tmpcur6102 = case2655 + sizeof(SymTy);
            SymTy x1725 = (SymTy) tmpval6101;
            CursorTy end_x1725 = (CursorTy) tmpcur6102;
            CursorTy jump3511 = case2655 + 8;

            *(TagTyPacked *) loc1996 = 14;

            CursorTy writetag4183 = loc1996 + 1;

            *(SymTy *) writetag4183 = x1725;

            CursorTy writecur4184 = writetag4183 + sizeof(SymTy);
            CursorTy pvrtmp6104 = (CursorTy) writecur4184;
            CursorTy pvrtmp6103 = (CursorTy) loc1996;
            CursorTy taildc3512 = (CursorTy) pvrtmp6103;
            CursorTy end_taildc3512 = (CursorTy) pvrtmp6104;
            CursorTy pvrtmp6106 = (CursorTy) end_taildc3512;
            CursorTy pvrtmp6105 = (CursorTy) taildc3512;
            CursorTy fltPrd5041 = (CursorTy) pvrtmp6105;
            CursorTy fltPrd5042 = (CursorTy) pvrtmp6106;

            return (CursorCursorCursorCursorProd) {end_r1998, jump3511,
                                                   fltPrd5041, fltPrd5042};
            break;
        }

      case 15:
        {
            CursorTy field_cur4186 = (CursorTy) tmpcur5864;
            CursorTy case2659 = (CursorTy) field_cur4186;
            SymTy tmpval6107 = *(SymTy *) case2659;
            CursorTy tmpcur6108 = case2659 + sizeof(SymTy);
            SymTy x1727 = (SymTy) tmpval6107;
            CursorTy end_x1727 = (CursorTy) tmpcur6108;
            CursorTy jump3513 = case2659 + 8;

            *(TagTyPacked *) loc1996 = 15;

            CursorTy writetag4188 = loc1996 + 1;

            *(SymTy *) writetag4188 = x1727;

            CursorTy writecur4189 = writetag4188 + sizeof(SymTy);
            CursorTy pvrtmp6110 = (CursorTy) writecur4189;
            CursorTy pvrtmp6109 = (CursorTy) loc1996;
            CursorTy taildc3514 = (CursorTy) pvrtmp6109;
            CursorTy end_taildc3514 = (CursorTy) pvrtmp6110;
            CursorTy pvrtmp6112 = (CursorTy) end_taildc3514;
            CursorTy pvrtmp6111 = (CursorTy) taildc3514;
            CursorTy fltPrd5043 = (CursorTy) pvrtmp6111;
            CursorTy fltPrd5044 = (CursorTy) pvrtmp6112;

            return (CursorCursorCursorCursorProd) {end_r1998, jump3513,
                                                   fltPrd5043, fltPrd5044};
            break;
        }

      case 16:
        {
            CursorTy field_cur4191 = (CursorTy) tmpcur5864;
            CursorTy case2663 = (CursorTy) field_cur4191;
            SymTy tmpval6113 = *(SymTy *) case2663;
            CursorTy tmpcur6114 = case2663 + sizeof(SymTy);
            SymTy x1729 = (SymTy) tmpval6113;
            CursorTy end_x1729 = (CursorTy) tmpcur6114;
            CursorTy jump3515 = case2663 + 8;

            *(TagTyPacked *) loc1996 = 16;

            CursorTy writetag4193 = loc1996 + 1;

            *(SymTy *) writetag4193 = x1729;

            CursorTy writecur4194 = writetag4193 + sizeof(SymTy);
            CursorTy pvrtmp6116 = (CursorTy) writecur4194;
            CursorTy pvrtmp6115 = (CursorTy) loc1996;
            CursorTy taildc3516 = (CursorTy) pvrtmp6115;
            CursorTy end_taildc3516 = (CursorTy) pvrtmp6116;
            CursorTy pvrtmp6118 = (CursorTy) end_taildc3516;
            CursorTy pvrtmp6117 = (CursorTy) taildc3516;
            CursorTy fltPrd5045 = (CursorTy) pvrtmp6117;
            CursorTy fltPrd5046 = (CursorTy) pvrtmp6118;

            return (CursorCursorCursorCursorProd) {end_r1998, jump3515,
                                                   fltPrd5045, fltPrd5046};
            break;
        }

      case 17:
        {
            CursorTy field_cur4196 = (CursorTy) tmpcur5864;
            CursorTy jump3517 = loc1995 + 1;

            *(TagTyPacked *) loc1996 = 17;

            CursorTy writetag4197 = loc1996 + 1;
            CursorTy pvrtmp6120 = (CursorTy) writetag4197;
            CursorTy pvrtmp6119 = (CursorTy) loc1996;
            CursorTy taildc3518 = (CursorTy) pvrtmp6119;
            CursorTy end_taildc3518 = (CursorTy) pvrtmp6120;
            CursorTy pvrtmp6122 = (CursorTy) end_taildc3518;
            CursorTy pvrtmp6121 = (CursorTy) taildc3518;
            CursorTy fltPrd5047 = (CursorTy) pvrtmp6121;
            CursorTy fltPrd5048 = (CursorTy) pvrtmp6122;

            return (CursorCursorCursorCursorProd) {end_r1998, jump3517,
                                                   fltPrd5047, fltPrd5048};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7342 = *(CursorTy *) tmpcur5864;
            CursorTy tmpaftercur7343 = tmpcur5864 + 8;
            TagTyPacked tagtmp7344 = *(TagTyPacked *) tmpcur7342;
            CursorTy tailtmp7345 = tmpcur7342 + 1;

            tmpval5863 = tagtmp7344;
            tmpcur5864 = tailtmp7345;
            goto switch6123;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7342 = *(CursorTy *) tmpcur5864;
            CursorTy tmpaftercur7343 = tmpcur5864 + 8;
            TagTyPacked tagtmp7344 = *(TagTyPacked *) tmpcur7342;
            CursorTy tailtmp7345 = tmpcur7342 + 1;

            tmpval5863 = tagtmp7344;
            tmpcur5864 = tailtmp7345;
            goto switch6123;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval5863");
            exit(1);
        }
    }
}

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

CursorCursorCursorCursorProd _copy_Toplvl(CursorTy end_r2003,
                                          CursorTy end_r2004, CursorTy loc2002,
                                          CursorTy arg1786)
{
    CursorTy loc2001 = (CursorTy) arg1786;

    if (loc2002 + 26 > end_r2004) {
        ChunkTy new_chunk173 = alloc_chunk(end_r2004);
        CursorTy chunk_start174 = new_chunk173.start_ptr;
        CursorTy chunk_end175 = new_chunk173.end_ptr;

        end_r2004 = chunk_end175;
        *(TagTyPacked *) loc2002 = 255;

        CursorTy redir = loc2002 + 1;

        *(CursorTy *) redir = chunk_start174;
        loc2002 = chunk_start174;
    }

    CursorTy loc2788 = loc2002 + 1;
    CursorTy loc2789 = loc2788 + 8;
    CursorTy loc2805 = loc2002 + 1;
    CursorTy loc2806 = loc2805 + 8;
    CursorTy loc2807 = loc2806 + 8;
    CursorTy loc2824 = loc2002 + 1;
    CursorTy loc2825 = loc2824 + 8;
    CursorTy loc2841 = loc2002 + 1;
    CursorTy loc2842 = loc2841 + 8;
    CursorTy loc2843 = loc2842 + 8;
    TagTyPacked tmpval6181 = *(TagTyPacked *) arg1786;
    CursorTy tmpcur6182 = arg1786 + 1;


  switch6339:
    ;
    switch (tmpval6181) {

      case 0:
        {
            CursorTy field_cur4244 = (CursorTy) tmpcur6182;
            CursorTy case2743 = (CursorTy) field_cur4244;
            CursorTy x1787 = (CursorTy) case2743;
            CursorTy loc2751 = loc2002 + 1;
            CursorCursorCursorCursorProd tmp_struct159 =
                                          _copy_ListSym(end_r2003, end_r2004, loc2751, x1787);
            CursorTy pvrtmp6183 = tmp_struct159.field0;
            CursorTy pvrtmp6184 = tmp_struct159.field1;
            CursorTy pvrtmp6185 = tmp_struct159.field2;
            CursorTy pvrtmp6186 = tmp_struct159.field3;
            CursorTy fltPrd5049 = (CursorTy) pvrtmp6185;
            CursorTy fltPrd5050 = (CursorTy) pvrtmp6186;
            CursorTy pvrtmp6188 = (CursorTy) fltPrd5050;
            CursorTy pvrtmp6187 = (CursorTy) fltPrd5049;
            CursorTy y1789 = (CursorTy) pvrtmp6187;
            CursorTy fltPrd5051 = (CursorTy) pvrtmp6185;
            CursorTy fltPrd5052 = (CursorTy) pvrtmp6186;
            CursorTy pvrtmp6190 = (CursorTy) fltPrd5052;
            CursorTy pvrtmp6189 = (CursorTy) fltPrd5051;
            CursorTy end_y1789 = (CursorTy) pvrtmp6190;
            CursorTy end_r2004_3752 = (CursorTy) pvrtmp6183;
            CursorTy endof3565 = (CursorTy) pvrtmp6184;
            CursorTy case2744 = (CursorTy) endof3565;
            CursorTy x1788 = (CursorTy) case2744;
            CursorTy loc2752 = (CursorTy) end_y1789;
            // TODO
            CursorCursorCursorCursorProd tmp_struct160 =
                duplicate_expr(4, end_r2003, end_r2004_3752, loc2752, x1788);
            CursorTy pvrtmp6191 = tmp_struct160.field0;
            CursorTy pvrtmp6192 = tmp_struct160.field1;
            CursorTy pvrtmp6193 = tmp_struct160.field2;
            CursorTy pvrtmp6194 = tmp_struct160.field3;
            CursorTy fltPrd5053 = (CursorTy) pvrtmp6193;
            CursorTy fltPrd5054 = (CursorTy) pvrtmp6194;
            CursorTy pvrtmp6196 = (CursorTy) fltPrd5054;
            CursorTy pvrtmp6195 = (CursorTy) fltPrd5053;
            CursorTy y1790 = (CursorTy) pvrtmp6195;
            CursorTy fltPrd5055 = (CursorTy) pvrtmp6193;
            CursorTy fltPrd5056 = (CursorTy) pvrtmp6194;
            CursorTy pvrtmp6198 = (CursorTy) fltPrd5056;
            CursorTy pvrtmp6197 = (CursorTy) fltPrd5055;
            CursorTy end_y1790 = (CursorTy) pvrtmp6198;
            CursorTy end_r2004_3752_3753 = (CursorTy) pvrtmp6191;
            CursorTy endof3566 = (CursorTy) pvrtmp6192;

            *(TagTyPacked *) loc2002 = 0;

            CursorTy writetag4247 = loc2002 + 1;
            CursorTy writecur4248 = (CursorTy) end_y1789;
            CursorTy writecur4249 = (CursorTy) end_y1790;
            CursorTy pvrtmp6200 = (CursorTy) writecur4249;
            CursorTy pvrtmp6199 = (CursorTy) loc2002;
            CursorTy taildc3567 = (CursorTy) pvrtmp6199;
            CursorTy end_taildc3567 = (CursorTy) pvrtmp6200;
            CursorTy pvrtmp6202 = (CursorTy) end_taildc3567;
            CursorTy pvrtmp6201 = (CursorTy) taildc3567;
            CursorTy fltPrd5057 = (CursorTy) pvrtmp6201;
            CursorTy fltPrd5058 = (CursorTy) pvrtmp6202;

            return (CursorCursorCursorCursorProd) {end_r2004_3752_3753,
                                                   endof3566, fltPrd5057,
                                                   fltPrd5058};
            break;
        }

      case 1:
        {
            CursorTy field_cur4251 = (CursorTy) tmpcur6182;
            CursorTy case2755 = (CursorTy) field_cur4251;
            CursorTy x1791 = (CursorTy) case2755;
            CursorTy loc2763 = loc2002 + 1;
            CursorCursorCursorCursorProd tmp_struct161 =
                                          _copy_ListSym(end_r2003, end_r2004, loc2763, x1791);
            CursorTy pvrtmp6203 = tmp_struct161.field0;
            CursorTy pvrtmp6204 = tmp_struct161.field1;
            CursorTy pvrtmp6205 = tmp_struct161.field2;
            CursorTy pvrtmp6206 = tmp_struct161.field3;
            CursorTy fltPrd5059 = (CursorTy) pvrtmp6205;
            CursorTy fltPrd5060 = (CursorTy) pvrtmp6206;
            CursorTy pvrtmp6208 = (CursorTy) fltPrd5060;
            CursorTy pvrtmp6207 = (CursorTy) fltPrd5059;
            CursorTy y1793 = (CursorTy) pvrtmp6207;
            CursorTy fltPrd5061 = (CursorTy) pvrtmp6205;
            CursorTy fltPrd5062 = (CursorTy) pvrtmp6206;
            CursorTy pvrtmp6210 = (CursorTy) fltPrd5062;
            CursorTy pvrtmp6209 = (CursorTy) fltPrd5061;
            CursorTy end_y1793 = (CursorTy) pvrtmp6210;
            CursorTy end_r2004_3754 = (CursorTy) pvrtmp6203;
            CursorTy endof3568 = (CursorTy) pvrtmp6204;
            CursorTy case2756 = (CursorTy) endof3568;
            CursorTy x1792 = (CursorTy) case2756;
            CursorTy loc2764 = (CursorTy) end_y1793;
            CursorCursorCursorCursorProd tmp_struct162 =
                                          _copy_Expr(end_r2003, end_r2004_3754, loc2764, x1792);
            CursorTy pvrtmp6211 = tmp_struct162.field0;
            CursorTy pvrtmp6212 = tmp_struct162.field1;
            CursorTy pvrtmp6213 = tmp_struct162.field2;
            CursorTy pvrtmp6214 = tmp_struct162.field3;
            CursorTy fltPrd5063 = (CursorTy) pvrtmp6213;
            CursorTy fltPrd5064 = (CursorTy) pvrtmp6214;
            CursorTy pvrtmp6216 = (CursorTy) fltPrd5064;
            CursorTy pvrtmp6215 = (CursorTy) fltPrd5063;
            CursorTy y1794 = (CursorTy) pvrtmp6215;
            CursorTy fltPrd5065 = (CursorTy) pvrtmp6213;
            CursorTy fltPrd5066 = (CursorTy) pvrtmp6214;
            CursorTy pvrtmp6218 = (CursorTy) fltPrd5066;
            CursorTy pvrtmp6217 = (CursorTy) fltPrd5065;
            CursorTy end_y1794 = (CursorTy) pvrtmp6218;
            CursorTy end_r2004_3754_3755 = (CursorTy) pvrtmp6211;
            CursorTy endof3569 = (CursorTy) pvrtmp6212;

            *(TagTyPacked *) loc2002 = 1;

            CursorTy writetag4254 = loc2002 + 1;
            CursorTy writecur4255 = (CursorTy) end_y1793;
            CursorTy writecur4256 = (CursorTy) end_y1794;
            CursorTy pvrtmp6220 = (CursorTy) writecur4256;
            CursorTy pvrtmp6219 = (CursorTy) loc2002;
            CursorTy taildc3570 = (CursorTy) pvrtmp6219;
            CursorTy end_taildc3570 = (CursorTy) pvrtmp6220;
            CursorTy pvrtmp6222 = (CursorTy) end_taildc3570;
            CursorTy pvrtmp6221 = (CursorTy) taildc3570;
            CursorTy fltPrd5067 = (CursorTy) pvrtmp6221;
            CursorTy fltPrd5068 = (CursorTy) pvrtmp6222;

            return (CursorCursorCursorCursorProd) {end_r2004_3754_3755,
                                                   endof3569, fltPrd5067,
                                                   fltPrd5068};
            break;
        }

      case 2:
        {
            CursorTy field_cur4258 = (CursorTy) tmpcur6182;
            CursorTy case2767 = (CursorTy) field_cur4258;
            CursorTy x1795 = (CursorTy) case2767;
            CursorTy loc2771 = loc2002 + 1;
            CursorCursorCursorCursorProd tmp_struct163 =
                                          _copy_ListToplvl(end_r2003, end_r2004, loc2771, x1795);
            CursorTy pvrtmp6223 = tmp_struct163.field0;
            CursorTy pvrtmp6224 = tmp_struct163.field1;
            CursorTy pvrtmp6225 = tmp_struct163.field2;
            CursorTy pvrtmp6226 = tmp_struct163.field3;
            CursorTy fltPrd5069 = (CursorTy) pvrtmp6225;
            CursorTy fltPrd5070 = (CursorTy) pvrtmp6226;
            CursorTy pvrtmp6228 = (CursorTy) fltPrd5070;
            CursorTy pvrtmp6227 = (CursorTy) fltPrd5069;
            CursorTy y1796 = (CursorTy) pvrtmp6227;
            CursorTy fltPrd5071 = (CursorTy) pvrtmp6225;
            CursorTy fltPrd5072 = (CursorTy) pvrtmp6226;
            CursorTy pvrtmp6230 = (CursorTy) fltPrd5072;
            CursorTy pvrtmp6229 = (CursorTy) fltPrd5071;
            CursorTy end_y1796 = (CursorTy) pvrtmp6230;
            CursorTy end_r2004_3756 = (CursorTy) pvrtmp6223;
            CursorTy endof3571 = (CursorTy) pvrtmp6224;

            *(TagTyPacked *) loc2002 = 2;

            CursorTy writetag4260 = loc2002 + 1;
            CursorTy writecur4261 = (CursorTy) end_y1796;
            CursorTy pvrtmp6232 = (CursorTy) writecur4261;
            CursorTy pvrtmp6231 = (CursorTy) loc2002;
            CursorTy taildc3572 = (CursorTy) pvrtmp6231;
            CursorTy end_taildc3572 = (CursorTy) pvrtmp6232;
            CursorTy pvrtmp6234 = (CursorTy) end_taildc3572;
            CursorTy pvrtmp6233 = (CursorTy) taildc3572;
            CursorTy fltPrd5073 = (CursorTy) pvrtmp6233;
            CursorTy fltPrd5074 = (CursorTy) pvrtmp6234;

            return (CursorCursorCursorCursorProd) {end_r2004_3756, endof3571,
                                                   fltPrd5073, fltPrd5074};
            break;
        }

      case 3:
        {
            CursorTy field_cur4263 = (CursorTy) tmpcur6182;
            CursorTy case2773 = (CursorTy) field_cur4263;
            CursorTy x1797 = (CursorTy) case2773;
            CursorTy loc2777 = loc2002 + 1;
            CursorCursorCursorCursorProd tmp_struct164 =
                                          _copy_Expr(end_r2003, end_r2004, loc2777, x1797);
            CursorTy pvrtmp6235 = tmp_struct164.field0;
            CursorTy pvrtmp6236 = tmp_struct164.field1;
            CursorTy pvrtmp6237 = tmp_struct164.field2;
            CursorTy pvrtmp6238 = tmp_struct164.field3;
            CursorTy fltPrd5075 = (CursorTy) pvrtmp6237;
            CursorTy fltPrd5076 = (CursorTy) pvrtmp6238;
            CursorTy pvrtmp6240 = (CursorTy) fltPrd5076;
            CursorTy pvrtmp6239 = (CursorTy) fltPrd5075;
            CursorTy y1798 = (CursorTy) pvrtmp6239;
            CursorTy fltPrd5077 = (CursorTy) pvrtmp6237;
            CursorTy fltPrd5078 = (CursorTy) pvrtmp6238;
            CursorTy pvrtmp6242 = (CursorTy) fltPrd5078;
            CursorTy pvrtmp6241 = (CursorTy) fltPrd5077;
            CursorTy end_y1798 = (CursorTy) pvrtmp6242;
            CursorTy end_r2004_3757 = (CursorTy) pvrtmp6235;
            CursorTy endof3573 = (CursorTy) pvrtmp6236;

            *(TagTyPacked *) loc2002 = 3;

            CursorTy writetag4265 = loc2002 + 1;
            CursorTy writecur4266 = (CursorTy) end_y1798;
            CursorTy pvrtmp6244 = (CursorTy) writecur4266;
            CursorTy pvrtmp6243 = (CursorTy) loc2002;
            CursorTy taildc3574 = (CursorTy) pvrtmp6243;
            CursorTy end_taildc3574 = (CursorTy) pvrtmp6244;
            CursorTy pvrtmp6246 = (CursorTy) end_taildc3574;
            CursorTy pvrtmp6245 = (CursorTy) taildc3574;
            CursorTy fltPrd5079 = (CursorTy) pvrtmp6245;
            CursorTy fltPrd5080 = (CursorTy) pvrtmp6246;

            return (CursorCursorCursorCursorProd) {end_r2004_3757, endof3573,
                                                   fltPrd5079, fltPrd5080};
            break;
        }

      case 4:
        {
            CursorTy field_cur4268 = (CursorTy) tmpcur6182;
            CursorTy tmpcur6247 = *(CursorTy *) field_cur4268;
            CursorTy tmpaftercur6248 = field_cur4268 + 8;
            CursorTy case2779 = (CursorTy) field_cur4268;
            CursorTy x1799 = (CursorTy) tmpcur6247;
            CursorTy end_x1799 = (CursorTy) tmpaftercur6248;
            CursorTy case2780 = (CursorTy) end_x1799;
            CursorTy x1800 = (CursorTy) case2780;
            CursorTy case2781 = (CursorTy) x1799;
            CursorTy x1801 = (CursorTy) case2781;
            CursorTy jump3575 = case2779 + 8;
            CursorCursorCursorCursorProd tmp_struct165 =
                                          _copy_ListSym(end_r2003, end_r2004, loc2789, x1800);
            CursorTy pvrtmp6249 = tmp_struct165.field0;
            CursorTy pvrtmp6250 = tmp_struct165.field1;
            CursorTy pvrtmp6251 = tmp_struct165.field2;
            CursorTy pvrtmp6252 = tmp_struct165.field3;
            CursorTy fltPrd5081 = (CursorTy) pvrtmp6251;
            CursorTy fltPrd5082 = (CursorTy) pvrtmp6252;
            CursorTy pvrtmp6254 = (CursorTy) fltPrd5082;
            CursorTy pvrtmp6253 = (CursorTy) fltPrd5081;
            CursorTy y1803 = (CursorTy) pvrtmp6253;
            CursorTy fltPrd5083 = (CursorTy) pvrtmp6251;
            CursorTy fltPrd5084 = (CursorTy) pvrtmp6252;
            CursorTy pvrtmp6256 = (CursorTy) fltPrd5084;
            CursorTy pvrtmp6255 = (CursorTy) fltPrd5083;
            CursorTy end_y1803 = (CursorTy) pvrtmp6256;
            CursorTy end_r2004_3758 = (CursorTy) pvrtmp6249;
            CursorTy endof3576 = (CursorTy) pvrtmp6250;
            CursorTy loc2790 = (CursorTy) end_y1803;
            CursorCursorCursorCursorProd tmp_struct166 =
                                          _copy_Expr(end_r2003, end_r2004_3758, loc2790, x1801);
            CursorTy pvrtmp6257 = tmp_struct166.field0;
            CursorTy pvrtmp6258 = tmp_struct166.field1;
            CursorTy pvrtmp6259 = tmp_struct166.field2;
            CursorTy pvrtmp6260 = tmp_struct166.field3;
            CursorTy fltPrd5085 = (CursorTy) pvrtmp6259;
            CursorTy fltPrd5086 = (CursorTy) pvrtmp6260;
            CursorTy pvrtmp6262 = (CursorTy) fltPrd5086;
            CursorTy pvrtmp6261 = (CursorTy) fltPrd5085;
            CursorTy y1804 = (CursorTy) pvrtmp6261;
            CursorTy fltPrd5087 = (CursorTy) pvrtmp6259;
            CursorTy fltPrd5088 = (CursorTy) pvrtmp6260;
            CursorTy pvrtmp6264 = (CursorTy) fltPrd5088;
            CursorTy pvrtmp6263 = (CursorTy) fltPrd5087;
            CursorTy end_y1804 = (CursorTy) pvrtmp6264;
            CursorTy end_r2004_3758_3759 = (CursorTy) pvrtmp6257;
            CursorTy endof3577 = (CursorTy) pvrtmp6258;
            CursorTy y1802 = (CursorTy) end_y1803;

            *(TagTyPacked *) loc2002 = 4;

            CursorTy writetag4272 = loc2002 + 1;

            *(CursorTy *) writetag4272 = y1802;

            CursorTy writecur4273 = writetag4272 + 8;
            CursorTy writecur4274 = (CursorTy) end_y1803;
            CursorTy writecur4275 = (CursorTy) end_y1804;
            CursorTy pvrtmp6266 = (CursorTy) writecur4275;
            CursorTy pvrtmp6265 = (CursorTy) loc2002;
            CursorTy taildc3578 = (CursorTy) pvrtmp6265;
            CursorTy end_taildc3578 = (CursorTy) pvrtmp6266;
            CursorTy pvrtmp6268 = (CursorTy) end_taildc3578;
            CursorTy pvrtmp6267 = (CursorTy) taildc3578;
            CursorTy fltPrd5089 = (CursorTy) pvrtmp6267;
            CursorTy fltPrd5090 = (CursorTy) pvrtmp6268;

            return (CursorCursorCursorCursorProd) {end_r2004_3758_3759,
                                                   endof3577, fltPrd5089,
                                                   fltPrd5090};
            break;
        }

      case 6:
        {
            CursorTy field_cur4290 = (CursorTy) tmpcur6182;
            CursorTy tmpcur6293 = *(CursorTy *) field_cur4290;
            CursorTy tmpaftercur6294 = field_cur4290 + 8;
            CursorTy case2815 = (CursorTy) field_cur4290;
            CursorTy x1813 = (CursorTy) tmpcur6293;
            CursorTy end_x1813 = (CursorTy) tmpaftercur6294;
            CursorTy case2816 = (CursorTy) end_x1813;
            CursorTy x1814 = (CursorTy) case2816;
            CursorTy case2817 = (CursorTy) x1813;
            CursorTy x1815 = (CursorTy) case2817;
            CursorTy jump3584 = case2815 + 8;
            CursorCursorCursorCursorProd tmp_struct169 =
                                          _copy_ListSym(end_r2003, end_r2004, loc2825, x1814);
            CursorTy pvrtmp6295 = tmp_struct169.field0;
            CursorTy pvrtmp6296 = tmp_struct169.field1;
            CursorTy pvrtmp6297 = tmp_struct169.field2;
            CursorTy pvrtmp6298 = tmp_struct169.field3;
            CursorTy fltPrd5101 = (CursorTy) pvrtmp6297;
            CursorTy fltPrd5102 = (CursorTy) pvrtmp6298;
            CursorTy pvrtmp6300 = (CursorTy) fltPrd5102;
            CursorTy pvrtmp6299 = (CursorTy) fltPrd5101;
            CursorTy y1817 = (CursorTy) pvrtmp6299;
            CursorTy fltPrd5103 = (CursorTy) pvrtmp6297;
            CursorTy fltPrd5104 = (CursorTy) pvrtmp6298;
            CursorTy pvrtmp6302 = (CursorTy) fltPrd5104;
            CursorTy pvrtmp6301 = (CursorTy) fltPrd5103;
            CursorTy end_y1817 = (CursorTy) pvrtmp6302;
            CursorTy end_r2004_3762 = (CursorTy) pvrtmp6295;
            CursorTy endof3585 = (CursorTy) pvrtmp6296;
            CursorTy loc2826 = (CursorTy) end_y1817;
            CursorCursorCursorCursorProd tmp_struct170 =
                                          _copy_Expr(end_r2003, end_r2004_3762, loc2826, x1815);
            CursorTy pvrtmp6303 = tmp_struct170.field0;
            CursorTy pvrtmp6304 = tmp_struct170.field1;
            CursorTy pvrtmp6305 = tmp_struct170.field2;
            CursorTy pvrtmp6306 = tmp_struct170.field3;
            CursorTy fltPrd5105 = (CursorTy) pvrtmp6305;
            CursorTy fltPrd5106 = (CursorTy) pvrtmp6306;
            CursorTy pvrtmp6308 = (CursorTy) fltPrd5106;
            CursorTy pvrtmp6307 = (CursorTy) fltPrd5105;
            CursorTy y1818 = (CursorTy) pvrtmp6307;
            CursorTy fltPrd5107 = (CursorTy) pvrtmp6305;
            CursorTy fltPrd5108 = (CursorTy) pvrtmp6306;
            CursorTy pvrtmp6310 = (CursorTy) fltPrd5108;
            CursorTy pvrtmp6309 = (CursorTy) fltPrd5107;
            CursorTy end_y1818 = (CursorTy) pvrtmp6310;
            CursorTy end_r2004_3762_3763 = (CursorTy) pvrtmp6303;
            CursorTy endof3586 = (CursorTy) pvrtmp6304;
            CursorTy y1816 = (CursorTy) end_y1817;

            *(TagTyPacked *) loc2002 = 6;

            CursorTy writetag4294 = loc2002 + 1;

            *(CursorTy *) writetag4294 = y1816;

            CursorTy writecur4295 = writetag4294 + 8;
            CursorTy writecur4296 = (CursorTy) end_y1817;
            CursorTy writecur4297 = (CursorTy) end_y1818;
            CursorTy pvrtmp6312 = (CursorTy) writecur4297;
            CursorTy pvrtmp6311 = (CursorTy) loc2002;
            CursorTy taildc3587 = (CursorTy) pvrtmp6311;
            CursorTy end_taildc3587 = (CursorTy) pvrtmp6312;
            CursorTy pvrtmp6314 = (CursorTy) end_taildc3587;
            CursorTy pvrtmp6313 = (CursorTy) taildc3587;
            CursorTy fltPrd5109 = (CursorTy) pvrtmp6313;
            CursorTy fltPrd5110 = (CursorTy) pvrtmp6314;

            return (CursorCursorCursorCursorProd) {end_r2004_3762_3763,
                                                   endof3586, fltPrd5109,
                                                   fltPrd5110};
            break;
        }

      case 255:
        {
            CursorTy tmpcur7350 = *(CursorTy *) tmpcur6182;
            CursorTy tmpaftercur7351 = tmpcur6182 + 8;
            TagTyPacked tagtmp7352 = *(TagTyPacked *) tmpcur7350;
            CursorTy tailtmp7353 = tmpcur7350 + 1;

            tmpval6181 = tagtmp7352;
            tmpcur6182 = tailtmp7353;
            goto switch6339;
            break;
        }

      case 254:
        {
            CursorTy tmpcur7350 = *(CursorTy *) tmpcur6182;
            CursorTy tmpaftercur7351 = tmpcur6182 + 8;
            TagTyPacked tagtmp7352 = *(TagTyPacked *) tmpcur7350;
            CursorTy tailtmp7353 = tmpcur7350 + 1;

            tmpval6181 = tagtmp7352;
            tmpcur6182 = tailtmp7353;
            goto switch6339;
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval6181");
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
    // printf("copied: %lld\n", copied);
}
