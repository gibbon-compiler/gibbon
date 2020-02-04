#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
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

typedef char TagTyPacked;   // Must be consistent with codegen in Target.hs
typedef char TagTyBoxed;    // Must be consistent with codegen in Target.hs
typedef long long IntTy;    // Int64 in Haskell
typedef int SymTy;          // Word16 in Haskell. This could actually be a
                            // uint16_t. However, uthash's HASH_*_INT macros
                            // only work with proper int's.
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
  printf("Error, key %d not found!\n",key);
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
    HASH_ADD_INT( global_sym_table, idx, s );
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
    HASH_FIND_INT( global_sym_table, &idx, s );
    return printf("%s", s->value);
  }
}

SymTy gensym() {
    global_gensym_counter += 1;
    SymTy idx = global_gensym_counter;
    char value[global_max_symbol_len];
    sprintf(value, "gensym_%d",idx);
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
    CursorTy end = start + size;

    RegionTy *reg = malloc(sizeof(RegionTy));
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
        trav_to_first_chunk(footer->prev);
    }
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
                    free_region(first_chunk);
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

BoolTy is_big(CursorTy cur) {
    return false;
}

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
            fprintf(stderr, "Not enough arguments after -file, expected <file>.\n");
            show_usage(argv);
            exit(1);
          }
          global_benchfile_param = argv[i+1];
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
typedef struct TagInt64CursorCursorProd_struct {
            TagTyPacked field0;
            IntTy field1;
            CursorTy field2;
            CursorTy field3;
        } TagInt64CursorCursorProd;
typedef struct TagInt64CursorCursorCursorProd_struct {
            TagTyPacked field0;
            IntTy field1;
            CursorTy field2;
            CursorTy field3;
            CursorTy field4;
        } TagInt64CursorCursorCursorProd;
typedef struct TagCursorProd_struct {
            TagTyPacked field0;
            CursorTy field1;
        } TagCursorProd;
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
typedef struct PtrProd_struct {
            PtrTy field0;
        } PtrProd;
typedef struct PtrCursorProd_struct {
            PtrTy field0;
            CursorTy field1;
        } PtrCursorProd;
CursorCursorCursorProd mkFoo_seq(CursorTy end_r740, CursorTy loc739, IntTy i88);
CursorCursorCursorProd copy(CursorTy end_r743, CursorTy end_r744,
                            CursorTy loc742, CursorTy foo92);
CursorCursorCursorCursorProd copy_seq(CursorTy end_r747, CursorTy end_r748,
                                      CursorTy loc746, CursorTy foo107);
IntTy sumFoo(CursorTy end_r750, CursorTy foo121);
CursorInt64Prod sumFoo_seq(CursorTy end_r752, CursorTy foo136);
CursorCursorCursorProd mkFoo(CursorTy end_r754, CursorTy loc753, IntTy i150);
CursorCursorCursorCursorProd _copy_Foo(CursorTy end_r757, CursorTy end_r758,
                                       CursorTy loc756, CursorTy arg655);
CursorInt64Prod _traverse_Foo(CursorTy end_r760, CursorTy arg692);
PtrCursorProd unpack_Foo(CursorTy p2613);
PtrTy print_Foo(CursorTy p2661);
CursorCursorCursorProd mkFoo_seq(CursorTy end_r740, CursorTy loc739, IntTy i88)
{
    if (loc739 + 9 > end_r740) {
        ChunkTy new_chunk5 = alloc_chunk(end_r740);
        CursorTy chunk_start6 = new_chunk5.start_ptr;
        CursorTy chunk_end7 = new_chunk5.end_ptr;
        
        end_r740 = chunk_end7;
        *(TagTyPacked *) loc739 = 100;
        
        CursorTy redir = loc739 + 1;
        
        *(CursorTy *) redir = chunk_start6;
        loc739 = chunk_start6;
    }
    
    CursorTy loc771 = loc739 + (IntTy) 1;
    CursorTy loc772 = loc771 + (IntTy) 8;
    CursorTy loc773 = loc772 + (IntTy) 8;
    CursorTy loc784 = loc739 + (IntTy) 1;
    CursorTy loc785 = loc784 + (IntTy) 8;
    CursorTy loc786 = loc785 + (IntTy) 8;
    CursorTy loc787 = loc786 + (IntTy) 8;
    BoolTy fltIf295 = i88 <= (IntTy) 0;
    
    
  switch2083:
    ;
    switch (fltIf295) {
        
      case 0:
        {
            BoolTy fltIf296 = i88 == (IntTy) 1;
            
            
          switch2082:
            ;
            switch (fltIf296) {
                
              case 0:
                {
                    IntTy fltAppE301 = i88 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct0 =
                                            mkFoo_seq(end_r740, loc787, fltAppE301);
                    CursorTy pvrtmp2059 = tmp_struct0.field0;
                    CursorTy pvrtmp2060 = tmp_struct0.field1;
                    CursorTy pvrtmp2061 = tmp_struct0.field2;
                    IntTy fltAppE302 = i88 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct1 =
                                            mkFoo_seq(pvrtmp2059, pvrtmp2061, fltAppE302);
                    CursorTy pvrtmp2066 = tmp_struct1.field0;
                    CursorTy pvrtmp2067 = tmp_struct1.field1;
                    CursorTy pvrtmp2068 = tmp_struct1.field2;
                    IntTy fltAppE303 = i88 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct2 =
                                            mkFoo_seq(pvrtmp2066, pvrtmp2068, fltAppE303);
                    CursorTy pvrtmp2073 = tmp_struct2.field0;
                    CursorTy pvrtmp2074 = tmp_struct2.field1;
                    CursorTy pvrtmp2075 = tmp_struct2.field2;
                    
                    *loc739 = 4;
                    
                    CursorTy writetag1475 = loc739 + 1;
                    
                    *(CursorTy *) writetag1475 = pvrtmp2061;
                    
                    CursorTy writecur1476 = writetag1475 + 8;
                    
                    *(CursorTy *) writecur1476 = pvrtmp2068;
                    
                    CursorTy writecur1477 = writecur1476 + 8;
                    
                    *(IntTy *) writecur1477 = i88;
                    
                    CursorTy writecur1478 = writecur1477 + sizeof(IntTy);
                    
                    return (CursorCursorCursorProd) {pvrtmp2073, loc739,
                                                     pvrtmp2075};
                    break;
                }
                
              default:
                {
                    IntTy fltAppE298 = i88 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct3 =
                                            mkFoo_seq(end_r740, loc773, fltAppE298);
                    CursorTy pvrtmp2043 = tmp_struct3.field0;
                    CursorTy pvrtmp2044 = tmp_struct3.field1;
                    CursorTy pvrtmp2045 = tmp_struct3.field2;
                    IntTy fltAppE300 = i88 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct4 =
                                            mkFoo_seq(pvrtmp2043, pvrtmp2045, fltAppE300);
                    CursorTy pvrtmp2050 = tmp_struct4.field0;
                    CursorTy pvrtmp2051 = tmp_struct4.field1;
                    CursorTy pvrtmp2052 = tmp_struct4.field2;
                    
                    *loc739 = 2;
                    
                    CursorTy writetag1466 = loc739 + 1;
                    
                    *(CursorTy *) writetag1466 = pvrtmp2045;
                    
                    CursorTy writecur1467 = writetag1466 + 8;
                    
                    *(IntTy *) writecur1467 = i88;
                    
                    CursorTy writecur1468 = writecur1467 + sizeof(IntTy);
                    
                    return (CursorCursorCursorProd) {pvrtmp2050, loc739,
                                                     pvrtmp2052};
                }
            }
            break;
        }
        
      default:
        {
            *loc739 = 0;
            
            CursorTy writetag1461 = loc739 + 1;
            
            *(IntTy *) writetag1461 = (IntTy) 1;
            
            CursorTy writecur1462 = writetag1461 + sizeof(IntTy);
            
            return (CursorCursorCursorProd) {end_r740, loc739, writecur1462};
        }
    }
}
CursorCursorCursorProd copy(CursorTy end_r743, CursorTy end_r744,
                            CursorTy loc742, CursorTy foo92)
{
    if (loc742 + 9 > end_r744) {
        ChunkTy new_chunk26 = alloc_chunk(end_r744);
        CursorTy chunk_start27 = new_chunk26.start_ptr;
        CursorTy chunk_end28 = new_chunk26.end_ptr;
        
        end_r744 = chunk_end28;
        *(TagTyPacked *) loc742 = 100;
        
        CursorTy redir = loc742 + 1;
        
        *(CursorTy *) redir = chunk_start27;
        loc742 = chunk_start27;
    }
    
    CursorTy loc815 = loc742 + (IntTy) 1;
    CursorTy loc816 = loc815 + (IntTy) 8;
    CursorTy loc817 = loc816 + (IntTy) 8;
    CursorTy loc834 = loc742 + (IntTy) 1;
    CursorTy loc835 = loc834 + (IntTy) 8;
    CursorTy loc860 = loc742 + (IntTy) 1;
    CursorTy loc861 = loc860 + (IntTy) 8;
    CursorTy loc862 = loc861 + (IntTy) 8;
    CursorTy loc863 = loc862 + (IntTy) 8;
    CursorTy loc892 = loc742 + (IntTy) 1;
    CursorTy loc893 = loc892 + (IntTy) 8;
    TagTyPacked tmpval2084 = *foo92;
    CursorTy tmpcur2085 = foo92 + 1;
    
    
  switch2220:
    ;
    switch (tmpval2084) {
        
      case 0:
        {
            IntTy tmpval2086 = *(IntTy *) tmpcur2085;
            CursorTy tmpcur2087 = tmpcur2085 + sizeof(IntTy);
            CursorTy jump1274 = tmpcur2085 + (IntTy) 8;
            
            *loc742 = 0;
            
            CursorTy writetag1485 = loc742 + 1;
            
            *(IntTy *) writetag1485 = tmpval2086;
            
            CursorTy writecur1486 = writetag1485 + sizeof(IntTy);
            
            return (CursorCursorCursorProd) {end_r744, loc742, writecur1486};
            break;
        }
        
      case 2:
        {
            CursorTy tmpcur2090 = *(CursorTy *) tmpcur2085;
            CursorTy tmpaftercur2091 = tmpcur2085 + 8;
            IntTy tmpval2092 = *(IntTy *) tmpaftercur2091;
            CursorTy tmpcur2093 = tmpaftercur2091 + sizeof(IntTy);
            CursorTy jump1277 = tmpaftercur2091 + (IntTy) 8;
            CursorTy jump1276 = tmpcur2085 + (IntTy) 8;
            CursorInt64Prod tmp_struct8 =  _traverse_Foo(end_r743, tmpcur2093);
            CursorTy pvrtmp2094 = tmp_struct8.field0;
            IntTy pvrtmp2095 = tmp_struct8.field1;
            CursorCursorCursorProd tmp_struct9 =
                                    copy(end_r743, end_r744, loc817, tmpcur2093);
            CursorTy pvrtmp2096 = tmp_struct9.field0;
            CursorTy pvrtmp2097 = tmp_struct9.field1;
            CursorTy pvrtmp2098 = tmp_struct9.field2;
            CursorCursorCursorProd tmp_struct10 =
                                    copy(end_r743, pvrtmp2096, pvrtmp2098, tmpcur2090);
            CursorTy pvrtmp2103 = tmp_struct10.field0;
            CursorTy pvrtmp2104 = tmp_struct10.field1;
            CursorTy pvrtmp2105 = tmp_struct10.field2;
            
            *loc742 = 2;
            
            CursorTy writetag1494 = loc742 + 1;
            
            *(CursorTy *) writetag1494 = pvrtmp2098;
            
            CursorTy writecur1495 = writetag1494 + 8;
            
            *(IntTy *) writecur1495 = tmpval2092;
            
            CursorTy writecur1496 = writecur1495 + sizeof(IntTy);
            
            return (CursorCursorCursorProd) {pvrtmp2103, loc742, pvrtmp2105};
            break;
        }
        
      case 1:
        {
            IntTy tmpval2112 = *(IntTy *) tmpcur2085;
            CursorTy tmpcur2113 = tmpcur2085 + sizeof(IntTy);
            CursorTy jump1280 = tmpcur2085 + (IntTy) 8;
            CursorInt64Prod tmp_struct11 =  _traverse_Foo(end_r743, tmpcur2113);
            CursorTy pvrtmp2114 = tmp_struct11.field0;
            IntTy pvrtmp2115 = tmp_struct11.field1;
            CursorCursorCursorProd tmp_struct12 =
                                    copy(end_r743, end_r744, loc835, tmpcur2113);
            CursorTy pvrtmp2116 = tmp_struct12.field0;
            CursorTy pvrtmp2117 = tmp_struct12.field1;
            CursorTy pvrtmp2118 = tmp_struct12.field2;
            CursorCursorCursorProd tmp_struct13 =
                                    copy(end_r743, pvrtmp2116, pvrtmp2118, pvrtmp2114);
            CursorTy pvrtmp2123 = tmp_struct13.field0;
            CursorTy pvrtmp2124 = tmp_struct13.field1;
            CursorTy pvrtmp2125 = tmp_struct13.field2;
            
            *loc742 = 1;
            
            CursorTy writetag1505 = loc742 + 1;
            
            *(IntTy *) writetag1505 = tmpval2112;
            
            CursorTy writecur1506 = writetag1505 + sizeof(IntTy);
            
            return (CursorCursorCursorProd) {pvrtmp2123, loc742, pvrtmp2125};
            break;
        }
        
      case 4:
        {
            CursorTy tmpcur2132 = *(CursorTy *) tmpcur2085;
            CursorTy tmpaftercur2133 = tmpcur2085 + 8;
            CursorTy tmpcur2134 = *(CursorTy *) tmpaftercur2133;
            CursorTy tmpaftercur2135 = tmpaftercur2133 + 8;
            IntTy tmpval2136 = *(IntTy *) tmpaftercur2135;
            CursorTy tmpcur2137 = tmpaftercur2135 + sizeof(IntTy);
            CursorTy jump1285 = tmpaftercur2135 + (IntTy) 8;
            CursorTy jump1284 = tmpaftercur2133 + (IntTy) 8;
            CursorTy jump1283 = tmpcur2085 + (IntTy) 8;
            CursorInt64Prod tmp_struct14 =  _traverse_Foo(end_r743, tmpcur2137);
            CursorTy pvrtmp2138 = tmp_struct14.field0;
            IntTy pvrtmp2139 = tmp_struct14.field1;
            CursorInt64Prod tmp_struct15 =  _traverse_Foo(end_r743, tmpcur2134);
            CursorTy pvrtmp2140 = tmp_struct15.field0;
            IntTy pvrtmp2141 = tmp_struct15.field1;
            BoolTy fltIf304 = tmpval2136 < (IntTy) 10;
            
            
          switch2181:
            ;
            switch (fltIf304) {
                
              case 0:
                {
                    RegionTy *region2150 =
                             alloc_region(global_init_inf_buf_size);
                    CursorTy r1259 = region2150->start_ptr;
                    IntTy sizeof_end_r12592151 = global_init_inf_buf_size;
                    CursorTy end_r1259 = r1259 + sizeof_end_r12592151;
                    RegionTy *region2152 =
                             alloc_region(global_init_inf_buf_size);
                    CursorTy r1261 = region2152->start_ptr;
                    IntTy sizeof_end_r12612153 = global_init_inf_buf_size;
                    CursorTy end_r1261 = r1261 + sizeof_end_r12612153;
                    CursorCursorCursorProd tmp_struct16 =
                                           cilk_spawn copy(end_r743, end_r744, loc863, tmpcur2137);
                    CursorCursorCursorProd tmp_struct17 =
                                           cilk_spawn copy(end_r743, end_r1259, r1259, tmpcur2134);
                    CursorCursorCursorProd tmp_struct18 =
                                            copy(end_r743, end_r1261, r1261, tmpcur2132);
                    CursorTy pvrtmp2160 = tmp_struct18.field0;
                    CursorTy pvrtmp2161 = tmp_struct18.field1;
                    CursorTy pvrtmp2162 = tmp_struct18.field2;
                    
                    cilk_sync;
                    
                    CursorTy pvrtmp2154 = tmp_struct16.field0;
                    CursorTy pvrtmp2155 = tmp_struct16.field1;
                    CursorTy pvrtmp2156 = tmp_struct16.field2;
                    CursorTy pvrtmp2157 = tmp_struct17.field0;
                    CursorTy pvrtmp2158 = tmp_struct17.field1;
                    CursorTy pvrtmp2159 = tmp_struct17.field2;
                    
                    *pvrtmp2159 = 90;
                    
                    CursorTy writetag1520 = pvrtmp2159 + 1;
                    
                    *(CursorTy *) writetag1520 = r1261;
                    
                    CursorTy writecur1521 = writetag1520 + 8;
                    
                    *pvrtmp2156 = 90;
                    
                    CursorTy writetag1523 = pvrtmp2156 + 1;
                    
                    *(CursorTy *) writetag1523 = r1259;
                    
                    CursorTy writecur1524 = writetag1523 + 8;
                    
                    *loc742 = 4;
                    
                    CursorTy writetag1526 = loc742 + 1;
                    
                    *(CursorTy *) writetag1526 = pvrtmp2156;
                    
                    CursorTy writecur1527 = writetag1526 + 8;
                    
                    *(CursorTy *) writecur1527 = pvrtmp2159;
                    
                    CursorTy writecur1528 = writecur1527 + 8;
                    
                    *(IntTy *) writecur1528 = tmpval2136;
                    
                    CursorTy writecur1529 = writecur1528 + sizeof(IntTy);
                    
                    return (CursorCursorCursorProd) {pvrtmp2160, loc742,
                                                     pvrtmp2162};
                    break;
                }
                
              default:
                {
                    CursorCursorCursorCursorProd tmp_struct19 =
                                                  copy_seq(end_r743, end_r744, loc742, foo92);
                    CursorTy pvrtmp2142 = tmp_struct19.field0;
                    CursorTy pvrtmp2143 = tmp_struct19.field1;
                    CursorTy pvrtmp2144 = tmp_struct19.field2;
                    CursorTy pvrtmp2145 = tmp_struct19.field3;
                    
                    return (CursorCursorCursorProd) {pvrtmp2142, pvrtmp2144,
                                                     pvrtmp2145};
                }
            }
            break;
        }
        
      case 100:
        {
            CursorTy tmpcur2715 = *(CursorTy *) tmpcur2085;
            CursorTy tmpaftercur2716 = tmpcur2085 + 8;
            TagTyPacked tagtmp2717 = *tmpcur2715;
            CursorTy tailtmp2718 = tmpcur2715 + 1;
            
            tmpval2084 = tagtmp2717;
            tmpcur2085 = tailtmp2718;
            goto switch2220;
            break;
        }
        
      case 90:
        {
            CursorTy tmpcur2715 = *(CursorTy *) tmpcur2085;
            CursorTy tmpaftercur2716 = tmpcur2085 + 8;
            TagTyPacked tagtmp2717 = *tmpcur2715;
            CursorTy tailtmp2718 = tmpcur2715 + 1;
            
            tmpval2084 = tagtmp2717;
            tmpcur2085 = tailtmp2718;
            goto switch2220;
            break;
        }
        
      default:
        {
            IntTy tmpval2182 = *(IntTy *) tmpcur2085;
            CursorTy tmpcur2183 = tmpcur2085 + sizeof(IntTy);
            CursorTy jump1291 = tmpcur2085 + (IntTy) 8;
            CursorInt64Prod tmp_struct20 =  _traverse_Foo(end_r743, tmpcur2183);
            CursorTy pvrtmp2184 = tmp_struct20.field0;
            IntTy pvrtmp2185 = tmp_struct20.field1;
            CursorInt64Prod tmp_struct21 =  _traverse_Foo(end_r743, pvrtmp2184);
            CursorTy pvrtmp2186 = tmp_struct21.field0;
            IntTy pvrtmp2187 = tmp_struct21.field1;
            BoolTy fltIf304 = tmpval2182 < (IntTy) 10;
            
            
          switch2219:
            ;
            switch (fltIf304) {
                
              case 0:
                {
                    CursorCursorCursorProd tmp_struct22 =
                                            copy(end_r743, end_r744, loc893, tmpcur2183);
                    CursorTy pvrtmp2196 = tmp_struct22.field0;
                    CursorTy pvrtmp2197 = tmp_struct22.field1;
                    CursorTy pvrtmp2198 = tmp_struct22.field2;
                    CursorCursorCursorProd tmp_struct23 =
                                            copy(end_r743, pvrtmp2196, pvrtmp2198, pvrtmp2184);
                    CursorTy pvrtmp2203 = tmp_struct23.field0;
                    CursorTy pvrtmp2204 = tmp_struct23.field1;
                    CursorTy pvrtmp2205 = tmp_struct23.field2;
                    CursorCursorCursorProd tmp_struct24 =
                                            copy(end_r743, pvrtmp2203, pvrtmp2205, pvrtmp2186);
                    CursorTy pvrtmp2210 = tmp_struct24.field0;
                    CursorTy pvrtmp2211 = tmp_struct24.field1;
                    CursorTy pvrtmp2212 = tmp_struct24.field2;
                    
                    *loc742 = 3;
                    
                    CursorTy writetag1542 = loc742 + 1;
                    
                    *(IntTy *) writetag1542 = tmpval2182;
                    
                    CursorTy writecur1543 = writetag1542 + sizeof(IntTy);
                    
                    return (CursorCursorCursorProd) {pvrtmp2210, loc742,
                                                     pvrtmp2212};
                    break;
                }
                
              default:
                {
                    CursorCursorCursorCursorProd tmp_struct25 =
                                                  copy_seq(end_r743, end_r744, loc742, foo92);
                    CursorTy pvrtmp2188 = tmp_struct25.field0;
                    CursorTy pvrtmp2189 = tmp_struct25.field1;
                    CursorTy pvrtmp2190 = tmp_struct25.field2;
                    CursorTy pvrtmp2191 = tmp_struct25.field3;
                    
                    return (CursorCursorCursorProd) {pvrtmp2188, pvrtmp2190,
                                                     pvrtmp2191};
                }
            }
        }
    }
}
CursorCursorCursorCursorProd copy_seq(CursorTy end_r747, CursorTy end_r748,
                                      CursorTy loc746, CursorTy foo107)
{
    if (loc746 + 9 > end_r748) {
        ChunkTy new_chunk39 = alloc_chunk(end_r748);
        CursorTy chunk_start40 = new_chunk39.start_ptr;
        CursorTy chunk_end41 = new_chunk39.end_ptr;
        
        end_r748 = chunk_end41;
        *(TagTyPacked *) loc746 = 100;
        
        CursorTy redir = loc746 + 1;
        
        *(CursorTy *) redir = chunk_start40;
        loc746 = chunk_start40;
    }
    
    CursorTy loc917 = loc746 + (IntTy) 1;
    CursorTy loc918 = loc917 + (IntTy) 8;
    CursorTy loc919 = loc918 + (IntTy) 8;
    CursorTy loc936 = loc746 + (IntTy) 1;
    CursorTy loc937 = loc936 + (IntTy) 8;
    CursorTy loc958 = loc746 + (IntTy) 1;
    CursorTy loc959 = loc958 + (IntTy) 8;
    CursorTy loc960 = loc959 + (IntTy) 8;
    CursorTy loc961 = loc960 + (IntTy) 8;
    CursorTy loc986 = loc746 + (IntTy) 1;
    CursorTy loc987 = loc986 + (IntTy) 8;
    TagTyPacked tmpval2221 = *foo107;
    CursorTy tmpcur2222 = foo107 + 1;
    
    
  switch2329:
    ;
    switch (tmpval2221) {
        
      case 0:
        {
            IntTy tmpval2223 = *(IntTy *) tmpcur2222;
            CursorTy tmpcur2224 = tmpcur2222 + sizeof(IntTy);
            CursorTy jump1297 = tmpcur2222 + (IntTy) 8;
            
            *loc746 = 0;
            
            CursorTy writetag1550 = loc746 + 1;
            
            *(IntTy *) writetag1550 = tmpval2223;
            
            CursorTy writecur1551 = writetag1550 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {end_r748, jump1297, loc746,
                                                   writecur1551};
            break;
        }
        
      case 2:
        {
            CursorTy tmpcur2227 = *(CursorTy *) tmpcur2222;
            CursorTy tmpaftercur2228 = tmpcur2222 + 8;
            IntTy tmpval2229 = *(IntTy *) tmpaftercur2228;
            CursorTy tmpcur2230 = tmpaftercur2228 + sizeof(IntTy);
            CursorTy jump1300 = tmpaftercur2228 + (IntTy) 8;
            CursorTy jump1299 = tmpcur2222 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct29 =
                                          copy_seq(end_r747, end_r748, loc919, tmpcur2230);
            CursorTy pvrtmp2231 = tmp_struct29.field0;
            CursorTy pvrtmp2232 = tmp_struct29.field1;
            CursorTy pvrtmp2233 = tmp_struct29.field2;
            CursorTy pvrtmp2234 = tmp_struct29.field3;
            CursorCursorCursorCursorProd tmp_struct30 =
                                          copy_seq(end_r747, pvrtmp2231, pvrtmp2234, tmpcur2227);
            CursorTy pvrtmp2239 = tmp_struct30.field0;
            CursorTy pvrtmp2240 = tmp_struct30.field1;
            CursorTy pvrtmp2241 = tmp_struct30.field2;
            CursorTy pvrtmp2242 = tmp_struct30.field3;
            
            *loc746 = 2;
            
            CursorTy writetag1558 = loc746 + 1;
            
            *(CursorTy *) writetag1558 = pvrtmp2234;
            
            CursorTy writecur1559 = writetag1558 + 8;
            
            *(IntTy *) writecur1559 = tmpval2229;
            
            CursorTy writecur1560 = writecur1559 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2239, pvrtmp2240,
                                                   loc746, pvrtmp2242};
            break;
        }
        
      case 1:
        {
            IntTy tmpval2249 = *(IntTy *) tmpcur2222;
            CursorTy tmpcur2250 = tmpcur2222 + sizeof(IntTy);
            CursorTy jump1304 = tmpcur2222 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct31 =
                                          copy_seq(end_r747, end_r748, loc937, tmpcur2250);
            CursorTy pvrtmp2251 = tmp_struct31.field0;
            CursorTy pvrtmp2252 = tmp_struct31.field1;
            CursorTy pvrtmp2253 = tmp_struct31.field2;
            CursorTy pvrtmp2254 = tmp_struct31.field3;
            CursorCursorCursorCursorProd tmp_struct32 =
                                          copy_seq(end_r747, pvrtmp2251, pvrtmp2254, pvrtmp2252);
            CursorTy pvrtmp2259 = tmp_struct32.field0;
            CursorTy pvrtmp2260 = tmp_struct32.field1;
            CursorTy pvrtmp2261 = tmp_struct32.field2;
            CursorTy pvrtmp2262 = tmp_struct32.field3;
            
            *loc746 = 1;
            
            CursorTy writetag1568 = loc746 + 1;
            
            *(IntTy *) writetag1568 = tmpval2249;
            
            CursorTy writecur1569 = writetag1568 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2259, pvrtmp2260,
                                                   loc746, pvrtmp2262};
            break;
        }
        
      case 4:
        {
            CursorTy tmpcur2269 = *(CursorTy *) tmpcur2222;
            CursorTy tmpaftercur2270 = tmpcur2222 + 8;
            CursorTy tmpcur2271 = *(CursorTy *) tmpaftercur2270;
            CursorTy tmpaftercur2272 = tmpaftercur2270 + 8;
            IntTy tmpval2273 = *(IntTy *) tmpaftercur2272;
            CursorTy tmpcur2274 = tmpaftercur2272 + sizeof(IntTy);
            CursorTy jump1310 = tmpaftercur2272 + (IntTy) 8;
            CursorTy jump1309 = tmpaftercur2270 + (IntTy) 8;
            CursorTy jump1308 = tmpcur2222 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct33 =
                                          copy_seq(end_r747, end_r748, loc961, tmpcur2274);
            CursorTy pvrtmp2275 = tmp_struct33.field0;
            CursorTy pvrtmp2276 = tmp_struct33.field1;
            CursorTy pvrtmp2277 = tmp_struct33.field2;
            CursorTy pvrtmp2278 = tmp_struct33.field3;
            CursorCursorCursorCursorProd tmp_struct34 =
                                          copy_seq(end_r747, pvrtmp2275, pvrtmp2278, tmpcur2271);
            CursorTy pvrtmp2283 = tmp_struct34.field0;
            CursorTy pvrtmp2284 = tmp_struct34.field1;
            CursorTy pvrtmp2285 = tmp_struct34.field2;
            CursorTy pvrtmp2286 = tmp_struct34.field3;
            CursorCursorCursorCursorProd tmp_struct35 =
                                          copy_seq(end_r747, pvrtmp2283, pvrtmp2286, tmpcur2269);
            CursorTy pvrtmp2291 = tmp_struct35.field0;
            CursorTy pvrtmp2292 = tmp_struct35.field1;
            CursorTy pvrtmp2293 = tmp_struct35.field2;
            CursorTy pvrtmp2294 = tmp_struct35.field3;
            
            *loc746 = 4;
            
            CursorTy writetag1580 = loc746 + 1;
            
            *(CursorTy *) writetag1580 = pvrtmp2278;
            
            CursorTy writecur1581 = writetag1580 + 8;
            
            *(CursorTy *) writecur1581 = pvrtmp2286;
            
            CursorTy writecur1582 = writecur1581 + 8;
            
            *(IntTy *) writecur1582 = tmpval2273;
            
            CursorTy writecur1583 = writecur1582 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2291, pvrtmp2292,
                                                   loc746, pvrtmp2294};
            break;
        }
        
      case 100:
        {
            CursorTy tmpcur2719 = *(CursorTy *) tmpcur2222;
            CursorTy tmpaftercur2720 = tmpcur2222 + 8;
            TagTyPacked tagtmp2721 = *tmpcur2719;
            CursorTy tailtmp2722 = tmpcur2719 + 1;
            
            tmpval2221 = tagtmp2721;
            tmpcur2222 = tailtmp2722;
            goto switch2329;
            break;
        }
        
      case 90:
        {
            CursorTy tmpcur2719 = *(CursorTy *) tmpcur2222;
            CursorTy tmpaftercur2720 = tmpcur2222 + 8;
            TagTyPacked tagtmp2721 = *tmpcur2719;
            CursorTy tailtmp2722 = tmpcur2719 + 1;
            
            tmpval2221 = tagtmp2721;
            tmpcur2222 = tailtmp2722;
            goto switch2329;
            break;
        }
        
      default:
        {
            IntTy tmpval2301 = *(IntTy *) tmpcur2222;
            CursorTy tmpcur2302 = tmpcur2222 + sizeof(IntTy);
            CursorTy jump1315 = tmpcur2222 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct36 =
                                          copy_seq(end_r747, end_r748, loc987, tmpcur2302);
            CursorTy pvrtmp2303 = tmp_struct36.field0;
            CursorTy pvrtmp2304 = tmp_struct36.field1;
            CursorTy pvrtmp2305 = tmp_struct36.field2;
            CursorTy pvrtmp2306 = tmp_struct36.field3;
            CursorCursorCursorCursorProd tmp_struct37 =
                                          copy_seq(end_r747, pvrtmp2303, pvrtmp2306, pvrtmp2304);
            CursorTy pvrtmp2311 = tmp_struct37.field0;
            CursorTy pvrtmp2312 = tmp_struct37.field1;
            CursorTy pvrtmp2313 = tmp_struct37.field2;
            CursorTy pvrtmp2314 = tmp_struct37.field3;
            CursorCursorCursorCursorProd tmp_struct38 =
                                          copy_seq(end_r747, pvrtmp2311, pvrtmp2314, pvrtmp2312);
            CursorTy pvrtmp2319 = tmp_struct38.field0;
            CursorTy pvrtmp2320 = tmp_struct38.field1;
            CursorTy pvrtmp2321 = tmp_struct38.field2;
            CursorTy pvrtmp2322 = tmp_struct38.field3;
            
            *loc746 = 3;
            
            CursorTy writetag1593 = loc746 + 1;
            
            *(IntTy *) writetag1593 = tmpval2301;
            
            CursorTy writecur1594 = writetag1593 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2319, pvrtmp2320,
                                                   loc746, pvrtmp2322};
        }
    }
}
IntTy sumFoo(CursorTy end_r750, CursorTy foo121)
{
    TagTyPacked tmpval2330 = *foo121;
    CursorTy tmpcur2331 = foo121 + 1;
    
    
  switch2366:
    ;
    switch (tmpval2330) {
        
      case 0:
        {
            IntTy tmpval2332 = *(IntTy *) tmpcur2331;
            CursorTy tmpcur2333 = tmpcur2331 + sizeof(IntTy);
            CursorTy jump1320 = tmpcur2331 + (IntTy) 8;
            
            return tmpval2332;
            break;
        }
        
      case 2:
        {
            CursorTy tmpcur2334 = *(CursorTy *) tmpcur2331;
            CursorTy tmpaftercur2335 = tmpcur2331 + 8;
            IntTy tmpval2336 = *(IntTy *) tmpaftercur2335;
            CursorTy tmpcur2337 = tmpaftercur2335 + sizeof(IntTy);
            CursorTy jump1322 = tmpaftercur2335 + (IntTy) 8;
            CursorTy jump1321 = tmpcur2331 + (IntTy) 8;
            CursorInt64Prod tmp_struct42 =  _traverse_Foo(end_r750, tmpcur2337);
            CursorTy pvrtmp2338 = tmp_struct42.field0;
            IntTy pvrtmp2339 = tmp_struct42.field1;
            IntTy x126 =  sumFoo(end_r750, tmpcur2337);
            IntTy y127 =  sumFoo(end_r750, tmpcur2334);
            IntTy tailprim1324 = x126 + y127;
            
            return tailprim1324;
            break;
        }
        
      case 1:
        {
            IntTy tmpval2340 = *(IntTy *) tmpcur2331;
            CursorTy tmpcur2341 = tmpcur2331 + sizeof(IntTy);
            CursorTy jump1325 = tmpcur2331 + (IntTy) 8;
            CursorInt64Prod tmp_struct43 =  _traverse_Foo(end_r750, tmpcur2341);
            CursorTy pvrtmp2342 = tmp_struct43.field0;
            IntTy pvrtmp2343 = tmp_struct43.field1;
            IntTy x126 =  sumFoo(end_r750, tmpcur2341);
            IntTy y127 =  sumFoo(end_r750, pvrtmp2342);
            IntTy tailprim1327 = x126 + y127;
            
            return tailprim1327;
            break;
        }
        
      case 4:
        {
            CursorTy tmpcur2344 = *(CursorTy *) tmpcur2331;
            CursorTy tmpaftercur2345 = tmpcur2331 + 8;
            CursorTy tmpcur2346 = *(CursorTy *) tmpaftercur2345;
            CursorTy tmpaftercur2347 = tmpaftercur2345 + 8;
            IntTy tmpval2348 = *(IntTy *) tmpaftercur2347;
            CursorTy tmpcur2349 = tmpaftercur2347 + sizeof(IntTy);
            CursorTy jump1330 = tmpaftercur2347 + (IntTy) 8;
            CursorTy jump1329 = tmpaftercur2345 + (IntTy) 8;
            CursorTy jump1328 = tmpcur2331 + (IntTy) 8;
            CursorInt64Prod tmp_struct44 =  _traverse_Foo(end_r750, tmpcur2349);
            CursorTy pvrtmp2350 = tmp_struct44.field0;
            IntTy pvrtmp2351 = tmp_struct44.field1;
            CursorInt64Prod tmp_struct45 =  _traverse_Foo(end_r750, tmpcur2346);
            CursorTy pvrtmp2352 = tmp_struct45.field0;
            IntTy pvrtmp2353 = tmp_struct45.field1;
            BoolTy fltIf305 = tmpval2348 < (IntTy) 10;
            
            
          switch2356:
            ;
            switch (fltIf305) {
                
              case 0:
                {
                    IntTy x132 = cilk_spawn sumFoo(end_r750, tmpcur2349);
                    IntTy y133 = cilk_spawn sumFoo(end_r750, tmpcur2346);
                    IntTy z134 =  sumFoo(end_r750, tmpcur2344);
                    
                    cilk_sync;
                    
                    IntTy fltPrm306 = x132 + y133;
                    IntTy tailprim1335 = fltPrm306 + z134;
                    
                    return tailprim1335;
                    break;
                }
                
              default:
                {
                    CursorInt64Prod tmp_struct46 =
                                     sumFoo_seq(end_r750, foo121);
                    CursorTy pvrtmp2354 = tmp_struct46.field0;
                    IntTy pvrtmp2355 = tmp_struct46.field1;
                    
                    return pvrtmp2355;
                }
            }
            break;
        }
        
      case 100:
        {
            CursorTy tmpcur2723 = *(CursorTy *) tmpcur2331;
            CursorTy tmpaftercur2724 = tmpcur2331 + 8;
            TagTyPacked tagtmp2725 = *tmpcur2723;
            CursorTy tailtmp2726 = tmpcur2723 + 1;
            
            tmpval2330 = tagtmp2725;
            tmpcur2331 = tailtmp2726;
            goto switch2366;
            break;
        }
        
      case 90:
        {
            CursorTy tmpcur2723 = *(CursorTy *) tmpcur2331;
            CursorTy tmpaftercur2724 = tmpcur2331 + 8;
            TagTyPacked tagtmp2725 = *tmpcur2723;
            CursorTy tailtmp2726 = tmpcur2723 + 1;
            
            tmpval2330 = tagtmp2725;
            tmpcur2331 = tailtmp2726;
            goto switch2366;
            break;
        }
        
      default:
        {
            IntTy tmpval2357 = *(IntTy *) tmpcur2331;
            CursorTy tmpcur2358 = tmpcur2331 + sizeof(IntTy);
            CursorTy jump1336 = tmpcur2331 + (IntTy) 8;
            CursorInt64Prod tmp_struct47 =  _traverse_Foo(end_r750, tmpcur2358);
            CursorTy pvrtmp2359 = tmp_struct47.field0;
            IntTy pvrtmp2360 = tmp_struct47.field1;
            CursorInt64Prod tmp_struct48 =  _traverse_Foo(end_r750, pvrtmp2359);
            CursorTy pvrtmp2361 = tmp_struct48.field0;
            IntTy pvrtmp2362 = tmp_struct48.field1;
            BoolTy fltIf305 = tmpval2357 < (IntTy) 10;
            
            
          switch2365:
            ;
            switch (fltIf305) {
                
              case 0:
                {
                    IntTy x132 =  sumFoo(end_r750, tmpcur2358);
                    IntTy y133 =  sumFoo(end_r750, pvrtmp2359);
                    IntTy z134 =  sumFoo(end_r750, pvrtmp2361);
                    IntTy fltPrm306 = x132 + y133;
                    IntTy tailprim1341 = fltPrm306 + z134;
                    
                    return tailprim1341;
                    break;
                }
                
              default:
                {
                    CursorInt64Prod tmp_struct49 =
                                     sumFoo_seq(end_r750, foo121);
                    CursorTy pvrtmp2363 = tmp_struct49.field0;
                    IntTy pvrtmp2364 = tmp_struct49.field1;
                    
                    return pvrtmp2364;
                }
            }
        }
    }
}
CursorInt64Prod sumFoo_seq(CursorTy end_r752, CursorTy foo136)
{
    TagTyPacked tmpval2367 = *foo136;
    CursorTy tmpcur2368 = foo136 + 1;
    
    
  switch2405:
    ;
    switch (tmpval2367) {
        
      case 0:
        {
            IntTy tmpval2369 = *(IntTy *) tmpcur2368;
            CursorTy tmpcur2370 = tmpcur2368 + sizeof(IntTy);
            CursorTy jump1342 = tmpcur2368 + (IntTy) 8;
            
            return (CursorInt64Prod) {jump1342, tmpval2369};
            break;
        }
        
      case 2:
        {
            CursorTy tmpcur2371 = *(CursorTy *) tmpcur2368;
            CursorTy tmpaftercur2372 = tmpcur2368 + 8;
            IntTy tmpval2373 = *(IntTy *) tmpaftercur2372;
            CursorTy tmpcur2374 = tmpaftercur2372 + sizeof(IntTy);
            CursorTy jump1344 = tmpaftercur2372 + (IntTy) 8;
            CursorTy jump1343 = tmpcur2368 + (IntTy) 8;
            CursorInt64Prod tmp_struct50 =  sumFoo_seq(end_r752, tmpcur2374);
            CursorTy pvrtmp2375 = tmp_struct50.field0;
            IntTy pvrtmp2376 = tmp_struct50.field1;
            CursorInt64Prod tmp_struct51 =  sumFoo_seq(end_r752, tmpcur2371);
            CursorTy pvrtmp2377 = tmp_struct51.field0;
            IntTy pvrtmp2378 = tmp_struct51.field1;
            IntTy tailprim1347 = pvrtmp2376 + pvrtmp2378;
            
            return (CursorInt64Prod) {pvrtmp2377, tailprim1347};
            break;
        }
        
      case 1:
        {
            IntTy tmpval2379 = *(IntTy *) tmpcur2368;
            CursorTy tmpcur2380 = tmpcur2368 + sizeof(IntTy);
            CursorTy jump1348 = tmpcur2368 + (IntTy) 8;
            CursorInt64Prod tmp_struct52 =  sumFoo_seq(end_r752, tmpcur2380);
            CursorTy pvrtmp2381 = tmp_struct52.field0;
            IntTy pvrtmp2382 = tmp_struct52.field1;
            CursorInt64Prod tmp_struct53 =  sumFoo_seq(end_r752, pvrtmp2381);
            CursorTy pvrtmp2383 = tmp_struct53.field0;
            IntTy pvrtmp2384 = tmp_struct53.field1;
            IntTy tailprim1351 = pvrtmp2382 + pvrtmp2384;
            
            return (CursorInt64Prod) {pvrtmp2383, tailprim1351};
            break;
        }
        
      case 4:
        {
            CursorTy tmpcur2385 = *(CursorTy *) tmpcur2368;
            CursorTy tmpaftercur2386 = tmpcur2368 + 8;
            CursorTy tmpcur2387 = *(CursorTy *) tmpaftercur2386;
            CursorTy tmpaftercur2388 = tmpaftercur2386 + 8;
            IntTy tmpval2389 = *(IntTy *) tmpaftercur2388;
            CursorTy tmpcur2390 = tmpaftercur2388 + sizeof(IntTy);
            CursorTy jump1354 = tmpaftercur2388 + (IntTy) 8;
            CursorTy jump1353 = tmpaftercur2386 + (IntTy) 8;
            CursorTy jump1352 = tmpcur2368 + (IntTy) 8;
            CursorInt64Prod tmp_struct54 =  sumFoo_seq(end_r752, tmpcur2390);
            CursorTy pvrtmp2391 = tmp_struct54.field0;
            IntTy pvrtmp2392 = tmp_struct54.field1;
            CursorInt64Prod tmp_struct55 =  sumFoo_seq(end_r752, tmpcur2387);
            CursorTy pvrtmp2393 = tmp_struct55.field0;
            IntTy pvrtmp2394 = tmp_struct55.field1;
            CursorInt64Prod tmp_struct56 =  sumFoo_seq(end_r752, tmpcur2385);
            CursorTy pvrtmp2395 = tmp_struct56.field0;
            IntTy pvrtmp2396 = tmp_struct56.field1;
            IntTy fltPrm307 = pvrtmp2392 + pvrtmp2394;
            IntTy tailprim1358 = fltPrm307 + pvrtmp2396;
            
            return (CursorInt64Prod) {pvrtmp2395, tailprim1358};
            break;
        }
        
      case 100:
        {
            CursorTy tmpcur2727 = *(CursorTy *) tmpcur2368;
            CursorTy tmpaftercur2728 = tmpcur2368 + 8;
            TagTyPacked tagtmp2729 = *tmpcur2727;
            CursorTy tailtmp2730 = tmpcur2727 + 1;
            
            tmpval2367 = tagtmp2729;
            tmpcur2368 = tailtmp2730;
            goto switch2405;
            break;
        }
        
      case 90:
        {
            CursorTy tmpcur2727 = *(CursorTy *) tmpcur2368;
            CursorTy tmpaftercur2728 = tmpcur2368 + 8;
            TagTyPacked tagtmp2729 = *tmpcur2727;
            CursorTy tailtmp2730 = tmpcur2727 + 1;
            
            tmpval2367 = tagtmp2729;
            tmpcur2368 = tailtmp2730;
            goto switch2405;
            break;
        }
        
      default:
        {
            IntTy tmpval2397 = *(IntTy *) tmpcur2368;
            CursorTy tmpcur2398 = tmpcur2368 + sizeof(IntTy);
            CursorTy jump1359 = tmpcur2368 + (IntTy) 8;
            CursorInt64Prod tmp_struct57 =  sumFoo_seq(end_r752, tmpcur2398);
            CursorTy pvrtmp2399 = tmp_struct57.field0;
            IntTy pvrtmp2400 = tmp_struct57.field1;
            CursorInt64Prod tmp_struct58 =  sumFoo_seq(end_r752, pvrtmp2399);
            CursorTy pvrtmp2401 = tmp_struct58.field0;
            IntTy pvrtmp2402 = tmp_struct58.field1;
            CursorInt64Prod tmp_struct59 =  sumFoo_seq(end_r752, pvrtmp2401);
            CursorTy pvrtmp2403 = tmp_struct59.field0;
            IntTy pvrtmp2404 = tmp_struct59.field1;
            IntTy fltPrm307 = pvrtmp2400 + pvrtmp2402;
            IntTy tailprim1363 = fltPrm307 + pvrtmp2404;
            
            return (CursorInt64Prod) {pvrtmp2403, tailprim1363};
        }
    }
}
CursorCursorCursorProd mkFoo(CursorTy end_r754, CursorTy loc753, IntTy i150)
{
    if (loc753 + 9 > end_r754) {
        ChunkTy new_chunk66 = alloc_chunk(end_r754);
        CursorTy chunk_start67 = new_chunk66.start_ptr;
        CursorTy chunk_end68 = new_chunk66.end_ptr;
        
        end_r754 = chunk_end68;
        *(TagTyPacked *) loc753 = 100;
        
        CursorTy redir = loc753 + 1;
        
        *(CursorTy *) redir = chunk_start67;
        loc753 = chunk_start67;
    }
    
    CursorTy loc1082 = loc753 + (IntTy) 1;
    CursorTy loc1083 = loc1082 + (IntTy) 8;
    CursorTy loc1084 = loc1083 + (IntTy) 8;
    CursorTy loc1097 = loc753 + (IntTy) 1;
    CursorTy loc1098 = loc1097 + (IntTy) 8;
    CursorTy loc1099 = loc1098 + (IntTy) 8;
    CursorTy loc1100 = loc1099 + (IntTy) 8;
    BoolTy fltIf308 = i150 <= (IntTy) 0;
    
    
  switch2464:
    ;
    switch (fltIf308) {
        
      case 0:
        {
            BoolTy fltIf309 = i150 == (IntTy) 1;
            
            
          switch2463:
            ;
            switch (fltIf309) {
                
              case 0:
                {
                    BoolTy fltIf314 = i150 < (IntTy) 10;
                    
                    
                  switch2462:
                    ;
                    switch (fltIf314) {
                        
                      case 0:
                        {
                            IntTy fltSpawnE315 = i150 - (IntTy) 1;
                            int parent_id =  __cilkrts_get_worker_number();
                            CursorCursorCursorProd tmp_struct60 =
                                                   cilk_spawn mkFoo(end_r754, loc1100, fltSpawnE315);

                            int cont_id1 =  __cilkrts_get_worker_number();
                            bool spawned1 = false;
                            CursorTy end1, start1;
                            if (parent_id != cont_id1) {
                                spawned1 = true;
                                RegionTy *region2431 =
                                         alloc_region(global_init_inf_buf_size);
                                CursorTy r1265 = region2431->start_ptr;
                                IntTy sizeof_end_r12652432 =
                                      global_init_inf_buf_size;
                                CursorTy end_r1265 = r1265 + sizeof_end_r12652432;
                                end1 = end_r1265;
                                start1 = r1265;
                            } else {

                                CursorTy pvrtmp2435 = tmp_struct60.field0;
                                CursorTy pvrtmp2436 = tmp_struct60.field1;
                                CursorTy pvrtmp2437 = tmp_struct60.field2;
                                end1 = pvrtmp2435;
                                start1 = pvrtmp2437;
                            }

                            IntTy fltSpawnE316 = i150 - (IntTy) 1;
                            int cont_id2 =  __cilkrts_get_worker_number();
                            CursorCursorCursorProd tmp_struct61 =
                                                   cilk_spawn mkFoo(end1, start1, fltSpawnE316);

                            bool spawned2 = false;
                            CursorTy end2, start2;
                            if (cont_id1 != cont_id2) {
                                spawned2 = true;
                                
                                RegionTy *region2433 =
                                         alloc_region(global_init_inf_buf_size);
                                CursorTy r1267 = region2433->start_ptr;
                                IntTy sizeof_end_r12672434 =
                                      global_init_inf_buf_size;
                                CursorTy end_r1267 = r1267 + sizeof_end_r12672434;

                                end2 = end_r1267;
                                start2 = r1267;
                            } else {

                                CursorTy pvrtmp2438 = tmp_struct61.field0;
                                CursorTy pvrtmp2439 = tmp_struct61.field1;
                                CursorTy pvrtmp2440 = tmp_struct61.field2;
                                end2 = pvrtmp2438;
                                start2 = pvrtmp2440;
                            }

                            IntTy fltAppE317 = i150 - (IntTy) 1;
                            CursorCursorCursorProd tmp_struct62 =
                                                    mkFoo(end2, start2, fltAppE317);
                            CursorTy pvrtmp2441 = tmp_struct62.field0;
                            CursorTy pvrtmp2442 = tmp_struct62.field1;
                            CursorTy pvrtmp2443 = tmp_struct62.field2;
                            
                            cilk_sync;
                            
                            CursorTy pvrtmp2435 = tmp_struct60.field0;
                            CursorTy pvrtmp2436 = tmp_struct60.field1;
                            CursorTy pvrtmp2437 = tmp_struct60.field2;
                            CursorTy pvrtmp2438 = tmp_struct61.field0;
                            CursorTy pvrtmp2439 = tmp_struct61.field1;
                            CursorTy pvrtmp2440 = tmp_struct61.field2;
                            
                            if (spawned1) {
                                *pvrtmp2440 = 90;
                                CursorTy writetag1658 = pvrtmp2440 + 1;
                                *(CursorTy *) writetag1658 = start2;
                                CursorTy writecur1659 = writetag1658 + 8;
                            }

                            if (spawned2) {
                                *pvrtmp2437 = 90;
                                CursorTy writetag1661 = pvrtmp2437 + 1;
                                *(CursorTy *) writetag1661 = start1;
                                CursorTy writecur1662 = writetag1661 + 8;
                            }
                            
                            *loc753 = 4;
                            
                            CursorTy writetag1664 = loc753 + 1;
                            *(CursorTy *) writetag1664 = pvrtmp2437;
                            CursorTy writecur1665 = writetag1664 + 8;
                            *(CursorTy *) writecur1665 = pvrtmp2440;
                            CursorTy writecur1666 = writecur1665 + 8;
                            *(IntTy *) writecur1666 = i150;
                            
                            CursorTy writecur1667 = writecur1666 +
                                     sizeof(IntTy);
                            
                            return (CursorCursorCursorProd) {pvrtmp2441, loc753,
                                                             pvrtmp2443};
                            break;
                        }
                        
                      default:
                        {
                            CursorCursorCursorProd tmp_struct63 =
                                                    mkFoo_seq(end_r754, loc753, i150);
                            CursorTy pvrtmp2424 = tmp_struct63.field0;
                            CursorTy pvrtmp2425 = tmp_struct63.field1;
                            CursorTy pvrtmp2426 = tmp_struct63.field2;
                            
                            return (CursorCursorCursorProd) {pvrtmp2424,
                                                             pvrtmp2425,
                                                             pvrtmp2426};
                        }
                    }
                    break;
                }
                
              default:
                {
                    IntTy fltAppE311 = i150 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct64 =
                                            mkFoo(end_r754, loc1084, fltAppE311);
                    CursorTy pvrtmp2408 = tmp_struct64.field0;
                    CursorTy pvrtmp2409 = tmp_struct64.field1;
                    CursorTy pvrtmp2410 = tmp_struct64.field2;
                    IntTy fltAppE313 = i150 - (IntTy) 1;
                    CursorCursorCursorProd tmp_struct65 =
                                            mkFoo(pvrtmp2408, pvrtmp2410, fltAppE313);
                    CursorTy pvrtmp2415 = tmp_struct65.field0;
                    CursorTy pvrtmp2416 = tmp_struct65.field1;
                    CursorTy pvrtmp2417 = tmp_struct65.field2;
                    
                    *loc753 = 2;
                    
                    CursorTy writetag1648 = loc753 + 1;
                    
                    *(CursorTy *) writetag1648 = pvrtmp2410;
                    
                    CursorTy writecur1649 = writetag1648 + 8;
                    
                    *(IntTy *) writecur1649 = i150;
                    
                    CursorTy writecur1650 = writecur1649 + sizeof(IntTy);
                    
                    return (CursorCursorCursorProd) {pvrtmp2415, loc753,
                                                     pvrtmp2417};
                }
            }
            break;
        }
        
      default:
        {
            *loc753 = 0;
            
            CursorTy writetag1643 = loc753 + 1;
            
            *(IntTy *) writetag1643 = (IntTy) 1;
            
            CursorTy writecur1644 = writetag1643 + sizeof(IntTy);
            
            return (CursorCursorCursorProd) {end_r754, loc753, writecur1644};
        }
    }
}
CursorCursorCursorCursorProd _copy_Foo(CursorTy end_r757, CursorTy end_r758,
                                       CursorTy loc756, CursorTy arg655)
{
    if (loc756 + 9 > end_r758) {
        ChunkTy new_chunk79 = alloc_chunk(end_r758);
        CursorTy chunk_start80 = new_chunk79.start_ptr;
        CursorTy chunk_end81 = new_chunk79.end_ptr;
        
        end_r758 = chunk_end81;
        *(TagTyPacked *) loc756 = 100;
        
        CursorTy redir = loc756 + 1;
        
        *(CursorTy *) redir = chunk_start80;
        loc756 = chunk_start80;
    }
    
    CursorTy loc1127 = loc756 + (IntTy) 1;
    CursorTy loc1128 = loc1127 + (IntTy) 8;
    CursorTy loc1144 = loc756 + (IntTy) 1;
    CursorTy loc1145 = loc1144 + (IntTy) 8;
    CursorTy loc1146 = loc1145 + (IntTy) 8;
    CursorTy loc1167 = loc756 + (IntTy) 1;
    CursorTy loc1168 = loc1167 + (IntTy) 8;
    CursorTy loc1191 = loc756 + (IntTy) 1;
    CursorTy loc1192 = loc1191 + (IntTy) 8;
    CursorTy loc1193 = loc1192 + (IntTy) 8;
    CursorTy loc1194 = loc1193 + (IntTy) 8;
    TagTyPacked tmpval2465 = *arg655;
    CursorTy tmpcur2466 = arg655 + 1;
    
    
  switch2573:
    ;
    switch (tmpval2465) {
        
      case 0:
        {
            IntTy tmpval2467 = *(IntTy *) tmpcur2466;
            CursorTy tmpcur2468 = tmpcur2466 + sizeof(IntTy);
            CursorTy jump1368 = tmpcur2466 + (IntTy) 8;
            
            *loc756 = 0;
            
            CursorTy writetag1674 = loc756 + 1;
            
            *(IntTy *) writetag1674 = tmpval2467;
            
            CursorTy writecur1675 = writetag1674 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {end_r758, jump1368, loc756,
                                                   writecur1675};
            break;
        }
        
      case 1:
        {
            IntTy tmpval2471 = *(IntTy *) tmpcur2466;
            CursorTy tmpcur2472 = tmpcur2466 + sizeof(IntTy);
            CursorTy jump1370 = tmpcur2466 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct69 =
                                          _copy_Foo(end_r757, end_r758, loc1128, tmpcur2472);
            CursorTy pvrtmp2473 = tmp_struct69.field0;
            CursorTy pvrtmp2474 = tmp_struct69.field1;
            CursorTy pvrtmp2475 = tmp_struct69.field2;
            CursorTy pvrtmp2476 = tmp_struct69.field3;
            CursorCursorCursorCursorProd tmp_struct70 =
                                          _copy_Foo(end_r757, pvrtmp2473, pvrtmp2476, pvrtmp2474);
            CursorTy pvrtmp2481 = tmp_struct70.field0;
            CursorTy pvrtmp2482 = tmp_struct70.field1;
            CursorTy pvrtmp2483 = tmp_struct70.field2;
            CursorTy pvrtmp2484 = tmp_struct70.field3;
            
            *loc756 = 1;
            
            CursorTy writetag1681 = loc756 + 1;
            
            *(IntTy *) writetag1681 = tmpval2471;
            
            CursorTy writecur1682 = writetag1681 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2481, pvrtmp2482,
                                                   loc756, pvrtmp2484};
            break;
        }
        
      case 2:
        {
            CursorTy tmpcur2491 = *(CursorTy *) tmpcur2466;
            CursorTy tmpaftercur2492 = tmpcur2466 + 8;
            IntTy tmpval2493 = *(IntTy *) tmpaftercur2492;
            CursorTy tmpcur2494 = tmpaftercur2492 + sizeof(IntTy);
            CursorTy jump1375 = tmpaftercur2492 + (IntTy) 8;
            CursorTy jump1374 = tmpcur2466 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct71 =
                                          _copy_Foo(end_r757, end_r758, loc1146, tmpcur2494);
            CursorTy pvrtmp2495 = tmp_struct71.field0;
            CursorTy pvrtmp2496 = tmp_struct71.field1;
            CursorTy pvrtmp2497 = tmp_struct71.field2;
            CursorTy pvrtmp2498 = tmp_struct71.field3;
            CursorCursorCursorCursorProd tmp_struct72 =
                                          _copy_Foo(end_r757, pvrtmp2495, pvrtmp2498, tmpcur2491);
            CursorTy pvrtmp2503 = tmp_struct72.field0;
            CursorTy pvrtmp2504 = tmp_struct72.field1;
            CursorTy pvrtmp2505 = tmp_struct72.field2;
            CursorTy pvrtmp2506 = tmp_struct72.field3;
            
            *loc756 = 2;
            
            CursorTy writetag1691 = loc756 + 1;
            
            *(CursorTy *) writetag1691 = pvrtmp2498;
            
            CursorTy writecur1692 = writetag1691 + 8;
            
            *(IntTy *) writecur1692 = tmpval2493;
            
            CursorTy writecur1693 = writecur1692 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2503, pvrtmp2504,
                                                   loc756, pvrtmp2506};
            break;
        }
        
      case 3:
        {
            IntTy tmpval2513 = *(IntTy *) tmpcur2466;
            CursorTy tmpcur2514 = tmpcur2466 + sizeof(IntTy);
            CursorTy jump1379 = tmpcur2466 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct73 =
                                          _copy_Foo(end_r757, end_r758, loc1168, tmpcur2514);
            CursorTy pvrtmp2515 = tmp_struct73.field0;
            CursorTy pvrtmp2516 = tmp_struct73.field1;
            CursorTy pvrtmp2517 = tmp_struct73.field2;
            CursorTy pvrtmp2518 = tmp_struct73.field3;
            CursorCursorCursorCursorProd tmp_struct74 =
                                          _copy_Foo(end_r757, pvrtmp2515, pvrtmp2518, pvrtmp2516);
            CursorTy pvrtmp2523 = tmp_struct74.field0;
            CursorTy pvrtmp2524 = tmp_struct74.field1;
            CursorTy pvrtmp2525 = tmp_struct74.field2;
            CursorTy pvrtmp2526 = tmp_struct74.field3;
            CursorCursorCursorCursorProd tmp_struct75 =
                                          _copy_Foo(end_r757, pvrtmp2523, pvrtmp2526, pvrtmp2524);
            CursorTy pvrtmp2531 = tmp_struct75.field0;
            CursorTy pvrtmp2532 = tmp_struct75.field1;
            CursorTy pvrtmp2533 = tmp_struct75.field2;
            CursorTy pvrtmp2534 = tmp_struct75.field3;
            
            *loc756 = 3;
            
            CursorTy writetag1702 = loc756 + 1;
            
            *(IntTy *) writetag1702 = tmpval2513;
            
            CursorTy writecur1703 = writetag1702 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2531, pvrtmp2532,
                                                   loc756, pvrtmp2534};
            break;
        }
        
      case 100:
        {
            CursorTy tmpcur2731 = *(CursorTy *) tmpcur2466;
            CursorTy tmpaftercur2732 = tmpcur2466 + 8;
            TagTyPacked tagtmp2733 = *tmpcur2731;
            CursorTy tailtmp2734 = tmpcur2731 + 1;
            
            tmpval2465 = tagtmp2733;
            tmpcur2466 = tailtmp2734;
            goto switch2573;
            break;
        }
        
      case 90:
        {
            CursorTy tmpcur2731 = *(CursorTy *) tmpcur2466;
            CursorTy tmpaftercur2732 = tmpcur2466 + 8;
            TagTyPacked tagtmp2733 = *tmpcur2731;
            CursorTy tailtmp2734 = tmpcur2731 + 1;
            
            tmpval2465 = tagtmp2733;
            tmpcur2466 = tailtmp2734;
            goto switch2573;
            break;
        }
        
      default:
        {
            CursorTy tmpcur2541 = *(CursorTy *) tmpcur2466;
            CursorTy tmpaftercur2542 = tmpcur2466 + 8;
            CursorTy tmpcur2543 = *(CursorTy *) tmpaftercur2542;
            CursorTy tmpaftercur2544 = tmpaftercur2542 + 8;
            IntTy tmpval2545 = *(IntTy *) tmpaftercur2544;
            CursorTy tmpcur2546 = tmpaftercur2544 + sizeof(IntTy);
            CursorTy jump1386 = tmpaftercur2544 + (IntTy) 8;
            CursorTy jump1385 = tmpaftercur2542 + (IntTy) 8;
            CursorTy jump1384 = tmpcur2466 + (IntTy) 8;
            CursorCursorCursorCursorProd tmp_struct76 =
                                          _copy_Foo(end_r757, end_r758, loc1194, tmpcur2546);
            CursorTy pvrtmp2547 = tmp_struct76.field0;
            CursorTy pvrtmp2548 = tmp_struct76.field1;
            CursorTy pvrtmp2549 = tmp_struct76.field2;
            CursorTy pvrtmp2550 = tmp_struct76.field3;
            CursorCursorCursorCursorProd tmp_struct77 =
                                          _copy_Foo(end_r757, pvrtmp2547, pvrtmp2550, tmpcur2543);
            CursorTy pvrtmp2555 = tmp_struct77.field0;
            CursorTy pvrtmp2556 = tmp_struct77.field1;
            CursorTy pvrtmp2557 = tmp_struct77.field2;
            CursorTy pvrtmp2558 = tmp_struct77.field3;
            CursorCursorCursorCursorProd tmp_struct78 =
                                          _copy_Foo(end_r757, pvrtmp2555, pvrtmp2558, tmpcur2541);
            CursorTy pvrtmp2563 = tmp_struct78.field0;
            CursorTy pvrtmp2564 = tmp_struct78.field1;
            CursorTy pvrtmp2565 = tmp_struct78.field2;
            CursorTy pvrtmp2566 = tmp_struct78.field3;
            
            *loc756 = 4;
            
            CursorTy writetag1715 = loc756 + 1;
            
            *(CursorTy *) writetag1715 = pvrtmp2550;
            
            CursorTy writecur1716 = writetag1715 + 8;
            
            *(CursorTy *) writecur1716 = pvrtmp2558;
            
            CursorTy writecur1717 = writecur1716 + 8;
            
            *(IntTy *) writecur1717 = tmpval2545;
            
            CursorTy writecur1718 = writecur1717 + sizeof(IntTy);
            
            return (CursorCursorCursorCursorProd) {pvrtmp2563, pvrtmp2564,
                                                   loc756, pvrtmp2566};
        }
    }
}
CursorInt64Prod _traverse_Foo(CursorTy end_r760, CursorTy arg692)
{
    TagTyPacked tmpval2574 = *arg692;
    CursorTy tmpcur2575 = arg692 + 1;
    
    
  switch2612:
    ;
    switch (tmpval2574) {
        
      case 0:
        {
            IntTy tmpval2576 = *(IntTy *) tmpcur2575;
            CursorTy tmpcur2577 = tmpcur2575 + sizeof(IntTy);
            CursorTy jump1391 = tmpcur2575 + (IntTy) 8;
            
            return (CursorInt64Prod) {jump1391, (IntTy) 42};
            break;
        }
        
      case 1:
        {
            IntTy tmpval2578 = *(IntTy *) tmpcur2575;
            CursorTy tmpcur2579 = tmpcur2575 + sizeof(IntTy);
            CursorTy jump1393 = tmpcur2575 + (IntTy) 8;
            CursorInt64Prod tmp_struct82 =  _traverse_Foo(end_r760, tmpcur2579);
            CursorTy pvrtmp2580 = tmp_struct82.field0;
            IntTy pvrtmp2581 = tmp_struct82.field1;
            CursorInt64Prod tmp_struct83 =  _traverse_Foo(end_r760, pvrtmp2580);
            CursorTy pvrtmp2582 = tmp_struct83.field0;
            IntTy pvrtmp2583 = tmp_struct83.field1;
            
            return (CursorInt64Prod) {pvrtmp2582, (IntTy) 42};
            break;
        }
        
      case 2:
        {
            CursorTy tmpcur2584 = *(CursorTy *) tmpcur2575;
            CursorTy tmpaftercur2585 = tmpcur2575 + 8;
            IntTy tmpval2586 = *(IntTy *) tmpaftercur2585;
            CursorTy tmpcur2587 = tmpaftercur2585 + sizeof(IntTy);
            CursorTy jump1398 = tmpaftercur2585 + (IntTy) 8;
            CursorTy jump1397 = tmpcur2575 + (IntTy) 8;
            CursorInt64Prod tmp_struct84 =  _traverse_Foo(end_r760, tmpcur2587);
            CursorTy pvrtmp2588 = tmp_struct84.field0;
            IntTy pvrtmp2589 = tmp_struct84.field1;
            CursorInt64Prod tmp_struct85 =  _traverse_Foo(end_r760, tmpcur2584);
            CursorTy pvrtmp2590 = tmp_struct85.field0;
            IntTy pvrtmp2591 = tmp_struct85.field1;
            
            return (CursorInt64Prod) {pvrtmp2590, (IntTy) 42};
            break;
        }
        
      case 3:
        {
            IntTy tmpval2592 = *(IntTy *) tmpcur2575;
            CursorTy tmpcur2593 = tmpcur2575 + sizeof(IntTy);
            CursorTy jump1402 = tmpcur2575 + (IntTy) 8;
            CursorInt64Prod tmp_struct86 =  _traverse_Foo(end_r760, tmpcur2593);
            CursorTy pvrtmp2594 = tmp_struct86.field0;
            IntTy pvrtmp2595 = tmp_struct86.field1;
            CursorInt64Prod tmp_struct87 =  _traverse_Foo(end_r760, pvrtmp2594);
            CursorTy pvrtmp2596 = tmp_struct87.field0;
            IntTy pvrtmp2597 = tmp_struct87.field1;
            CursorInt64Prod tmp_struct88 =  _traverse_Foo(end_r760, pvrtmp2596);
            CursorTy pvrtmp2598 = tmp_struct88.field0;
            IntTy pvrtmp2599 = tmp_struct88.field1;
            
            return (CursorInt64Prod) {pvrtmp2598, (IntTy) 42};
            break;
        }
        
      case 100:
        {
            CursorTy tmpcur2735 = *(CursorTy *) tmpcur2575;
            CursorTy tmpaftercur2736 = tmpcur2575 + 8;
            TagTyPacked tagtmp2737 = *tmpcur2735;
            CursorTy tailtmp2738 = tmpcur2735 + 1;
            
            tmpval2574 = tagtmp2737;
            tmpcur2575 = tailtmp2738;
            goto switch2612;
            break;
        }
        
      case 90:
        {
            CursorTy tmpcur2735 = *(CursorTy *) tmpcur2575;
            CursorTy tmpaftercur2736 = tmpcur2575 + 8;
            TagTyPacked tagtmp2737 = *tmpcur2735;
            CursorTy tailtmp2738 = tmpcur2735 + 1;
            
            tmpval2574 = tagtmp2737;
            tmpcur2575 = tailtmp2738;
            goto switch2612;
            break;
        }
        
      default:
        {
            CursorTy tmpcur2600 = *(CursorTy *) tmpcur2575;
            CursorTy tmpaftercur2601 = tmpcur2575 + 8;
            CursorTy tmpcur2602 = *(CursorTy *) tmpaftercur2601;
            CursorTy tmpaftercur2603 = tmpaftercur2601 + 8;
            IntTy tmpval2604 = *(IntTy *) tmpaftercur2603;
            CursorTy tmpcur2605 = tmpaftercur2603 + sizeof(IntTy);
            CursorTy jump1409 = tmpaftercur2603 + (IntTy) 8;
            CursorTy jump1408 = tmpaftercur2601 + (IntTy) 8;
            CursorTy jump1407 = tmpcur2575 + (IntTy) 8;
            CursorInt64Prod tmp_struct89 =  _traverse_Foo(end_r760, tmpcur2605);
            CursorTy pvrtmp2606 = tmp_struct89.field0;
            IntTy pvrtmp2607 = tmp_struct89.field1;
            CursorInt64Prod tmp_struct90 =  _traverse_Foo(end_r760, tmpcur2602);
            CursorTy pvrtmp2608 = tmp_struct90.field0;
            IntTy pvrtmp2609 = tmp_struct90.field1;
            CursorInt64Prod tmp_struct91 =  _traverse_Foo(end_r760, tmpcur2600);
            CursorTy pvrtmp2610 = tmp_struct91.field0;
            IntTy pvrtmp2611 = tmp_struct91.field1;
            
            return (CursorInt64Prod) {pvrtmp2610, (IntTy) 42};
        }
    }
}
PtrCursorProd unpack_Foo(CursorTy p2613)
{
    TagTyPacked tag2614 = *p2613;
    CursorTy tail2615 = p2613 + 1;
    
    
  switch2660:
    ;
    switch (tag2614) {
        
      case 0:
        {
            IntTy val2616 = *(IntTy *) tail2615;
            CursorTy tail2617 = tail2615 + sizeof(IntTy);
            PtrTy ptr2618 = (TagInt64Prod *) ALLOC(sizeof(TagInt64Prod));
            
            ((TagInt64Prod *) ptr2618)->field0 = tag2614;
            ((TagInt64Prod *) ptr2618)->field1 = val2616;
            return (PtrCursorProd) {ptr2618, tail2617};
            break;
        }
        
      case 1:
        {
            IntTy val2619 = *(IntTy *) tail2615;
            CursorTy tail2620 = tail2615 + sizeof(IntTy);
            PtrCursorProd tmp_struct92 =  unpack_Foo(tail2620);
            PtrTy ptr2621 = tmp_struct92.field0;
            CursorTy tail2622 = tmp_struct92.field1;
            PtrCursorProd tmp_struct93 =  unpack_Foo(tail2622);
            PtrTy ptr2623 = tmp_struct93.field0;
            CursorTy tail2624 = tmp_struct93.field1;
            PtrTy ptr2625 =
                  (TagInt64CursorCursorProd *) ALLOC(sizeof(TagInt64CursorCursorProd));
            
            ((TagInt64CursorCursorProd *) ptr2625)->field0 = tag2614;
            ((TagInt64CursorCursorProd *) ptr2625)->field1 = val2619;
            ((TagInt64CursorCursorProd *) ptr2625)->field2 = ptr2621;
            ((TagInt64CursorCursorProd *) ptr2625)->field3 = ptr2623;
            return (PtrCursorProd) {ptr2625, tail2624};
            break;
        }
        
      case 2:
        {
            CursorTy next2626 = *(CursorTy *) tail2615;
            CursorTy afternext2627 = tail2615 + 8;
            IntTy val2628 = *(IntTy *) afternext2627;
            CursorTy tail2629 = afternext2627 + sizeof(IntTy);
            PtrCursorProd tmp_struct94 =  unpack_Foo(tail2629);
            PtrTy ptr2630 = tmp_struct94.field0;
            CursorTy tail2631 = tmp_struct94.field1;
            PtrCursorProd tmp_struct95 =  unpack_Foo(tail2631);
            PtrTy ptr2632 = tmp_struct95.field0;
            CursorTy tail2633 = tmp_struct95.field1;
            PtrTy ptr2634 =
                  (TagInt64CursorCursorProd *) ALLOC(sizeof(TagInt64CursorCursorProd));
            
            ((TagInt64CursorCursorProd *) ptr2634)->field0 = tag2614;
            ((TagInt64CursorCursorProd *) ptr2634)->field1 = val2628;
            ((TagInt64CursorCursorProd *) ptr2634)->field2 = ptr2630;
            ((TagInt64CursorCursorProd *) ptr2634)->field3 = ptr2632;
            return (PtrCursorProd) {ptr2634, tail2633};
            break;
        }
        
      case 3:
        {
            IntTy val2635 = *(IntTy *) tail2615;
            CursorTy tail2636 = tail2615 + sizeof(IntTy);
            PtrCursorProd tmp_struct96 =  unpack_Foo(tail2636);
            PtrTy ptr2637 = tmp_struct96.field0;
            CursorTy tail2638 = tmp_struct96.field1;
            PtrCursorProd tmp_struct97 =  unpack_Foo(tail2638);
            PtrTy ptr2639 = tmp_struct97.field0;
            CursorTy tail2640 = tmp_struct97.field1;
            PtrCursorProd tmp_struct98 =  unpack_Foo(tail2640);
            PtrTy ptr2641 = tmp_struct98.field0;
            CursorTy tail2642 = tmp_struct98.field1;
            PtrTy ptr2643 =
                  (TagInt64CursorCursorCursorProd *) ALLOC(sizeof(TagInt64CursorCursorCursorProd));
            
            ((TagInt64CursorCursorCursorProd *) ptr2643)->field0 = tag2614;
            ((TagInt64CursorCursorCursorProd *) ptr2643)->field1 = val2635;
            ((TagInt64CursorCursorCursorProd *) ptr2643)->field2 = ptr2637;
            ((TagInt64CursorCursorCursorProd *) ptr2643)->field3 = ptr2639;
            ((TagInt64CursorCursorCursorProd *) ptr2643)->field4 = ptr2641;
            return (PtrCursorProd) {ptr2643, tail2642};
            break;
        }
        
      case 4:
        {
            CursorTy next2644 = *(CursorTy *) tail2615;
            CursorTy afternext2645 = tail2615 + 8;
            CursorTy next2646 = *(CursorTy *) afternext2645;
            CursorTy afternext2647 = afternext2645 + 8;
            IntTy val2648 = *(IntTy *) afternext2647;
            CursorTy tail2649 = afternext2647 + sizeof(IntTy);
            PtrCursorProd tmp_struct99 =  unpack_Foo(tail2649);
            PtrTy ptr2650 = tmp_struct99.field0;
            CursorTy tail2651 = tmp_struct99.field1;
            PtrCursorProd tmp_struct100 =  unpack_Foo(tail2651);
            PtrTy ptr2652 = tmp_struct100.field0;
            CursorTy tail2653 = tmp_struct100.field1;
            PtrCursorProd tmp_struct101 =  unpack_Foo(tail2653);
            PtrTy ptr2654 = tmp_struct101.field0;
            CursorTy tail2655 = tmp_struct101.field1;
            PtrTy ptr2656 =
                  (TagInt64CursorCursorCursorProd *) ALLOC(sizeof(TagInt64CursorCursorCursorProd));
            
            ((TagInt64CursorCursorCursorProd *) ptr2656)->field0 = tag2614;
            ((TagInt64CursorCursorCursorProd *) ptr2656)->field1 = val2648;
            ((TagInt64CursorCursorCursorProd *) ptr2656)->field2 = ptr2650;
            ((TagInt64CursorCursorCursorProd *) ptr2656)->field3 = ptr2652;
            ((TagInt64CursorCursorCursorProd *) ptr2656)->field4 = ptr2654;
            return (PtrCursorProd) {ptr2656, tail2655};
            break;
        }
        
      case 90:
        {
            CursorTy next2657 = *(CursorTy *) tail2615;
            CursorTy afternext2658 = tail2615 + 8;
            PtrTy ptr2659 = (TagProd *) ALLOC(sizeof(TagProd));
            
            ((TagProd *) ptr2659)->field0 = tag2614;
            return (PtrCursorProd) {ptr2659, afternext2658};
            break;
        }
        
      default:
        {
            CursorTy tmpcur2739 = *(CursorTy *) tail2615;
            CursorTy tmpaftercur2740 = tail2615 + 8;
            TagTyPacked tagtmp2741 = *tmpcur2739;
            CursorTy tailtmp2742 = tmpcur2739 + 1;
            
            tag2614 = tagtmp2741;
            tail2615 = tailtmp2742;
            goto switch2660;
        }
    }
}
PtrTy print_Foo(CursorTy p2661)
{
    TagTyPacked tag2662 = *(TagTyPacked *) p2661;
    CursorTy tail2663 = p2661 + sizeof(IntTy);
    
    
  switch2714:
    ;
    switch (tag2662) {
        
      case 0:
        {
            fputs("(A ", stdout);
            
            IntTy val2664 = *(IntTy *) tail2663;
            CursorTy tail2665 = tail2663 + sizeof(IntTy);
            
            printf("%lld", val2664);
            fputs(")", stdout);
            return tail2665;
            break;
        }
        
      case 1:
        {
            fputs("(B ", stdout);
            
            IntTy val2666 = *(IntTy *) tail2663;
            CursorTy tail2667 = tail2663 + sizeof(IntTy);
            
            printf("%lld", val2666);
            fputs(" ", stdout);
            
            IntTy val2668 = *(IntTy *) tail2667;
            CursorTy tail2669 = tail2667 + sizeof(IntTy);
            PtrTy temp2670 =  print_Foo(val2668);
            
            fputs(" ", stdout);
            
            IntTy val2672 = *(IntTy *) tail2669;
            CursorTy tail2673 = tail2669 + sizeof(IntTy);
            PtrTy temp2674 =  print_Foo(val2672);
            
            fputs(")", stdout);
            return tail2673;
            break;
        }
        
      case 2:
        {
            fputs("(B^ ", stdout);
            
            IntTy val2676 = *(IntTy *) tail2663;
            CursorTy tail2677 = tail2663 + sizeof(IntTy);
            
            printf("%lld", val2676);
            fputs(" ", stdout);
            
            IntTy val2678 = *(IntTy *) tail2677;
            CursorTy tail2679 = tail2677 + sizeof(IntTy);
            PtrTy temp2680 =  print_Foo(val2678);
            
            fputs(" ", stdout);
            
            IntTy val2682 = *(IntTy *) tail2679;
            CursorTy tail2683 = tail2679 + sizeof(IntTy);
            PtrTy temp2684 =  print_Foo(val2682);
            
            fputs(")", stdout);
            return tail2683;
            break;
        }
        
      case 3:
        {
            fputs("(C ", stdout);
            
            IntTy val2686 = *(IntTy *) tail2663;
            CursorTy tail2687 = tail2663 + sizeof(IntTy);
            
            printf("%lld", val2686);
            fputs(" ", stdout);
            
            IntTy val2688 = *(IntTy *) tail2687;
            CursorTy tail2689 = tail2687 + sizeof(IntTy);
            PtrTy temp2690 =  print_Foo(val2688);
            
            fputs(" ", stdout);
            
            IntTy val2692 = *(IntTy *) tail2689;
            CursorTy tail2693 = tail2689 + sizeof(IntTy);
            PtrTy temp2694 =  print_Foo(val2692);
            
            fputs(" ", stdout);
            
            IntTy val2696 = *(IntTy *) tail2693;
            CursorTy tail2697 = tail2693 + sizeof(IntTy);
            PtrTy temp2698 =  print_Foo(val2696);
            
            fputs(")", stdout);
            return tail2697;
            break;
        }
        
      case 4:
        {
            fputs("(C^ ", stdout);
            
            IntTy val2700 = *(IntTy *) tail2663;
            CursorTy tail2701 = tail2663 + sizeof(IntTy);
            
            printf("%lld", val2700);
            fputs(" ", stdout);
            
            IntTy val2702 = *(IntTy *) tail2701;
            CursorTy tail2703 = tail2701 + sizeof(IntTy);
            PtrTy temp2704 =  print_Foo(val2702);
            
            fputs(" ", stdout);
            
            IntTy val2706 = *(IntTy *) tail2703;
            CursorTy tail2707 = tail2703 + sizeof(IntTy);
            PtrTy temp2708 =  print_Foo(val2706);
            
            fputs(" ", stdout);
            
            IntTy val2710 = *(IntTy *) tail2707;
            CursorTy tail2711 = tail2707 + sizeof(IntTy);
            PtrTy temp2712 =  print_Foo(val2710);
            
            fputs(")", stdout);
            return tail2711;
            break;
        }
        
      case 90:
        {
            fputs("(INDIRECTION1246 ", stdout);
            fputs(")", stdout);
            return tail2663;
            break;
        }
        
      default:
        {
            CursorTy tmpcur2743 = *(CursorTy *) tail2663;
            CursorTy tmpaftercur2744 = tail2663 + 8;
            TagTyPacked tagtmp2745 = *tmpcur2743;
            CursorTy tailtmp2746 = tmpcur2743 + 1;
            
            tag2662 = tagtmp2745;
            tail2663 = tailtmp2746;
            goto switch2714;
        }
    }
}
void __main_expr()
{
    RegionTy *region2020 = alloc_region(global_init_inf_buf_size);
    CursorTy r767 = region2020->start_ptr;
    IntTy sizeof_end_r7672021 = global_init_inf_buf_size;
    CursorTy end_r767 = r767 + sizeof_end_r7672021;
    IntTy n86 = global_size_param;
    CursorTy pvrtmp2029;
    CursorTy pvrtmp2030;
    CursorTy pvrtmp2031;
    struct timespec begin_pvrtmp2029;
    
    clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp2029);
    for (long long iters_pvrtmp2029 = 0; iters_pvrtmp2029 < global_iters_param;
         iters_pvrtmp2029++) {
        if (iters_pvrtmp2029 != global_iters_param - 1)
            save_alloc_state();
        
        CursorCursorCursorProd tmp_struct102 =  mkFoo(end_r767, r767, n86);
        CursorTy pvrtmp2022 = tmp_struct102.field0;
        CursorTy pvrtmp2023 = tmp_struct102.field1;
        CursorTy pvrtmp2024 = tmp_struct102.field2;
        
        pvrtmp2029 = pvrtmp2022;
        pvrtmp2030 = pvrtmp2023;
        pvrtmp2031 = pvrtmp2024;
        if (iters_pvrtmp2029 != global_iters_param - 1)
            restore_alloc_state();
    }
    
    struct timespec end_pvrtmp2029;
    
    clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp2029);
    
    double batchtime103 = difftimespecs(&begin_pvrtmp2029, &end_pvrtmp2029);
    double selftimed104 = batchtime103 / global_iters_param;
    
    printf("ITERS: %lld\n", global_iters_param);
    printf("SIZE: %lld\n", global_size_param);
    printf("BATCHTIME: %e\n", batchtime103);
    printf("SELFTIMED: %e\n", selftimed104);
    
    CursorInt64Prod tmp_struct105 =  sumFoo_seq(end_r767, pvrtmp2030);
    CursorTy pvrtmp2039 = tmp_struct105.field0;
    IntTy pvrtmp2040 = tmp_struct105.field1;
    
    printf("%lld", pvrtmp2040);
    fputs("\n", stdout);
    free_symtable();
    return;
}
