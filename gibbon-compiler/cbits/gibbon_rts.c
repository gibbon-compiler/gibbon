// The imports here must be kept in sync with
// 'hashIncludes' in Gibbon.Passes.Codegen.

#include "gibbon_rts.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
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
#include <stdarg.h>
#include <errno.h>
#include <uthash.h>

#ifdef _WIN64
#include <windows.h>
#endif

#ifdef _GIBBON_POINTER
#include <gc.h>
#endif

#ifdef _GIBBON_PARALLEL
#include <cilk/cilk.h>
#include <cilk/cilk_api.h>
#endif


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Globals and their accessors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

#define MAX_CHUNK_SIZE 65535

// Chunk sizes of buffers, see GitHub #79 and #110.
static uint64_t gib_global_biginf_init_chunk_size = 4 * GB;
static uint64_t gib_global_inf_init_chunk_size = 1 * KB;

// Runtime arguments, values updated by the flags parser.
static GibInt gib_global_size_param = 1;
static GibInt gib_global_iters_param = 1;
static char *gib_global_bench_prog_param = (char *) NULL;
static char *gib_global_benchfile_param = (char *) NULL;
static char *gib_global_arrayfile_param = (char *) NULL;
static uint64_t gib_global_arrayfile_length_param = -1;

// Number of regions allocated.
static int64_t gib_global_region_count = 0;

// Invariant: should always be equal to max(sym_table_keys).
static GibSym gib_global_gensym_counter = 0;



uint64_t gib_get_biginf_init_chunk_size(void)
{
    return gib_global_biginf_init_chunk_size;
}

uint64_t gib_get_inf_init_chunk_size(void)
{
    return gib_global_inf_init_chunk_size;
}

GibInt gib_get_size_param(void)
{
    return gib_global_size_param;
}

GibInt gib_get_iters_param(void)
{
    return gib_global_iters_param;
}

char *gib_read_bench_prog_param(void)
{
    if (gib_global_bench_prog_param == NULL) {
        fprintf(stderr, "gib_read_bench_prog_param: benchmark program was not set! Set using --bench-prog.\n");
        exit(1);
    } else {
        return gib_global_bench_prog_param;
    }
}

char *gib_read_benchfile_param(void)
{
    if (gib_global_benchfile_param == NULL) {
        fprintf(stderr, "gib_read_benchfile_param: benchmark input file was not set! Set using --bench-input.\n");
        exit(1);
    } else {
        return gib_global_benchfile_param;
    }
}

char *gib_read_arrayfile_param(void)
{
    if (gib_global_arrayfile_param == NULL) {
        fprintf(stderr, "gib_read_arrayfile_param: array input file was not set! Set using --array-input.\n");
        exit(1);
    } else {
        return gib_global_arrayfile_param;
    }
}

uint64_t gib_read_arrayfile_length_param(void)
{
    return gib_global_arrayfile_length_param;
}

int64_t gib_read_region_count(void)
{
    return gib_global_region_count;
}

GibSym gib_read_gensym_counter(void)
{
    return gib_global_gensym_counter;
}



/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Allocators
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/*
 * If parallelism is enabled, we always use a nursery/malloc based allocator
 * since Boehm GC is not thread-safe in its default configuration. It can be
 * made thread-safe by building it with appropriate flags, but we don't do that.
 * Presently, all parallel pointer-based programs will leak memory.
 */

#ifdef _GIBBON_POINTER
#ifndef _GIBBON_PARALLEL
void *gib_alloc(size_t n) { return GC_MALLOC(n); }
#else
void *gib_alloc(size_t n) { return malloc(n); }
#endif // ifndef _GIBBON_PARALLEL
#else
void *gib_alloc(size_t n) { return malloc(n); }
#endif // ifdef _GIBBON_POINTER

void *gib_counted_alloc(size_t n) {
    gib_bump_global_region_count();
    return gib_alloc(n);
}

// Could try alloca() here.  Better yet, we could keep our own,
// separate stack and insert our own code to restore the pointer
// before any function that (may have) called gib_scoped_alloc returns.
void *gib_scoped_alloc(size_t n) { return alloca(n); }

// Stack allocation is either too small or blows our stack.
// We need a way to make a giant stack if we want to use alloca.

// Our global pointer.  No parallelism.
// static char* stack_scoped_region;
// char* alloc_scoped() { return stack_scoped_region; }



/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Arenas
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

GibArena *gib_alloc_arena(void)
{
    GibArena *ar = gib_alloc(sizeof(GibArena));
    ar->ind = 0;
    ar->mem = (char *) gib_alloc(MAX_CHUNK_SIZE);
    ar->reflist = 0;
    return ar;
}

void gib_free_arena(GibArena *ar)
{
    free(ar->mem);
    // TODO(vollmerm): free everything in ar->reflist
    free(ar);
    return;
}

GibCursor gib_extend_arena(GibArena *ar, int size)
{
    GibCursor ret = ar->mem + ar->ind;
    ar->ind += size;
    return ret;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Arena-based dictionaries
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


GibSymDict *gib_dict_alloc(GibArena *ar)
{
    return (GibSymDict *) gib_extend_arena(ar, sizeof(GibSymDict));
}

GibSymDict *gib_dict_insert_ptr(GibArena *ar, GibSymDict *ptr, GibSym key, GibPtr val)
{
    GibSymDict *ret = gib_dict_alloc(ar);
    ret->key = key;
    ret->ptrval = val;
    ret->next = ptr;
    return ret;
}

GibPtr gib_dict_lookup_ptr(GibSymDict *ptr, GibSym key)
{
    while (ptr != 0) {
        if (ptr->key == key) {
            return ptr->ptrval;
        } else {
            ptr = ptr->next;
        }
    }
    fprintf(stderr, "Error, key %" PRId64 " not found!\n",key);
    exit(1);
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Sets
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


GibSymSet *gib_empty_set(void)
{
    return (GibSymSet *) NULL;
}

GibSymSet *gib_insert_set(GibSymSet *set, int sym)
{
    GibSymSet *s;
    HASH_FIND_INT(set, &sym, s);  /* sym already in the hash? */
    if (s==NULL) {
        s = (GibSymSet *) gib_alloc(sizeof(GibSymSet));
        s->val = sym;
        HASH_ADD_INT(set,val,s);
    }
    return set;
}

GibBool gib_contains_set(GibSymSet *set, int sym)
{
    GibSymSet *s;
    HASH_FIND_INT(set, &sym, s);
    return (s!=NULL);
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Sym Hash
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


GibSymHash *gib_empty_hash(void)
{
    return (GibSymHash *) NULL;
}

GibSymHash *gib_insert_hash(GibSymHash *hash, int k, int v)
{
    GibSymHash *s;
    // NOTE: not checking for duplicates!
    s = (GibSymHash *) gib_alloc(sizeof(GibSymHash));
    s->val = v;
    s->key = k;
    HASH_ADD_INT(hash,key,s);

    return hash;
}

GibSym gib_lookup_hash(GibSymHash *hash, int k)
{
    GibSymHash *s;
    HASH_FIND_INT(hash,&k,s);
    if (s==NULL) {
        return k; // NOTE: return original key if val not found
        // TODO(vollmerm): come up with something better to do here
    } else {
        return s->val;
    }
}

GibBool gib_contains_hash(GibSymHash *hash, int sym)
{
    GibSymHash *s;
    HASH_FIND_INT(hash,&sym,s);
    return (s!=NULL);
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Symbol table
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

static GibSym newline_symbol = -1;
static GibSym space_symbol = -1;
static GibSym comma_symbol = -1;
static GibSym leftparen_symbol = -1;
static GibSym rightparen_symbol = -1;


// important! initialize to NULL
static GibSymtable *global_sym_table = (GibSymtable *) NULL;

void gib_add_symbol(GibSym idx, char *value)
{
    GibSymtable *s;
    s = (GibSymtable *) gib_alloc(sizeof(GibSymtable));
    s->idx = idx;
    strcpy(s->value, value);
    HASH_ADD(hh, global_sym_table, idx, sizeof(GibSym), s);
    if (idx > gib_global_gensym_counter) {
        gib_global_gensym_counter = idx;
    }
    return;
}

void gib_set_newline(GibSym idx)
{
    newline_symbol = idx;
    gib_add_symbol(idx,"NEWLINE");
    return;
}

void gib_set_space(GibSym idx)
{
    space_symbol = idx;
    gib_add_symbol(idx,"SPACE");
    return;
}

void gib_set_comma(GibSym idx)
{
    comma_symbol = idx;
    gib_add_symbol(idx,"COMMA");
    return;
}

void gib_set_leftparen(GibSym idx)
{
    leftparen_symbol = idx;
    gib_add_symbol(idx,"LEFTPAREN");
    return;
}

void gib_set_rightparen(GibSym idx)
{
    rightparen_symbol = idx;
    gib_add_symbol(idx,"RIGHTPAREN");
    return;
}

int gib_print_symbol(GibSym idx)
{
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
        GibSymtable *s;
        HASH_FIND(hh, global_sym_table, &idx, sizeof(GibSym), s);
        if (s == NULL) {
            return printf("%" PRId64, idx);
        } else {
            return printf("%s", s->value);
        }

    }
}

GibSym gib_gensym(void)
{
    GibSym idx;
#ifdef _GIBBON_PARALLEL
    idx = __atomic_add_fetch(&gib_global_gensym_counter, 1, __ATOMIC_SEQ_CST);
#else
    gib_global_gensym_counter += 1;
    idx = gib_global_gensym_counter;
#endif
    return idx;
}


void gib_free_symtable(void)
{
    GibSymtable *elt, *tmp;
    HASH_ITER(hh, global_sym_table, elt, tmp) {
        HASH_DEL(global_sym_table,elt);
        free(elt);
    }
    return;
}



/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Vectors
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

GibVector *gib_vector_alloc(GibInt num, size_t elt_size)
{
    GibVector *vec = (GibVector *) gib_alloc(sizeof(GibVector));
    if (vec == NULL) {
        fprintf(stderr, "alloc_vector: gib_alloc failed: %ld", sizeof(GibVector));
        exit(1);
    }
    void *data = (void *) gib_alloc(num * elt_size);
    if (data == NULL) {
        fprintf(stderr, "alloc_vector: gib_alloc failed: %ld", sizeof(num * elt_size));
        exit(1);
    }
    vec->lower = 0;
    vec->upper = num;
    vec->elt_size = elt_size;
    vec->data = data;
    return vec;
}

GibInt gib_vector_length(GibVector *vec)
{
    return (vec->upper - vec->lower);
}

GibBool gib_vector_is_empty(GibVector *vec)
{
    return (gib_vector_length(vec) == 0);
}

GibVector *gib_vector_slice(GibInt i, GibInt n, GibVector *vec)
{
    GibInt lower = vec->lower + i;
    GibInt upper = vec->lower + i + n;
    if ((lower > vec->upper)) {
        fprintf(stderr, "gib_vector_slice: lower out of bounds, %" PRId64
                " > %" PRId64, lower, vec->upper);
        exit(1);
    }
    if ((upper > vec->upper)) {
        fprintf(stderr, "gib_vector_slice: upper out of bounds, %" PRId64
                " > %" PRId64, upper, vec->upper);
        exit(1);
    }
    GibVector *vec2 = (GibVector *) gib_alloc(sizeof(GibVector));
    if (vec == NULL) {
        fprintf(stderr, "gib_vector_slice: gib_alloc failed: %ld", sizeof(GibVector));
        exit(1);
    }
    vec2->lower = lower;
    vec2->upper = upper;
    vec2->elt_size = vec->elt_size;
    vec2->data = vec->data;
    return vec2;
}

// The callers must cast the return value.
void *gib_vector_nth(GibVector *vec, GibInt i)
{
#ifdef _GIBBON_BOUNDSCHECK
    if (i < vec->lower || i > vec->upper) {
        fprintf(stdderr, "gib_vector_nth index out of bounds: %lld (%lld,%lld)\n",
                i, vec->lower, vec->upper);
        exit(1);
    }
#endif
    return ((char*)vec->data + (vec->elt_size * (vec->lower + i)));
}

GibVector *gib_vector_inplace_update(GibVector *vec, GibInt i, void* elt)
{
    void* dst = gib_vector_nth(vec, i);
    memcpy(dst, elt, vec->elt_size);
    return vec;
}

GibVector *gib_vector_copy(GibVector *vec)
{
    GibInt len = gib_vector_length(vec);
    void *start = gib_vector_nth(vec, 0);
    GibVector *vec2 = gib_vector_alloc(len, vec->elt_size);
    memcpy(vec2->data, start, len * vec->elt_size);
    return vec2;
}

GibVector *gib_vector_inplace_sort(GibVector *vec, int (*compar)(const void *, const void*))
{
    void *start = gib_vector_nth(vec, 0);
    qsort(start, gib_vector_length(vec), vec->elt_size, compar);
    return vec;
}

GibVector *gib_vector_sort(GibVector *vec, int (*compar)(const void *, const void*))
{
    GibVector *vec2 = gib_vector_copy(vec);
    gib_vector_inplace_sort(vec2, compar);
    return vec2;
}

GibVector *gib_vector_concat(GibVector *vec)
{
    // Length of the input vector.
    GibInt len = gib_vector_length(vec);
    // Length of the concatenated vector.
    GibInt result_len = 0;
    // Size of each element in the concatenated vector.
    GibInt result_elt_size = 0;
    GibVector **elt_ref, *elt;
    for (GibInt i = 0; i < len; i++) {
        elt_ref = gib_vector_nth(vec, i);
        elt = *elt_ref;
        result_elt_size = elt->elt_size;
        result_len += gib_vector_length(elt);
    }

    // Concatenated vector.
    GibVector *result = gib_vector_alloc(result_len, result_elt_size);
    GibInt elt_len;
    // A counter that tracks the index of elements in 'result'.
    GibInt k = 0;
    for (GibInt i = 0; i < len; i++) {
        elt_ref = gib_vector_nth(vec, i);
        elt = *elt_ref;
        elt_len = gib_vector_length(elt);

        for (GibInt j = 0; j < elt_len; j++) {
            void* k_elt = gib_vector_nth(elt, j);
            gib_vector_inplace_update(result, k, k_elt);
            k++;
        }
    }

    return result;
}

void gib_vector_free(GibVector *vec)
{
    free(vec->data);
    free(vec);
    return;
}

GibVector *gib_vector_merge(GibVector *vec1, GibVector *vec2)
{
    if (vec1->upper != vec2->lower) {
        fprintf(stderr,"gib_vector_merge: non-contiguous slices, (%" PRId64
                ",%" PRId64 "), (%" PRId64 ",%" PRId64 ")",
               vec1->lower, vec1->upper, vec2->lower, vec2->upper);
        exit(1);
    }
    GibVector *merged = (GibVector *) gib_alloc(sizeof(GibVector));
    if (merged == NULL) {
        fprintf(stderr, "gib_vector_merge: gib_alloc failed: %ld", sizeof(GibVector));
        exit(1);
    }
    merged->lower = vec1->lower;
    merged->upper = vec2->upper;
    merged->elt_size = vec1->elt_size;
    merged->data = vec1->data;
    return merged;
}

void gib_print_timing_array(GibVector *times) {
    printf("ITER TIMES: [");
    double *d;
    GibInt n = gib_vector_length(times);
    for(GibInt i = 0; i < n; i++) {
        d = gib_vector_nth(times, i);
        if (i == (n-1)) {
            printf("%f",*d);
        }
        else {
            printf("%f, ",*d);
        }
    }
    printf("]\n");
    return;
}

double gib_sum_timing_array(GibVector *times)
{
    double *d;
    double acc = 0;
    for(int i = 0; i < gib_vector_length(times); i++) {
        d = gib_vector_nth(times, i);
        acc += *d;
    }
    return acc;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Linked lists
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


#ifdef _BUMPALLOC
// #define _GIBBON_DEBUG
#warning "Using bump allocator."

static __thread char *gib_global_list_bumpalloc_heap_ptr = (char *) NULL;
static __thread char *gib_global_list_bumpalloc_heap_ptr_end = (char *) NULL;
static char *gib_global_list_saved_heap_ptr_stack[100];
static int gib_global_list_num_saved_heap_ptr = 0;

// For simplicity just use a single large slab:
void gib_init_bumpalloc(void)
{
    gib_global_list_bumpalloc_heap_ptr =
        (char*) gib_alloc(gib_global_biginf_init_chunk_size);
    gib_global_list_bumpalloc_heap_ptr_end =
        gib_global_list_bumpalloc_heap_ptr + gib_global_biginf_init_chunk_size;
#ifdef _GIBBON_DEBUG
    printf("Arena size for bump alloc: %lld\n", gib_global_biginf_init_chunk_size);
    printf("gib_list_bumpalloc/gib_init_bumpalloc DONE: heap_ptr = %p\n",
           gib_global_list_bumpalloc_heap_ptr);
#endif
}

void *gib_list_bumpalloc(int64_t n)
{
    if (! gib_global_list_bumpalloc_heap_ptr) {
        gib_init_bumpalloc();
    }
    if (gib_global_list_bumpalloc_heap_ptr + n <
        gib_global_list_bumpalloc_heap_ptr_end) {
        char* old= gib_global_list_bumpalloc_heap_ptr;
        gib_global_list_bumpalloc_heap_ptr += n;
        return old;
    } else {
        fprintf(stderr, "Warning: bump allocator ran out of memory.");
        exit(1);
    }
}

// Snapshot the current heap pointer value across all threads.
void gib_list_save_alloc_state(void)
{
#ifdef _GIBBON_DEBUG
    printf("Saving(%p): pos %d", heap_ptr, gib_global_list_num_saved_heap_ptr);
#endif
    gib_global_list_saved_heap_ptr_stack[gib_global_list_num_saved_heap_ptr] = heap_ptr;
    gib_global_list_num_saved_heap_ptr++;
#ifdef _GIBBON_DEBUG
    printf("\n");
#endif
}

void gib_list_restore_alloc_state(void)
{
    if(gib_global_list_num_saved_heap_ptr <= 0) {
        fprintf(stderr, "Bad call to gib_list_restore_alloc_state!  Saved stack empty!\ne");
        exit(1);
    }
    gib_global_list_num_saved_heap_ptr--;
#ifdef _GIBBON_DEBUG
    printf("Restoring(%p): pos %d, discarding %p",
           gib_global_list_saved_heap_ptr_stack[gib_global_list_num_saved_heap_ptr],
           gib_global_list_num_saved_heap_ptr,
           gib_global_list_bumpalloc_heap_ptr);
#endif
    gib_global_list_bumpalloc_heap_ptr =
        gib_global_list_saved_heap_ptr_stack[gib_global_list_num_saved_heap_ptr];
}

#else
// Regular malloc mode:
void gib_init_bumpalloc(void) {}
void *gib_list_bumpalloc(int64_t n) { return gib_alloc(n); }
void gib_list_save_alloc_state(void) {}
void gib_list_restore_alloc_state(void) {}

#endif // BUMPALLOC


// List API.

GibList *gib_list_alloc(size_t data_size)
{
    // GibList *ls = gib_alloc(sizeof(GibList));
    GibList *ls = gib_list_bumpalloc(sizeof(GibList));
    ls->data_size = data_size;
    ls->data = (void *) NULL;
    ls->next = (GibList *) NULL;
    return ls;
}

GibBool gib_list_is_empty(GibList *ls)
{
    return ls->next == NULL;
}

GibList *gib_list_cons(void *elt, GibList *ls)
{
    // void* data = gib_alloc(ls->data_size);
    void* data = gib_list_bumpalloc(ls->data_size);
    if (data == NULL) {
        fprintf(stderr, "gib_list_cons: gib_alloc failed: %ld", ls->data_size);
        exit(1);
    }
    memcpy(data, elt, ls->data_size);
    // GibList *res = gib_alloc(sizeof(GibList));
    GibList *res = gib_list_bumpalloc(sizeof(GibList));
    res->data_size = ls->data_size;
    res->data = data;
    res->next = (GibList*) ls;
    return res;
}

void *gib_list_head(GibList *ls)
{
    return ls->data;
}

GibList* gib_list_tail(GibList *ls)
{
    return ls->next;
}

void gib_list_free(GibList *ls)
{
    free(ls->data);
    free(ls);
    return;
}

GibList *gib_list_copy(GibList *ls)
{
    GibList *ls2 = gib_list_alloc(ls->data_size);
    if (ls->data != NULL) {
        void* data = gib_list_bumpalloc(ls->data_size);
        memcpy(data, ls->data, ls->data_size);
        ls2->data = data;
    }
    ls2->next = ls->next;
    return ls2;
}

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ppm images
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Example: writePpm("gibbon_rgb_1000.ppm", 1000, 1000, pixels);
void gib_write_ppm(char* filename, GibInt width, GibInt height, GibVector *pixels)
{
    FILE *fp;
    fp = fopen(filename, "w+");
    fprintf(fp, "P3\n");
    // fprintf(fp, "%lld %lld\n255\n", width, height);
    fprintf(fp, "%" PRId64 " %" PRId64 "\n255\n", width, height);
    GibInt len = gib_vector_length(pixels);
    gib_write_ppm_loop(fp, 0, len, pixels);
    fclose(fp);
    return;
}

void gib_write_ppm_loop(FILE *fp, GibInt idx, GibInt end, GibVector *pixels)
{
    bool fltIf_5768_6575 = idx == end;

    if (fltIf_5768_6575) {
        return;
    } else {
        GibPixel *tmp_112;
        tmp_112 = (GibPixel *) gib_vector_nth(pixels, idx);
        GibPixel tup = *tmp_112;
        GibInt x = tup.field0;
        GibInt y = tup.field1;
        GibInt z = tup.field2;
        // write to file.
        // fprintf(fp, "%lld %lld %lld\n", x, y, z);
        fprintf(fp, "%" PRId64 " %" PRId64 " %" PRId64 "\n", x, y, z);
        gib_write_ppm_loop(fp, (idx+1), end, pixels);
    }
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Memory Management; regions, chunks, GC etc.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

/*

  Gibbon has "growing regions" i.e each logical region is backed by a doubly
  linked-list of smaller chunks which grows as required. In addition to actual
  data, each chunk stores some additional metadata (GibChunkFooter) to chain
  the chunks together in a list and for garbage collection. The footer:

  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  data | reg_info | seq_no | size | next | prev
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  The metadata after the serialized data serves various purposes:

  - reg_info: A pointer to a GibRegionInfo struct that contains
  various metadata. Of particular interest to us are the fields:

  = id: A unique identifier for a region.

  = refcount and outset: Whenever an inter-region indirection is created, we
    record that information using these two fields. Suppose we have an
    indirection from region A that points to some chunk in region B. Then A's
    outset will store a pointer to that chunk's footer, and B's refcount will
    be bumped by 1. Note that all there's only 1 refcount cell, and 1 outset
    per logical region, and chunks only store a pointer to them.

  - seq_no: The index of this particular chunk in the list.

  - size: Used during bounds checking to calculate the size of the next
    region in the linked list.

  - next / prev: Point to the next and previous chunk respectively.


  There are two ways in which a region may be freed:

  (1) Whenever it goes out of scope

  The RTS tries to free a region whenever it goes out of scope. But this doesn't
  always succeed as regions sometimes contain values that "escape". One reason
  why this'll happen is if there's an indirection from A->B, and A lives longer
  than B. In such a case, when B goes out of scope it's refcount won't be 0,
  and the RTS won't free it. This brings us to (2).

  (2)

  When the RTS successfully frees a region, it decrements the refcounts of all
  the regions it points to (via the outset). At the same time, if it encounters
  a region in the outset whoose refcount becomes 0 after the decrement, it
  calls gib_free_region on that. This way we can be sure that all regions will
  eventually be garbage collected before the program exits.



  Why is it a doubly linked-list?
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  Due to way that bounds-checking works, the pointers in the outset may
  actually point to any arbitrary chunk in the chain. However, we must call
  gib_free_region on the first one to ensure that all of them are GC'd.
  So we need pointers to traverse backward get to the first one.
  'gib_trav_to_first_chunk' accomplishes this.

*/

#define MAX_OUTSET_LENGTH 10

typedef struct gib_region_meta {
    GibSym id;
    uint16_t refcount;
    uint16_t outset_len;
    GibCursor outset[MAX_OUTSET_LENGTH];
    void *outset2;
} GibRegionInfo;

typedef struct gib_chunk_footer {
    GibRegionInfo *reg_info;

    uint16_t seq_no;
    uint64_t size;
    struct gib_chunk_footer *next;
    struct gib_chunk_footer *prev;
} GibChunkFooter;

static void gib_insert_into_outset(GibCursor ptr, GibRegionInfo *reg);
static void gib_remove_from_outset(GibCursor ptr, GibRegionInfo *reg);
static GibChunkFooter *gib_trav_to_first_chunk(GibChunkFooter *footer);
static uint16_t gib_get_ref_count(GibCursor end_ptr);


GibChunk *gib_alloc_region(uint64_t size)
{
    // Allocate the region metadata.
    GibRegionInfo *reg_info = gib_alloc(sizeof(GibRegionInfo));
    if (reg_info == NULL) {
        fprintf(stderr, "gib_alloc_region: allocation failed: %ld",
                sizeof(GibRegionInfo));
        exit(1);
    }

    // Allocate the first chunk.
    int64_t total_size = size + sizeof(GibChunkFooter);
    GibCursor heap_start = gib_alloc(total_size);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_alloc_region: gib_alloc failed: %" PRId64,
                total_size);
        exit(1);
    }
    // Not start+total_size, since we must keep space for the footer.
    GibCursor heap_end = heap_start + size;

    // Initialize metadata fields.
    reg_info->id = gib_gensym();
    reg_info->refcount = 1;
    reg_info->outset_len = 0;
    reg_info->outset2 = NULL;

#ifdef _GIBBON_DEBUG
    printf("Allocated a region(%" PRIu64 "): %" PRIu64 " bytes.\n",
           reg_info->id, size);
#endif

    // Write the footer.
    GibChunkFooter *footer = (GibChunkFooter *) heap_end;
    footer->reg_info = reg_info;
    footer->seq_no = 1;
    footer->size = size;
    footer->next = (GibChunkFooter *) NULL;
    footer->prev = (GibChunkFooter *) NULL;

    GibChunk *region = (GibChunk *) gib_alloc(sizeof(GibChunk));
    region->start = heap_start;
    region->end = heap_end;
    return region;
}

GibChunk gib_alloc_chunk(GibCursor footer_ptr)
{
    // Get size from current footer.
    GibChunkFooter *footer = (GibChunkFooter *) footer_ptr;
    uint64_t newsize = footer->size * 2;
    // See #110.
    if (newsize > MAX_CHUNK_SIZE) {
        newsize = MAX_CHUNK_SIZE;
    }
    uint64_t total_size = newsize + sizeof(GibChunkFooter);

    // Allocate.
    GibCursor start = (char *) gib_alloc(total_size);
    if (start == NULL) {
        fprintf(stderr, "gib_alloc_chunk: gib_alloc failed: %" PRId64,
                total_size);
        exit(1);
    }
    GibCursor end = start + newsize;

    // Link the next chunk's footer.
    footer->next = (GibChunkFooter *) end;

    // Write the footer.
    GibChunkFooter *new_footer = (GibChunkFooter *) end;
    new_footer->reg_info = footer->reg_info;
    new_footer->seq_no = footer->seq_no + 1;
    new_footer->size = newsize;
    new_footer->next = (GibChunkFooter *) NULL;
    new_footer->prev = footer;

#ifdef _GIBBON_DEBUG
    GibRegionInfo *reg = (GibRegionInfo*) new_footer->reg_info;
    printf("gib_alloc_chunk: allocated %" PRIu64 " bytes for region %" PRIu64 "\n",
           total_size,
           (footer->reg_info)->id);
#endif

    return (GibChunk) {start , end};
}

// Bump to's refcount and insert 'to' into 'from's outset.
void gib_bump_refcount(GibCursor from_footer_ptr, GibCursor to_footer_ptr)
{
    if (to_footer_ptr == from_footer_ptr) {
#ifdef _GIBBON_DEBUG
        printf("gib_bump_refcount: indirection within a region found, refcount not bumped. TODO.\n");
#endif
        return;
    }
    // Grab footers.
    GibChunkFooter *to_footer = (GibChunkFooter *) to_footer_ptr;
    GibChunkFooter *from_footer = (GibChunkFooter *) from_footer_ptr;

    // Grab metadata.
    GibRegionInfo *to_reg = (GibRegionInfo *) to_footer->reg_info;
    GibRegionInfo *from_reg = (GibRegionInfo *) from_footer->reg_info;

    // Bump A's refcount.
    uint16_t current_refcount, new_refcount;
    current_refcount = to_reg->refcount;
    new_refcount = current_refcount + 1;
    to_reg->refcount = new_refcount;

#ifdef _GIBBON_DEBUG
    printf("gib_bump_refcount: %" PRIu64 "-> %" PRIu64 "\n",
           from_reg->id, to_reg->id);
    printf("gib_bump_refcount: old-refcount=%d, old-outset-len=%d:\n",
           current_refcount, from_reg->outset_len);
    assert(current_refcount == from_reg->outset_len+1);
#endif

    // Add 'to' to 'from's outset.
    gib_insert_into_outset(to_footer_ptr, from_reg);

#ifdef _GIBBON_DEBUG
    printf("gib_bump_refcount: Added %p to %" PRIu64 "'s outset, %p.\n",
           to_footer_ptr, from_reg->id, (void *) from_reg);
    printf("gib_bump_refcount: new-refcount=%" PRIu16 ", new-outset-len=%d\n",
           new_refcount, from_reg->outset_len);
    assert(new_refcount == from_reg->outset_len+1);
#endif

    return;
}

void gib_free_region(GibCursor reg_footer_ptr) {
    // Grab footer and the metadata.
    GibChunkFooter *footer = (GibChunkFooter *) reg_footer_ptr;
    GibRegionInfo *reg = (GibRegionInfo *) footer->reg_info;

    //
    GibChunkFooter *first_chunk_footer, *next_chunk_footer;
    GibCursor first_chunk, next_chunk;

    // Decrement current reference count.
    uint16_t current_refcount, new_refcount;
    current_refcount = reg->refcount;
    new_refcount = 0;
    if (current_refcount != 0) {
        new_refcount = current_refcount - 1;
        reg->refcount = new_refcount;
    }

#ifdef _GIBBON_DEBUG
    printf("gib_free_region(%" PRIu64 "): refcounts (1): old-refcount=%d, new-refcount=%d:\n",
           reg->id, current_refcount, new_refcount);
#endif


    // Free this region recount is 0.
    if (new_refcount == 0) {

#ifdef _GIBBON_DEBUG
        printf("gib_free_region(%" PRIu64 "): outset length: %d\n",
               reg->id, reg->outset_len);
#endif

        // Decrement refcounts, free regions with refcount==0 and also free
        // elements of the outset.
        if (reg->outset_len != 0) {
            uint16_t outset_len = reg->outset_len;
            GibCursor *outset = reg->outset;
            GibChunkFooter *elt_footer;
            GibRegionInfo *elt_reg;
            uint16_t elt_current_refcount, elt_new_refcount;
            GibCursor to_be_removed[MAX_OUTSET_LENGTH];
            uint16_t to_be_removed_idx = 0;
            for (uint16_t i = 0; i < outset_len; i++) {
                elt_footer = (GibChunkFooter *) outset[i];
                elt_reg = (GibRegionInfo *) elt_footer->reg_info;
                elt_current_refcount = elt_reg->refcount;
                elt_new_refcount = elt_current_refcount - 1;
                elt_reg->refcount = elt_new_refcount;
#ifdef _GIBBON_DEBUG
                printf("gib_free_region(%" PRIu64 "): old-refcount=%d, new-refcount=%d:\n",
                       elt_reg->id,
                       elt_current_refcount,
                       elt_reg->refcount);
#endif
                if (elt_new_refcount == 0) {
                    // See [Why is it a doubly linked-list?] above
                    first_chunk_footer = gib_trav_to_first_chunk(elt_footer);
                    if (first_chunk_footer != NULL) {
                        gib_free_region((GibCursor) first_chunk_footer);
                    }
                }
                to_be_removed[to_be_removed_idx] = outset[i];
                to_be_removed_idx++;
            }
            // Remove elements from the outset.
            for (uint16_t i = 0; i < to_be_removed_idx; i++) {
                gib_remove_from_outset(to_be_removed[i], reg);
            }
        }


#ifdef _GIBBON_DEBUG
        // Bookkeeping
        int64_t num_freed_chunks = 0, total_bytesize = 0;
#endif

        // Free the chunks in this region.
        first_chunk = reg_footer_ptr - footer->size;
        first_chunk_footer = footer;
        next_chunk = (char*) footer->next;

#ifdef _GIBBON_DEBUG
        num_freed_chunks++;
        total_bytesize = total_bytesize + first_chunk_footer->size;
#endif
        free(first_chunk);

        while (next_chunk != NULL) {
            next_chunk_footer = (GibChunkFooter *) next_chunk;
#ifdef _GIBBON_DEBUG
            num_freed_chunks++;
            total_bytesize = total_bytesize + next_chunk_footer->size;
#endif
            free(next_chunk - next_chunk_footer->size);
            next_chunk = (char*) next_chunk_footer->next;
        }

#ifdef _GIBBON_DEBUG
        printf("gib_free_region(%" PRIu64 "): Freed %" PRId64
               " bytes across %" PRId64 " chunks.\n",
               reg->id, total_bytesize, num_freed_chunks);
#endif

        // Free the metadata.
        free(reg);

    } else {
#ifdef _GIBBON_DEBUG
        printf("gib_free_region(%" PRIu64 "): non-zero refcount: %d.\n",
               reg->id, reg->refcount);
#endif
    }
}

static void gib_insert_into_outset(GibCursor to_ptr, GibRegionInfo *from_reg)
{
    uint16_t outset_len = from_reg->outset_len;
    // Check for duplicates.
    for (uint16_t i = 0; i < outset_len; i++) {
        if (to_ptr == from_reg->outset[i]) {
            return;
        }
    }
    // Otherwise, insert into the outset.
    from_reg->outset[outset_len] = to_ptr;
    from_reg->outset_len = outset_len + 1;
    return;
}

static void gib_remove_from_outset(GibCursor ptr, GibRegionInfo *reg)
{
    uint16_t outset_len = reg->outset_len;
    GibCursor *outset = reg->outset;
    uint16_t i;
    if (outset_len == 0) {
        fprintf(stderr, "gib_remove_from_outset: empty outset\n");
        exit(1);
    }
    // Position of 'ptr' in the outset.
    int elt_idx = -1;
    for (i = 0; i < outset_len; i++) {
        if (ptr == outset[i]) {
            elt_idx = i;
        }
    }
    if (elt_idx == -1) {
        fprintf(stderr, "gib_remove_from_outset: element not found\n");
        exit(1);
    }
    // Move all elements ahead of 'elt_idx' back by one position.
    for (i = elt_idx; i < outset_len; i++) {
        outset[i] = outset[i+1];
    }
    return;
}

static GibChunkFooter *gib_trav_to_first_chunk(GibChunkFooter *footer)
{
    if (footer->seq_no == 1) {
        return footer;
    } else if (footer->prev == NULL) {
        fprintf(stderr, "No previous chunk found at seq_no: %" PRIu16,
                footer->seq_no);
        return (GibChunkFooter *) NULL;
    } else {
        gib_trav_to_first_chunk((GibChunkFooter *) footer->prev);
    }
    return (GibChunkFooter *) NULL;
}

static uint16_t gib_get_ref_count(GibCursor footer_ptr)
{
    GibChunkFooter *footer = (GibChunkFooter *) footer_ptr;
    GibRegionInfo *reg = (GibRegionInfo *) footer->reg_info;
    return reg->refcount;
}


// Functions related to counting the number of allocated regions.

GibChunk *gib_alloc_counted_region(int64_t size)
{
    // Bump the count.
    gib_bump_global_region_count();
    return gib_alloc_region(size);
}

void gib_bump_global_region_count(void)
{
#ifdef _GIBBON_PARALLEL
    __atomic_add_fetch(&gib_global_region_count, 1, __ATOMIC_SEQ_CST);
    return;
#else
    gib_global_region_count++;
#endif
    return;
}

void gib_print_global_region_count(void)
{
    printf("REGION_COUNT: %" PRId64 "\n", gib_global_region_count);
    return;
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Generational GC
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// 4 megabytes for each semi-space.
// #define NURSERY_SIZE (4 * MB)

// 5KB for debugging.
#define NURSERY_SIZE (4 * KB)

// If a region is over this size, alloc to refcounted heap directly.
#define NURSERY_REGION_MAX_SIZE (NURSERY_SIZE / 2)

#define NUM_GENERATIONS 1

// TODO(ckopaprkar): The shadow stack doesn't grow and we don't check for
// overflows at the moment. But this stack probably wouldn't overflow since
// each stack frame is only 16 bytes.
#define SHADOWSTACK_SIZE (sizeof(GibShadowstackFrame) * 4 * 1024 * 1024)

// Same as SHADOWSTACK_SIZE, overflows are not checked.
#define REMEMBERED_SET_SIZE (sizeof(GibRememberedSetElt) * 1024)

typedef struct gib_nursery {
    // Step.
    uint64_t num_collections;

    // Allocation area.
    uint64_t heap_size;
    char *heap_start;
    char *heap_end;
    char *alloc;

    // A place to store starting addresses of chunks.
    char *chunk_starts;
    uint64_t chunk_starts_i;

} GibNursery;

typedef struct gib_generation {
    // Generation number.
    uint8_t no;

    // Destination generation for live objects.
    struct gib_generation *dest;

    // Is this the oldest generation?
    bool oldest;

    // Amount of memory allocated in this generation.
    uint64_t mem_allocated;

    // Allocation area; uninitialized in the oldest gen which uses malloc.
    uint64_t heap_size;
    char *heap_start;
    char *heap_end;
    char *alloc;

    // Remembered set to store old to young pointers.
    GibRememberedSet *rem_set;

    // Zero count tables; pointers to structures on the Rust Heap.
    void *old_zct;
    void *new_zct;

} GibGeneration;

// Array of nurseries, indexed by thread_id.
GibNursery *gib_global_nurseries = (GibNursery *) NULL;

// Array of all generations.
GibGeneration *gib_global_generations = (GibGeneration *) NULL;
// For convenience.
GibGeneration *gib_global_gen0 = (GibGeneration *) NULL;
GibGeneration *gib_global_oldest_gen = (GibGeneration *) NULL;

// Shadow stacks for readable and writeable locations respectively,
// indexed by thread_id.
//
// TODO(ckoparkar): not clear how shadow stacks would be when we have
// parallel mutators.. These arrays are abstract enough for now.
GibShadowstack *gib_global_read_shadowstacks = (GibShadowstack *) NULL;
GibShadowstack *gib_global_write_shadowstacks = (GibShadowstack *) NULL;

// Convenience macros since we don't really need the arrays of nurseries and
// shadowstacks since mutators are still sequential.
// #define DEFAULT_NURSERY gib_global_nurseries
#define DEFAULT_NURSERY (&(gib_global_nurseries[0]))
#define DEFAULT_GENERATION gib_global_oldest_gen
#define DEFAULT_READ_SHADOWSTACK (&(gib_global_read_shadowstacks[0]))
#define DEFAULT_WRITE_SHADOWSTACK (&(gib_global_write_shadowstacks[0]))

// Initialize nurseries, shadow stacks and generations.
static void gib_storage_initialize(void);
static void gib_storage_free(void);
static void gib_nursery_initialize(GibNursery *nursery);
static void gib_nursery_free(GibNursery *nursery);
static void gib_generation_initialize(GibGeneration *gen, uint8_t gen_no);
static void gib_generation_free(GibGeneration *gen, uint8_t gen_no);
static void gib_shadowstack_initialize(GibShadowstack *stack, uint64_t stack_size);
static void gib_shadowstack_free(GibShadowstack *stack);

// Initialize nurseries, shadow stacks and generations.
static void gib_storage_initialize(void)
{
    if (gib_global_nurseries != NULL) {
        return;
    }

    // Initialize nurseries.
    uint64_t n;
    gib_global_nurseries = (GibNursery *) gib_alloc(gib_global_num_threads *
                                                    sizeof(GibNursery));
    for (n = 0; n < gib_global_num_threads; n++) {
        gib_nursery_initialize(&(gib_global_nurseries[n]));
     }

    // Initialize generations.
    int g;
    gib_global_generations = (GibGeneration *) gib_alloc(NUM_GENERATIONS *
                                                         sizeof(GibGeneration));
    for (g = 0; g < NUM_GENERATIONS; g++) {
        gib_generation_initialize(&(gib_global_generations[g]), g);
    }
    gib_global_gen0 = &(gib_global_generations[0]);
    gib_global_oldest_gen = &(gib_global_generations[NUM_GENERATIONS-1]);
    // Set up destination pointers in each generation.
    for (g = 0; g < NUM_GENERATIONS-1; g++) {
        gib_global_generations[g].dest = &(gib_global_generations[g+1]);
    }
    gib_global_oldest_gen->dest = gib_global_oldest_gen;

    // Initialize shadow stacks.
    uint64_t ss;
    gib_global_read_shadowstacks =
            (GibShadowstack *) gib_alloc(gib_global_num_threads *
                                         sizeof(GibShadowstack));
    gib_global_write_shadowstacks =
            (GibShadowstack *) gib_alloc(gib_global_num_threads *
                                         sizeof(GibShadowstack));
    for (ss = 0; ss < gib_global_num_threads; ss++) {
        gib_shadowstack_initialize(&(gib_global_read_shadowstacks[ss]),
                                   SHADOWSTACK_SIZE);
        gib_shadowstack_initialize(&(gib_global_write_shadowstacks[ss]),
                                   SHADOWSTACK_SIZE);
     }

    return;
}

static void gib_storage_free(void)
{
    if (gib_global_nurseries == NULL) {
        return;
    }

    // Free nurseries.
    uint64_t n;
    for (n = 0; n < gib_global_num_threads; n++) {
        gib_nursery_free(&(gib_global_nurseries[n]));
     }
    free(gib_global_nurseries);

    // Free generations.
    int g;
    for (g = 0; g < NUM_GENERATIONS; g++) {
        gib_generation_free(&(gib_global_generations[g]), g);
    }
    free(gib_global_generations);

    // Free shadow-stacks.
    uint64_t ss;
    for (ss = 0; ss < gib_global_num_threads; ss++) {
        gib_shadowstack_free(&(gib_global_read_shadowstacks[ss]));
        gib_shadowstack_free(&(gib_global_write_shadowstacks[ss]));
    }
    free(gib_global_read_shadowstacks);
    free(gib_global_write_shadowstacks);
}

// Initialize a nursery.
static void gib_nursery_initialize(GibNursery *nursery)
{
    nursery->num_collections = 0;
    nursery->heap_size = NURSERY_SIZE;
    nursery->heap_start = (char *) gib_alloc(NURSERY_SIZE);
    if (nursery->heap_start == NULL) {
        fprintf(stderr, "gib_nursery_initialize: gib_alloc failed: %ld",
                NURSERY_SIZE);
        exit(1);
    }
    nursery->heap_end = nursery->heap_start + NURSERY_SIZE;
    nursery->alloc = nursery->heap_end;
    nursery->chunk_starts = (char *) gib_alloc(NURSERY_SIZE);
    if (nursery->chunk_starts == NULL) {
        fprintf(stderr, "gib_nursery_initialize: gib_alloc failed: %ld",
                NURSERY_SIZE);
        exit(1);
    }
    nursery->chunk_starts_i = 0;

    return;
}

// Free data associated with a nursery.
static void gib_nursery_free(GibNursery *nursery)
{
    free(nursery->heap_start);
    free(nursery->chunk_starts);
    return;
}

// Initialize a generation.
static void gib_generation_initialize(GibGeneration *gen, uint8_t gen_no)
{
    gen->no = gen_no;
    gen->dest = (GibGeneration *) NULL;
    gen->mem_allocated = 0;
    gen->old_zct = (void *) NULL;
    gen->new_zct = (void *) NULL;
    // Initialize the remembered set.
    gen->rem_set = (GibRememberedSet *) gib_alloc(sizeof(GibRememberedSet));
    if (gen->rem_set == NULL) {
        fprintf(stderr, "gib_generation_initialize: gib_alloc failed: %ld",
                sizeof(GibRememberedSet));
        exit(1);
    }
    gib_shadowstack_initialize(gen->rem_set, REMEMBERED_SET_SIZE);
    // Initialize the heap if this is not the oldest generation.
    if (gen_no == (NUM_GENERATIONS - 1)) {
        gen->oldest = true;
        gen->heap_size = 0;
        gen->heap_start = (char *) NULL;
        gen->heap_end = (char *) NULL;
        gen->alloc = (char *) NULL;
    } else {
        gen->oldest = false;
        gen->heap_size = ((gen_no+1) * 256 * MB);
        gen->heap_start = (char *) gib_alloc(gen->heap_size);
        if (gen->heap_start == NULL) {
            fprintf(stderr, "gib_generation_initialize: gib_alloc failed: %ld",
                    gen->heap_size);
        }
        gen->heap_end = gen->heap_start + gen->heap_size;
        gen->alloc = gen->heap_start;
    }

    return;
}

static void gib_generation_free(GibGeneration *gen, uint8_t gen_no)
{
    gib_shadowstack_free(gen->rem_set);
    free(gen->rem_set);
    // Initialize the heap if this is not the oldest generation.
    if (gen_no != (NUM_GENERATIONS - 1)) {
        free(gen->heap_start);
    }
    return;
}

// Initialize a shadow stack.
static void gib_shadowstack_initialize(GibShadowstack* stack, uint64_t stack_size)
{
    stack->start = (char *) gib_alloc(stack_size);
    if (stack->start == NULL) {
        fprintf(stderr, "gib_shadowstack_initialize: gib_alloc failed: %ld",
                stack_size);
        exit(1);
    }
    stack->end = stack->start + stack_size;
    stack->alloc = stack->start;
    return;
}

static void gib_shadowstack_free(GibShadowstack* stack)
{
    free(stack->start);
    return;
}

// Nursery API.
// TODO(ckoparkar):
// If we allocate the nursery at a high address AND ensure that all of the
// subsequent mallocs return a block at addresses lower than this, we can
// implement addr_in_nursery with one address check instead than two. -- RRN
bool gib_addr_in_nursery(char *ptr)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    return ((ptr >= nursery->heap_start) && (ptr <= nursery->heap_end));
}

// Shadowstack API.
void gib_shadowstack_push(
    GibShadowstack *stack,
    char *ptr,
    char *endptr,
    uint32_t datatype
)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_end = stack->end;
    char **stack_alloc_ptr_addr = &(stack->alloc);
    size_t size = sizeof(GibShadowstackFrame);
    if ((stack_alloc_ptr + size) > stack_end) {
        fprintf(stderr, "gib_shadowstack_push: out of memory");
        exit(1);
    }
    GibShadowstackFrame *frame = (GibShadowstackFrame *) stack_alloc_ptr;
    frame->ptr = ptr;
    frame->endptr = endptr;
    frame->datatype = datatype;
    (*stack_alloc_ptr_addr) += size;
    return;
}

GibShadowstackFrame *gib_shadowstack_pop(GibShadowstack *stack)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_start = stack->start;
    char **stack_alloc_ptr_addr = &(stack->alloc);
    size_t size = sizeof(GibShadowstackFrame);
    if ((stack_alloc_ptr - size) < stack_start) {
        fprintf(stderr, "gib_shadowstack_pop: stack empty");
        exit(1);
    }
    (*stack_alloc_ptr_addr) -= size;
    GibShadowstackFrame *frame = (GibShadowstackFrame *) (*stack_alloc_ptr_addr);
    return frame;
}

int32_t gib_shadowstack_length(GibShadowstack *stack)
{
    char *stack_alloc_ptr = stack->alloc;
    char *stack_start = stack->start;
    return ( (stack_alloc_ptr - stack_start) / sizeof(GibShadowstackFrame) );
}

void gib_shadowstack_print_all(GibShadowstack *stack)
{
    char *run_ptr = stack->start;
    char *end_ptr = stack->alloc;
    GibShadowstackFrame *frame;
    while (run_ptr < end_ptr) {
        frame = (GibShadowstackFrame *) run_ptr;
        printf("ptr=%p, endptr=%p, datatype=%d\n",
               frame->ptr, frame->endptr, frame->datatype);
        run_ptr += sizeof(GibShadowstackFrame);
    }
    return;
}

void gib_remset_reset(GibRememberedSet *set)
{
    set->alloc = set->start;
}

static GibChunk *gib_alloc_region_on_heap(uint64_t size);
static GibChunk *gib_alloc_region_in_nursery(uint64_t size);

GibChunk *gib_alloc_region2(uint64_t size)
{
    if (size > NURSERY_REGION_MAX_SIZE) {
        return gib_alloc_region_on_heap(size);
    } else {
        return gib_alloc_region_in_nursery(size);
    }
}

static GibChunk *gib_alloc_region_on_heap(uint64_t size)
{
    char *heap_start = gib_alloc(size);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_alloc_region_on_heap: gib_alloc failed: %" PRId64,
                 size);
        exit(1);
    }
    char *heap_end = heap_start + size;
    GibChunk *region = gib_alloc(sizeof(GibChunk));
    region->start = heap_start;
    region->end = heap_end;
    return region;
}

static GibChunk *gib_alloc_region_in_nursery_fast(uint64_t size, bool collected);
static GibChunk *gib_alloc_region_in_nursery_slow(uint64_t size, bool collected);

GibChunk *gib_alloc_region_in_nursery(uint64_t size)
{
    return gib_alloc_region_in_nursery_fast(size, false);
}

static GibChunk *gib_alloc_region_in_nursery_fast(uint64_t size, bool collected)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    char *old = nursery->alloc;
    char *bump = old - size;
    if (bump >= nursery->heap_start) {
        nursery->alloc = bump;
        char *chunk_starts_alloc = nursery->chunk_starts +
            (nursery->chunk_starts_i * sizeof(char*));
        *(char**) chunk_starts_alloc = bump;
        nursery->chunk_starts_i = nursery->chunk_starts_i + 1;
        GibChunk *region = gib_alloc(sizeof(GibChunk));
        region->start = bump;
        region->end = old;
        return region;
    }
    return gib_alloc_region_in_nursery_slow(size, collected);
}

static GibChunk *gib_alloc_region_in_nursery_slow(uint64_t size, bool collected)
{
    if (collected) {
        fprintf(stderr, "Couldn't free space after garbage collection.\n");
        exit(1);
    }
    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibGeneration *generations = gib_global_generations;
    int err = gib_garbage_collect(rstack, wstack, nursery, generations, false);
    if (err < 0) {
        fprintf(stderr, "Couldn't perform minor collection, errorno=%d.", err);
        exit(1);
    }
    return gib_alloc_region_in_nursery_fast(size, true);
}


void gib_free_region2(GibChunk *region)
{
    free(region);
    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Write barrier
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * The following is how different types of indirections are handled:
 *
 * (1) oldgen -> nursery
 *
 *     Add to remembered set.
 *
 * (2) oldgen -> oldgen
 *
 *     Same as old Gibbon, bump refcount and insert into outset.
 *
 */

// Write barrier. INLINE!!!
void gib_indirection_barrier(
    // Address where the indirection tag is written.
    GibCursor from,
    GibCursor from_footer_ptr,
    // Address of the pointed-to data.
    GibCursor to,
    GibCursor to_footer_ptr,
    // Data type written at from/to.
    uint32_t datatype
)
{
    UNUSED(to_footer_ptr);

    bool from_old = !gib_addr_in_nursery(from);
    bool to_young = gib_addr_in_nursery(to);
    bool to_old = !to_young;
    if (from_old) {
        if (to_young) {
            // (3) oldgen -> nursery
#ifdef _GIBBON_DEBUG
            printf("gib_indirection_barrier: old to young pointer\n");
#endif
            GibGeneration *gen = DEFAULT_GENERATION;
            // Store the address of the indirection pointer, *NOT* the address of
            // the indirection tag, in the remembered set.
            GibCursor indr_addr = from + sizeof(GibPackedTag);
            gib_remset_push(gen->rem_set, indr_addr, from_footer_ptr, datatype);
            return;
        } else if (to_old) {
            // (4) oldgen -> oldgen
#ifdef _GIBBON_DEBUG
            printf("gib_indirection_barrier: old to old pointer\n");
#endif
            gib_bump_refcount(from_footer_ptr, to_footer_ptr);
            return;
        }
    }
    return;
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Helpers
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


void gib_show_usage(char** argv)
{
    printf("\n");
    printf("This binary was generated by the Gibbon compiler.\n");
    printf("\n");
    printf("Usage: %s [OPTS] [size] [iters]\n", argv[0]);

    printf("\n");
    printf("Options:\n");
    printf(" --buffer-size <bytes>      Set the buffer size (default %" PRId64 ").\n", gib_global_biginf_init_chunk_size);
    printf(" --bench-input <path>       Set the input file read for benchmarking. Applies only\n");
    printf("                            IF the program was *compiled* with --bench-fun. \n");
    return;
}

double gib_avg(const double* arr, int n)
{
    double sum = 0.0;
    for(int i=0; i<n; i++) sum += arr[i];
    return sum / (double)n;
}

double gib_difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
            + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

int gib_compare_doubles(const void *a, const void *b)
{
    const double *da = (const double *) a;
    const double *db = (const double *) b;
    return (*da > *db) - (*da < *db);
}

// Exponentiation
GibInt gib_expll(GibInt base, GibInt pow)
{
    if (base == 2) {
        return (1 << pow);
    } else {
        GibInt i, result = 1;
        for (i = 0; i < pow; i++)
            result *= base;
        return result;
    }
}

// https://www.cprogramming.com/snippets/source-code/find-the-number-of-cpu-cores-for-windows-mac-or-linux
GibInt gib_get_num_processors(void)
{
#ifdef _WIN64
    SYSTEM_INFO sysinfo;
    GetSystemInfo(&sysinfo);
    return sysinfo.dwNumberOfProcessors;
#else
    return sysconf(_SC_NPROCESSORS_ONLN);
#endif
}

// Requires -std=gnu11
int dbgprintf(const char *format, ...)
{
    int code = 0;
    va_list args;
    va_start(args, format);
#ifdef _GIBBON_DEBUG
    code = vprintf(format, args);
#endif
    va_end(args);
    return code;
}


/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Main functions
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

int main(int argc, char **argv)
{
    // parameters to parse:
    //
    //   num iterations: How many times to repeat a benchmark.
    //   tree size: An integer passes to `build_tree()`.

    struct rlimit lim;
    int code;
    if ( (code = getrlimit(RLIMIT_STACK, &lim)) ) {
        fprintf(stderr, " [gibbon rts] failed to getrlimit, code %d\n", code);
        exit(1);
    }

    // lim.rlim_cur = 1024LU * 1024LU * 1024LU; // 1GB stack.
    lim.rlim_cur = 512LU * 1024LU * 1024LU; // 500MB stack.
    // lim.rlim_max = lim.rlim_cur; // Normal users may only be able to decrease this.

    // WARNING: Haven't yet figured out why this doesn't work on MacOS...
#ifndef __APPLE__
    code = setrlimit(RLIMIT_STACK, &lim);
    while (code) {
        fprintf(stderr, " [gibbon rts] Failed to set stack size to %lu, code %d\n",
                (uint64_t)lim.rlim_cur, code);
        lim.rlim_cur /= 2;
        // lim.rlim_max /= 2;
        if(lim.rlim_cur < 100 * 1024) {
            fprintf(stderr, " [gibbon rts] Failed setrlimit stack size to something reasonable; giving up.\n");
            break; // abort();
        }
        int code = setrlimit(RLIMIT_STACK, &lim);
    }
#endif

    int got_numargs = 0; // How many numeric arguments have we got.

    int i;
    for (i = 1; i < argc; ++i)
    {
        if (strcmp(argv[i], "-h") == 0 || strcmp(argv[i], "--help") == 0) {
            gib_show_usage(argv);
            exit(0);
        }
        else if (strcmp(argv[i], "--biginf-buffer-size") == 0 && i < argc - 1)
        {
            gib_global_biginf_init_chunk_size = atoll(argv[i + 1]);
            i++;
        }
        else if (strcmp(argv[i], "--inf-buffer-size") == 0 && i < argc - 1)
        {
            gib_global_inf_init_chunk_size = atoll(argv[i + 1]);
            i++;
        }
        else if ((strcmp(argv[i], "--bench-input") == 0)) {
            if (i+1 >= argc) {
                fprintf(stderr, "Not enough arguments after --bench-input, expected <file>.\n");
                gib_show_usage(argv);
                exit(1);
            }
            gib_global_benchfile_param = argv[i+1];
            i++;
        }
        else if ((strcmp(argv[i], "--array-input") == 0)) {
            if (i+1 >= argc) {
                fprintf(stderr, "Not enough arguments after --array-input, expected <file>.\n");
                gib_show_usage(argv);
                exit(1);
            }
            gib_global_arrayfile_param = argv[i+1];
            i++;
        }
        else if (strcmp(argv[i], "--array-input-length") == 0 && i < argc - 1) {
            gib_global_arrayfile_length_param = atoll(argv[i+1]);
            i++;
        }
        else if (strcmp(argv[i], "--bench-prog") == 0 && i < argc - 1) {
            int len = strlen(argv[i+1]);
            gib_global_bench_prog_param = (char*) gib_alloc((len+1)*sizeof(char));
            strncpy(gib_global_bench_prog_param,argv[i+1],len);
            i++;
        }
        // If present, we expect the two arguments to be <size> <iters>
        else if (got_numargs >= 2) {
            fprintf(stderr, "Extra arguments left over: ");
            for(; i < argc; i++) fprintf(stderr, "%s ", argv[i]);
            gib_show_usage(argv);
            exit(1);
        } else {
            if (got_numargs == 0) {
                gib_global_size_param  = atoll(argv[i]);
                got_numargs ++;
            } else {
                gib_global_iters_param = atoll(argv[i]);
            }
        }
    }

    // Initialize gib_global_bench_prog_param to an empty string in case
    // the runtime argument --bench-prog isn't passed.
    if (gib_global_bench_prog_param == NULL) {
        gib_global_bench_prog_param = (char*) gib_alloc(1*sizeof(char));
        *gib_global_bench_prog_param = '\n';
    }

    // Initialize the nursery and shadow stack.
    gib_storage_initialize();

    // Run the program.
    gib_main_expr();

    // Free all objects initialized by the Rust RTS.
    free(gib_global_bench_prog_param);
    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibGeneration *generations = gib_global_generations;
    gib_gc_cleanup(rstack, wstack, nursery, generations);

    // Next, free all objects initialized by the C RTS.
    gib_storage_free();
    gib_free_symtable();

    return 0;
}
