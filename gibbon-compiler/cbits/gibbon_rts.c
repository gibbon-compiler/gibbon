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

#define MAX_CHUNK_SIZE (1 * GB)

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
    }
    free(elt);
    free(tmp);
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
    vec->vec_lower = 0;
    vec->vec_upper = num;
    vec->vec_elt_size = elt_size;
    vec->vec_data = data;
    return vec;
}

GibInt gib_vector_length(GibVector *vec)
{
    return (vec->vec_upper - vec->vec_lower);
}

GibBool gib_vector_is_empty(GibVector *vec)
{
    return (gib_vector_length(vec) == 0);
}

GibVector *gib_vector_slice(GibInt i, GibInt n, GibVector *vec)
{
    GibInt lower = vec->vec_lower + i;
    GibInt upper = vec->vec_lower + i + n;
    if ((lower > vec->vec_upper)) {
        fprintf(stderr, "gib_vector_slice: lower out of bounds, %" PRId64
                " > %" PRId64, lower, vec->vec_upper);
        exit(1);
    }
    if ((upper > vec->vec_upper)) {
        fprintf(stderr, "gib_vector_slice: upper out of bounds, %" PRId64
                " > %" PRId64, upper, vec->vec_upper);
        exit(1);
    }
    GibVector *vec2 = (GibVector *) gib_alloc(sizeof(GibVector));
    if (vec == NULL) {
        fprintf(stderr, "gib_vector_slice: gib_alloc failed: %ld", sizeof(GibVector));
        exit(1);
    }
    vec2->vec_lower = lower;
    vec2->vec_upper = upper;
    vec2->vec_elt_size = vec->vec_elt_size;
    vec2->vec_data = vec->vec_data;
    return vec2;
}

// The callers must cast the return value.
void *gib_vector_nth(GibVector *vec, GibInt i)
{
#ifdef _GIBBON_BOUNDSCHECK
    if (i < vec->lower || i > vec->upper) {
        fprintf(stdderr, "gib_vector_nth index out of bounds: %lld (%lld,%lld)\n",
                i, vec->vec_lower, vec->vec_upper);
        exit(1);
    }
#endif
    return ((char*)vec->vec_data + (vec->vec_elt_size * (vec->vec_lower + i)));
}

GibVector *gib_vector_inplace_update(GibVector *vec, GibInt i, void* elt)
{
    void* dst = gib_vector_nth(vec, i);
    memcpy(dst, elt, vec->vec_elt_size);
    return vec;
}

GibVector *gib_vector_copy(GibVector *vec)
{
    GibInt len = gib_vector_length(vec);
    void *start = gib_vector_nth(vec, 0);
    GibVector *vec2 = gib_vector_alloc(len, vec->vec_elt_size);
    memcpy(vec2->vec_data, start, len * vec->vec_elt_size);
    return vec2;
}

GibVector *gib_vector_inplace_sort(GibVector *vec, int (*compar)(const void *, const void*))
{
    void *start = gib_vector_nth(vec, 0);
    qsort(start, gib_vector_length(vec), vec->vec_elt_size, compar);
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
        result_elt_size = elt->vec_elt_size;
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
    free(vec->vec_data);
    free(vec);
    return;
}

GibVector *gib_vector_merge(GibVector *vec1, GibVector *vec2)
{
    if (vec1->vec_upper != vec2->vec_lower) {
        fprintf(stderr,"gib_vector_merge: non-contiguous slices, (%" PRId64
                ",%" PRId64 "), (%" PRId64 ",%" PRId64 ")",
               vec1->vec_lower, vec1->vec_upper, vec2->vec_lower, vec2->vec_upper);
        exit(1);
    }
    GibVector *merged = (GibVector *) gib_alloc(sizeof(GibVector));
    if (merged == NULL) {
        fprintf(stderr, "gib_vector_merge: gib_alloc failed: %ld", sizeof(GibVector));
        exit(1);
    }
    merged->vec_lower = vec1->vec_lower;
    merged->vec_upper = vec2->vec_upper;
    merged->vec_elt_size = vec1->vec_elt_size;
    merged->vec_data = vec1->vec_data;
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
    ls->ll_data_size = data_size;
    ls->ll_data = (void *) NULL;
    ls->ll_next = (GibList *) NULL;
    return ls;
}

GibBool gib_list_is_empty(GibList *ls)
{
    return ls->ll_next == NULL;
}

GibList *gib_list_cons(void *elt, GibList *ls)
{
    // void* data = gib_alloc(ls->data_size);
    void* data = gib_list_bumpalloc(ls->ll_data_size);
    if (data == NULL) {
        fprintf(stderr, "gib_list_cons: gib_alloc failed: %ld", ls->ll_data_size);
        exit(1);
    }
    memcpy(data, elt, ls->ll_data_size);
    // GibList *res = gib_alloc(sizeof(GibList));
    GibList *res = gib_list_bumpalloc(sizeof(GibList));
    res->ll_data_size = ls->ll_data_size;
    res->ll_data = data;
    res->ll_next = (GibList*) ls;
    return res;
}

void *gib_list_head(GibList *ls)
{
    return ls->ll_data;
}

GibList* gib_list_tail(GibList *ls)
{
    return ls->ll_next;
}

void gib_list_free(GibList *ls)
{
    free(ls->ll_data);
    free(ls);
    return;
}

GibList *gib_list_copy(GibList *ls)
{
    GibList *ls2 = gib_list_alloc(ls->ll_data_size);
    if (ls->ll_data != NULL) {
        void* data = gib_list_bumpalloc(ls->ll_data_size);
        memcpy(data, ls->ll_data, ls->ll_data_size);
        ls2->ll_data = data;
    }
    ls2->ll_next = ls->ll_next;
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
  data | cf_reg_info | cf_seq_no | cf_size | cf_next | cf_prev
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

  The metadata after the serialized data serves various purposes:

  - cf_reg_info: A pointer to a GibRegionInfo struct that contains
  various metadata. Of particular interest to us are the fields:

  = reg_id: A unique identifier for a region.

  = refcount and outset: Whenever an inter-region indirection is created, we
    record that information using these two fields. Suppose we have an
    indirection from region A that points to some chunk in region B. Then A's
    outset will store a pointer to that chunk's footer, and B's refcount will
    be bumped by 1. Note that all there's only 1 refcount cell, and 1 outset
    per logical region, and chunks only store a pointer to them.

  - cf_seq_no: The index of this particular chunk in the list.

  - cf_size: Used during bounds checking to calculate the size of the next
    region in the linked list.

  - cf_next / cf_prev: Point to the next and previous chunk respectively.


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
    GibSym reg_id;
    uint16_t reg_refcount;
    uint16_t reg_outset_len;
    GibCursor reg_outset[MAX_OUTSET_LENGTH];
} GibRegionInfo;

typedef struct gib_chunk_footer {
    GibRegionInfo *cf_reg_info;

    uint16_t cf_seq_no;
    uint64_t cf_size;
    struct gib_chunk_footer *cf_next;
    struct gib_chunk_footer *cf_prev;
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
    reg_info->reg_id = gib_gensym();
    reg_info->reg_refcount = 1;
    reg_info->reg_outset_len = 0;

#ifdef _GIBBON_DEBUG
    printf("Allocated a region(%" PRIu64 "): %" PRIu64 " bytes.\n",
           reg_info->reg_id, size);
#endif

    // Write the footer.
    GibChunkFooter *footer = (GibChunkFooter *) heap_end;
    footer->cf_reg_info = reg_info;
    footer->cf_seq_no = 1;
    footer->cf_size = size;
    footer->cf_next = (GibChunkFooter *) NULL;
    footer->cf_prev = (GibChunkFooter *) NULL;

    GibChunk *region = (GibChunk *) gib_alloc(sizeof(GibChunk));
    region->c_start = heap_start;
    region->c_end = heap_end;
    return region;
}

GibChunk gib_alloc_chunk(GibCursor footer_ptr)
{
    // Get size from current footer.
    GibChunkFooter *footer = (GibChunkFooter *) footer_ptr;
    uint64_t newsize = footer->cf_size * 2;
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
    footer->cf_next = (GibChunkFooter *) end;

    // Write the footer.
    GibChunkFooter *new_footer = (GibChunkFooter *) end;
    new_footer->cf_reg_info = footer->cf_reg_info;
    new_footer->cf_seq_no = footer->cf_seq_no + 1;
    new_footer->cf_size = newsize;
    new_footer->cf_next = (GibChunkFooter *) NULL;
    new_footer->cf_prev = footer;

#ifdef _GIBBON_DEBUG
    GibRegionInfo *reg = (GibRegionInfo*) new_footer->cf_reg_info;
    printf("gib_alloc_chunk: allocated %" PRIu64 " bytes for region %" PRIu64 "\n",
           total_size,
           (footer->cf_reg_info)->reg_id);
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
    GibRegionInfo *to_reg = (GibRegionInfo *) to_footer->cf_reg_info;
    GibRegionInfo *from_reg = (GibRegionInfo *) from_footer->cf_reg_info;

    // Bump A's refcount.
    uint16_t current_refcount, new_refcount;
    current_refcount = to_reg->reg_refcount;
    new_refcount = current_refcount + 1;
    to_reg->reg_refcount = new_refcount;

#ifdef _GIBBON_DEBUG
    printf("gib_bump_refcount: %" PRIu64 "-> %" PRIu64 "\n",
           from_reg->reg_id, to_reg->reg_id);
    printf("gib_bump_refcount: old-refcount=%d, old-outset-len=%d:\n",
           current_refcount, from_reg->reg_outset_len);
    assert(current_refcount == from_reg->reg_outset_len+1);
#endif

    // Add 'to' to 'from's outset.
    gib_insert_into_outset(to_footer_ptr, from_reg);

#ifdef _GIBBON_DEBUG
    printf("gib_bump_refcount: Added %p to %" PRIu64 "'s outset, %p.\n",
           to_footer_ptr, from_reg->reg_id, (void *) from_reg);
    printf("gib_bump_refcount: new-refcount=%" PRIu16 ", new-outset-len=%d\n",
           new_refcount, from_reg->reg_outset_len);
    assert(new_refcount == from_reg->reg_outset_len+1);
#endif

    return;
}

void gib_free_region(GibCursor reg_footer_ptr) {
    // Grab footer and the metadata.
    GibChunkFooter *footer = (GibChunkFooter *) reg_footer_ptr;
    GibRegionInfo *reg = (GibRegionInfo *) footer->cf_reg_info;

    //
    GibChunkFooter *first_chunk_footer, *next_chunk_footer;
    GibCursor first_chunk, next_chunk;

    // Decrement current reference count.
    uint16_t current_refcount, new_refcount;
    current_refcount = reg->reg_refcount;
    new_refcount = 0;
    if (current_refcount != 0) {
        new_refcount = current_refcount - 1;
        reg->reg_refcount = new_refcount;
    }

#ifdef _GIBBON_DEBUG
    printf("gib_free_region(%" PRIu64 "): refcounts (1): old-refcount=%d, new-refcount=%d:\n",
           reg->reg_id, current_refcount, new_refcount);
#endif


    // Free this region recount is 0.
    if (new_refcount == 0) {

#ifdef _GIBBON_DEBUG
        printf("gib_free_region(%" PRIu64 "): outset length: %d\n",
               reg->reg_id, reg->reg_outset_len);
#endif

        // Decrement refcounts, free regions with refcount==0 and also free
        // elements of the outset.
        if (reg->reg_outset_len != 0) {
            uint16_t outset_len = reg->reg_outset_len;
            GibCursor *outset = reg->reg_outset;
            GibChunkFooter *elt_footer;
            GibRegionInfo *elt_reg;
            uint16_t elt_current_refcount, elt_new_refcount;
            GibCursor to_be_removed[MAX_OUTSET_LENGTH];
            uint16_t to_be_removed_idx = 0;
            for (uint16_t i = 0; i < outset_len; i++) {
                elt_footer = (GibChunkFooter *) outset[i];
                elt_reg = (GibRegionInfo *) elt_footer->cf_reg_info;
                elt_current_refcount = elt_reg->reg_refcount;
                elt_new_refcount = elt_current_refcount - 1;
                elt_reg->reg_refcount = elt_new_refcount;
#ifdef _GIBBON_DEBUG
                printf("gib_free_region(%" PRIu64 "): old-refcount=%d, new-refcount=%d:\n",
                       elt_reg->reg_id,
                       elt_current_refcount,
                       elt_reg->reg_refcount);
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
        first_chunk = reg_footer_ptr - footer->cf_size;
        first_chunk_footer = footer;
        next_chunk = (char*) footer->cf_next;

#ifdef _GIBBON_DEBUG
        num_freed_chunks++;
        total_bytesize = total_bytesize + first_chunk_footer->cf_size;
#endif
        free(first_chunk);

        while (next_chunk != NULL) {
            next_chunk_footer = (GibChunkFooter *) next_chunk;
#ifdef _GIBBON_DEBUG
            num_freed_chunks++;
            total_bytesize = total_bytesize + next_chunk_footer->cf_size;
#endif
            free(next_chunk - next_chunk_footer->cf_size);
            next_chunk = (char*) next_chunk_footer->cf_next;
        }

#ifdef _GIBBON_DEBUG
        printf("gib_free_region(%" PRIu64 "): Freed %" PRId64
               " bytes across %" PRId64 " chunks.\n",
               reg->reg_id, total_bytesize, num_freed_chunks);
#endif

        // Free the metadata.
        free(reg);

    } else {
#ifdef _GIBBON_DEBUG
        printf("gib_free_region(%" PRIu64 "): non-zero refcount: %d.\n",
               reg->reg_id, reg->reg_refcount);
#endif
    }
}

static void gib_insert_into_outset(GibCursor to_ptr, GibRegionInfo *from_reg)
{
    uint16_t outset_len = from_reg->reg_outset_len;
    // Check for duplicates.
    for (uint16_t i = 0; i < outset_len; i++) {
        if (to_ptr == from_reg->reg_outset[i]) {
            return;
        }
    }
    // Otherwise, insert into the outset.
    from_reg->reg_outset[outset_len] = to_ptr;
    from_reg->reg_outset_len = outset_len + 1;
    return;
}

static void gib_remove_from_outset(GibCursor ptr, GibRegionInfo *reg)
{
    uint16_t outset_len = reg->reg_outset_len;
    GibCursor *outset = reg->reg_outset;
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
    if (footer->cf_seq_no == 1) {
        return footer;
    } else if (footer->cf_prev == NULL) {
        fprintf(stderr, "No previous chunk found at cf_seq_no: %" PRIu16,
                footer->cf_seq_no);
        return (GibChunkFooter *) NULL;
    } else {
        gib_trav_to_first_chunk((GibChunkFooter *) footer->cf_prev);
    }
    return (GibChunkFooter *) NULL;
}

static uint16_t gib_get_ref_count(GibCursor footer_ptr)
{
    GibChunkFooter *footer = (GibChunkFooter *) footer_ptr;
    GibRegionInfo *reg = (GibRegionInfo *) footer->cf_reg_info;
    return reg->reg_refcount;
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

// 4KB for debugging.
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
    uint64_t n_num_collections;

    // Allocation area.
    uint64_t n_heap_size;
    char *n_heap_start;
    char *n_heap_end;
    char *n_alloc;

    // Is the allocation area initialized?
    bool n_initialized;

    // Remembered set to store young to old pointers;
    // this is a pointer to a structure on the Rust Heap.
    void *n_rem_set;

} GibNursery;

typedef struct gib_generation {
    // Generation number.
    uint8_t g_no;

    // Destination generation for live objects.
    struct gib_generation *g_dest;

    // Is this the oldest generation?
    bool g_oldest;

    // Amount of memory allocated in this generation.
    uint64_t g_mem_allocated;

    // Allocation area; uninitialized in the oldest gen which uses malloc.
    uint64_t g_heap_size;
    char *g_heap_start;
    char *g_heap_end;
    char *g_alloc;

    // Remembered set to store old to young pointers.
    GibRememberedSet *g_rem_set;

    // Zero count table;
    // this is a pointer to a structure on the Rust Heap.
    void *g_zct;

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
static void gib_nursery_initialize(GibNursery *nursery);
static void gib_generation_initialize(GibGeneration *gen, uint8_t gen_no);
static void gib_shadowstack_initialize(GibShadowstack *stack, uint64_t stack_size);

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
        gib_global_generations[g].g_dest = &(gib_global_generations[g+1]);
    }
    gib_global_oldest_gen->g_dest = gib_global_oldest_gen;

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

// Initialize a nursery.
static void gib_nursery_initialize(GibNursery *nursery)
{
    nursery->n_num_collections = 0;
    nursery->n_heap_size = NURSERY_SIZE;
    nursery->n_heap_start = (char *) gib_alloc(NURSERY_SIZE);
    if (nursery->n_heap_start == NULL) {
        fprintf(stderr, "gib_nursery_initialize: gib_alloc failed: %ld",
                NURSERY_SIZE);
        exit(1);
    }
    nursery->n_heap_end = nursery->n_heap_start + NURSERY_SIZE;
    nursery->n_alloc = nursery->n_heap_start;
    nursery->n_initialized = true;
    nursery->n_rem_set = (void *) NULL;

    return;
}

// Initialize a generation.
static void gib_generation_initialize(GibGeneration *gen, uint8_t gen_no)
{
    gen->g_no = gen_no;
    gen->g_dest = (GibGeneration *) NULL;
    gen->g_mem_allocated = 0;
    gen->g_zct = (void *) NULL;
    // Initialize the remembered set.
    gen->g_rem_set = (GibRememberedSet *) gib_alloc(sizeof(GibRememberedSet));
    if (gen->g_rem_set == NULL) {
        fprintf(stderr, "gib_generation_initialize: gib_alloc failed: %ld",
                sizeof(GibRememberedSet));
        exit(1);
    }
    gib_shadowstack_initialize(gen->g_rem_set, REMEMBERED_SET_SIZE);
    // Initialize the heap if this is not the oldest generation.
    if (gen_no == (NUM_GENERATIONS - 1)) {
        gen->g_oldest = true;
        gen->g_heap_size = 0;
        gen->g_heap_start = (char *) NULL;
        gen->g_heap_end = (char *) NULL;
        gen->g_alloc = (char *) NULL;
    } else {
        gen->g_oldest = false;
        gen->g_heap_size = ((gen_no+1) * 256 * MB);
        gen->g_heap_start = (char *) gib_alloc(gen->g_heap_size);
        if (gen->g_heap_start == NULL) {
            fprintf(stderr, "gib_generation_initialize: gib_alloc failed: %ld",
                    gen->g_heap_size);
        }
        gen->g_heap_end = gen->g_heap_start + gen->g_heap_size;
        gen->g_alloc = gen->g_heap_start;
    }

    return;
}

// Initialize a shadow stack.
static void gib_shadowstack_initialize(GibShadowstack* stack, uint64_t stack_size)
{
    stack->ss_start = (char *) gib_alloc(stack_size);
    if (stack->ss_start == NULL) {
        fprintf(stderr, "gib_shadowstack_initialize: gib_alloc failed: %ld",
                stack_size);
        exit(1);
    }
    stack->ss_end = stack->ss_start + stack_size;
    stack->ss_alloc = stack->ss_start;
    stack->ss_initialized = true;
    return;
}

// Nursery API.
bool gib_addr_in_nursery(char *ptr)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    return ((ptr >= nursery->n_heap_start) && (ptr <= nursery->n_heap_end));
}

// Shadowstack API.
void gib_shadowstack_push(
    GibShadowstack *stack,
    char *ptr,
    char *endptr,
    uint32_t datatype,
    bool start_of_chunk
)
{
    assert(stack->ss_initialized);
    char *stack_alloc_ptr = stack->ss_alloc;
    char *stack_end = stack->ss_end;
    char **stack_alloc_ptr_addr = &(stack->ss_alloc);
    size_t size = sizeof(GibShadowstackFrame);
    if ((stack_alloc_ptr + size) > stack_end) {
        fprintf(stderr, "gib_shadowstack_push: out of memory");
        exit(1);
    }
    GibShadowstackFrame *frame = (GibShadowstackFrame *) stack_alloc_ptr;
    frame->ssf_ptr = ptr;
    frame->ssf_endptr = endptr;
    frame->ssf_datatype = datatype;
    frame->ssf_start_of_chunk = start_of_chunk;
    (*stack_alloc_ptr_addr) += size;
    return;
}

GibShadowstackFrame *gib_shadowstack_pop(GibShadowstack *stack)
{
    assert(stack->ss_initialized);
    char *stack_alloc_ptr = stack->ss_alloc;
    char *stack_start = stack->ss_start;
    char **stack_alloc_ptr_addr = &(stack->ss_alloc);
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
    assert(stack->ss_initialized);
    char *stack_alloc_ptr = stack->ss_alloc;
    char *stack_start = stack->ss_start;
    return ( (stack_alloc_ptr - stack_start) / sizeof(GibShadowstackFrame) );
}

void gib_shadowstack_print_all(GibShadowstack *stack)
{
    char *run_ptr = stack->ss_start;
    char *end_ptr = stack->ss_alloc;
    GibShadowstackFrame *frame;
    while (run_ptr < end_ptr) {
        frame = (GibShadowstackFrame *) run_ptr;
        printf("ptr=%p, endptr=%p, datatype=%d\n",
               frame->ssf_ptr, frame->ssf_endptr, frame->ssf_datatype);
        run_ptr += sizeof(GibShadowstackFrame);
    }
    return;
}

void gib_remset_reset(GibRememberedSet *set)
{
    set->ss_alloc = set->ss_start;
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
    region->c_start = heap_start;
    region->c_end = heap_end;
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
    assert(nursery->n_initialized);
    char *old = nursery->n_alloc;
    char *bump = old + size;
    if (bump < nursery->n_heap_end) {
        nursery->n_alloc = bump;
        GibChunk *region = gib_alloc(sizeof(GibChunk));
        region->c_start = old;
        region->c_end = bump;
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
    (void) region;
    printf("gib_free_region2: TODO.\n");
    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Write barrier
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * The following is how different types of indirections are handled:
 *
 * (1) nursery -> oldgen
 *
 *     We have two options here:
 *
 *     (a) Do nothing. However, when this region gets evacuated out of the
 *         nursery, we'll always have to inline the pointed-to data since we
 *         won't have access to its metadata to bump its refcount.
 *
 *     (b) Record it in a "deferred increment set" in the nursery. This way the
 *         evacuate function is free to decide whether to inline the pointed-to
 *         data or not. If it doesn't, it can find the correct metadata object
 *         to apply the refcount increment to in this "deferred increment set".
 *
 * (2) nursery -> nursery
 *
 *     Do nothing.
 *
 * (3) oldgen -> nursery
 *
 *     Add to remembered set.
 *
 * (4) oldgen -> oldgen
 *
 *     Same as old Gibbon, bump refcount and insert into outset.
 *
 */

// Write barrier. INLINE!!!
void gib_indirection_barrier(
    // Address where the indirection tag will be written.
    GibCursor from,
    GibCursor from_footer_ptr,
    // Address where the indirection pointer points to.
    GibCursor to,
    GibCursor to_footer_ptr,
    // Data type written at from/to.
    uint32_t datatype
)
{
    (void) to_footer_ptr;

    bool from_young = gib_addr_in_nursery(from);
    bool from_old = !from_young;
    bool to_young = gib_addr_in_nursery(to);
    bool to_old = !to_young;
    if (from_young && to_old) {
        // (1) nursery -> oldgen
        printf("young to old pointer\n");
        fprintf(stderr, "indirection barrier: todo nursery -> oldgen\n");
        exit(1);
    } else if (from_young && to_young) {
        printf("young to young pointer\n");
        // (2) nursery -> nursery
        return;
    } else if (from_old && to_young) {
        // (3) oldgen -> nursery
        printf("old to young pointer\n");
        GibGeneration *gen = DEFAULT_GENERATION;
        gib_remset_push(gen->g_rem_set, from, from_footer_ptr, datatype);
        return;
    } else if (from_old && to_old) {
        // (4) oldgen -> oldgen
        printf("old to old pointer\n");
        // gib_bump_refcount(from_footer_ptr, to_footer_ptr);
        return;
    }
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

    return 0;
}
