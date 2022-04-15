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

#define MAX_CHUNK_SIZE 65500

// Chunk sizes of buffers, see GitHub #79 and #110.
static size_t gib_global_biginf_init_chunk_size = 4 * GB;
static size_t gib_global_inf_init_chunk_size = 1 * KB;

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



size_t gib_get_biginf_init_chunk_size(void)
{
    return gib_global_biginf_init_chunk_size;
}

size_t gib_get_inf_init_chunk_size(void)
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

static void gib_bump_global_region_count(void);

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
        fprintf(stderr, "alloc_vector: gib_alloc failed: %zu", sizeof(GibVector));
        exit(1);
    }
    void *data = (void *) gib_alloc(num * elt_size);
    if (data == NULL) {
        fprintf(stderr, "alloc_vector: gib_alloc failed: %zu", sizeof(num * elt_size));
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
        fprintf(stderr, "gib_vector_slice: gib_alloc failed: %zu", sizeof(GibVector));
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
        fprintf(stderr, "gib_vector_merge: gib_alloc failed: %zu", sizeof(GibVector));
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
void gib_init_list_bumpalloc(void)
{
    gib_global_list_bumpalloc_heap_ptr =
        (char*) gib_alloc(gib_global_biginf_init_chunk_size);
    gib_global_list_bumpalloc_heap_ptr_end =
        gib_global_list_bumpalloc_heap_ptr + gib_global_biginf_init_chunk_size;
#ifdef _GIBBON_DEBUG
    printf("Arena size for bump alloc: %zu\n", gib_global_biginf_init_chunk_size);
    printf("gib_init_list_bumpalloc DONE: heap_ptr = %p\n",
           gib_global_list_bumpalloc_heap_ptr);
#endif
}

void *gib_list_bumpalloc(size_t n)
{
    if (! gib_global_list_bumpalloc_heap_ptr) {
        gib_init_list_bumpalloc();
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
void gib_list_bumpalloc_save_state(void)
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

void gib_list_bumpalloc_restore_state(void)
{
    if(gib_global_list_num_saved_heap_ptr <= 0) {
        fprintf(stderr, "Bad call to gib_list_bumpalloc_restore_state!  Saved stack empty!\ne");
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
void gib_init_list_bumpalloc(void) {}
void *gib_list_bumpalloc(size_t n) { return gib_alloc(n); }
void gib_list_bumpalloc_save_state(void) {}
void gib_list_bumpalloc_restore_state(void) {}

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
        fprintf(stderr, "gib_list_cons: gib_alloc failed: %zu", ls->data_size);
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

  Gibbon has "growing regions" i.e each logical region is backed by a singly
  linked-list of smaller chunks which grows as required. In addition to actual
  data, each chunk stores some additional metadata (GibChunkFooter) to chain
  the chunks together in a list and for garbage collection. The footer:

  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
  data | reg_info | size | next
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

  = first_chunk_footer: Address of the first chunk in this region;
    used to garbage collect the linked-list of chunks.

  - size: Used during bounds checking to calculate the size of the next
    region in the linked list.

  - next: Pointer to the next chunk's footer.


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


*/

#ifdef _GIBBON_DEBUG
#define NURSERY_SIZE (4 * gib_global_inf_init_chunk_size)
#else
#define NURSERY_SIZE (4 * MB)
// #define NURSERY_SIZE (1 * MB)
// #define NURSERY_SIZE (10 * 4096)
// #define NURSERY_SIZE (4096)
// #define NURSERY_SIZE (2048) // This seems to mess things up.
#endif

// If a region is over this size, alloc to refcounted heap directly.
#define NURSERY_REGION_MAX_SIZE (NURSERY_SIZE / 2)

#define NUM_GENERATIONS 1

// TODO(ckopaprkar): The shadow stack doesn't grow and we don't check for
// overflows at the moment. But this stack probably wouldn't overflow since
// each stack frame is only 16 bytes.
#define SHADOWSTACK_SIZE (sizeof(GibShadowstackFrame) * 4 * 1024 * 1024)

// Same as SHADOWSTACK_SIZE, overflows are not checked.
#define REMEMBERED_SET_SIZE (sizeof(GibRememberedSetElt) * 1024)


typedef struct gib_region_info {
    GibSym id;
    uint16_t refcount;
    // Pointers to a structure that is initialized and tracked on the Rust heap.
    void *outset;
    char *first_chunk_footer;
} GibRegionInfo;

typedef struct gib_chunk_footer {
    GibRegionInfo *reg_info;
    size_t size;
    struct gib_chunk_footer *next;
} GibChunkFooter;

typedef struct gib_nursery {
    // Allocation area.
    size_t heap_size;
    char *heap_start;
    char *heap_end;
    char *alloc;

} GibNursery;

typedef struct gib_generation {
    // Generation number.
    uint8_t no;

    // Destination generation for live objects.
    struct gib_generation *dest;

    // Is this the oldest generation?
    bool oldest;

    // Allocation area; uninitialized in the oldest gen which uses malloc.
    size_t heap_size;
    char *heap_start;
    char *heap_end;
    char *alloc;

    // Remembered set to store old to young pointers.
    GibRememberedSet *rem_set;

    // Zero count tables; pointers to structures that are initialized and
    // tracked on the Rust Heap.
    void *old_zct;
    void *new_zct;

} GibGeneration;

typedef struct gib_gc_stats {
    // Number of copying minor collections (maintained by Rust RTS).
    uint64_t minor_collections;

    // Number of copying major collections (maintained by Rust RTS).
    uint64_t major_collections;

    // Overall memory allocated (maintained by C and Rust RTS).
    size_t mem_allocated;

    // Overall memory copied (maintained by Rust RTS).
    size_t mem_copied;

    // Overall memory burned (maintained by Rust RTS).
    size_t mem_burned;

    // Number of regions in the nursery (maintained by C RTS).
    uint64_t nursery_regions;

    // Number of regions in the old generation (maintained by Rust RTS).
    uint64_t oldgen_regions;

    // Total GC time (maintained by C RTS).
    double gc_elapsed_time;
    double gc_cpu_time;

    // Fine grained stats to measure various different parts of the collector
    // (maintained by Rust RTS).
    double gc_rootset_sort_time;
    double gc_burn_time;
    double gc_find_fwdptr_time;
    double gc_info_tbl_lkp_time;
    double gc_zct_mgmt_time;

} GibGcStats;

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

// Collect GC statistics.
GibGcStats *gib_global_gc_stats = (GibGcStats *) NULL;

// Convenience macros since we don't really need the arrays of nurseries and
// shadowstacks since mutators are still sequential.
// #define DEFAULT_NURSERY gib_global_nurseries
#define DEFAULT_NURSERY gib_global_nurseries
#define DEFAULT_GENERATION gib_global_oldest_gen
#define GC_STATS gib_global_gc_stats


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Ensure that C and Rust agree on sizes
 * of structs that cross the boundary.
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */
void gib_check_rust_struct_sizes(void)
{
    // Sizes in the Rust RTS.
    size_t *stack, *frame, *nursery, *generation, *reg_info, *footer, *gc_stats;
    stack = (size_t *) malloc(sizeof(size_t) * 7);
    frame = (size_t *) ((char *) stack + sizeof(size_t));
    nursery = (size_t *) ((char *) frame + sizeof(size_t));
    generation = (size_t *) ((char *) nursery + sizeof(size_t));
    reg_info = (size_t *) ((char *) generation + sizeof(size_t));
    footer = (size_t *) ((char *) reg_info + sizeof(size_t));
    gc_stats = (size_t *) ((char *) footer + sizeof(size_t));
    gib_get_rust_struct_sizes(stack, frame, nursery, generation, reg_info, footer, gc_stats);

    // Check if they match with sizes in the C RTS.
    assert(*stack == sizeof(GibShadowstack));
    assert(*frame == sizeof(GibShadowstackFrame));
    assert(*nursery == sizeof(GibNursery));
    assert(*generation == sizeof(GibGeneration));
    assert(*reg_info == sizeof(GibRegionInfo));
    assert(*footer == sizeof(GibChunkFooter));
    assert(*gc_stats == sizeof(GibGcStats));

    // Done.
    free(stack);

    return;
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Region allocation and growth
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

STATIC_INLINE GibChunk gib_alloc_region_in_nursery(size_t size);
STATIC_INLINE GibChunk gib_alloc_region_in_nursery_fast(size_t size, bool collected);
static GibChunk gib_alloc_region_in_nursery_slow(size_t size, bool collected);
STATIC_INLINE bool gib_addr_in_nursery(char *ptr);

GibChunk gib_alloc_region(size_t size)
{
    return gib_alloc_region_in_nursery(size);
}

GibChunk gib_alloc_region_on_heap(size_t size)
{
    char *heap_start = gib_alloc(size);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_alloc_region_on_heap: gib_alloc failed: %zu",size);
        exit(1);
    }
    char *heap_end = heap_start + size;
    char *footer_start = gib_init_footer_at(heap_end, size, 0);
#ifdef _GIBBON_GCSTATS
    GC_STATS->mem_allocated += size;
#endif
    return (GibChunk) {heap_start, footer_start};
}

STATIC_INLINE GibChunk gib_alloc_region_in_nursery(size_t size)
{
#ifdef _GIBBON_GCSTATS
    GC_STATS->nursery_regions++;
#endif
    return gib_alloc_region_in_nursery_fast(size, false);
}

STATIC_INLINE GibChunk gib_alloc_region_in_nursery_fast(size_t size, bool collected)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    char *old = nursery->alloc;
    char *bump = old - size - sizeof(uint16_t);
    if (LIKELY((bump >= nursery->heap_start))) {
        nursery->alloc = bump;
        char *footer = old - sizeof(uint16_t);
        *(uint16_t *) footer = size;
        return (GibChunk) {bump, footer};
    } else {
        return gib_alloc_region_in_nursery_slow(size, collected);
    }
}

static GibChunk gib_alloc_region_in_nursery_slow(size_t size, bool collected)
{
    if (UNLIKELY((size > NURSERY_REGION_MAX_SIZE))) {
        return gib_alloc_region_on_heap(size);
    }
    if (collected) {
        fprintf(stderr, "Couldn't free space after garbage collection.\n");
        exit(1);
    }
    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibGeneration *generations = gib_global_generations;
    GibGcStats *gc_stats = GC_STATS;

#ifdef _GIBBON_GCSTATS
    struct timespec begin;
    struct timespec end;
    clock_gettime(CLOCK_MONOTONIC_RAW, &begin);
    gib_garbage_collect(rstack, wstack, nursery, generations, gc_stats, false);
    /*
    int err =
    if (err < 0) {
        fprintf(stderr, "Couldn't perform minor collection, errorno=%d.", err);
        exit(1);
    }
    */
    clock_gettime(CLOCK_MONOTONIC_RAW, &end);
    gc_stats->gc_elapsed_time += gib_difftimespecs(&begin, &end);
    gc_stats->gc_cpu_time += gc_stats->gc_elapsed_time / CLOCKS_PER_SEC;
#else
    gib_garbage_collect(rstack, wstack, nursery, generations, gc_stats, false);
#endif

    return gib_alloc_region_in_nursery_fast(size, true);
}

void gib_grow_region(char **writeloc_addr, char **footer_addr)
{
    char *footer_ptr = *footer_addr;
    size_t newsize;
    bool old_chunk_in_nursery;
    GibChunkFooter *footer = NULL;

    if (gib_addr_in_nursery(footer_ptr)) {
        old_chunk_in_nursery = true;
        newsize = gib_global_inf_init_chunk_size;
    } else {
        old_chunk_in_nursery = false;
        // Get size from current footer.
        footer = (GibChunkFooter *) footer_ptr;
        newsize = (footer->size) << 1;
        // See #110.
        if (newsize > MAX_CHUNK_SIZE) {
            newsize = MAX_CHUNK_SIZE;
        }
    }

    // Allocate.
    char *heap_start = (char *) gib_alloc(newsize);
    if (heap_start == NULL) {
        fprintf(stderr, "gib_grow_region: gib_alloc failed: %zu", newsize);
        exit(1);
    }
    char *heap_end = heap_start + newsize;
#ifdef _GIBBON_GCSTATS
    GC_STATS->mem_allocated += newsize;
#endif

    // Write a new footer for this chunk and link it with the old chunk's footer.
    char *new_footer_start = NULL;
    GibChunkFooter *new_footer = NULL;
    if (old_chunk_in_nursery) {
        new_footer_start = gib_init_footer_at(heap_end, newsize, 0);
        new_footer = (GibChunkFooter *) new_footer_start;
        gib_insert_into_new_zct(DEFAULT_GENERATION, new_footer->reg_info);
    } else {
        new_footer_start = heap_end - sizeof(GibChunkFooter);
        new_footer = (GibChunkFooter *) new_footer_start;
        new_footer->reg_info = footer->reg_info;
        new_footer->size = newsize;
        new_footer->next = (GibChunkFooter *) NULL;
        // Link with the old chunk's footer.
        footer->next = (GibChunkFooter *) new_footer;
    }

#ifdef _GIBBON_DEBUG
    GibRegionInfo *reg = (GibRegionInfo*) new_footer->reg_info;
    printf("gib_grow_region: allocated %zu bytes for region %" PRIu64 "\n",
           newsize,
           (new_footer->reg_info)->id);
#endif

    // Write a redirection tag at writeloc and make it point to the start of
    // this fresh chunk, but store a tagged pointer here.
    uint16_t new_footer_offset = new_footer_start - heap_start;
    uintptr_t tagged = GIB_STORE_TAG(heap_start, new_footer_offset);
    GibCursor writeloc = *writeloc_addr;
    *(GibBoxedTag *) writeloc = GIB_REDIRECTION_TAG;
    writeloc += 1;
    *(uintptr_t *) writeloc = tagged;

    // Update start and end cursors.
    *(char **) writeloc_addr = heap_start;
    *(char **) footer_addr = new_footer_start;

    return;
}

// Functions related to counting the number of allocated regions.
GibChunk gib_alloc_counted_region(size_t size)
{
    // Bump the count.
    gib_bump_global_region_count();
    return gib_alloc_region(size);
}

static void gib_bump_global_region_count(void)
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


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Storage management
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Initialize nurseries, shadow stacks and generations.
static void gib_storage_initialize(void);
static void gib_storage_free(void);
static void gib_nursery_initialize(GibNursery *nursery);
static void gib_nursery_free(GibNursery *nursery);
static void gib_generation_initialize(GibGeneration *gen, uint8_t gen_no);
static void gib_generation_free(GibGeneration *gen, uint8_t gen_no);
static void gib_shadowstack_initialize(GibShadowstack *stack, size_t stack_size);
static void gib_shadowstack_free(GibShadowstack *stack);
static void gib_gc_stats_initialize(GibGcStats *stats);
static void gib_gc_stats_free(GibGcStats *stats);

// Initialize nurseries, shadow stacks and generations.
static void gib_storage_initialize(void)
{
    if (gib_global_nurseries != NULL) {
        return;
    }

    // Initialize the stats object.
    gib_global_gc_stats = (GibGcStats *) gib_alloc(sizeof(GibGcStats));
    gib_gc_stats_initialize(gib_global_gc_stats);

    // Initialize nurseries.
    int n;
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
    int ss;
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
    int n;
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
    int ss;
    for (ss = 0; ss < gib_global_num_threads; ss++) {
        gib_shadowstack_free(&(gib_global_read_shadowstacks[ss]));
        gib_shadowstack_free(&(gib_global_write_shadowstacks[ss]));
    }
    free(gib_global_read_shadowstacks);
    free(gib_global_write_shadowstacks);

    // Free the stats object.
    gib_gc_stats_free(gib_global_gc_stats);
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Nursery
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

static void gib_nursery_initialize(GibNursery *nursery)
{
    nursery->heap_size = NURSERY_SIZE;
    nursery->heap_start = (char *) gib_alloc(NURSERY_SIZE);
    if (nursery->heap_start == NULL) {
        fprintf(stderr, "gib_nursery_initialize: gib_alloc failed: %zu",
                NURSERY_SIZE);
        exit(1);
    }
    nursery->heap_end = nursery->heap_start + NURSERY_SIZE;
    nursery->alloc = nursery->heap_end;

#ifdef _GIBBON_GCSTATS
    GC_STATS->mem_allocated += NURSERY_SIZE;
#endif

    return;
}

// Free data associated with a nursery.
static void gib_nursery_free(GibNursery *nursery)
{
    free(nursery->heap_start);
    return;
}

// TODO(ckoparkar):
// If we allocate the nursery at a high address AND ensure that all of the
// subsequent mallocs return a block at addresses lower than this, we can
// implement addr_in_nursery with one address check instead than two. -- RRN
STATIC_INLINE bool gib_addr_in_nursery(char *ptr)
{
    GibNursery *nursery = DEFAULT_NURSERY;
    return ((ptr >= nursery->heap_start) && (ptr <= nursery->heap_end));
}


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Middle and old generations
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

static void gib_generation_initialize(GibGeneration *gen, uint8_t gen_no)
{
    gen->no = gen_no;
    gen->dest = (GibGeneration *) NULL;
    gen->old_zct = (void *) NULL;
    gen->new_zct = (void *) NULL;
    // Initialize the remembered set.
    gen->rem_set = (GibRememberedSet *) gib_alloc(sizeof(GibRememberedSet));
    if (gen->rem_set == NULL) {
        fprintf(stderr, "gib_generation_initialize: gib_alloc failed: %zu",
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
            fprintf(stderr, "gib_generation_initialize: gib_alloc failed: %zu",
                    gen->heap_size);
        }
        gen->heap_end = gen->heap_start + gen->heap_size;
        gen->alloc = gen->heap_start;
#ifdef _GIBBON_GCSTATS
    GC_STATS->mem_allocated += gen->heap_size;
#endif
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


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Shadow-stack
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

// Initialize a shadow stack.
static void gib_shadowstack_initialize(GibShadowstack* stack, size_t stack_size)
{
    stack->start = (char *) gib_alloc(stack_size);
    if (stack->start == NULL) {
        fprintf(stderr, "gib_shadowstack_initialize: gib_alloc failed: %zu",
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


/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Remembered set
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */



/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Gc statistics
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


static void gib_gc_stats_initialize(GibGcStats *stats)
{
    stats->minor_collections = 0;
    stats->major_collections = 0;
    stats->mem_allocated = 0;
    stats->mem_copied = 0;
    stats->mem_burned = 0;
    stats->nursery_regions = 0;
    stats->oldgen_regions = 0;
    stats->gc_elapsed_time = 0;
    stats->gc_cpu_time = 0;
    stats->gc_rootset_sort_time = 0;
    stats->gc_burn_time = 0;
    stats->gc_find_fwdptr_time = 0;
    stats->gc_info_tbl_lkp_time = 0;
    stats->gc_zct_mgmt_time = 0;
}

static void gib_gc_stats_free(GibGcStats *stats)
{
    free(stats);
}

static void gib_gc_stats_print(GibGcStats *stats)
{
    printf("\nGC statistics\n----------------------------------------\n");
    printf("Major collections:\t\t %" PRIu64 "\n", stats->major_collections);
    printf("Minor collections:\t\t %" PRIu64 "\n", stats->minor_collections);

    printf("\n");
    printf("Mem allocated:\t\t\t %zu\n", stats->mem_allocated);
    printf("Mem copied:\t\t\t %zu\n", stats->mem_copied);
    printf("Mem burned:\t\t\t %zu\n", stats->mem_burned);

    printf("\n");
    printf("GC nursery regions:\t\t %lu\n", stats->nursery_regions);
    printf("GC oldgen regions:\t\t %lu\n", stats->oldgen_regions);

    printf("\n");
    printf("GC elapsed time:\t\t %e\n", stats->gc_elapsed_time);
    printf("GC cpu time:\t\t\t %e\n", stats->gc_cpu_time);

    printf("\n");
    printf("GC rootset sort time:\t\t %e\n", stats->gc_rootset_sort_time);
    printf("GC burn time:\t\t\t %e\n", stats->gc_burn_time);
    printf("GC fwd scan time:\t\t %e\n", stats->gc_find_fwdptr_time);
    printf("GC info table lookup time:\t %e\n", stats->gc_info_tbl_lkp_time);
    printf("GC ZCT mgmt time:\t\t %e\n", stats->gc_zct_mgmt_time);

}

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Write barrier
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 *
 * INLINE!!!
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
    // Write the indirection.
    uint16_t footer_offset = to_footer_ptr - to;
    uintptr_t tagged = GIB_STORE_TAG(to, footer_offset);
    GibCursor writeloc = from;
    *(GibBoxedTag *) writeloc = GIB_INDIRECTION_TAG;
    writeloc += sizeof(GibPackedTag);
    *(uintptr_t *) writeloc = tagged;

    // Add to remembered set if it's an old to young pointer.
    bool from_old = !gib_addr_in_nursery(from);
    bool to_young = gib_addr_in_nursery(to);
    bool to_old = !to_young;
    if (from_old) {
        if (to_young) {
            // (3) oldgen -> nursery
            GibGeneration *gen = DEFAULT_GENERATION;
            // Store the address of the indirection pointer, *NOT* the address of
            // the indirection tag, in the remembered set.
            char *indr_addr = (char *) from + sizeof(GibPackedTag);
            gib_remset_push(gen->rem_set, indr_addr, from_footer_ptr, datatype);
            return;
        } else {
            // (4) oldgen -> oldgen
            gib_handle_old_to_old_indirection(from_footer_ptr, to_footer_ptr);
            return;
        }
    }
    return;
}

/*
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Save and restore GC's state
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct gib_gc_state_snapshot {
    // nursery
    char *nursery_alloc;
    char *nursery_heap;

    // generations
    char *gen_alloc;
    char *gen_rem_set_alloc;
    void *gen_old_zct;
    void *gen_new_zct;

    // shadow-stacks
    char *ss_read_alloc;
    char *ss_write_alloc;

    // region metadata
    uint64_t num_regions;
    GibRegionInfo **reg_info_addrs;
    char **outsets;

} GibGcStateSnapshot;

GibGcStateSnapshot *gib_gc_init_state(uint64_t num_regions)
{
    GibGcStateSnapshot *snapshot = gib_alloc(sizeof(GibGcStateSnapshot));
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu", sizeof(GibGcStateSnapshot));
        exit(1);
    }
    snapshot->nursery_heap = gib_alloc(NURSERY_SIZE);
    if (snapshot->nursery_heap == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu", NURSERY_SIZE);
        exit(1);
    }
    snapshot->reg_info_addrs = gib_alloc(num_regions * sizeof(GibRegionInfo*));
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu",
                num_regions * sizeof(GibRegionInfo *));
        exit(1);
    }
    snapshot->outsets = gib_alloc(num_regions * sizeof(char*));
    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_save_state: gib_alloc failed: %zu",
                num_regions * sizeof(void*));
        exit(1);
    }
    return snapshot;
}

void gib_gc_save_state(GibGcStateSnapshot *snapshot, uint64_t num_regions, ...)
{
    if (NUM_GENERATIONS != 1) {
        fprintf(stderr, "gib_gc_save_state: NUM_GENERATIONS != 1");
        exit(1);
    }

    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibGeneration *oldest_gen = gib_global_generations;

    // nursery
    snapshot->nursery_alloc = nursery->alloc;
    memcpy(snapshot->nursery_heap, nursery->heap_start, NURSERY_SIZE);

    // generations
    snapshot->gen_alloc = oldest_gen->alloc;
    snapshot->gen_rem_set_alloc = (oldest_gen->rem_set)->alloc;
    snapshot->gen_old_zct = gib_clone_zct(oldest_gen->old_zct);
    snapshot->gen_new_zct = gib_clone_zct(oldest_gen->new_zct);

    // shadow-stacks
    snapshot->ss_read_alloc = rstack->alloc;
    snapshot->ss_write_alloc = wstack->alloc;

    // regions
    snapshot->num_regions = num_regions;
    char *footer_addr;
    GibChunkFooter *footer;
    GibRegionInfo *reg_info;
    void *outset;
    va_list ap;
    uint64_t i;
    va_start(ap, num_regions);
    for (i = 0; i < num_regions; i++) {
        footer_addr = va_arg(ap, char *);
        if (!gib_addr_in_nursery(footer_addr)) {
            footer = (GibChunkFooter *) footer_addr;
            reg_info = footer->reg_info;
            outset = gib_clone_outset(reg_info->outset);
            snapshot->reg_info_addrs[i] = reg_info;
            snapshot->outsets[i] = outset;
            // memcpy(&(snapshot->reg_info_addrs[i]), reg_info_addr, sizeof(GibRegionInfo *));
            // memcpy(&(snapshot->outsets[i]), &outset, sizeof(void *));
        }
        else {
            snapshot->reg_info_addrs[i] = (GibRegionInfo *) NULL;
            snapshot->outsets[i] = (void *) NULL;
        }
    }
    va_end(ap);

    return;
}

void gib_gc_restore_state(GibGcStateSnapshot *snapshot)
{
    if (NUM_GENERATIONS != 1) {
        fprintf(stderr, "gib_gc_restore_state: NUM_GENERATIONS != 1");
        exit(1);
    }

    if (snapshot == NULL) {
        fprintf(stderr, "gib_gc_restore_state: NULL snapshot");
        exit(1);
    }

    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibGeneration *oldest_gen = gib_global_generations;

    // nursery
    nursery->alloc = snapshot->nursery_alloc;
    memcpy(nursery->heap_start, snapshot->nursery_heap, NURSERY_SIZE);

    // generations
    oldest_gen->alloc = snapshot->gen_alloc;
    (oldest_gen->rem_set)->alloc = snapshot->gen_rem_set_alloc;
    gib_free_zct(oldest_gen->old_zct);
    gib_free_zct(oldest_gen->new_zct);
    oldest_gen->old_zct = snapshot->gen_old_zct;
    oldest_gen->new_zct = snapshot->gen_new_zct;

    // shadow-stacks
    rstack->alloc = snapshot->ss_read_alloc;
    wstack->alloc = snapshot->ss_write_alloc;

    // regions
    uint64_t i;
    GibRegionInfo *reg_info;
    for (i = 0; i < snapshot->num_regions; i++) {
        if (snapshot->reg_info_addrs[i] != NULL) {
            reg_info = snapshot->reg_info_addrs[i];
            gib_free_outset(reg_info->outset);
            reg_info->outset = snapshot->outsets[i];
        }
    }
}

void gib_gc_free_state(GibGcStateSnapshot *snapshot)
{
    free(snapshot->nursery_heap);
    free(snapshot->reg_info_addrs);
    free(snapshot->outsets);
    free(snapshot);
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
    // Ensure that C and Rust agree on sizes of structs that cross the boundary.
    gib_check_rust_struct_sizes();

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
    GibNursery *nursery = DEFAULT_NURSERY;
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibGeneration *generations = gib_global_generations;
    gib_init_zcts(generations);

    // Run the program.
    gib_main_expr();

    // Free all objects initialized by the Rust RTS.
    free(gib_global_bench_prog_param);
    // gib_gc_cleanup(rstack, wstack, nursery, generations);

#ifdef _GIBBON_GCSTATS
    // Print GC statistics.
    gib_gc_stats_print(GC_STATS);
#endif

    // Next, free all objects initialized by the C RTS.
    gib_storage_free();
    gib_free_symtable();

    return 0;
}
