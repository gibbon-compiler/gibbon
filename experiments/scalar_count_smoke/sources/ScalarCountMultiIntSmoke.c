/* Gibbon program. */

#include "gibbon_rts.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
#include <stddef.h>
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

#include <immintrin.h>

#ifndef SCALAR_COUNT_MULTI_LIST_LEN
#define SCALAR_COUNT_MULTI_LIST_LEN 8000
#endif

#ifndef SCALAR_COUNT_MULTI_BENCH_ITERS
#define SCALAR_COUNT_MULTI_BENCH_ITERS 50
#endif

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

#ifdef _GIBBON_ENABLE_PAPI
#include <papi.h>
#endif

#ifdef _GIBBON_ENABLE_PAPI_NATIVE
static int gibbon_native_papi_eventset = PAPI_NULL;
static int gibbon_native_papi_inited = 0;
#define GIBBON_NATIVE_PAPI_EVENT_COUNT 7
#define GIBBON_NATIVE_PAPI_MAX_ALTS 4
static const char *gibbon_native_papi_metric_labels[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {
    "CPU_CYCLES",
    "INSTRUCTIONS",
    "L1D_LOAD_MISSES",
    "L1I_LOAD_MISSES",
    "L2D_MISSES",
    "L2I_MISSES",
    "LLC_LOAD_MISSES",
};
static const char *gibbon_native_papi_event_candidates[GIBBON_NATIVE_PAPI_EVENT_COUNT][GIBBON_NATIVE_PAPI_MAX_ALTS] = {
    {"perf::PERF_COUNT_HW_CPU_CYCLES", "perf::CPU-CYCLES", "perf::CYCLES", "ix86arch::UNHALTED_CORE_CYCLES"},
    {"perf::PERF_COUNT_HW_INSTRUCTIONS", "perf::INSTRUCTIONS", "ix86arch::INSTRUCTION_RETIRED", NULL},
    {"perf::L1-DCACHE-LOAD-MISSES", "perf::PERF_COUNT_HW_CACHE_L1D", NULL, NULL},
    {"perf::L1-ICACHE-LOAD-MISSES", "perf::PERF_COUNT_HW_CACHE_L1I", NULL, NULL},
    {"L2_RQSTS:DEMAND_DATA_RD_MISS", "L2_RQSTS:MISS", "L2_REQUEST:DEMAND_DATA_RD_MISS", "L2_REQUEST:MISS"},
    {"L2_RQSTS:CODE_RD_MISS", "L2_REQUEST:CODE_RD_MISS", NULL, NULL},
    {"perf::LLC-LOAD-MISSES", "ix86arch::LLC_MISSES", "LONGEST_LAT_CACHE:MISS", "adl_grt::LONGEST_LAT_CACHE:MISS"},
};
static const char *gibbon_native_papi_selected_events[GIBBON_NATIVE_PAPI_EVENT_COUNT] = {NULL};
static void papi_init_or_die(void) {
    if (gibbon_native_papi_inited) return;
    int rv = PAPI_library_init(PAPI_VER_CURRENT);
    if (rv != PAPI_VER_CURRENT) {
        fprintf(stderr, "PAPI_library_init failed: %d\n", rv);
        exit(1);
    }
    rv = PAPI_create_eventset(&gibbon_native_papi_eventset);
    if (rv != PAPI_OK) {
        fprintf(stderr, "PAPI_create_eventset failed: %s\n", PAPI_strerror(rv));
        exit(1);
    }
    for (int i = 0; i < GIBBON_NATIVE_PAPI_EVENT_COUNT; i++) {
        int added = 0;
        for (int j = 0; j < GIBBON_NATIVE_PAPI_MAX_ALTS; j++) {
            const char *ev_name = gibbon_native_papi_event_candidates[i][j];
            int code;
            if (ev_name == NULL) {
                continue;
            }
            rv = PAPI_event_name_to_code((char*)ev_name, &code);
            if (rv != PAPI_OK) {
                continue;
            }
            rv = PAPI_add_event(gibbon_native_papi_eventset, code);
            if (rv == PAPI_OK) {
                gibbon_native_papi_selected_events[i] = ev_name;
                added = 1;
                break;
            }
        }
        if (!added) {
            fprintf(stderr, "No usable native PAPI event found for metric %s\n", gibbon_native_papi_metric_labels[i]);
            exit(1);
        }
    }
    gibbon_native_papi_inited = 1;
}
#endif

/* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 * Program starts here
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */

typedef struct GibIntProd_struct {
            GibInt field0;
        } GibIntProd;
typedef struct GibIntGibCursorProd_struct {
            GibInt field0;
            GibCursor field1;
        } GibIntGibCursorProd;
typedef struct GibFloatGibCursorProd_struct {
            GibFloat field0;
            GibCursor field1;
        } GibFloatGibCursorProd;
typedef struct GibBoolProd_struct {
            GibBool field0;
        } GibBoolProd;
typedef struct GibPackedTagGibCursorProd_struct {
            GibPackedTag field0;
            GibCursor field1;
        } GibPackedTagGibCursorProd;
typedef struct GibCursorProd_struct {
            GibCursor field0;
        } GibCursorProd;
typedef struct GibCursorGibCursorGibIntProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibInt field2;
        } GibCursorGibCursorGibIntProd;
typedef struct GibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
        } GibCursorGibCursorGibCursorProd;
typedef struct GibCursorPtr6Prod_struct {
            GibCursor field0[6];
        } GibCursorPtr6Prod;
typedef struct GibMutCursorProd_struct {
            GibCursor *field0;
        } GibMutCursorProd;
unsigned char _print_MultiList(GibCursor cursor_ptr_1532[6],
                               GibCursor arg_99_124_201[6]);
unsigned char add1MultiList(GibCursor cursor_ptr_1685[6],
                            GibCursor cursor_ptr_1684[6],
                            GibCursor cursor_ptr_1686[6],
                            GibCursor xs_29_147_224[6]);
unsigned char manual_vectorized_add1MultiList(GibCursor cursor_ptr_1685[6],
                                              GibCursor cursor_ptr_1684[6],
                                              GibCursor cursor_ptr_1686[6],
                                              GibCursor xs_29_147_224[6]);
unsigned char _copy_MultiList(GibCursor cursor_ptr_1970[6],
                              GibCursor cursor_ptr_1969[6],
                              GibCursor cursor_ptr_1971[6],
                              GibCursor arg_73_154_236[6]);
unsigned char mkMultiList(GibCursor cursor_ptr_2253[6],
                          GibCursor cursor_ptr_2254[6], GibInt len_36_167_249);
GibInt sumMultiList(GibCursor cursor_ptr_2340[6], GibCursor xs_42_173_257[6]);
unsigned char _traverse_MultiList(GibCursor cursor_ptr_2491[6],
                                  GibCursor arg_86_180_268[6]);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            MultiList_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);
    
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    
    GibDatatype field_tys[6];
    
    field_tys[0] = MultiList_T;
    error = gib_info_table_insert_packed_dcon(MultiList_T, 0, 36, 0, 5, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, MultiList_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(MultiList_T, 1, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, MultiList_T, 1);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(2739, ")");
    gib_add_symbol(2740, "(MNil");
    gib_add_symbol(2741, "(MCons");
    gib_add_symbol(2742, " ->r ");
    gib_add_symbol(2743, " ->i ");
    gib_add_symbol(2744, " ");
}
static inline double manual_now_seconds(void)
{
    struct timespec ts;

    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double) ts.tv_sec + ((double) ts.tv_nsec / 1000000000.0);
}

typedef struct ManualLoopTiming_struct {
    double seconds;
    uint64_t calls;
    uint64_t elements;
} ManualLoopTiming;

static void manual_loop_timing_reset(ManualLoopTiming *timing)
{
    timing->seconds = 0.0;
    timing->calls = 0;
    timing->elements = 0;
}

static void manual_loop_timing_record(ManualLoopTiming *timing,
                                      double seconds,
                                      uint64_t elements)
{
    timing->seconds += seconds;
    timing->calls += 1;
    timing->elements += elements;
}

static double manual_measure_empty_timing_overhead(uint64_t samples)
{
    double best = INFINITY;

    for (uint64_t i = 0; i < samples; i++) {
        double start = manual_now_seconds();
        double delta = manual_now_seconds() - start;

        if (delta > 0.0 && delta < best) {
            best = delta;
        }
    }

    return isfinite(best) ? best : 0.0;
}

static double manual_loop_timing_adjusted_seconds(const ManualLoopTiming *timing,
                                                  double measurement_overhead)
{
    double adjusted =
        timing->seconds - ((double) timing->calls * measurement_overhead);

    return adjusted > 0.0 ? adjusted : 0.0;
}

static double manual_loop_timing_ns_per_elem(const ManualLoopTiming *timing)
{
    if (timing->elements == 0) {
        return 0.0;
    }

    return (timing->seconds * 1000000000.0) / (double) timing->elements;
}

static double manual_loop_timing_ns_per_elem_for_seconds(
    const ManualLoopTiming *timing,
    double seconds)
{
    if (timing->elements == 0) {
        return 0.0;
    }

    return (seconds * 1000000000.0) / (double) timing->elements;
}

#define MANUAL_MULTI_INT_FIELDS 4

static void manual_loop_timing_reset_many(ManualLoopTiming timings[],
                                          size_t len)
{
    for (size_t i = 0; i < len; i++) {
        manual_loop_timing_reset(&timings[i]);
    }
}

static double manual_loop_timing_total_seconds(const ManualLoopTiming timings[],
                                               size_t len)
{
    double total = 0.0;

    for (size_t i = 0; i < len; i++) {
        total += timings[i].seconds;
    }

    return total;
}

static uint64_t manual_loop_timing_total_calls(const ManualLoopTiming timings[],
                                               size_t len)
{
    uint64_t total = 0;

    for (size_t i = 0; i < len; i++) {
        total += timings[i].calls;
    }

    return total;
}

static uint64_t manual_loop_timing_total_elements(const ManualLoopTiming timings[],
                                                  size_t len)
{
    uint64_t total = 0;

    for (size_t i = 0; i < len; i++) {
        total += timings[i].elements;
    }

    return total;
}

static ManualLoopTiming loop_scalar_hot_loop_timings[MANUAL_MULTI_INT_FIELDS] = {{0}};
static ManualLoopTiming indir_loop_scalar_hot_loop_timings[MANUAL_MULTI_INT_FIELDS] = {{0}};
static ManualLoopTiming indir_loop_auto_hot_loop_timings[MANUAL_MULTI_INT_FIELDS] = {{0}};
static ManualLoopTiming indir_loop_vectorized_hot_loop_timings[MANUAL_MULTI_INT_FIELDS] = {{0}};

static void manual_alloc_multilist_output(GibCursor reg_ptr[6],
                                          GibCursor reg_cursor_ptr[6],
                                          GibCursor cursor_ptr[6])
{
    for (int i = 0; i < 6; i++) {
        GibChunk region = gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
        reg_ptr[i] = region.start;
        reg_cursor_ptr[i] = region.end;
        cursor_ptr[i] = region.start;
    }
}

static void manual_write_indirection_header(GibCursor from,
                                            GibCursor to,
                                            GibCursor to_footer)
{
    ptrdiff_t raw_offset = to_footer - to;

    if (raw_offset < 0 || raw_offset > UINT16_MAX) {
        fprintf(stderr,
                "manual_write_indirection_header offset out of range: %td\n",
                raw_offset);
        exit(1);
    }

    uint16_t footer_offset = (uint16_t) raw_offset;
    GibTaggedPtr tagged = GIB_STORE_TAG(to, footer_offset);

    *(GibPackedTag *) from = GIB_INDIRECTION_TAG;
    gib_store_taggedptr_unaligned(from + sizeof(GibPackedTag), tagged);
}

static GibCursor manual_first_chunk_footer_or_end(GibCursor end_footer)
{
    char *first = gib_scalar_count_first_footer(end_footer);

    return first == NULL ? end_footer : first;
}

static GibCursor manual_follow_redirection(GibCursor cursor)
{
    GibPackedTag tag = *(GibPackedTag *) cursor;

    if (tag != GIB_REDIRECTION_TAG) {
        fprintf(stderr,
                "manual_follow_redirection expected redirection tag, got %u at %p\n",
                (unsigned) tag,
                (void *) cursor);
        exit(1);
    }

    GibTaggedPtr tagged = gib_load_taggedptr_unaligned(cursor + sizeof(GibPackedTag));
    return GIB_UNTAG(tagged);
}

typedef enum {
    MANUAL_ADD_SCALAR,
    MANUAL_ADD_AUTO,
    MANUAL_ADD_SSE2,
} ManualAddMode;

static void __attribute__((noinline,optimize("no-tree-vectorize")))
manual_add1_int_chunk_scalar(GibCursor in, GibCursor out, uint64_t count)
{
    const GibInt *src = (const GibInt *) in;
    GibInt *dst = (GibInt *) out;

    for (uint64_t i = 0; i < count; i++) {
        dst[i] = src[i] + 1;
    }
}

static void __attribute__((noinline))
manual_add1_int_chunk_auto(GibCursor in, GibCursor out, uint64_t count)
{
    const GibInt *restrict src = (const GibInt *restrict) in;
    GibInt *restrict dst = (GibInt *restrict) out;

    for (uint64_t i = 0; i < count; i++) {
        dst[i] = src[i] + 1;
    }
}

static void __attribute__((noinline))
manual_add1_int_chunk_sse2(GibCursor in, GibCursor out, uint64_t count)
{
#ifdef MANUAL_USE_AVX2
    uint64_t i = 0;
    __m256i ones256 = _mm256_set1_epi64x(1);
    __m128i ones128 = _mm_set1_epi64x(1);

    for (; i + 4 <= count; i += 4) {
        __m256i vals = _mm256_loadu_si256((const __m256i *) (const void *)
                                          ((const GibInt *) in + i));
        vals = _mm256_add_epi64(vals, ones256);
        _mm256_storeu_si256((__m256i *) (void *) ((GibInt *) out + i), vals);
    }

    for (; i + 2 <= count; i += 2) {
        __m128i vals = _mm_loadu_si128((const __m128i *) (const void *)
                                       ((const GibInt *) in + i));
        vals = _mm_add_epi64(vals, ones128);
        _mm_storeu_si128((__m128i *) (void *) ((GibInt *) out + i), vals);
    }

    for (; i < count; i++) {
        ((GibInt *) out)[i] = ((const GibInt *) in)[i] + 1;
    }
#else
    uint64_t i = 0;
    __m128i ones = _mm_set1_epi64x(1);

    for (; i + 4 <= count; i += 4) {
        __m128i vals0 = _mm_loadu_si128((const __m128i *) (const void *)
                                        ((const GibInt *) in + i));
        __m128i vals1 = _mm_loadu_si128((const __m128i *) (const void *)
                                        ((const GibInt *) in + i + 2));
        vals0 = _mm_add_epi64(vals0, ones);
        vals1 = _mm_add_epi64(vals1, ones);
        _mm_storeu_si128((__m128i *) (void *) ((GibInt *) out + i), vals0);
        _mm_storeu_si128((__m128i *) (void *) ((GibInt *) out + i + 2), vals1);
    }

    for (; i + 2 <= count; i += 2) {
        __m128i vals = _mm_loadu_si128((const __m128i *) (const void *)
                                       ((const GibInt *) in + i));
        vals = _mm_add_epi64(vals, ones);
        _mm_storeu_si128((__m128i *) (void *) ((GibInt *) out + i), vals);
    }

    for (; i < count; i++) {
        ((GibInt *) out)[i] = ((const GibInt *) in)[i] + 1;
    }
#endif
}

static void manual_add1_int_chunk_mode(GibCursor in,
                                       GibCursor out,
                                       uint64_t count,
                                       ManualAddMode mode)
{
    switch (mode) {
      case MANUAL_ADD_SCALAR:
        manual_add1_int_chunk_scalar(in, out, count);
        break;
      case MANUAL_ADD_AUTO:
        manual_add1_int_chunk_auto(in, out, count);
        break;
      case MANUAL_ADD_SSE2:
        manual_add1_int_chunk_sse2(in, out, count);
        break;
    }
}

static void __attribute__((noinline,optimize("no-tree-vectorize")))
manual_zero_dcon_chunk(GibCursor out, uint64_t count)
{
    for (uint64_t i = 0; i < count; i++) {
        out[i] = 0;
    }
}

static void __attribute__((noinline,optimize("no-tree-vectorize")))
manual_copy_float_chunk(GibCursor in, GibCursor out, uint64_t count)
{
    const GibFloat *src = (const GibFloat *) in;
    GibFloat *dst = (GibFloat *) out;

    for (uint64_t i = 0; i < count; i++) {
        dst[i] = src[i];
    }
}

static void manual_add1_scalar_field_chunks(GibCursor input_end,
                                            GibCursor *output_end,
                                            GibCursor input_cursor,
                                            GibCursor *output_cursor,
                                            ManualAddMode mode,
                                            ManualLoopTiming *int_loop_timing)
{
    GibCursor out_data_cursor = *output_cursor + sizeof(GibPackedTag) + sizeof(GibTaggedPtr);
    char *next_count_footer = gib_scalar_count_first_footer(input_end);
    uint64_t count = gib_scalar_count_footer_get(input_end);

    manual_write_indirection_header(*output_cursor, out_data_cursor, *output_end);

    while (true) {
        double int_loop_start = manual_now_seconds();
        manual_add1_int_chunk_mode(input_cursor, out_data_cursor, count, mode);
        manual_loop_timing_record(int_loop_timing,
                                  manual_now_seconds() - int_loop_start,
                                  count);
        input_cursor += count * sizeof(GibInt);
        out_data_cursor += count * sizeof(GibInt);

        if (next_count_footer == NULL || next_count_footer == input_end) {
            break;
        }

        input_cursor = manual_follow_redirection(input_cursor);
        gib_grow_region(&out_data_cursor, output_end);
        count = gib_scalar_count_footer_get(next_count_footer);
        next_count_footer = gib_scalar_count_footer_next(next_count_footer);
    }

    *output_cursor = out_data_cursor;
}

static unsigned char manual_indirect_add1MultiList(GibCursor cursor_ptr_1685[6],
                                                   GibCursor cursor_ptr_1684[6],
                                                   GibCursor cursor_ptr_1686[6],
                                                   GibCursor xs_29_147_224[6],
                                                   ManualAddMode mode,
                                                   ManualLoopTiming int_loop_timings[MANUAL_MULTI_INT_FIELDS])
{
    manual_write_indirection_header(cursor_ptr_1686[0],
                                    xs_29_147_224[0],
                                    manual_first_chunk_footer_or_end(cursor_ptr_1685[0]));
    cursor_ptr_1686[0] += sizeof(GibPackedTag) + sizeof(GibTaggedPtr);

    manual_add1_scalar_field_chunks(cursor_ptr_1685[1],
                                    &cursor_ptr_1684[1],
                                    xs_29_147_224[1],
                                    &cursor_ptr_1686[1],
                                    mode,
                                    &int_loop_timings[0]);
    manual_add1_scalar_field_chunks(cursor_ptr_1685[2],
                                    &cursor_ptr_1684[2],
                                    xs_29_147_224[2],
                                    &cursor_ptr_1686[2],
                                    mode,
                                    &int_loop_timings[1]);
    manual_add1_scalar_field_chunks(cursor_ptr_1685[3],
                                    &cursor_ptr_1684[3],
                                    xs_29_147_224[3],
                                    &cursor_ptr_1686[3],
                                    mode,
                                    &int_loop_timings[2]);
    manual_add1_scalar_field_chunks(cursor_ptr_1685[4],
                                    &cursor_ptr_1684[4],
                                    xs_29_147_224[4],
                                    &cursor_ptr_1686[4],
                                    mode,
                                    &int_loop_timings[3]);

    manual_write_indirection_header(cursor_ptr_1686[5],
                                    xs_29_147_224[5],
                                    manual_first_chunk_footer_or_end(cursor_ptr_1685[5]));
    cursor_ptr_1686[5] += sizeof(GibPackedTag) + sizeof(GibTaggedPtr);

    return 0;
}

static unsigned char manual_copy_scalar_add1MultiList(GibCursor cursor_ptr_1685[6],
                                                      GibCursor cursor_ptr_1684[6],
                                                      GibCursor cursor_ptr_1686[6],
                                                      GibCursor xs_29_147_224[6])
{
    GibCursor in_dcon = xs_29_147_224[0];
    GibCursor in_int0 = xs_29_147_224[1];
    GibCursor in_int1 = xs_29_147_224[2];
    GibCursor in_int2 = xs_29_147_224[3];
    GibCursor in_int3 = xs_29_147_224[4];
    GibCursor in_float = xs_29_147_224[5];
    GibCursor out_dcon = cursor_ptr_1686[0];
    GibCursor out_int0 = cursor_ptr_1686[1];
    GibCursor out_int1 = cursor_ptr_1686[2];
    GibCursor out_int2 = cursor_ptr_1686[3];
    GibCursor out_int3 = cursor_ptr_1686[4];
    GibCursor out_float = cursor_ptr_1686[5];
    GibCursor out_dcon_end = cursor_ptr_1684[0];
    GibCursor out_int0_end = cursor_ptr_1684[1];
    GibCursor out_int1_end = cursor_ptr_1684[2];
    GibCursor out_int2_end = cursor_ptr_1684[3];
    GibCursor out_int3_end = cursor_ptr_1684[4];
    GibCursor out_float_end = cursor_ptr_1684[5];
    GibOldgenChunkFooter *final_footers[5] = {
        (GibOldgenChunkFooter *) cursor_ptr_1685[1],
        (GibOldgenChunkFooter *) cursor_ptr_1685[2],
        (GibOldgenChunkFooter *) cursor_ptr_1685[3],
        (GibOldgenChunkFooter *) cursor_ptr_1685[4],
        (GibOldgenChunkFooter *) cursor_ptr_1685[5],
    };
    GibOldgenChunkFooter *next_footers[5] = {0};
    bool first_chunk = true;

    for (int i = 0; i < 5; i++) {
        if (final_footers[i] == NULL ||
            final_footers[i]->reg_info == NULL ||
            final_footers[i]->reg_info->first_chunk_footer == NULL) {
            fprintf(stderr,
                    "manual copy add1MultiList could not find scalar-count footer %d\n",
                    i);
            exit(1);
        }
        next_footers[i] =
            (GibOldgenChunkFooter *) final_footers[i]->reg_info->first_chunk_footer;
    }

    while (true) {
        GibOldgenChunkFooter *count_footers[5];

        for (int i = 0; i < 5; i++) {
            count_footers[i] = first_chunk ? final_footers[i] : next_footers[i];
            if (count_footers[i] == NULL) {
                fprintf(stderr,
                        "manual copy add1MultiList reached null count footer %d\n",
                        i);
                exit(1);
            }
        }

        uint64_t count = gib_scalar_count_footer_get((char *) count_footers[0]);

        for (int i = 1; i < 5; i++) {
            uint64_t other = gib_scalar_count_footer_get((char *) count_footers[i]);

            if (other != count) {
                fprintf(stderr,
                        "manual copy add1MultiList count mismatch: field0=%" PRIu64
                        " field%d=%" PRIu64 "\n",
                        count, i, other);
                exit(1);
            }
        }

        size_t int_bytes = (size_t) count * sizeof(GibInt);
        size_t float_bytes = (size_t) count * sizeof(GibFloat);

        manual_zero_dcon_chunk(out_dcon, count);
        in_dcon += count;
        out_dcon += count;

        double int0_loop_start = manual_now_seconds();
        manual_add1_int_chunk_scalar(in_int0, out_int0, count);
        manual_loop_timing_record(&loop_scalar_hot_loop_timings[0],
                                  manual_now_seconds() - int0_loop_start,
                                  count);
        double int1_loop_start = manual_now_seconds();
        manual_add1_int_chunk_scalar(in_int1, out_int1, count);
        manual_loop_timing_record(&loop_scalar_hot_loop_timings[1],
                                  manual_now_seconds() - int1_loop_start,
                                  count);
        double int2_loop_start = manual_now_seconds();
        manual_add1_int_chunk_scalar(in_int2, out_int2, count);
        manual_loop_timing_record(&loop_scalar_hot_loop_timings[2],
                                  manual_now_seconds() - int2_loop_start,
                                  count);
        double int3_loop_start = manual_now_seconds();
        manual_add1_int_chunk_scalar(in_int3, out_int3, count);
        manual_loop_timing_record(&loop_scalar_hot_loop_timings[3],
                                  manual_now_seconds() - int3_loop_start,
                                  count);
        in_int0 += int_bytes;
        in_int1 += int_bytes;
        in_int2 += int_bytes;
        in_int3 += int_bytes;
        out_int0 += int_bytes;
        out_int1 += int_bytes;
        out_int2 += int_bytes;
        out_int3 += int_bytes;

        manual_copy_float_chunk(in_float, out_float, count);
        in_float += float_bytes;
        out_float += float_bytes;

        GibPackedTag next_tag = *(GibPackedTag *) in_dcon;

        if (next_tag == 1) {
            *(GibPackedTag *) out_dcon = 1;
            in_dcon += 1;
            out_dcon += 1;
            break;
        } else if (next_tag == GIB_REDIRECTION_TAG) {
            gib_grow_region(&out_dcon, &out_dcon_end);
            gib_grow_region(&out_int0, &out_int0_end);
            gib_grow_region(&out_int1, &out_int1_end);
            gib_grow_region(&out_int2, &out_int2_end);
            gib_grow_region(&out_int3, &out_int3_end);
            gib_grow_region(&out_float, &out_float_end);

            in_dcon = manual_follow_redirection(in_dcon);
            in_int0 = manual_follow_redirection(in_int0);
            in_int1 = manual_follow_redirection(in_int1);
            in_int2 = manual_follow_redirection(in_int2);
            in_int3 = manual_follow_redirection(in_int3);
            in_float = manual_follow_redirection(in_float);

            if (first_chunk) {
                first_chunk = false;
            } else {
                for (int i = 0; i < 5; i++) {
                    next_footers[i] =
                        (GibOldgenChunkFooter *)
                        gib_scalar_count_footer_next((char *) next_footers[i]);
                }
            }
        } else {
            fprintf(stderr,
                    "manual copy add1MultiList expected Nil or redirection, found %u\n",
                    (unsigned) next_tag);
            exit(1);
        }
    }

    xs_29_147_224[0] = in_dcon;
    xs_29_147_224[1] = in_int0;
    xs_29_147_224[2] = in_int1;
    xs_29_147_224[3] = in_int2;
    xs_29_147_224[4] = in_int3;
    xs_29_147_224[5] = in_float;
    cursor_ptr_1686[0] = out_dcon;
    cursor_ptr_1686[1] = out_int0;
    cursor_ptr_1686[2] = out_int1;
    cursor_ptr_1686[3] = out_int2;
    cursor_ptr_1686[4] = out_int3;
    cursor_ptr_1686[5] = out_float;
    cursor_ptr_1684[0] = out_dcon_end;
    cursor_ptr_1684[1] = out_int0_end;
    cursor_ptr_1684[2] = out_int1_end;
    cursor_ptr_1684[3] = out_int2_end;
    cursor_ptr_1684[4] = out_int3_end;
    cursor_ptr_1684[5] = out_float_end;
    return 0;
}

unsigned char manual_indir_scalar_add1MultiList(GibCursor cursor_ptr_1685[6],
                                                GibCursor cursor_ptr_1684[6],
                                                GibCursor cursor_ptr_1686[6],
                                                GibCursor xs_29_147_224[6])
{
    return manual_indirect_add1MultiList(cursor_ptr_1685, cursor_ptr_1684,
                                         cursor_ptr_1686, xs_29_147_224,
                                         MANUAL_ADD_SCALAR,
                                         indir_loop_scalar_hot_loop_timings);
}

unsigned char manual_indir_auto_add1MultiList(GibCursor cursor_ptr_1685[6],
                                              GibCursor cursor_ptr_1684[6],
                                              GibCursor cursor_ptr_1686[6],
                                              GibCursor xs_29_147_224[6])
{
    return manual_indirect_add1MultiList(cursor_ptr_1685, cursor_ptr_1684,
                                         cursor_ptr_1686, xs_29_147_224,
                                         MANUAL_ADD_AUTO,
                                         indir_loop_auto_hot_loop_timings);
}

unsigned char manual_vectorized_add1MultiList(GibCursor cursor_ptr_1685[6],
                                              GibCursor cursor_ptr_1684[6],
                                              GibCursor cursor_ptr_1686[6],
                                              GibCursor xs_29_147_224[6])
{
    return manual_indirect_add1MultiList(cursor_ptr_1685, cursor_ptr_1684,
                                         cursor_ptr_1686, xs_29_147_224,
                                         MANUAL_ADD_SSE2,
                                         indir_loop_vectorized_hot_loop_timings);
}

typedef unsigned char (*ManualMultiAdd1Fn)(GibCursor end_in[6],
                                           GibCursor end_out[6],
                                           GibCursor out[6],
                                           GibCursor in[6]);

static double manual_time_add1_multilist(ManualMultiAdd1Fn fn,
                                         GibCursor input_end[6],
                                         GibCursor input_start[6],
                                         int iters,
                                         GibCursor result_reg_ptr[6],
                                         GibCursor result_reg_end[6])
{
    double total_seconds = 0.0;

    for (int iter = 0; iter < iters; iter++) {
        GibCursor reg_ptr[6] = {0};
        GibCursor reg_end[6] = {0};
        GibCursor cursor_ptr[6] = {0};
        GibCursor input_copy[6];

        manual_alloc_multilist_output(reg_ptr, reg_end, cursor_ptr);
        memcpy(input_copy, input_start, sizeof(GibCursor [6]));

        double start = manual_now_seconds();
        fn(input_end, reg_end, cursor_ptr, input_copy);
        total_seconds += manual_now_seconds() - start;

        if (iter == iters - 1) {
            memcpy(result_reg_ptr, reg_ptr, sizeof(GibCursor [6]));
            memcpy(result_reg_end, reg_end, sizeof(GibCursor [6]));
        }
    }

    return total_seconds / (double) iters;
}

static GibInt manual_sum_multilist_result(GibCursor reg_end[6],
                                          GibCursor reg_ptr[6])
{
    GibCursor sum_address[6];

    memcpy(sum_address, reg_ptr, sizeof(GibCursor [6]));
    return sumMultiList(reg_end, sum_address);
}
unsigned char _print_MultiList(GibCursor cursor_ptr_1532[6],
                               GibCursor arg_99_124_201[6])
{
    GibCursor *end_r_691 = &cursor_ptr_1532[0];
    GibCursor *end_r_692 = &cursor_ptr_1532[1];
    GibCursor *end_r_693 = &cursor_ptr_1532[2];
    GibCursor *end_r_694 = &cursor_ptr_1532[3];
    GibCursor *end_r_695 = &cursor_ptr_1532[4];
    GibCursor *end_r_696 = &cursor_ptr_1532[5];
    GibCursor *restrict loc_685 = &arg_99_124_201[0];
    GibCursor deref_dcon_var_1536 = *loc_685;
    GibPackedTag tmpval_2757 = *(GibPackedTag *) deref_dcon_var_1536;
    GibCursor tmpcur_2758 = deref_dcon_var_1536 + 1;
    
    
  switch_2805:
    ;
    switch (tmpval_2757) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1538 = &arg_99_124_201[1];
            GibCursor deref_1539 = *soa_field_0_1538;
            GibCursor *restrict soa_field_1_1540 = &arg_99_124_201[2];
            GibCursor deref_1541 = *soa_field_1_1540;
            GibCursor *restrict soa_field_2_1542 = &arg_99_124_201[3];
            GibCursor deref_1543 = *soa_field_2_1542;
            GibCursor *restrict soa_field_3_1544 = &arg_99_124_201[4];
            GibCursor deref_1545 = *soa_field_3_1544;
            GibCursor *restrict soa_field_4_1546 = &arg_99_124_201[5];
            GibCursor deref_1547 = *soa_field_4_1546;
            GibInt tmpval_2759 = *(GibInt *) deref_1539;
            GibCursor tmpcur_2760 = deref_1539 + sizeof(GibInt);
            
            *soa_field_0_1538 += 8;
            
            GibInt tmpval_2761 = *(GibInt *) deref_1541;
            GibCursor tmpcur_2762 = deref_1541 + sizeof(GibInt);
            
            *soa_field_1_1540 += 8;
            
            GibInt tmpval_2763 = *(GibInt *) deref_1543;
            GibCursor tmpcur_2764 = deref_1543 + sizeof(GibInt);
            
            *soa_field_2_1542 += 8;
            
            GibInt tmpval_2765 = *(GibInt *) deref_1545;
            GibCursor tmpcur_2766 = deref_1545 + sizeof(GibInt);
            
            *soa_field_3_1544 += 8;
            
            GibFloat tmpval_2767 = *(GibFloat *) deref_1547;
            GibCursor tmpcur_2768 = deref_1547 + sizeof(GibFloat);
            
            *soa_field_4_1546 += 4;
            
            GibCursor cursor_ptr_1534[6] = {tmpcur_2758, tmpcur_2760,
                                            tmpcur_2762, tmpcur_2764,
                                            tmpcur_2766, tmpcur_2768};
            
            *loc_685 += 1;
            
            GibCursor jumpf_floc_loc_1089 = deref_1539 + 8;
            GibCursor jumpf_floc_loc_1090 = deref_1541 + 8;
            GibCursor jumpf_floc_loc_1091 = deref_1543 + 8;
            GibCursor jumpf_floc_loc_1092 = deref_1545 + 8;
            GibCursor jumpf_floc_loc_1093 = deref_1547 + 4;
            GibCursor loc_853 = tmpcur_2758 + 0;
            
            *loc_685 += 0;
            
            GibCursor loc_852 = jumpf_floc_loc_1093 + 0;
            GibCursor loc_851 = jumpf_floc_loc_1092 + 0;
            GibCursor loc_850 = jumpf_floc_loc_1091 + 0;
            GibCursor loc_849 = jumpf_floc_loc_1090 + 0;
            GibCursor loc_848 = jumpf_floc_loc_1089 + 0;
            GibCursor cursor_ptr_1562[6] = {tmpcur_2758, jumpf_floc_loc_1089,
                                            jumpf_floc_loc_1090,
                                            jumpf_floc_loc_1091,
                                            jumpf_floc_loc_1092,
                                            jumpf_floc_loc_1093};
            unsigned char wildcard_112_131_208 = gib_print_symbol(2741);
            unsigned char wildcard_119_132_209 = gib_print_symbol(2744);
            unsigned char y_106_133_210 = printf("%ld", tmpval_2759);
            unsigned char wildcard_118_134_211 = gib_print_symbol(2744);
            unsigned char y_107_135_212 = printf("%ld", tmpval_2761);
            unsigned char wildcard_117_136_213 = gib_print_symbol(2744);
            unsigned char y_108_137_214 = printf("%ld", tmpval_2763);
            unsigned char wildcard_116_138_215 = gib_print_symbol(2744);
            unsigned char y_109_139_216 = printf("%ld", tmpval_2765);
            unsigned char wildcard_115_140_217 = gib_print_symbol(2744);
            unsigned char y_110_141_218 = printf("%.2f", tmpval_2767);
            unsigned char wildcard_114_142_219 = gib_print_symbol(2744);
            GibCursor chk_loc_1582 = cursor_ptr_1534[0];
            GibCursor chk_end_1583 = cursor_ptr_1532[0];
            GibBool chk_1584 = chk_loc_1582 < chk_end_1583;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1579 = cursor_ptr_1534[1];
            GibCursor chk_end_1580 = cursor_ptr_1532[1];
            GibBool chk_1581 = chk_loc_1579 < chk_end_1580;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1576 = cursor_ptr_1534[2];
            GibCursor chk_end_1577 = cursor_ptr_1532[2];
            GibBool chk_1578 = chk_loc_1576 < chk_end_1577;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1573 = cursor_ptr_1534[3];
            GibCursor chk_end_1574 = cursor_ptr_1532[3];
            GibBool chk_1575 = chk_loc_1573 < chk_end_1574;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1570 = cursor_ptr_1534[4];
            GibCursor chk_end_1571 = cursor_ptr_1532[4];
            GibBool chk_1572 = chk_loc_1570 < chk_end_1571;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1567 = cursor_ptr_1534[5];
            GibCursor chk_end_1568 = cursor_ptr_1532[5];
            GibBool chk_1569 = chk_loc_1567 < chk_end_1568;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char y_111_143_220 =
                           _print_MultiList(cursor_ptr_1532, arg_99_124_201);
            GibCursor loc_cursor_ptr_1563[6];
            
            memcpy(loc_cursor_ptr_1563, arg_99_124_201, sizeof(GibCursor [6]));
            
            unsigned char wildcard_113_144_221 = gib_print_symbol(2739);
            
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1587 = &arg_99_124_201[1];
            GibCursor deref_1588 = *soa_field_0_1587;
            GibCursor *restrict soa_field_1_1589 = &arg_99_124_201[2];
            GibCursor deref_1590 = *soa_field_1_1589;
            GibCursor *restrict soa_field_2_1591 = &arg_99_124_201[3];
            GibCursor deref_1592 = *soa_field_2_1591;
            GibCursor *restrict soa_field_3_1593 = &arg_99_124_201[4];
            GibCursor deref_1594 = *soa_field_3_1593;
            GibCursor *restrict soa_field_4_1595 = &arg_99_124_201[5];
            GibCursor deref_1596 = *soa_field_4_1595;
            
            *loc_685 += 1;
            
            GibCursor jump_floc_loc_1102 = deref_1588 + 0;
            GibCursor jump_floc_loc_1103 = deref_1590 + 0;
            GibCursor jump_floc_loc_1104 = deref_1592 + 0;
            GibCursor jump_floc_loc_1105 = deref_1594 + 0;
            GibCursor jump_floc_loc_1106 = deref_1596 + 0;
            GibCursor cursor_ptr_1599[6] = {tmpcur_2758, jump_floc_loc_1102,
                                            jump_floc_loc_1103,
                                            jump_floc_loc_1104,
                                            jump_floc_loc_1105,
                                            jump_floc_loc_1106};
            unsigned char wildcard_120_145_222 = gib_print_symbol(2740);
            unsigned char wildcard_121_146_223 = gib_print_symbol(2739);
            
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1601 = &arg_99_124_201[1];
            GibCursor deref_1602 = *soa_field_0_1601;
            GibCursor *restrict soa_field_1_1603 = &arg_99_124_201[2];
            GibCursor deref_1604 = *soa_field_1_1603;
            GibCursor *restrict soa_field_2_1605 = &arg_99_124_201[3];
            GibCursor deref_1606 = *soa_field_2_1605;
            GibCursor *restrict soa_field_3_1607 = &arg_99_124_201[4];
            GibCursor deref_1608 = *soa_field_3_1607;
            GibCursor *restrict soa_field_4_1609 = &arg_99_124_201[5];
            GibCursor deref_1610 = *soa_field_4_1609;
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) tmpcur_2758;
            GibCursor tmpcur_2769 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_2770 = tmpcur_2758 + 8;
            uint16_t tmptag_2771 = GIB_GET_TAG(tagged_tmpcur_5);
            
            *(GibCursor *) loc_685 = tmpcur_2769;
            
            GibCursor end_from_tagged_dcon_redir_1632 = tmpcur_2769 +
                      tmptag_2771;
            GibCursor field_nxt_1626 = deref_1602 + 1;
            uintptr_t tagged_tmpcur_4 = *(uintptr_t *) field_nxt_1626;
            GibCursor tmpcur_2772 = GIB_UNTAG(tagged_tmpcur_4);
            GibCursor tmpaftercur_2773 = field_nxt_1626 + 8;
            uint16_t tmptag_2774 = GIB_GET_TAG(tagged_tmpcur_4);
            
            *(GibCursor *) soa_field_0_1601 = tmpcur_2772;
            
            GibCursor end_from_tagged_fld_redir_1633 = tmpcur_2772 +
                      tmptag_2774;
            GibCursor field_nxt_1627 = deref_1604 + 1;
            uintptr_t tagged_tmpcur_3 = *(uintptr_t *) field_nxt_1627;
            GibCursor tmpcur_2775 = GIB_UNTAG(tagged_tmpcur_3);
            GibCursor tmpaftercur_2776 = field_nxt_1627 + 8;
            uint16_t tmptag_2777 = GIB_GET_TAG(tagged_tmpcur_3);
            
            *(GibCursor *) soa_field_1_1603 = tmpcur_2775;
            
            GibCursor end_from_tagged_fld_redir_1634 = tmpcur_2775 +
                      tmptag_2777;
            GibCursor field_nxt_1628 = deref_1606 + 1;
            uintptr_t tagged_tmpcur_2 = *(uintptr_t *) field_nxt_1628;
            GibCursor tmpcur_2778 = GIB_UNTAG(tagged_tmpcur_2);
            GibCursor tmpaftercur_2779 = field_nxt_1628 + 8;
            uint16_t tmptag_2780 = GIB_GET_TAG(tagged_tmpcur_2);
            
            *(GibCursor *) soa_field_2_1605 = tmpcur_2778;
            
            GibCursor end_from_tagged_fld_redir_1635 = tmpcur_2778 +
                      tmptag_2780;
            GibCursor field_nxt_1629 = deref_1608 + 1;
            uintptr_t tagged_tmpcur_1 = *(uintptr_t *) field_nxt_1629;
            GibCursor tmpcur_2781 = GIB_UNTAG(tagged_tmpcur_1);
            GibCursor tmpaftercur_2782 = field_nxt_1629 + 8;
            uint16_t tmptag_2783 = GIB_GET_TAG(tagged_tmpcur_1);
            
            *(GibCursor *) soa_field_3_1607 = tmpcur_2781;
            
            GibCursor end_from_tagged_fld_redir_1636 = tmpcur_2781 +
                      tmptag_2783;
            GibCursor field_nxt_1630 = deref_1610 + 1;
            uintptr_t tagged_tmpcur_0 = *(uintptr_t *) field_nxt_1630;
            GibCursor tmpcur_2784 = GIB_UNTAG(tagged_tmpcur_0);
            GibCursor tmpaftercur_2785 = field_nxt_1630 + 8;
            uint16_t tmptag_2786 = GIB_GET_TAG(tagged_tmpcur_0);
            
            *(GibCursor *) soa_field_4_1609 = tmpcur_2784;
            
            GibCursor end_from_tagged_fld_redir_1637 = tmpcur_2784 +
                      tmptag_2786;
            GibCursor indr_1204[6] = {tmpcur_2769, tmpcur_2772, tmpcur_2775,
                                      tmpcur_2778, tmpcur_2781, tmpcur_2784};
            GibCursor jump_dloc_1211 = deref_dcon_var_1536 + 9;
            GibCursor aft_indir_loc_1225 = deref_1602 + 9;
            GibCursor aft_indir_loc_1226 = deref_1604 + 9;
            GibCursor aft_indir_loc_1227 = deref_1606 + 9;
            GibCursor aft_indir_loc_1228 = deref_1608 + 9;
            GibCursor aft_indir_loc_1229 = deref_1610 + 9;
            GibCursor cursor_ptr_1638[6] = {jump_dloc_1211, aft_indir_loc_1225,
                                            aft_indir_loc_1226,
                                            aft_indir_loc_1227,
                                            aft_indir_loc_1228,
                                            aft_indir_loc_1229};
            unsigned char wildcard_1224 = gib_print_symbol(2743);
            GibCursor chk_end_1643 = cursor_ptr_1532[0];
            GibBool chk_1644 = deref_dcon_var_1536 < chk_end_1643;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char call_1217 =
                           _print_MultiList(arg_99_124_201, arg_99_124_201);
            GibCursor loc_cursor_ptr_1639[6];
            
            memcpy(loc_cursor_ptr_1639, arg_99_124_201, sizeof(GibCursor [6]));
            return call_1217;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1647 = &arg_99_124_201[1];
            GibCursor deref_1648 = *soa_field_0_1647;
            GibCursor *restrict soa_field_1_1649 = &arg_99_124_201[2];
            GibCursor deref_1650 = *soa_field_1_1649;
            GibCursor *restrict soa_field_2_1651 = &arg_99_124_201[3];
            GibCursor deref_1652 = *soa_field_2_1651;
            GibCursor *restrict soa_field_3_1653 = &arg_99_124_201[4];
            GibCursor deref_1654 = *soa_field_3_1653;
            GibCursor *restrict soa_field_4_1655 = &arg_99_124_201[5];
            GibCursor deref_1656 = *soa_field_4_1655;
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) tmpcur_2758;
            GibCursor tmpcur_2787 = GIB_UNTAG(tagged_tmpcur_11);
            GibCursor tmpaftercur_2788 = tmpcur_2758 + 8;
            uint16_t tmptag_2789 = GIB_GET_TAG(tagged_tmpcur_11);
            
            *(GibCursor *) loc_685 = tmpcur_2787;
            
            GibCursor end_from_tagged_dcon_redir_1670 = tmpcur_2787 +
                      tmptag_2789;
            GibCursor field_nxt_1665 = deref_1648 + 1;
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) field_nxt_1665;
            GibCursor tmpcur_2790 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_2791 = field_nxt_1665 + 8;
            uint16_t tmptag_2792 = GIB_GET_TAG(tagged_tmpcur_10);
            
            *(GibCursor *) soa_field_0_1647 = tmpcur_2790;
            
            GibCursor end_from_tagged_fld_redir_1671 = tmpcur_2790 +
                      tmptag_2792;
            GibCursor field_nxt_1666 = deref_1650 + 1;
            uintptr_t tagged_tmpcur_9 = *(uintptr_t *) field_nxt_1666;
            GibCursor tmpcur_2793 = GIB_UNTAG(tagged_tmpcur_9);
            GibCursor tmpaftercur_2794 = field_nxt_1666 + 8;
            uint16_t tmptag_2795 = GIB_GET_TAG(tagged_tmpcur_9);
            
            *(GibCursor *) soa_field_1_1649 = tmpcur_2793;
            
            GibCursor end_from_tagged_fld_redir_1672 = tmpcur_2793 +
                      tmptag_2795;
            GibCursor field_nxt_1667 = deref_1652 + 1;
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) field_nxt_1667;
            GibCursor tmpcur_2796 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_2797 = field_nxt_1667 + 8;
            uint16_t tmptag_2798 = GIB_GET_TAG(tagged_tmpcur_8);
            
            *(GibCursor *) soa_field_2_1651 = tmpcur_2796;
            
            GibCursor end_from_tagged_fld_redir_1673 = tmpcur_2796 +
                      tmptag_2798;
            GibCursor field_nxt_1668 = deref_1654 + 1;
            uintptr_t tagged_tmpcur_7 = *(uintptr_t *) field_nxt_1668;
            GibCursor tmpcur_2799 = GIB_UNTAG(tagged_tmpcur_7);
            GibCursor tmpaftercur_2800 = field_nxt_1668 + 8;
            uint16_t tmptag_2801 = GIB_GET_TAG(tagged_tmpcur_7);
            
            *(GibCursor *) soa_field_3_1653 = tmpcur_2799;
            
            GibCursor end_from_tagged_fld_redir_1674 = tmpcur_2799 +
                      tmptag_2801;
            GibCursor field_nxt_1669 = deref_1656 + 1;
            uintptr_t tagged_tmpcur_6 = *(uintptr_t *) field_nxt_1669;
            GibCursor tmpcur_2802 = GIB_UNTAG(tagged_tmpcur_6);
            GibCursor tmpaftercur_2803 = field_nxt_1669 + 8;
            uint16_t tmptag_2804 = GIB_GET_TAG(tagged_tmpcur_6);
            
            *(GibCursor *) soa_field_4_1655 = tmpcur_2802;
            
            GibCursor end_from_tagged_fld_redir_1675 = tmpcur_2802 +
                      tmptag_2804;
            GibCursor indr_1204[6] = {tmpcur_2787, tmpcur_2790, tmpcur_2793,
                                      tmpcur_2796, tmpcur_2799, tmpcur_2802};
            unsigned char wildcard_1224 = gib_print_symbol(2742);
            GibCursor chk_end_1680 = cursor_ptr_1532[0];
            GibBool chk_1681 = deref_dcon_var_1536 < chk_end_1680;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char call_1217 =
                           _print_MultiList(arg_99_124_201, arg_99_124_201);
            GibCursor loc_cursor_ptr_1676[6];
            
            memcpy(loc_cursor_ptr_1676, arg_99_124_201, sizeof(GibCursor [6]));
            return call_1217;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2757");
            exit(1);
        }
    }
}
unsigned char add1MultiList(GibCursor cursor_ptr_1685[6],
                            GibCursor cursor_ptr_1684[6],
                            GibCursor cursor_ptr_1686[6],
                            GibCursor xs_29_147_224[6])
{
    GibCursor *end_r_718 = &cursor_ptr_1684[3];
    GibCursor *end_r_715 = &cursor_ptr_1684[0];
    GibCursor *end_r_717 = &cursor_ptr_1684[2];
    GibCursor *end_r_720 = &cursor_ptr_1684[5];
    GibCursor *end_r_716 = &cursor_ptr_1684[1];
    GibCursor *end_r_719 = &cursor_ptr_1684[4];
    GibCursor *restrict loc_IntTy_706 = &cursor_ptr_1686[3];
    GibCursor deref_1688 = *loc_IntTy_706;
    GibCursor cpy_1689[6];
    
    memcpy(cpy_1689, cursor_ptr_1686, sizeof(GibCursor [6]));
    
    GibCursor *restrict loc_FloatTy_708 = &cursor_ptr_1686[5];
    GibCursor deref_1690 = *loc_FloatTy_708;
    GibCursor *restrict loc_IntTy_705 = &cursor_ptr_1686[2];
    GibCursor deref_1691 = *loc_IntTy_705;
    GibCursor *restrict loc_IntTy_707 = &cursor_ptr_1686[4];
    GibCursor deref_1692 = *loc_IntTy_707;
    GibCursor *restrict loc_IntTy_704 = &cursor_ptr_1686[1];
    GibCursor deref_1693 = *loc_IntTy_704;
    GibCursor *restrict loc_703 = &cursor_ptr_1686[0];
    GibCursor deref_1694 = *end_r_720;
    GibCursor deref_1695 = *loc_FloatTy_708;
    GibCursor deref_1696 = *end_r_719;
    GibCursor deref_1697 = *loc_IntTy_707;
    GibCursor deref_1698 = *end_r_718;
    GibCursor deref_1699 = *loc_IntTy_706;
    GibCursor deref_1700 = *end_r_717;
    GibCursor deref_1701 = *loc_IntTy_705;
    GibCursor deref_1702 = *end_r_716;
    GibCursor deref_1703 = *loc_IntTy_704;
    GibCursor deref_1704 = *end_r_715;
    GibCursor deref_1705 = *loc_703;
    
    if (deref_1695 + 13 > deref_1694 || (deref_1697 + 17 > deref_1696 ||
                                         (deref_1699 + 17 > deref_1698 ||
                                          (deref_1701 + 17 > deref_1700 ||
                                           (deref_1703 + 17 > deref_1702 ||
                                            deref_1705 + 58 > deref_1704))))) {
        gib_grow_region(loc_FloatTy_708, end_r_720);
        gib_grow_region(loc_IntTy_707, end_r_719);
        gib_grow_region(loc_IntTy_706, end_r_718);
        gib_grow_region(loc_IntTy_705, end_r_717);
        gib_grow_region(loc_IntTy_704, end_r_716);
        gib_grow_region(loc_703, end_r_715);
        deref_1695 = *loc_FloatTy_708;
        deref_1697 = *loc_IntTy_707;
        deref_1699 = *loc_IntTy_706;
        deref_1701 = *loc_IntTy_705;
        deref_1703 = *loc_IntTy_704;
        deref_1705 = *loc_703;
    }
    
    GibCursor *end_r_709 = &cursor_ptr_1685[0];
    GibCursor *end_r_710 = &cursor_ptr_1685[1];
    GibCursor *end_r_711 = &cursor_ptr_1685[2];
    GibCursor *end_r_712 = &cursor_ptr_1685[3];
    GibCursor *end_r_713 = &cursor_ptr_1685[4];
    GibCursor *end_r_714 = &cursor_ptr_1685[5];
    GibCursor *restrict loc_697 = &xs_29_147_224[0];
    GibCursor deref_dcon_var_1709 = *loc_697;
    GibPackedTag tmpval_2806 = *(GibPackedTag *) deref_dcon_var_1709;
    GibCursor tmpcur_2807 = deref_dcon_var_1709 + 1;
    
    
  switch_2854:
    ;
    switch (tmpval_2806) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_1711 = &xs_29_147_224[1];
            GibCursor deref_1712 = *soa_field_0_1711;
            GibCursor *restrict soa_field_1_1713 = &xs_29_147_224[2];
            GibCursor deref_1714 = *soa_field_1_1713;
            GibCursor *restrict soa_field_2_1715 = &xs_29_147_224[3];
            GibCursor deref_1716 = *soa_field_2_1715;
            GibCursor *restrict soa_field_3_1717 = &xs_29_147_224[4];
            GibCursor deref_1718 = *soa_field_3_1717;
            GibCursor *restrict soa_field_4_1719 = &xs_29_147_224[5];
            GibCursor deref_1720 = *soa_field_4_1719;
            
            *loc_697 += 1;
            
            GibCursor jump_floc_loc_1109 = deref_1712 + 0;
            GibCursor jump_floc_loc_1110 = deref_1714 + 0;
            GibCursor jump_floc_loc_1111 = deref_1716 + 0;
            GibCursor jump_floc_loc_1112 = deref_1718 + 0;
            GibCursor jump_floc_loc_1113 = deref_1720 + 0;
            GibCursor cursor_ptr_1723[6] = {tmpcur_2807, jump_floc_loc_1109,
                                            jump_floc_loc_1110,
                                            jump_floc_loc_1111,
                                            jump_floc_loc_1112,
                                            jump_floc_loc_1113};
            
            *(GibPackedTag *) deref_1705 = 1;
            
            GibCursor writetag_1730 = deref_1705 + 1;
            GibCursor after_tag_1731 = deref_1705 + 1;
            
            *loc_703 += 1;
            
            GibCursor aft_soa_loc_1736[6] = {after_tag_1731, deref_1703,
                                             deref_1701, deref_1699, deref_1697,
                                             deref_1695};
            GibCursor end_taildc_1114[6];
            
            memcpy(end_taildc_1114, cursor_ptr_1686, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1741 = &xs_29_147_224[1];
            GibCursor deref_1742 = *soa_field_0_1741;
            GibCursor *restrict soa_field_1_1743 = &xs_29_147_224[2];
            GibCursor deref_1744 = *soa_field_1_1743;
            GibCursor *restrict soa_field_2_1745 = &xs_29_147_224[3];
            GibCursor deref_1746 = *soa_field_2_1745;
            GibCursor *restrict soa_field_3_1747 = &xs_29_147_224[4];
            GibCursor deref_1748 = *soa_field_3_1747;
            GibCursor *restrict soa_field_4_1749 = &xs_29_147_224[5];
            GibCursor deref_1750 = *soa_field_4_1749;
            GibInt tmpval_2808 = *(GibInt *) deref_1742;
            GibCursor tmpcur_2809 = deref_1742 + sizeof(GibInt);
            
            *soa_field_0_1741 += 8;
            
            GibInt tmpval_2810 = *(GibInt *) deref_1744;
            GibCursor tmpcur_2811 = deref_1744 + sizeof(GibInt);
            
            *soa_field_1_1743 += 8;
            
            GibInt tmpval_2812 = *(GibInt *) deref_1746;
            GibCursor tmpcur_2813 = deref_1746 + sizeof(GibInt);
            
            *soa_field_2_1745 += 8;
            
            GibInt tmpval_2814 = *(GibInt *) deref_1748;
            GibCursor tmpcur_2815 = deref_1748 + sizeof(GibInt);
            
            *soa_field_3_1747 += 8;
            
            GibFloat tmpval_2816 = *(GibFloat *) deref_1750;
            GibCursor tmpcur_2817 = deref_1750 + sizeof(GibFloat);
            
            *soa_field_4_1749 += 4;
            
            GibCursor cursor_ptr_1707[6] = {tmpcur_2807, tmpcur_2809,
                                            tmpcur_2811, tmpcur_2813,
                                            tmpcur_2815, tmpcur_2817};
            
            *loc_697 += 1;
            
            GibCursor jumpf_floc_loc_1116 = deref_1742 + 8;
            GibCursor jumpf_floc_loc_1117 = deref_1744 + 8;
            GibCursor jumpf_floc_loc_1118 = deref_1746 + 8;
            GibCursor jumpf_floc_loc_1119 = deref_1748 + 8;
            GibCursor jumpf_floc_loc_1120 = deref_1750 + 4;
            GibInt fltPkd_188_231 = tmpval_2808 + 1;
            GibInt fltPkd_189_232 = tmpval_2810 + 1;
            GibInt fltPkd_190_233 = tmpval_2812 + 1;
            GibInt fltPkd_191_234 = tmpval_2814 + 1;
            GibCursor new_dloc_908 = deref_1705 + 1;
            
            *loc_703 += 1;
            
            GibCursor new_floc_loc_909 = deref_1703 + 8;
            
            *loc_IntTy_704 += 8;
            
            GibCursor new_floc_loc_910 = deref_1701 + 8;
            
            *loc_IntTy_705 += 8;
            
            GibCursor new_floc_loc_912 = deref_1697 + 8;
            
            *loc_IntTy_707 += 8;
            
            GibCursor new_floc_loc_913 = deref_1695 + 4;
            
            *loc_FloatTy_708 += 4;
            
            GibCursor new_floc_loc_911 = deref_1699 + 8;
            
            *loc_IntTy_706 += 8;
            
            GibCursor cursor_ptr_1772[6] = {new_dloc_908, new_floc_loc_909,
                                            new_floc_loc_910, new_floc_loc_911,
                                            new_floc_loc_912, new_floc_loc_913};
            
            *(GibPackedTag *) deref_1705 = 0;
            
            GibCursor writetag_1817 = deref_1705 + 1;
            GibCursor after_tag_1818 = deref_1705 + 1;
            
            *(GibInt *) deref_1703 = fltPkd_188_231;
            
            GibCursor writecur_1822 = deref_1703 + sizeof(GibInt);
            
            *(GibInt *) deref_1701 = fltPkd_189_232;
            
            GibCursor writecur_1824 = deref_1701 + sizeof(GibInt);
            
            *(GibInt *) deref_1699 = fltPkd_190_233;
            
            GibCursor writecur_1826 = deref_1699 + sizeof(GibInt);
            
            *(GibInt *) deref_1697 = fltPkd_191_234;
            
            GibCursor writecur_1828 = deref_1697 + sizeof(GibInt);
            
            *(GibFloat *) deref_1695 = tmpval_2816;
            
            GibCursor writecur_1830 = deref_1695 + sizeof(GibFloat);
            GibCursor chk_loc_1812 = cursor_ptr_1707[0];
            GibCursor chk_end_1813 = cursor_ptr_1685[0];
            GibBool chk_1814 = chk_loc_1812 < chk_end_1813;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1809 = cursor_ptr_1707[1];
            GibCursor chk_end_1810 = cursor_ptr_1685[1];
            GibBool chk_1811 = chk_loc_1809 < chk_end_1810;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1806 = cursor_ptr_1707[2];
            GibCursor chk_end_1807 = cursor_ptr_1685[2];
            GibBool chk_1808 = chk_loc_1806 < chk_end_1807;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1803 = cursor_ptr_1707[3];
            GibCursor chk_end_1804 = cursor_ptr_1685[3];
            GibBool chk_1805 = chk_loc_1803 < chk_end_1804;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1800 = cursor_ptr_1707[4];
            GibCursor chk_end_1801 = cursor_ptr_1685[4];
            GibBool chk_1802 = chk_loc_1800 < chk_end_1801;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1797 = cursor_ptr_1707[5];
            GibCursor chk_end_1798 = cursor_ptr_1685[5];
            GibBool chk_1799 = chk_loc_1797 < chk_end_1798;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1794 = cursor_ptr_1772[0];
            GibCursor chk_end_1795 = cursor_ptr_1684[0];
            GibBool chk_1796 = chk_loc_1794 < chk_end_1795;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1791 = cursor_ptr_1772[1];
            GibCursor chk_end_1792 = cursor_ptr_1684[1];
            GibBool chk_1793 = chk_loc_1791 < chk_end_1792;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1788 = cursor_ptr_1772[2];
            GibCursor chk_end_1789 = cursor_ptr_1684[2];
            GibBool chk_1790 = chk_loc_1788 < chk_end_1789;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1785 = cursor_ptr_1772[3];
            GibCursor chk_end_1786 = cursor_ptr_1684[3];
            GibBool chk_1787 = chk_loc_1785 < chk_end_1786;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1782 = cursor_ptr_1772[4];
            GibCursor chk_end_1783 = cursor_ptr_1684[4];
            GibBool chk_1784 = chk_loc_1782 < chk_end_1783;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1779 = cursor_ptr_1772[5];
            GibCursor chk_end_1780 = cursor_ptr_1684[5];
            GibBool chk_1781 = chk_loc_1779 < chk_end_1780;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1815 =
                           add1MultiList(cursor_ptr_1685, cursor_ptr_1684, cursor_ptr_1686, xs_29_147_224);
            GibCursor end_fltPkd_192_235[6];
            
            memcpy(end_fltPkd_192_235, cursor_ptr_1686, sizeof(GibCursor [6]));
            
            GibCursor loc_cursor_ptr_1773[6];
            
            memcpy(loc_cursor_ptr_1773, xs_29_147_224, sizeof(GibCursor [6]));
            
            GibCursor end_taildc_1127[6];
            
            memcpy(end_taildc_1127, cursor_ptr_1686, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1837 = &xs_29_147_224[1];
            GibCursor deref_1838 = *soa_field_0_1837;
            GibCursor *restrict soa_field_1_1839 = &xs_29_147_224[2];
            GibCursor deref_1840 = *soa_field_1_1839;
            GibCursor *restrict soa_field_2_1841 = &xs_29_147_224[3];
            GibCursor deref_1842 = *soa_field_2_1841;
            GibCursor *restrict soa_field_3_1843 = &xs_29_147_224[4];
            GibCursor deref_1844 = *soa_field_3_1843;
            GibCursor *restrict soa_field_4_1845 = &xs_29_147_224[5];
            GibCursor deref_1846 = *soa_field_4_1845;
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_2807;
            GibCursor tmpcur_2818 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_2819 = tmpcur_2807 + 8;
            uint16_t tmptag_2820 = GIB_GET_TAG(tagged_tmpcur_17);
            
            *(GibCursor *) loc_697 = tmpcur_2818;
            
            GibCursor end_from_tagged_dcon_redir_1868 = tmpcur_2818 +
                      tmptag_2820;
            GibCursor field_nxt_1862 = deref_1838 + 1;
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) field_nxt_1862;
            GibCursor tmpcur_2821 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_2822 = field_nxt_1862 + 8;
            uint16_t tmptag_2823 = GIB_GET_TAG(tagged_tmpcur_16);
            
            *(GibCursor *) soa_field_0_1837 = tmpcur_2821;
            
            GibCursor end_from_tagged_fld_redir_1869 = tmpcur_2821 +
                      tmptag_2823;
            GibCursor field_nxt_1863 = deref_1840 + 1;
            uintptr_t tagged_tmpcur_15 = *(uintptr_t *) field_nxt_1863;
            GibCursor tmpcur_2824 = GIB_UNTAG(tagged_tmpcur_15);
            GibCursor tmpaftercur_2825 = field_nxt_1863 + 8;
            uint16_t tmptag_2826 = GIB_GET_TAG(tagged_tmpcur_15);
            
            *(GibCursor *) soa_field_1_1839 = tmpcur_2824;
            
            GibCursor end_from_tagged_fld_redir_1870 = tmpcur_2824 +
                      tmptag_2826;
            GibCursor field_nxt_1864 = deref_1842 + 1;
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) field_nxt_1864;
            GibCursor tmpcur_2827 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_2828 = field_nxt_1864 + 8;
            uint16_t tmptag_2829 = GIB_GET_TAG(tagged_tmpcur_14);
            
            *(GibCursor *) soa_field_2_1841 = tmpcur_2827;
            
            GibCursor end_from_tagged_fld_redir_1871 = tmpcur_2827 +
                      tmptag_2829;
            GibCursor field_nxt_1865 = deref_1844 + 1;
            uintptr_t tagged_tmpcur_13 = *(uintptr_t *) field_nxt_1865;
            GibCursor tmpcur_2830 = GIB_UNTAG(tagged_tmpcur_13);
            GibCursor tmpaftercur_2831 = field_nxt_1865 + 8;
            uint16_t tmptag_2832 = GIB_GET_TAG(tagged_tmpcur_13);
            
            *(GibCursor *) soa_field_3_1843 = tmpcur_2830;
            
            GibCursor end_from_tagged_fld_redir_1872 = tmpcur_2830 +
                      tmptag_2832;
            GibCursor field_nxt_1866 = deref_1846 + 1;
            uintptr_t tagged_tmpcur_12 = *(uintptr_t *) field_nxt_1866;
            GibCursor tmpcur_2833 = GIB_UNTAG(tagged_tmpcur_12);
            GibCursor tmpaftercur_2834 = field_nxt_1866 + 8;
            uint16_t tmptag_2835 = GIB_GET_TAG(tagged_tmpcur_12);
            
            *(GibCursor *) soa_field_4_1845 = tmpcur_2833;
            
            GibCursor end_from_tagged_fld_redir_1873 = tmpcur_2833 +
                      tmptag_2835;
            GibCursor indr_1230[6] = {tmpcur_2818, tmpcur_2821, tmpcur_2824,
                                      tmpcur_2827, tmpcur_2830, tmpcur_2833};
            GibCursor jump_dloc_1237 = deref_dcon_var_1709 + 9;
            GibCursor aft_indir_loc_1251 = deref_1838 + 9;
            GibCursor aft_indir_loc_1252 = deref_1840 + 9;
            GibCursor aft_indir_loc_1253 = deref_1842 + 9;
            GibCursor aft_indir_loc_1254 = deref_1844 + 9;
            GibCursor aft_indir_loc_1255 = deref_1846 + 9;
            GibCursor cursor_ptr_1874[6] = {jump_dloc_1237, aft_indir_loc_1251,
                                            aft_indir_loc_1252,
                                            aft_indir_loc_1253,
                                            aft_indir_loc_1254,
                                            aft_indir_loc_1255};
            GibCursor chk_end_1899 = cursor_ptr_1685[0];
            GibBool chk_1900 = deref_dcon_var_1709 < chk_end_1899;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1896 = cursor_ptr_1686[0];
            GibCursor chk_end_1897 = cursor_ptr_1684[0];
            GibBool chk_1898 = chk_loc_1896 < chk_end_1897;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1893 = cursor_ptr_1686[1];
            GibCursor chk_end_1894 = cursor_ptr_1684[1];
            GibBool chk_1895 = chk_loc_1893 < chk_end_1894;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1890 = cursor_ptr_1686[2];
            GibCursor chk_end_1891 = cursor_ptr_1684[2];
            GibBool chk_1892 = chk_loc_1890 < chk_end_1891;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1887 = cursor_ptr_1686[3];
            GibCursor chk_end_1888 = cursor_ptr_1684[3];
            GibBool chk_1889 = chk_loc_1887 < chk_end_1888;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1884 = cursor_ptr_1686[4];
            GibCursor chk_end_1885 = cursor_ptr_1684[4];
            GibBool chk_1886 = chk_loc_1884 < chk_end_1885;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1881 = cursor_ptr_1686[5];
            GibCursor chk_end_1882 = cursor_ptr_1684[5];
            GibBool chk_1883 = chk_loc_1881 < chk_end_1882;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1901 =
                           add1MultiList(xs_29_147_224, cursor_ptr_1684, cursor_ptr_1686, xs_29_147_224);
            GibCursor end_call_1243[6];
            
            memcpy(end_call_1243, cursor_ptr_1686, sizeof(GibCursor [6]));
            
            GibCursor loc_cursor_ptr_1875[6];
            
            memcpy(loc_cursor_ptr_1875, xs_29_147_224, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_1904 = &xs_29_147_224[1];
            GibCursor deref_1905 = *soa_field_0_1904;
            GibCursor *restrict soa_field_1_1906 = &xs_29_147_224[2];
            GibCursor deref_1907 = *soa_field_1_1906;
            GibCursor *restrict soa_field_2_1908 = &xs_29_147_224[3];
            GibCursor deref_1909 = *soa_field_2_1908;
            GibCursor *restrict soa_field_3_1910 = &xs_29_147_224[4];
            GibCursor deref_1911 = *soa_field_3_1910;
            GibCursor *restrict soa_field_4_1912 = &xs_29_147_224[5];
            GibCursor deref_1913 = *soa_field_4_1912;
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) tmpcur_2807;
            GibCursor tmpcur_2836 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_2837 = tmpcur_2807 + 8;
            uint16_t tmptag_2838 = GIB_GET_TAG(tagged_tmpcur_23);
            
            *(GibCursor *) loc_697 = tmpcur_2836;
            
            GibCursor end_from_tagged_dcon_redir_1927 = tmpcur_2836 +
                      tmptag_2838;
            GibCursor field_nxt_1922 = deref_1905 + 1;
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) field_nxt_1922;
            GibCursor tmpcur_2839 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_2840 = field_nxt_1922 + 8;
            uint16_t tmptag_2841 = GIB_GET_TAG(tagged_tmpcur_22);
            
            *(GibCursor *) soa_field_0_1904 = tmpcur_2839;
            
            GibCursor end_from_tagged_fld_redir_1928 = tmpcur_2839 +
                      tmptag_2841;
            GibCursor field_nxt_1923 = deref_1907 + 1;
            uintptr_t tagged_tmpcur_21 = *(uintptr_t *) field_nxt_1923;
            GibCursor tmpcur_2842 = GIB_UNTAG(tagged_tmpcur_21);
            GibCursor tmpaftercur_2843 = field_nxt_1923 + 8;
            uint16_t tmptag_2844 = GIB_GET_TAG(tagged_tmpcur_21);
            
            *(GibCursor *) soa_field_1_1906 = tmpcur_2842;
            
            GibCursor end_from_tagged_fld_redir_1929 = tmpcur_2842 +
                      tmptag_2844;
            GibCursor field_nxt_1924 = deref_1909 + 1;
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) field_nxt_1924;
            GibCursor tmpcur_2845 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_2846 = field_nxt_1924 + 8;
            uint16_t tmptag_2847 = GIB_GET_TAG(tagged_tmpcur_20);
            
            *(GibCursor *) soa_field_2_1908 = tmpcur_2845;
            
            GibCursor end_from_tagged_fld_redir_1930 = tmpcur_2845 +
                      tmptag_2847;
            GibCursor field_nxt_1925 = deref_1911 + 1;
            uintptr_t tagged_tmpcur_19 = *(uintptr_t *) field_nxt_1925;
            GibCursor tmpcur_2848 = GIB_UNTAG(tagged_tmpcur_19);
            GibCursor tmpaftercur_2849 = field_nxt_1925 + 8;
            uint16_t tmptag_2850 = GIB_GET_TAG(tagged_tmpcur_19);
            
            *(GibCursor *) soa_field_3_1910 = tmpcur_2848;
            
            GibCursor end_from_tagged_fld_redir_1931 = tmpcur_2848 +
                      tmptag_2850;
            GibCursor field_nxt_1926 = deref_1913 + 1;
            uintptr_t tagged_tmpcur_18 = *(uintptr_t *) field_nxt_1926;
            GibCursor tmpcur_2851 = GIB_UNTAG(tagged_tmpcur_18);
            GibCursor tmpaftercur_2852 = field_nxt_1926 + 8;
            uint16_t tmptag_2853 = GIB_GET_TAG(tagged_tmpcur_18);
            
            *(GibCursor *) soa_field_4_1912 = tmpcur_2851;
            
            GibCursor end_from_tagged_fld_redir_1932 = tmpcur_2851 +
                      tmptag_2853;
            GibCursor indr_1230[6] = {tmpcur_2836, tmpcur_2839, tmpcur_2842,
                                      tmpcur_2845, tmpcur_2848, tmpcur_2851};
            GibCursor copy_dloc_1256 = deref_1705 + 0;
            
            *loc_703 += 0;
            
            GibCursor copy_floc_loc_1261 = deref_1695 + 0;
            
            *loc_FloatTy_708 += 0;
            
            GibCursor copy_floc_loc_1260 = deref_1697 + 0;
            
            *loc_IntTy_707 += 0;
            
            GibCursor copy_floc_loc_1259 = deref_1699 + 0;
            
            *loc_IntTy_706 += 0;
            
            GibCursor copy_floc_loc_1258 = deref_1701 + 0;
            
            *loc_IntTy_705 += 0;
            
            GibCursor copy_floc_loc_1257 = deref_1703 + 0;
            
            *loc_IntTy_704 += 0;
            
            GibCursor cursor_ptr_1939[6] = {copy_dloc_1256, copy_floc_loc_1257,
                                            copy_floc_loc_1258,
                                            copy_floc_loc_1259,
                                            copy_floc_loc_1260,
                                            copy_floc_loc_1261};
            GibCursor chk_end_1964 = cursor_ptr_1685[0];
            GibBool chk_1965 = deref_dcon_var_1709 < chk_end_1964;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1961 = cursor_ptr_1939[0];
            GibCursor chk_end_1962 = cursor_ptr_1684[0];
            GibBool chk_1963 = chk_loc_1961 < chk_end_1962;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1958 = cursor_ptr_1939[1];
            GibCursor chk_end_1959 = cursor_ptr_1684[1];
            GibBool chk_1960 = chk_loc_1958 < chk_end_1959;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1955 = cursor_ptr_1939[2];
            GibCursor chk_end_1956 = cursor_ptr_1684[2];
            GibBool chk_1957 = chk_loc_1955 < chk_end_1956;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1952 = cursor_ptr_1939[3];
            GibCursor chk_end_1953 = cursor_ptr_1684[3];
            GibBool chk_1954 = chk_loc_1952 < chk_end_1953;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1949 = cursor_ptr_1939[4];
            GibCursor chk_end_1950 = cursor_ptr_1684[4];
            GibBool chk_1951 = chk_loc_1949 < chk_end_1950;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_1946 = cursor_ptr_1939[5];
            GibCursor chk_end_1947 = cursor_ptr_1684[5];
            GibBool chk_1948 = chk_loc_1946 < chk_end_1947;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_1966 =
                           add1MultiList(xs_29_147_224, cursor_ptr_1684, cursor_ptr_1686, xs_29_147_224);
            GibCursor end_call_1243[6];
            
            memcpy(end_call_1243, cursor_ptr_1686, sizeof(GibCursor [6]));
            
            GibCursor loc_cursor_ptr_1940[6];
            
            memcpy(loc_cursor_ptr_1940, xs_29_147_224, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2806");
            exit(1);
        }
    }
}
unsigned char _copy_MultiList(GibCursor cursor_ptr_1970[6],
                              GibCursor cursor_ptr_1969[6],
                              GibCursor cursor_ptr_1971[6],
                              GibCursor arg_73_154_236[6])
{
    GibCursor *end_r_744 = &cursor_ptr_1969[5];
    GibCursor *end_r_743 = &cursor_ptr_1969[4];
    GibCursor *end_r_740 = &cursor_ptr_1969[1];
    GibCursor *end_r_741 = &cursor_ptr_1969[2];
    GibCursor *end_r_739 = &cursor_ptr_1969[0];
    GibCursor *end_r_742 = &cursor_ptr_1969[3];
    GibCursor *restrict loc_IntTy_730 = &cursor_ptr_1971[3];
    GibCursor deref_1973 = *loc_IntTy_730;
    GibCursor cpy_1974[6];
    
    memcpy(cpy_1974, cursor_ptr_1971, sizeof(GibCursor [6]));
    
    GibCursor *restrict loc_IntTy_728 = &cursor_ptr_1971[1];
    GibCursor deref_1975 = *loc_IntTy_728;
    GibCursor *restrict loc_727 = &cursor_ptr_1971[0];
    GibCursor *restrict loc_IntTy_731 = &cursor_ptr_1971[4];
    GibCursor deref_1976 = *loc_IntTy_731;
    GibCursor *restrict loc_FloatTy_732 = &cursor_ptr_1971[5];
    GibCursor deref_1977 = *loc_FloatTy_732;
    GibCursor *restrict loc_IntTy_729 = &cursor_ptr_1971[2];
    GibCursor deref_1978 = *loc_IntTy_729;
    GibCursor deref_1979 = *end_r_744;
    GibCursor deref_1980 = *loc_FloatTy_732;
    GibCursor deref_1981 = *end_r_743;
    GibCursor deref_1982 = *loc_IntTy_731;
    GibCursor deref_1983 = *end_r_742;
    GibCursor deref_1984 = *loc_IntTy_730;
    GibCursor deref_1985 = *end_r_741;
    GibCursor deref_1986 = *loc_IntTy_729;
    GibCursor deref_1987 = *end_r_740;
    GibCursor deref_1988 = *loc_IntTy_728;
    GibCursor deref_1989 = *end_r_739;
    GibCursor deref_1990 = *loc_727;
    
    if (deref_1980 + 13 > deref_1979 || (deref_1982 + 17 > deref_1981 ||
                                         (deref_1984 + 17 > deref_1983 ||
                                          (deref_1986 + 17 > deref_1985 ||
                                           (deref_1988 + 17 > deref_1987 ||
                                            deref_1990 + 58 > deref_1989))))) {
        gib_grow_region(loc_FloatTy_732, end_r_744);
        gib_grow_region(loc_IntTy_731, end_r_743);
        gib_grow_region(loc_IntTy_730, end_r_742);
        gib_grow_region(loc_IntTy_729, end_r_741);
        gib_grow_region(loc_IntTy_728, end_r_740);
        gib_grow_region(loc_727, end_r_739);
        deref_1980 = *loc_FloatTy_732;
        deref_1982 = *loc_IntTy_731;
        deref_1984 = *loc_IntTy_730;
        deref_1986 = *loc_IntTy_729;
        deref_1988 = *loc_IntTy_728;
        deref_1990 = *loc_727;
    }
    
    GibCursor *end_r_733 = &cursor_ptr_1970[0];
    GibCursor *end_r_734 = &cursor_ptr_1970[1];
    GibCursor *end_r_735 = &cursor_ptr_1970[2];
    GibCursor *end_r_736 = &cursor_ptr_1970[3];
    GibCursor *end_r_737 = &cursor_ptr_1970[4];
    GibCursor *end_r_738 = &cursor_ptr_1970[5];
    GibCursor *restrict loc_721 = &arg_73_154_236[0];
    GibCursor deref_dcon_var_1994 = *loc_721;
    GibPackedTag tmpval_2855 = *(GibPackedTag *) deref_dcon_var_1994;
    GibCursor tmpcur_2856 = deref_dcon_var_1994 + 1;
    
    
  switch_2903:
    ;
    switch (tmpval_2855) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_1996 = &arg_73_154_236[1];
            GibCursor deref_1997 = *soa_field_0_1996;
            GibCursor *restrict soa_field_1_1998 = &arg_73_154_236[2];
            GibCursor deref_1999 = *soa_field_1_1998;
            GibCursor *restrict soa_field_2_2000 = &arg_73_154_236[3];
            GibCursor deref_2001 = *soa_field_2_2000;
            GibCursor *restrict soa_field_3_2002 = &arg_73_154_236[4];
            GibCursor deref_2003 = *soa_field_3_2002;
            GibCursor *restrict soa_field_4_2004 = &arg_73_154_236[5];
            GibCursor deref_2005 = *soa_field_4_2004;
            GibInt tmpval_2857 = *(GibInt *) deref_1997;
            GibCursor tmpcur_2858 = deref_1997 + sizeof(GibInt);
            
            *soa_field_0_1996 += 8;
            
            GibInt tmpval_2859 = *(GibInt *) deref_1999;
            GibCursor tmpcur_2860 = deref_1999 + sizeof(GibInt);
            
            *soa_field_1_1998 += 8;
            
            GibInt tmpval_2861 = *(GibInt *) deref_2001;
            GibCursor tmpcur_2862 = deref_2001 + sizeof(GibInt);
            
            *soa_field_2_2000 += 8;
            
            GibInt tmpval_2863 = *(GibInt *) deref_2003;
            GibCursor tmpcur_2864 = deref_2003 + sizeof(GibInt);
            
            *soa_field_3_2002 += 8;
            
            GibFloat tmpval_2865 = *(GibFloat *) deref_2005;
            GibCursor tmpcur_2866 = deref_2005 + sizeof(GibFloat);
            
            *soa_field_4_2004 += 4;
            
            GibCursor cursor_ptr_1992[6] = {tmpcur_2856, tmpcur_2858,
                                            tmpcur_2860, tmpcur_2862,
                                            tmpcur_2864, tmpcur_2866};
            
            *loc_721 += 1;
            
            GibCursor jumpf_floc_loc_1129 = deref_1997 + 8;
            GibCursor jumpf_floc_loc_1130 = deref_1999 + 8;
            GibCursor jumpf_floc_loc_1131 = deref_2001 + 8;
            GibCursor jumpf_floc_loc_1132 = deref_2003 + 8;
            GibCursor jumpf_floc_loc_1133 = deref_2005 + 4;
            GibCursor new_floc_loc_968 = deref_1986 + 8;
            
            *loc_IntTy_729 += 8;
            
            GibCursor new_floc_loc_971 = deref_1980 + 4;
            
            *loc_FloatTy_732 += 4;
            
            GibCursor new_floc_loc_970 = deref_1982 + 8;
            
            *loc_IntTy_731 += 8;
            
            GibCursor new_dloc_966 = deref_1990 + 1;
            
            *loc_727 += 1;
            
            GibCursor new_floc_loc_967 = deref_1988 + 8;
            
            *loc_IntTy_728 += 8;
            
            GibCursor new_floc_loc_969 = deref_1984 + 8;
            
            *loc_IntTy_730 += 8;
            
            GibCursor cursor_ptr_2027[6] = {new_dloc_966, new_floc_loc_967,
                                            new_floc_loc_968, new_floc_loc_969,
                                            new_floc_loc_970, new_floc_loc_971};
            
            *(GibPackedTag *) deref_1990 = 0;
            
            GibCursor writetag_2072 = deref_1990 + 1;
            GibCursor after_tag_2073 = deref_1990 + 1;
            
            *(GibInt *) deref_1988 = tmpval_2857;
            
            GibCursor writecur_2077 = deref_1988 + sizeof(GibInt);
            
            *(GibInt *) deref_1986 = tmpval_2859;
            
            GibCursor writecur_2079 = deref_1986 + sizeof(GibInt);
            
            *(GibInt *) deref_1984 = tmpval_2861;
            
            GibCursor writecur_2081 = deref_1984 + sizeof(GibInt);
            
            *(GibInt *) deref_1982 = tmpval_2863;
            
            GibCursor writecur_2083 = deref_1982 + sizeof(GibInt);
            
            *(GibFloat *) deref_1980 = tmpval_2865;
            
            GibCursor writecur_2085 = deref_1980 + sizeof(GibFloat);
            GibCursor chk_loc_2067 = cursor_ptr_1992[0];
            GibCursor chk_end_2068 = cursor_ptr_1970[0];
            GibBool chk_2069 = chk_loc_2067 < chk_end_2068;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2064 = cursor_ptr_1992[1];
            GibCursor chk_end_2065 = cursor_ptr_1970[1];
            GibBool chk_2066 = chk_loc_2064 < chk_end_2065;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2061 = cursor_ptr_1992[2];
            GibCursor chk_end_2062 = cursor_ptr_1970[2];
            GibBool chk_2063 = chk_loc_2061 < chk_end_2062;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2058 = cursor_ptr_1992[3];
            GibCursor chk_end_2059 = cursor_ptr_1970[3];
            GibBool chk_2060 = chk_loc_2058 < chk_end_2059;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2055 = cursor_ptr_1992[4];
            GibCursor chk_end_2056 = cursor_ptr_1970[4];
            GibBool chk_2057 = chk_loc_2055 < chk_end_2056;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2052 = cursor_ptr_1992[5];
            GibCursor chk_end_2053 = cursor_ptr_1970[5];
            GibBool chk_2054 = chk_loc_2052 < chk_end_2053;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2049 = cursor_ptr_2027[0];
            GibCursor chk_end_2050 = cursor_ptr_1969[0];
            GibBool chk_2051 = chk_loc_2049 < chk_end_2050;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2046 = cursor_ptr_2027[1];
            GibCursor chk_end_2047 = cursor_ptr_1969[1];
            GibBool chk_2048 = chk_loc_2046 < chk_end_2047;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2043 = cursor_ptr_2027[2];
            GibCursor chk_end_2044 = cursor_ptr_1969[2];
            GibBool chk_2045 = chk_loc_2043 < chk_end_2044;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2040 = cursor_ptr_2027[3];
            GibCursor chk_end_2041 = cursor_ptr_1969[3];
            GibBool chk_2042 = chk_loc_2040 < chk_end_2041;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2037 = cursor_ptr_2027[4];
            GibCursor chk_end_2038 = cursor_ptr_1969[4];
            GibBool chk_2039 = chk_loc_2037 < chk_end_2038;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2034 = cursor_ptr_2027[5];
            GibCursor chk_end_2035 = cursor_ptr_1969[5];
            GibBool chk_2036 = chk_loc_2034 < chk_end_2035;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_2070 =
                           _copy_MultiList(cursor_ptr_1970, cursor_ptr_1969, cursor_ptr_1971, arg_73_154_236);
            GibCursor end_y_85_166_248[6];
            
            memcpy(end_y_85_166_248, cursor_ptr_1971, sizeof(GibCursor [6]));
            
            GibCursor loc_cursor_ptr_2028[6];
            
            memcpy(loc_cursor_ptr_2028, arg_73_154_236, sizeof(GibCursor [6]));
            
            GibCursor end_taildc_1140[6];
            
            memcpy(end_taildc_1140, cursor_ptr_1971, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_2092 = &arg_73_154_236[1];
            GibCursor deref_2093 = *soa_field_0_2092;
            GibCursor *restrict soa_field_1_2094 = &arg_73_154_236[2];
            GibCursor deref_2095 = *soa_field_1_2094;
            GibCursor *restrict soa_field_2_2096 = &arg_73_154_236[3];
            GibCursor deref_2097 = *soa_field_2_2096;
            GibCursor *restrict soa_field_3_2098 = &arg_73_154_236[4];
            GibCursor deref_2099 = *soa_field_3_2098;
            GibCursor *restrict soa_field_4_2100 = &arg_73_154_236[5];
            GibCursor deref_2101 = *soa_field_4_2100;
            
            *loc_721 += 1;
            
            GibCursor jump_floc_loc_1142 = deref_2093 + 0;
            GibCursor jump_floc_loc_1143 = deref_2095 + 0;
            GibCursor jump_floc_loc_1144 = deref_2097 + 0;
            GibCursor jump_floc_loc_1145 = deref_2099 + 0;
            GibCursor jump_floc_loc_1146 = deref_2101 + 0;
            GibCursor cursor_ptr_2104[6] = {tmpcur_2856, jump_floc_loc_1142,
                                            jump_floc_loc_1143,
                                            jump_floc_loc_1144,
                                            jump_floc_loc_1145,
                                            jump_floc_loc_1146};
            
            *(GibPackedTag *) deref_1990 = 1;
            
            GibCursor writetag_2111 = deref_1990 + 1;
            GibCursor after_tag_2112 = deref_1990 + 1;
            
            *loc_727 += 1;
            
            GibCursor aft_soa_loc_2117[6] = {after_tag_2112, deref_1988,
                                             deref_1986, deref_1984, deref_1982,
                                             deref_1980};
            GibCursor end_taildc_1147[6];
            
            memcpy(end_taildc_1147, cursor_ptr_1971, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_2122 = &arg_73_154_236[1];
            GibCursor deref_2123 = *soa_field_0_2122;
            GibCursor *restrict soa_field_1_2124 = &arg_73_154_236[2];
            GibCursor deref_2125 = *soa_field_1_2124;
            GibCursor *restrict soa_field_2_2126 = &arg_73_154_236[3];
            GibCursor deref_2127 = *soa_field_2_2126;
            GibCursor *restrict soa_field_3_2128 = &arg_73_154_236[4];
            GibCursor deref_2129 = *soa_field_3_2128;
            GibCursor *restrict soa_field_4_2130 = &arg_73_154_236[5];
            GibCursor deref_2131 = *soa_field_4_2130;
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_2856;
            GibCursor tmpcur_2867 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_2868 = tmpcur_2856 + 8;
            uint16_t tmptag_2869 = GIB_GET_TAG(tagged_tmpcur_29);
            
            *(GibCursor *) loc_721 = tmpcur_2867;
            
            GibCursor end_from_tagged_dcon_redir_2153 = tmpcur_2867 +
                      tmptag_2869;
            GibCursor field_nxt_2147 = deref_2123 + 1;
            uintptr_t tagged_tmpcur_28 = *(uintptr_t *) field_nxt_2147;
            GibCursor tmpcur_2870 = GIB_UNTAG(tagged_tmpcur_28);
            GibCursor tmpaftercur_2871 = field_nxt_2147 + 8;
            uint16_t tmptag_2872 = GIB_GET_TAG(tagged_tmpcur_28);
            
            *(GibCursor *) soa_field_0_2122 = tmpcur_2870;
            
            GibCursor end_from_tagged_fld_redir_2154 = tmpcur_2870 +
                      tmptag_2872;
            GibCursor field_nxt_2148 = deref_2125 + 1;
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) field_nxt_2148;
            GibCursor tmpcur_2873 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2874 = field_nxt_2148 + 8;
            uint16_t tmptag_2875 = GIB_GET_TAG(tagged_tmpcur_27);
            
            *(GibCursor *) soa_field_1_2124 = tmpcur_2873;
            
            GibCursor end_from_tagged_fld_redir_2155 = tmpcur_2873 +
                      tmptag_2875;
            GibCursor field_nxt_2149 = deref_2127 + 1;
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) field_nxt_2149;
            GibCursor tmpcur_2876 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_2877 = field_nxt_2149 + 8;
            uint16_t tmptag_2878 = GIB_GET_TAG(tagged_tmpcur_26);
            
            *(GibCursor *) soa_field_2_2126 = tmpcur_2876;
            
            GibCursor end_from_tagged_fld_redir_2156 = tmpcur_2876 +
                      tmptag_2878;
            GibCursor field_nxt_2150 = deref_2129 + 1;
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) field_nxt_2150;
            GibCursor tmpcur_2879 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_2880 = field_nxt_2150 + 8;
            uint16_t tmptag_2881 = GIB_GET_TAG(tagged_tmpcur_25);
            
            *(GibCursor *) soa_field_3_2128 = tmpcur_2879;
            
            GibCursor end_from_tagged_fld_redir_2157 = tmpcur_2879 +
                      tmptag_2881;
            GibCursor field_nxt_2151 = deref_2131 + 1;
            uintptr_t tagged_tmpcur_24 = *(uintptr_t *) field_nxt_2151;
            GibCursor tmpcur_2882 = GIB_UNTAG(tagged_tmpcur_24);
            GibCursor tmpaftercur_2883 = field_nxt_2151 + 8;
            uint16_t tmptag_2884 = GIB_GET_TAG(tagged_tmpcur_24);
            
            *(GibCursor *) soa_field_4_2130 = tmpcur_2882;
            
            GibCursor end_from_tagged_fld_redir_2158 = tmpcur_2882 +
                      tmptag_2884;
            GibCursor indr_1262[6] = {tmpcur_2867, tmpcur_2870, tmpcur_2873,
                                      tmpcur_2876, tmpcur_2879, tmpcur_2882};
            GibCursor jump_dloc_1269 = deref_dcon_var_1994 + 9;
            GibCursor aft_indir_loc_1283 = deref_2123 + 9;
            GibCursor aft_indir_loc_1284 = deref_2125 + 9;
            GibCursor aft_indir_loc_1285 = deref_2127 + 9;
            GibCursor aft_indir_loc_1286 = deref_2129 + 9;
            GibCursor aft_indir_loc_1287 = deref_2131 + 9;
            GibCursor cursor_ptr_2159[6] = {jump_dloc_1269, aft_indir_loc_1283,
                                            aft_indir_loc_1284,
                                            aft_indir_loc_1285,
                                            aft_indir_loc_1286,
                                            aft_indir_loc_1287};
            GibCursor chk_end_2184 = cursor_ptr_1970[0];
            GibBool chk_2185 = deref_dcon_var_1994 < chk_end_2184;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2181 = cursor_ptr_1971[0];
            GibCursor chk_end_2182 = cursor_ptr_1969[0];
            GibBool chk_2183 = chk_loc_2181 < chk_end_2182;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2178 = cursor_ptr_1971[1];
            GibCursor chk_end_2179 = cursor_ptr_1969[1];
            GibBool chk_2180 = chk_loc_2178 < chk_end_2179;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2175 = cursor_ptr_1971[2];
            GibCursor chk_end_2176 = cursor_ptr_1969[2];
            GibBool chk_2177 = chk_loc_2175 < chk_end_2176;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2172 = cursor_ptr_1971[3];
            GibCursor chk_end_2173 = cursor_ptr_1969[3];
            GibBool chk_2174 = chk_loc_2172 < chk_end_2173;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2169 = cursor_ptr_1971[4];
            GibCursor chk_end_2170 = cursor_ptr_1969[4];
            GibBool chk_2171 = chk_loc_2169 < chk_end_2170;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2166 = cursor_ptr_1971[5];
            GibCursor chk_end_2167 = cursor_ptr_1969[5];
            GibBool chk_2168 = chk_loc_2166 < chk_end_2167;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_2186 =
                           _copy_MultiList(arg_73_154_236, cursor_ptr_1969, cursor_ptr_1971, arg_73_154_236);
            GibCursor end_call_1275[6];
            
            memcpy(end_call_1275, cursor_ptr_1971, sizeof(GibCursor [6]));
            
            GibCursor loc_cursor_ptr_2160[6];
            
            memcpy(loc_cursor_ptr_2160, arg_73_154_236, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_2189 = &arg_73_154_236[1];
            GibCursor deref_2190 = *soa_field_0_2189;
            GibCursor *restrict soa_field_1_2191 = &arg_73_154_236[2];
            GibCursor deref_2192 = *soa_field_1_2191;
            GibCursor *restrict soa_field_2_2193 = &arg_73_154_236[3];
            GibCursor deref_2194 = *soa_field_2_2193;
            GibCursor *restrict soa_field_3_2195 = &arg_73_154_236[4];
            GibCursor deref_2196 = *soa_field_3_2195;
            GibCursor *restrict soa_field_4_2197 = &arg_73_154_236[5];
            GibCursor deref_2198 = *soa_field_4_2197;
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_2856;
            GibCursor tmpcur_2885 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_2886 = tmpcur_2856 + 8;
            uint16_t tmptag_2887 = GIB_GET_TAG(tagged_tmpcur_35);
            
            *(GibCursor *) loc_721 = tmpcur_2885;
            
            GibCursor end_from_tagged_dcon_redir_2212 = tmpcur_2885 +
                      tmptag_2887;
            GibCursor field_nxt_2207 = deref_2190 + 1;
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) field_nxt_2207;
            GibCursor tmpcur_2888 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_2889 = field_nxt_2207 + 8;
            uint16_t tmptag_2890 = GIB_GET_TAG(tagged_tmpcur_34);
            
            *(GibCursor *) soa_field_0_2189 = tmpcur_2888;
            
            GibCursor end_from_tagged_fld_redir_2213 = tmpcur_2888 +
                      tmptag_2890;
            GibCursor field_nxt_2208 = deref_2192 + 1;
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) field_nxt_2208;
            GibCursor tmpcur_2891 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_2892 = field_nxt_2208 + 8;
            uint16_t tmptag_2893 = GIB_GET_TAG(tagged_tmpcur_33);
            
            *(GibCursor *) soa_field_1_2191 = tmpcur_2891;
            
            GibCursor end_from_tagged_fld_redir_2214 = tmpcur_2891 +
                      tmptag_2893;
            GibCursor field_nxt_2209 = deref_2194 + 1;
            uintptr_t tagged_tmpcur_32 = *(uintptr_t *) field_nxt_2209;
            GibCursor tmpcur_2894 = GIB_UNTAG(tagged_tmpcur_32);
            GibCursor tmpaftercur_2895 = field_nxt_2209 + 8;
            uint16_t tmptag_2896 = GIB_GET_TAG(tagged_tmpcur_32);
            
            *(GibCursor *) soa_field_2_2193 = tmpcur_2894;
            
            GibCursor end_from_tagged_fld_redir_2215 = tmpcur_2894 +
                      tmptag_2896;
            GibCursor field_nxt_2210 = deref_2196 + 1;
            uintptr_t tagged_tmpcur_31 = *(uintptr_t *) field_nxt_2210;
            GibCursor tmpcur_2897 = GIB_UNTAG(tagged_tmpcur_31);
            GibCursor tmpaftercur_2898 = field_nxt_2210 + 8;
            uint16_t tmptag_2899 = GIB_GET_TAG(tagged_tmpcur_31);
            
            *(GibCursor *) soa_field_3_2195 = tmpcur_2897;
            
            GibCursor end_from_tagged_fld_redir_2216 = tmpcur_2897 +
                      tmptag_2899;
            GibCursor field_nxt_2211 = deref_2198 + 1;
            uintptr_t tagged_tmpcur_30 = *(uintptr_t *) field_nxt_2211;
            GibCursor tmpcur_2900 = GIB_UNTAG(tagged_tmpcur_30);
            GibCursor tmpaftercur_2901 = field_nxt_2211 + 8;
            uint16_t tmptag_2902 = GIB_GET_TAG(tagged_tmpcur_30);
            
            *(GibCursor *) soa_field_4_2197 = tmpcur_2900;
            
            GibCursor end_from_tagged_fld_redir_2217 = tmpcur_2900 +
                      tmptag_2902;
            GibCursor indr_1262[6] = {tmpcur_2885, tmpcur_2888, tmpcur_2891,
                                      tmpcur_2894, tmpcur_2897, tmpcur_2900};
            GibCursor copy_dloc_1288 = deref_1990 + 0;
            
            *loc_727 += 0;
            
            GibCursor copy_floc_loc_1293 = deref_1980 + 0;
            
            *loc_FloatTy_732 += 0;
            
            GibCursor copy_floc_loc_1292 = deref_1982 + 0;
            
            *loc_IntTy_731 += 0;
            
            GibCursor copy_floc_loc_1291 = deref_1984 + 0;
            
            *loc_IntTy_730 += 0;
            
            GibCursor copy_floc_loc_1290 = deref_1986 + 0;
            
            *loc_IntTy_729 += 0;
            
            GibCursor copy_floc_loc_1289 = deref_1988 + 0;
            
            *loc_IntTy_728 += 0;
            
            GibCursor cursor_ptr_2224[6] = {copy_dloc_1288, copy_floc_loc_1289,
                                            copy_floc_loc_1290,
                                            copy_floc_loc_1291,
                                            copy_floc_loc_1292,
                                            copy_floc_loc_1293};
            GibCursor chk_end_2249 = cursor_ptr_1970[0];
            GibBool chk_2250 = deref_dcon_var_1994 < chk_end_2249;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2246 = cursor_ptr_2224[0];
            GibCursor chk_end_2247 = cursor_ptr_1969[0];
            GibBool chk_2248 = chk_loc_2246 < chk_end_2247;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2243 = cursor_ptr_2224[1];
            GibCursor chk_end_2244 = cursor_ptr_1969[1];
            GibBool chk_2245 = chk_loc_2243 < chk_end_2244;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2240 = cursor_ptr_2224[2];
            GibCursor chk_end_2241 = cursor_ptr_1969[2];
            GibBool chk_2242 = chk_loc_2240 < chk_end_2241;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2237 = cursor_ptr_2224[3];
            GibCursor chk_end_2238 = cursor_ptr_1969[3];
            GibBool chk_2239 = chk_loc_2237 < chk_end_2238;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2234 = cursor_ptr_2224[4];
            GibCursor chk_end_2235 = cursor_ptr_1969[4];
            GibBool chk_2236 = chk_loc_2234 < chk_end_2235;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2231 = cursor_ptr_2224[5];
            GibCursor chk_end_2232 = cursor_ptr_1969[5];
            GibBool chk_2233 = chk_loc_2231 < chk_end_2232;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char tup_packed_2251 =
                           _copy_MultiList(arg_73_154_236, cursor_ptr_1969, cursor_ptr_1971, arg_73_154_236);
            GibCursor end_call_1275[6];
            
            memcpy(end_call_1275, cursor_ptr_1971, sizeof(GibCursor [6]));
            
            GibCursor loc_cursor_ptr_2225[6];
            
            memcpy(loc_cursor_ptr_2225, arg_73_154_236, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2855");
            exit(1);
        }
    }
}
unsigned char mkMultiList(GibCursor cursor_ptr_2253[6],
                          GibCursor cursor_ptr_2254[6], GibInt len_36_167_249)
{
    gib_scalar_count_footer_begin();
    
    GibCursor *end_r_751 = &cursor_ptr_2253[0];
    GibCursor *end_r_752 = &cursor_ptr_2253[1];
    GibCursor *end_r_753 = &cursor_ptr_2253[2];
    GibCursor *end_r_755 = &cursor_ptr_2253[4];
    GibCursor *end_r_754 = &cursor_ptr_2253[3];
    GibCursor *end_r_756 = &cursor_ptr_2253[5];
    GibCursor *restrict loc_IntTy_749 = &cursor_ptr_2254[4];
    GibCursor deref_2256 = *loc_IntTy_749;
    GibCursor cpy_2257[6];
    
    memcpy(cpy_2257, cursor_ptr_2254, sizeof(GibCursor [6]));
    
    GibCursor *restrict loc_IntTy_747 = &cursor_ptr_2254[2];
    GibCursor deref_2258 = *loc_IntTy_747;
    GibCursor *restrict loc_FloatTy_750 = &cursor_ptr_2254[5];
    GibCursor deref_2259 = *loc_FloatTy_750;
    GibCursor *restrict loc_IntTy_746 = &cursor_ptr_2254[1];
    GibCursor deref_2260 = *loc_IntTy_746;
    GibCursor *restrict loc_IntTy_748 = &cursor_ptr_2254[3];
    GibCursor deref_2261 = *loc_IntTy_748;
    GibCursor *restrict loc_745 = &cursor_ptr_2254[0];
    GibCursor deref_2262 = *end_r_756;
    GibCursor deref_2263 = *loc_FloatTy_750;
    GibCursor deref_2264 = *end_r_755;
    GibCursor deref_2265 = *loc_IntTy_749;
    GibCursor deref_2266 = *end_r_754;
    GibCursor deref_2267 = *loc_IntTy_748;
    GibCursor deref_2268 = *end_r_753;
    GibCursor deref_2269 = *loc_IntTy_747;
    GibCursor deref_2270 = *end_r_752;
    GibCursor deref_2271 = *loc_IntTy_746;
    GibCursor deref_2272 = *end_r_751;
    GibCursor deref_2273 = *loc_745;
    
    if (deref_2263 + 13 > deref_2262 || (deref_2265 + 17 > deref_2264 ||
                                         (deref_2267 + 17 > deref_2266 ||
                                          (deref_2269 + 17 > deref_2268 ||
                                           (deref_2271 + 17 > deref_2270 ||
                                            deref_2273 + 58 > deref_2272))))) {
        gib_grow_region(loc_FloatTy_750, end_r_756);
        gib_grow_region(loc_IntTy_749, end_r_755);
        gib_grow_region(loc_IntTy_748, end_r_754);
        gib_grow_region(loc_IntTy_747, end_r_753);
        gib_grow_region(loc_IntTy_746, end_r_752);
        gib_grow_region(loc_745, end_r_751);
        deref_2263 = *loc_FloatTy_750;
        deref_2265 = *loc_IntTy_749;
        deref_2267 = *loc_IntTy_748;
        deref_2269 = *loc_IntTy_747;
        deref_2271 = *loc_IntTy_746;
        deref_2273 = *loc_745;
    }
    
    GibBool fltIf_193_250 = len_36_167_249 <= 0;
    
    if (fltIf_193_250) {
        *(GibPackedTag *) deref_2273 = 1;
        
        GibCursor writetag_2280 = deref_2273 + 1;
        GibCursor after_tag_2281 = deref_2273 + 1;
        
        *loc_745 += 1;
        
        GibCursor aft_soa_loc_2286[6] = {after_tag_2281, deref_2271, deref_2269,
                                         deref_2267, deref_2265, deref_2263};
        GibCursor end_taildc_1148[6];
        
        memcpy(end_taildc_1148, cursor_ptr_2254, sizeof(GibCursor [6]));
        gib_scalar_count_footer_end("mkMultiList");
        return 0;
    } else {
        GibInt fltAppE_194_251 = len_36_167_249 - 1;
        GibCursor new_floc_loc_1014 = deref_2267 + 8;
        
        *loc_IntTy_748 += 8;
        
        GibCursor new_dloc_1011 = deref_2273 + 1;
        
        *loc_745 += 1;
        
        GibCursor new_floc_loc_1013 = deref_2269 + 8;
        
        *loc_IntTy_747 += 8;
        
        GibCursor new_floc_loc_1012 = deref_2271 + 8;
        
        *loc_IntTy_746 += 8;
        
        GibCursor new_floc_loc_1016 = deref_2263 + 4;
        
        *loc_FloatTy_750 += 4;
        
        GibCursor new_floc_loc_1015 = deref_2265 + 8;
        
        *loc_IntTy_749 += 8;
        
        GibCursor cursor_ptr_2296[6] = {new_dloc_1011, new_floc_loc_1012,
                                        new_floc_loc_1013, new_floc_loc_1014,
                                        new_floc_loc_1015, new_floc_loc_1016};
        
        *(GibPackedTag *) deref_2273 = 0;
        
        GibCursor writetag_2319 = deref_2273 + 1;
        
        gib_scalar_count_footer_bump(deref_2270);
        gib_scalar_count_footer_bump(deref_2268);
        gib_scalar_count_footer_bump(deref_2266);
        gib_scalar_count_footer_bump(deref_2264);
        gib_scalar_count_footer_bump(deref_2262);
        
        GibCursor chk_loc_2314 = cursor_ptr_2296[0];
        GibCursor chk_end_2315 = cursor_ptr_2253[0];
        GibBool chk_2316 = chk_loc_2314 < chk_end_2315;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_2311 = cursor_ptr_2296[1];
        GibCursor chk_end_2312 = cursor_ptr_2253[1];
        GibBool chk_2313 = chk_loc_2311 < chk_end_2312;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_2308 = cursor_ptr_2296[2];
        GibCursor chk_end_2309 = cursor_ptr_2253[2];
        GibBool chk_2310 = chk_loc_2308 < chk_end_2309;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_2305 = cursor_ptr_2296[3];
        GibCursor chk_end_2306 = cursor_ptr_2253[3];
        GibBool chk_2307 = chk_loc_2305 < chk_end_2306;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_2302 = cursor_ptr_2296[4];
        GibCursor chk_end_2303 = cursor_ptr_2253[4];
        GibBool chk_2304 = chk_loc_2302 < chk_end_2303;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursor chk_loc_2299 = cursor_ptr_2296[5];
        GibCursor chk_end_2300 = cursor_ptr_2253[5];
        GibBool chk_2301 = chk_loc_2299 < chk_end_2300;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        unsigned char tup_packed_2317 =
                       mkMultiList(cursor_ptr_2253, cursor_ptr_2254, fltAppE_194_251);
        GibCursor end_rst_37_168_252[6];
        
        memcpy(end_rst_37_168_252, cursor_ptr_2254, sizeof(GibCursor [6]));
        
        GibInt b_39_170_254 = len_36_167_249 + 1;
        GibInt c_40_171_255 = len_36_167_249 + 2;
        GibInt d_41_172_256 = len_36_167_249 + 3;
        GibCursor after_tag_2320 = deref_2273 + 1;
        
        *(GibInt *) deref_2271 = len_36_167_249;
        
        GibCursor writecur_2325 = deref_2271 + sizeof(GibInt);
        
        *(GibInt *) deref_2269 = b_39_170_254;
        
        GibCursor writecur_2327 = deref_2269 + sizeof(GibInt);
        
        *(GibInt *) deref_2267 = c_40_171_255;
        
        GibCursor writecur_2329 = deref_2267 + sizeof(GibInt);
        
        *(GibInt *) deref_2265 = d_41_172_256;
        
        GibCursor writecur_2331 = deref_2265 + sizeof(GibInt);
        
        *(GibFloat *) deref_2263 = 1.0;
        
        GibCursor writecur_2333 = deref_2263 + sizeof(GibFloat);
        GibCursor end_taildc_1149[6];
        
        memcpy(end_taildc_1149, cursor_ptr_2254, sizeof(GibCursor [6]));
        gib_scalar_count_footer_end("mkMultiList");
        return 0;
    }
}
GibInt sumMultiList(GibCursor cursor_ptr_2340[6], GibCursor xs_42_173_257[6])
{
    GibCursor *end_r_763 = &cursor_ptr_2340[0];
    GibCursor *end_r_764 = &cursor_ptr_2340[1];
    GibCursor *end_r_765 = &cursor_ptr_2340[2];
    GibCursor *end_r_766 = &cursor_ptr_2340[3];
    GibCursor *end_r_767 = &cursor_ptr_2340[4];
    GibCursor *end_r_768 = &cursor_ptr_2340[5];
    GibCursor *restrict loc_757 = &xs_42_173_257[0];
    GibCursor deref_dcon_var_2344 = *loc_757;
    GibPackedTag tmpval_2904 = *(GibPackedTag *) deref_dcon_var_2344;
    GibCursor tmpcur_2905 = deref_dcon_var_2344 + 1;
    
    
  switch_2952:
    ;
    switch (tmpval_2904) {
        
      case 1:
        {
            GibCursor *restrict soa_field_0_2346 = &xs_42_173_257[1];
            GibCursor deref_2347 = *soa_field_0_2346;
            GibCursor *restrict soa_field_1_2348 = &xs_42_173_257[2];
            GibCursor deref_2349 = *soa_field_1_2348;
            GibCursor *restrict soa_field_2_2350 = &xs_42_173_257[3];
            GibCursor deref_2351 = *soa_field_2_2350;
            GibCursor *restrict soa_field_3_2352 = &xs_42_173_257[4];
            GibCursor deref_2353 = *soa_field_3_2352;
            GibCursor *restrict soa_field_4_2354 = &xs_42_173_257[5];
            GibCursor deref_2355 = *soa_field_4_2354;
            
            *loc_757 += 1;
            
            GibCursor jump_floc_loc_1152 = deref_2347 + 0;
            GibCursor jump_floc_loc_1153 = deref_2349 + 0;
            GibCursor jump_floc_loc_1154 = deref_2351 + 0;
            GibCursor jump_floc_loc_1155 = deref_2353 + 0;
            GibCursor jump_floc_loc_1156 = deref_2355 + 0;
            GibCursor cursor_ptr_2358[6] = {tmpcur_2905, jump_floc_loc_1152,
                                            jump_floc_loc_1153,
                                            jump_floc_loc_1154,
                                            jump_floc_loc_1155,
                                            jump_floc_loc_1156};
            
            return 0;
            break;
        }
        
      case 0:
        {
            GibCursor *restrict soa_field_0_2360 = &xs_42_173_257[1];
            GibCursor deref_2361 = *soa_field_0_2360;
            GibCursor *restrict soa_field_1_2362 = &xs_42_173_257[2];
            GibCursor deref_2363 = *soa_field_1_2362;
            GibCursor *restrict soa_field_2_2364 = &xs_42_173_257[3];
            GibCursor deref_2365 = *soa_field_2_2364;
            GibCursor *restrict soa_field_3_2366 = &xs_42_173_257[4];
            GibCursor deref_2367 = *soa_field_3_2366;
            GibCursor *restrict soa_field_4_2368 = &xs_42_173_257[5];
            GibCursor deref_2369 = *soa_field_4_2368;
            GibInt tmpval_2906 = *(GibInt *) deref_2361;
            GibCursor tmpcur_2907 = deref_2361 + sizeof(GibInt);
            
            *soa_field_0_2360 += 8;
            
            GibInt tmpval_2908 = *(GibInt *) deref_2363;
            GibCursor tmpcur_2909 = deref_2363 + sizeof(GibInt);
            
            *soa_field_1_2362 += 8;
            
            GibInt tmpval_2910 = *(GibInt *) deref_2365;
            GibCursor tmpcur_2911 = deref_2365 + sizeof(GibInt);
            
            *soa_field_2_2364 += 8;
            
            GibInt tmpval_2912 = *(GibInt *) deref_2367;
            GibCursor tmpcur_2913 = deref_2367 + sizeof(GibInt);
            
            *soa_field_3_2366 += 8;
            
            GibFloat tmpval_2914 = *(GibFloat *) deref_2369;
            GibCursor tmpcur_2915 = deref_2369 + sizeof(GibFloat);
            GibCursor cursor_ptr_2342[6] = {tmpcur_2905, tmpcur_2907,
                                            tmpcur_2909, tmpcur_2911,
                                            tmpcur_2913, tmpcur_2915};
            
            *loc_757 += 1;
            
            GibCursor jumpf_floc_loc_1158 = deref_2361 + 8;
            GibCursor jumpf_floc_loc_1159 = deref_2363 + 8;
            GibCursor jumpf_floc_loc_1160 = deref_2365 + 8;
            GibCursor jumpf_floc_loc_1161 = deref_2367 + 8;
            GibCursor jumpf_floc_loc_1162 = deref_2369 + 4;
            GibCursor loc_1043 = tmpcur_2905 + 0;
            
            *loc_757 += 0;
            
            GibCursor loc_1042 = jumpf_floc_loc_1162 + 0;
            GibCursor loc_1041 = jumpf_floc_loc_1161 + 0;
            GibCursor loc_1040 = jumpf_floc_loc_1160 + 0;
            GibCursor loc_1039 = jumpf_floc_loc_1159 + 0;
            GibCursor loc_1038 = jumpf_floc_loc_1158 + 0;
            GibCursor cursor_ptr_2383[6] = {tmpcur_2905, jumpf_floc_loc_1158,
                                            jumpf_floc_loc_1159,
                                            jumpf_floc_loc_1160,
                                            jumpf_floc_loc_1161,
                                            jumpf_floc_loc_1162};
            GibInt fltPrm_197_264 = tmpval_2906 + tmpval_2908;
            GibInt fltPrm_196_265 = fltPrm_197_264 + tmpval_2910;
            GibInt fltPrm_195_266 = fltPrm_196_265 + tmpval_2912;
            GibCursor chk_loc_2403 = cursor_ptr_2342[0];
            GibCursor chk_end_2404 = cursor_ptr_2340[0];
            GibBool chk_2405 = chk_loc_2403 < chk_end_2404;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2400 = cursor_ptr_2342[1];
            GibCursor chk_end_2401 = cursor_ptr_2340[1];
            GibBool chk_2402 = chk_loc_2400 < chk_end_2401;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2397 = cursor_ptr_2342[2];
            GibCursor chk_end_2398 = cursor_ptr_2340[2];
            GibBool chk_2399 = chk_loc_2397 < chk_end_2398;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2394 = cursor_ptr_2342[3];
            GibCursor chk_end_2395 = cursor_ptr_2340[3];
            GibBool chk_2396 = chk_loc_2394 < chk_end_2395;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2391 = cursor_ptr_2342[4];
            GibCursor chk_end_2392 = cursor_ptr_2340[4];
            GibBool chk_2393 = chk_loc_2391 < chk_end_2392;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2388 = cursor_ptr_2342[5];
            GibCursor chk_end_2389 = cursor_ptr_2340[5];
            GibBool chk_2390 = chk_loc_2388 < chk_end_2389;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibInt fltPrm_198_267 =
                    sumMultiList(cursor_ptr_2340, xs_42_173_257);
            GibCursor loc_cursor_ptr_2384[6];
            
            memcpy(loc_cursor_ptr_2384, xs_42_173_257, sizeof(GibCursor [6]));
            
            GibInt tailprim_1169 = fltPrm_195_266 + fltPrm_198_267;
            
            return tailprim_1169;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_2408 = &xs_42_173_257[1];
            GibCursor deref_2409 = *soa_field_0_2408;
            GibCursor *restrict soa_field_1_2410 = &xs_42_173_257[2];
            GibCursor deref_2411 = *soa_field_1_2410;
            GibCursor *restrict soa_field_2_2412 = &xs_42_173_257[3];
            GibCursor deref_2413 = *soa_field_2_2412;
            GibCursor *restrict soa_field_3_2414 = &xs_42_173_257[4];
            GibCursor deref_2415 = *soa_field_3_2414;
            GibCursor *restrict soa_field_4_2416 = &xs_42_173_257[5];
            GibCursor deref_2417 = *soa_field_4_2416;
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) tmpcur_2905;
            GibCursor tmpcur_2916 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_2917 = tmpcur_2905 + 8;
            uint16_t tmptag_2918 = GIB_GET_TAG(tagged_tmpcur_41);
            
            *(GibCursor *) loc_757 = tmpcur_2916;
            
            GibCursor end_from_tagged_dcon_redir_2439 = tmpcur_2916 +
                      tmptag_2918;
            GibCursor field_nxt_2433 = deref_2409 + 1;
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) field_nxt_2433;
            GibCursor tmpcur_2919 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_2920 = field_nxt_2433 + 8;
            uint16_t tmptag_2921 = GIB_GET_TAG(tagged_tmpcur_40);
            
            *(GibCursor *) soa_field_0_2408 = tmpcur_2919;
            
            GibCursor end_from_tagged_fld_redir_2440 = tmpcur_2919 +
                      tmptag_2921;
            GibCursor field_nxt_2434 = deref_2411 + 1;
            uintptr_t tagged_tmpcur_39 = *(uintptr_t *) field_nxt_2434;
            GibCursor tmpcur_2922 = GIB_UNTAG(tagged_tmpcur_39);
            GibCursor tmpaftercur_2923 = field_nxt_2434 + 8;
            uint16_t tmptag_2924 = GIB_GET_TAG(tagged_tmpcur_39);
            
            *(GibCursor *) soa_field_1_2410 = tmpcur_2922;
            
            GibCursor end_from_tagged_fld_redir_2441 = tmpcur_2922 +
                      tmptag_2924;
            GibCursor field_nxt_2435 = deref_2413 + 1;
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) field_nxt_2435;
            GibCursor tmpcur_2925 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_2926 = field_nxt_2435 + 8;
            uint16_t tmptag_2927 = GIB_GET_TAG(tagged_tmpcur_38);
            
            *(GibCursor *) soa_field_2_2412 = tmpcur_2925;
            
            GibCursor end_from_tagged_fld_redir_2442 = tmpcur_2925 +
                      tmptag_2927;
            GibCursor field_nxt_2436 = deref_2415 + 1;
            uintptr_t tagged_tmpcur_37 = *(uintptr_t *) field_nxt_2436;
            GibCursor tmpcur_2928 = GIB_UNTAG(tagged_tmpcur_37);
            GibCursor tmpaftercur_2929 = field_nxt_2436 + 8;
            uint16_t tmptag_2930 = GIB_GET_TAG(tagged_tmpcur_37);
            
            *(GibCursor *) soa_field_3_2414 = tmpcur_2928;
            
            GibCursor end_from_tagged_fld_redir_2443 = tmpcur_2928 +
                      tmptag_2930;
            GibCursor field_nxt_2437 = deref_2417 + 1;
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) field_nxt_2437;
            GibCursor tmpcur_2931 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_2932 = field_nxt_2437 + 8;
            uint16_t tmptag_2933 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_fld_redir_2444 = tmpcur_2931 +
                      tmptag_2933;
            GibCursor indr_1294[6] = {tmpcur_2916, tmpcur_2919, tmpcur_2922,
                                      tmpcur_2925, tmpcur_2928, tmpcur_2931};
            GibCursor jump_dloc_1301 = deref_dcon_var_2344 + 9;
            GibCursor aft_indir_loc_1315 = deref_2409 + 9;
            GibCursor aft_indir_loc_1316 = deref_2411 + 9;
            GibCursor aft_indir_loc_1317 = deref_2413 + 9;
            GibCursor aft_indir_loc_1318 = deref_2415 + 9;
            GibCursor aft_indir_loc_1319 = deref_2417 + 9;
            GibCursor cursor_ptr_2445[6] = {jump_dloc_1301, aft_indir_loc_1315,
                                            aft_indir_loc_1316,
                                            aft_indir_loc_1317,
                                            aft_indir_loc_1318,
                                            aft_indir_loc_1319};
            GibCursor chk_end_2450 = cursor_ptr_2340[0];
            GibBool chk_2451 = deref_dcon_var_2344 < chk_end_2450;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibInt call_1307 =  sumMultiList(xs_42_173_257, xs_42_173_257);
            GibCursor loc_cursor_ptr_2446[6];
            
            memcpy(loc_cursor_ptr_2446, xs_42_173_257, sizeof(GibCursor [6]));
            return call_1307;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_2454 = &xs_42_173_257[1];
            GibCursor deref_2455 = *soa_field_0_2454;
            GibCursor *restrict soa_field_1_2456 = &xs_42_173_257[2];
            GibCursor deref_2457 = *soa_field_1_2456;
            GibCursor *restrict soa_field_2_2458 = &xs_42_173_257[3];
            GibCursor deref_2459 = *soa_field_2_2458;
            GibCursor *restrict soa_field_3_2460 = &xs_42_173_257[4];
            GibCursor deref_2461 = *soa_field_3_2460;
            GibCursor *restrict soa_field_4_2462 = &xs_42_173_257[5];
            GibCursor deref_2463 = *soa_field_4_2462;
            uintptr_t tagged_tmpcur_47 = *(uintptr_t *) tmpcur_2905;
            GibCursor tmpcur_2934 = GIB_UNTAG(tagged_tmpcur_47);
            GibCursor tmpaftercur_2935 = tmpcur_2905 + 8;
            uint16_t tmptag_2936 = GIB_GET_TAG(tagged_tmpcur_47);
            
            *(GibCursor *) loc_757 = tmpcur_2934;
            
            GibCursor end_from_tagged_dcon_redir_2477 = tmpcur_2934 +
                      tmptag_2936;
            GibCursor field_nxt_2472 = deref_2455 + 1;
            uintptr_t tagged_tmpcur_46 = *(uintptr_t *) field_nxt_2472;
            GibCursor tmpcur_2937 = GIB_UNTAG(tagged_tmpcur_46);
            GibCursor tmpaftercur_2938 = field_nxt_2472 + 8;
            uint16_t tmptag_2939 = GIB_GET_TAG(tagged_tmpcur_46);
            
            *(GibCursor *) soa_field_0_2454 = tmpcur_2937;
            
            GibCursor end_from_tagged_fld_redir_2478 = tmpcur_2937 +
                      tmptag_2939;
            GibCursor field_nxt_2473 = deref_2457 + 1;
            uintptr_t tagged_tmpcur_45 = *(uintptr_t *) field_nxt_2473;
            GibCursor tmpcur_2940 = GIB_UNTAG(tagged_tmpcur_45);
            GibCursor tmpaftercur_2941 = field_nxt_2473 + 8;
            uint16_t tmptag_2942 = GIB_GET_TAG(tagged_tmpcur_45);
            
            *(GibCursor *) soa_field_1_2456 = tmpcur_2940;
            
            GibCursor end_from_tagged_fld_redir_2479 = tmpcur_2940 +
                      tmptag_2942;
            GibCursor field_nxt_2474 = deref_2459 + 1;
            uintptr_t tagged_tmpcur_44 = *(uintptr_t *) field_nxt_2474;
            GibCursor tmpcur_2943 = GIB_UNTAG(tagged_tmpcur_44);
            GibCursor tmpaftercur_2944 = field_nxt_2474 + 8;
            uint16_t tmptag_2945 = GIB_GET_TAG(tagged_tmpcur_44);
            
            *(GibCursor *) soa_field_2_2458 = tmpcur_2943;
            
            GibCursor end_from_tagged_fld_redir_2480 = tmpcur_2943 +
                      tmptag_2945;
            GibCursor field_nxt_2475 = deref_2461 + 1;
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) field_nxt_2475;
            GibCursor tmpcur_2946 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_2947 = field_nxt_2475 + 8;
            uint16_t tmptag_2948 = GIB_GET_TAG(tagged_tmpcur_43);
            
            *(GibCursor *) soa_field_3_2460 = tmpcur_2946;
            
            GibCursor end_from_tagged_fld_redir_2481 = tmpcur_2946 +
                      tmptag_2948;
            GibCursor field_nxt_2476 = deref_2463 + 1;
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) field_nxt_2476;
            GibCursor tmpcur_2949 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_2950 = field_nxt_2476 + 8;
            uint16_t tmptag_2951 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_fld_redir_2482 = tmpcur_2949 +
                      tmptag_2951;
            GibCursor indr_1294[6] = {tmpcur_2934, tmpcur_2937, tmpcur_2940,
                                      tmpcur_2943, tmpcur_2946, tmpcur_2949};
            GibCursor chk_end_2487 = cursor_ptr_2340[0];
            GibBool chk_2488 = deref_dcon_var_2344 < chk_end_2487;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibInt call_1307 =  sumMultiList(xs_42_173_257, xs_42_173_257);
            GibCursor loc_cursor_ptr_2483[6];
            
            memcpy(loc_cursor_ptr_2483, xs_42_173_257, sizeof(GibCursor [6]));
            return call_1307;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2904");
            exit(1);
        }
    }
}
unsigned char _traverse_MultiList(GibCursor cursor_ptr_2491[6],
                                  GibCursor arg_86_180_268[6])
{
    GibCursor *end_r_775 = &cursor_ptr_2491[0];
    GibCursor *end_r_776 = &cursor_ptr_2491[1];
    GibCursor *end_r_777 = &cursor_ptr_2491[2];
    GibCursor *end_r_778 = &cursor_ptr_2491[3];
    GibCursor *end_r_779 = &cursor_ptr_2491[4];
    GibCursor *end_r_780 = &cursor_ptr_2491[5];
    GibCursor *restrict loc_769 = &arg_86_180_268[0];
    GibCursor deref_dcon_var_2495 = *loc_769;
    GibPackedTag tmpval_2953 = *(GibPackedTag *) deref_dcon_var_2495;
    GibCursor tmpcur_2954 = deref_dcon_var_2495 + 1;
    
    
  switch_3001:
    ;
    switch (tmpval_2953) {
        
      case 0:
        {
            GibCursor *restrict soa_field_0_2497 = &arg_86_180_268[1];
            GibCursor deref_2498 = *soa_field_0_2497;
            GibCursor *restrict soa_field_1_2499 = &arg_86_180_268[2];
            GibCursor deref_2500 = *soa_field_1_2499;
            GibCursor *restrict soa_field_2_2501 = &arg_86_180_268[3];
            GibCursor deref_2502 = *soa_field_2_2501;
            GibCursor *restrict soa_field_3_2503 = &arg_86_180_268[4];
            GibCursor deref_2504 = *soa_field_3_2503;
            GibCursor *restrict soa_field_4_2505 = &arg_86_180_268[5];
            GibCursor deref_2506 = *soa_field_4_2505;
            GibInt tmpval_2955 = *(GibInt *) deref_2498;
            GibCursor tmpcur_2956 = deref_2498 + sizeof(GibInt);
            
            *soa_field_0_2497 += 8;
            
            GibInt tmpval_2957 = *(GibInt *) deref_2500;
            GibCursor tmpcur_2958 = deref_2500 + sizeof(GibInt);
            
            *soa_field_1_2499 += 8;
            
            GibInt tmpval_2959 = *(GibInt *) deref_2502;
            GibCursor tmpcur_2960 = deref_2502 + sizeof(GibInt);
            
            *soa_field_2_2501 += 8;
            
            GibInt tmpval_2961 = *(GibInt *) deref_2504;
            GibCursor tmpcur_2962 = deref_2504 + sizeof(GibInt);
            
            *soa_field_3_2503 += 8;
            
            GibFloat tmpval_2963 = *(GibFloat *) deref_2506;
            GibCursor tmpcur_2964 = deref_2506 + sizeof(GibFloat);
            
            *soa_field_4_2505 += 4;
            
            GibCursor cursor_ptr_2493[6] = {tmpcur_2954, tmpcur_2956,
                                            tmpcur_2958, tmpcur_2960,
                                            tmpcur_2962, tmpcur_2964};
            
            *loc_769 += 1;
            
            GibCursor jumpf_floc_loc_1171 = deref_2498 + 8;
            GibCursor jumpf_floc_loc_1172 = deref_2500 + 8;
            GibCursor jumpf_floc_loc_1173 = deref_2502 + 8;
            GibCursor jumpf_floc_loc_1174 = deref_2504 + 8;
            GibCursor jumpf_floc_loc_1175 = deref_2506 + 4;
            GibCursor loc_1068 = tmpcur_2954 + 0;
            
            *loc_769 += 0;
            
            GibCursor loc_1067 = jumpf_floc_loc_1175 + 0;
            GibCursor loc_1066 = jumpf_floc_loc_1174 + 0;
            GibCursor loc_1065 = jumpf_floc_loc_1173 + 0;
            GibCursor loc_1064 = jumpf_floc_loc_1172 + 0;
            GibCursor loc_1063 = jumpf_floc_loc_1171 + 0;
            GibCursor cursor_ptr_2521[6] = {tmpcur_2954, jumpf_floc_loc_1171,
                                            jumpf_floc_loc_1172,
                                            jumpf_floc_loc_1173,
                                            jumpf_floc_loc_1174,
                                            jumpf_floc_loc_1175};
            GibCursor chk_loc_2541 = cursor_ptr_2493[0];
            GibCursor chk_end_2542 = cursor_ptr_2491[0];
            GibBool chk_2543 = chk_loc_2541 < chk_end_2542;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2538 = cursor_ptr_2493[1];
            GibCursor chk_end_2539 = cursor_ptr_2491[1];
            GibBool chk_2540 = chk_loc_2538 < chk_end_2539;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2535 = cursor_ptr_2493[2];
            GibCursor chk_end_2536 = cursor_ptr_2491[2];
            GibBool chk_2537 = chk_loc_2535 < chk_end_2536;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2532 = cursor_ptr_2493[3];
            GibCursor chk_end_2533 = cursor_ptr_2491[3];
            GibBool chk_2534 = chk_loc_2532 < chk_end_2533;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2529 = cursor_ptr_2493[4];
            GibCursor chk_end_2530 = cursor_ptr_2491[4];
            GibBool chk_2531 = chk_loc_2529 < chk_end_2530;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursor chk_loc_2526 = cursor_ptr_2493[5];
            GibCursor chk_end_2527 = cursor_ptr_2491[5];
            GibBool chk_2528 = chk_loc_2526 < chk_end_2527;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char y_98_187_275 =
                           _traverse_MultiList(cursor_ptr_2491, arg_86_180_268);
            GibCursor loc_cursor_ptr_2522[6];
            
            memcpy(loc_cursor_ptr_2522, arg_86_180_268, sizeof(GibCursor [6]));
            return 0;
            break;
        }
        
      case 1:
        {
            GibCursor *restrict soa_field_0_2546 = &arg_86_180_268[1];
            GibCursor deref_2547 = *soa_field_0_2546;
            GibCursor *restrict soa_field_1_2548 = &arg_86_180_268[2];
            GibCursor deref_2549 = *soa_field_1_2548;
            GibCursor *restrict soa_field_2_2550 = &arg_86_180_268[3];
            GibCursor deref_2551 = *soa_field_2_2550;
            GibCursor *restrict soa_field_3_2552 = &arg_86_180_268[4];
            GibCursor deref_2553 = *soa_field_3_2552;
            GibCursor *restrict soa_field_4_2554 = &arg_86_180_268[5];
            GibCursor deref_2555 = *soa_field_4_2554;
            
            *loc_769 += 1;
            
            GibCursor jump_floc_loc_1184 = deref_2547 + 0;
            GibCursor jump_floc_loc_1185 = deref_2549 + 0;
            GibCursor jump_floc_loc_1186 = deref_2551 + 0;
            GibCursor jump_floc_loc_1187 = deref_2553 + 0;
            GibCursor jump_floc_loc_1188 = deref_2555 + 0;
            GibCursor cursor_ptr_2558[6] = {tmpcur_2954, jump_floc_loc_1184,
                                            jump_floc_loc_1185,
                                            jump_floc_loc_1186,
                                            jump_floc_loc_1187,
                                            jump_floc_loc_1188};
            
            return 0;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_2560 = &arg_86_180_268[1];
            GibCursor deref_2561 = *soa_field_0_2560;
            GibCursor *restrict soa_field_1_2562 = &arg_86_180_268[2];
            GibCursor deref_2563 = *soa_field_1_2562;
            GibCursor *restrict soa_field_2_2564 = &arg_86_180_268[3];
            GibCursor deref_2565 = *soa_field_2_2564;
            GibCursor *restrict soa_field_3_2566 = &arg_86_180_268[4];
            GibCursor deref_2567 = *soa_field_3_2566;
            GibCursor *restrict soa_field_4_2568 = &arg_86_180_268[5];
            GibCursor deref_2569 = *soa_field_4_2568;
            uintptr_t tagged_tmpcur_53 = *(uintptr_t *) tmpcur_2954;
            GibCursor tmpcur_2965 = GIB_UNTAG(tagged_tmpcur_53);
            GibCursor tmpaftercur_2966 = tmpcur_2954 + 8;
            uint16_t tmptag_2967 = GIB_GET_TAG(tagged_tmpcur_53);
            
            *(GibCursor *) loc_769 = tmpcur_2965;
            
            GibCursor end_from_tagged_dcon_redir_2591 = tmpcur_2965 +
                      tmptag_2967;
            GibCursor field_nxt_2585 = deref_2561 + 1;
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) field_nxt_2585;
            GibCursor tmpcur_2968 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_2969 = field_nxt_2585 + 8;
            uint16_t tmptag_2970 = GIB_GET_TAG(tagged_tmpcur_52);
            
            *(GibCursor *) soa_field_0_2560 = tmpcur_2968;
            
            GibCursor end_from_tagged_fld_redir_2592 = tmpcur_2968 +
                      tmptag_2970;
            GibCursor field_nxt_2586 = deref_2563 + 1;
            uintptr_t tagged_tmpcur_51 = *(uintptr_t *) field_nxt_2586;
            GibCursor tmpcur_2971 = GIB_UNTAG(tagged_tmpcur_51);
            GibCursor tmpaftercur_2972 = field_nxt_2586 + 8;
            uint16_t tmptag_2973 = GIB_GET_TAG(tagged_tmpcur_51);
            
            *(GibCursor *) soa_field_1_2562 = tmpcur_2971;
            
            GibCursor end_from_tagged_fld_redir_2593 = tmpcur_2971 +
                      tmptag_2973;
            GibCursor field_nxt_2587 = deref_2565 + 1;
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) field_nxt_2587;
            GibCursor tmpcur_2974 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_2975 = field_nxt_2587 + 8;
            uint16_t tmptag_2976 = GIB_GET_TAG(tagged_tmpcur_50);
            
            *(GibCursor *) soa_field_2_2564 = tmpcur_2974;
            
            GibCursor end_from_tagged_fld_redir_2594 = tmpcur_2974 +
                      tmptag_2976;
            GibCursor field_nxt_2588 = deref_2567 + 1;
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) field_nxt_2588;
            GibCursor tmpcur_2977 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_2978 = field_nxt_2588 + 8;
            uint16_t tmptag_2979 = GIB_GET_TAG(tagged_tmpcur_49);
            
            *(GibCursor *) soa_field_3_2566 = tmpcur_2977;
            
            GibCursor end_from_tagged_fld_redir_2595 = tmpcur_2977 +
                      tmptag_2979;
            GibCursor field_nxt_2589 = deref_2569 + 1;
            uintptr_t tagged_tmpcur_48 = *(uintptr_t *) field_nxt_2589;
            GibCursor tmpcur_2980 = GIB_UNTAG(tagged_tmpcur_48);
            GibCursor tmpaftercur_2981 = field_nxt_2589 + 8;
            uint16_t tmptag_2982 = GIB_GET_TAG(tagged_tmpcur_48);
            
            *(GibCursor *) soa_field_4_2568 = tmpcur_2980;
            
            GibCursor end_from_tagged_fld_redir_2596 = tmpcur_2980 +
                      tmptag_2982;
            GibCursor indr_1320[6] = {tmpcur_2965, tmpcur_2968, tmpcur_2971,
                                      tmpcur_2974, tmpcur_2977, tmpcur_2980};
            GibCursor jump_dloc_1327 = deref_dcon_var_2495 + 9;
            GibCursor aft_indir_loc_1341 = deref_2561 + 9;
            GibCursor aft_indir_loc_1342 = deref_2563 + 9;
            GibCursor aft_indir_loc_1343 = deref_2565 + 9;
            GibCursor aft_indir_loc_1344 = deref_2567 + 9;
            GibCursor aft_indir_loc_1345 = deref_2569 + 9;
            GibCursor cursor_ptr_2597[6] = {jump_dloc_1327, aft_indir_loc_1341,
                                            aft_indir_loc_1342,
                                            aft_indir_loc_1343,
                                            aft_indir_loc_1344,
                                            aft_indir_loc_1345};
            GibCursor chk_end_2602 = cursor_ptr_2491[0];
            GibBool chk_2603 = deref_dcon_var_2495 < chk_end_2602;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char call_1333 =
                           _traverse_MultiList(arg_86_180_268, arg_86_180_268);
            GibCursor loc_cursor_ptr_2598[6];
            
            memcpy(loc_cursor_ptr_2598, arg_86_180_268, sizeof(GibCursor [6]));
            return call_1333;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *restrict soa_field_0_2606 = &arg_86_180_268[1];
            GibCursor deref_2607 = *soa_field_0_2606;
            GibCursor *restrict soa_field_1_2608 = &arg_86_180_268[2];
            GibCursor deref_2609 = *soa_field_1_2608;
            GibCursor *restrict soa_field_2_2610 = &arg_86_180_268[3];
            GibCursor deref_2611 = *soa_field_2_2610;
            GibCursor *restrict soa_field_3_2612 = &arg_86_180_268[4];
            GibCursor deref_2613 = *soa_field_3_2612;
            GibCursor *restrict soa_field_4_2614 = &arg_86_180_268[5];
            GibCursor deref_2615 = *soa_field_4_2614;
            uintptr_t tagged_tmpcur_59 = *(uintptr_t *) tmpcur_2954;
            GibCursor tmpcur_2983 = GIB_UNTAG(tagged_tmpcur_59);
            GibCursor tmpaftercur_2984 = tmpcur_2954 + 8;
            uint16_t tmptag_2985 = GIB_GET_TAG(tagged_tmpcur_59);
            
            *(GibCursor *) loc_769 = tmpcur_2983;
            
            GibCursor end_from_tagged_dcon_redir_2629 = tmpcur_2983 +
                      tmptag_2985;
            GibCursor field_nxt_2624 = deref_2607 + 1;
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) field_nxt_2624;
            GibCursor tmpcur_2986 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_2987 = field_nxt_2624 + 8;
            uint16_t tmptag_2988 = GIB_GET_TAG(tagged_tmpcur_58);
            
            *(GibCursor *) soa_field_0_2606 = tmpcur_2986;
            
            GibCursor end_from_tagged_fld_redir_2630 = tmpcur_2986 +
                      tmptag_2988;
            GibCursor field_nxt_2625 = deref_2609 + 1;
            uintptr_t tagged_tmpcur_57 = *(uintptr_t *) field_nxt_2625;
            GibCursor tmpcur_2989 = GIB_UNTAG(tagged_tmpcur_57);
            GibCursor tmpaftercur_2990 = field_nxt_2625 + 8;
            uint16_t tmptag_2991 = GIB_GET_TAG(tagged_tmpcur_57);
            
            *(GibCursor *) soa_field_1_2608 = tmpcur_2989;
            
            GibCursor end_from_tagged_fld_redir_2631 = tmpcur_2989 +
                      tmptag_2991;
            GibCursor field_nxt_2626 = deref_2611 + 1;
            uintptr_t tagged_tmpcur_56 = *(uintptr_t *) field_nxt_2626;
            GibCursor tmpcur_2992 = GIB_UNTAG(tagged_tmpcur_56);
            GibCursor tmpaftercur_2993 = field_nxt_2626 + 8;
            uint16_t tmptag_2994 = GIB_GET_TAG(tagged_tmpcur_56);
            
            *(GibCursor *) soa_field_2_2610 = tmpcur_2992;
            
            GibCursor end_from_tagged_fld_redir_2632 = tmpcur_2992 +
                      tmptag_2994;
            GibCursor field_nxt_2627 = deref_2613 + 1;
            uintptr_t tagged_tmpcur_55 = *(uintptr_t *) field_nxt_2627;
            GibCursor tmpcur_2995 = GIB_UNTAG(tagged_tmpcur_55);
            GibCursor tmpaftercur_2996 = field_nxt_2627 + 8;
            uint16_t tmptag_2997 = GIB_GET_TAG(tagged_tmpcur_55);
            
            *(GibCursor *) soa_field_3_2612 = tmpcur_2995;
            
            GibCursor end_from_tagged_fld_redir_2633 = tmpcur_2995 +
                      tmptag_2997;
            GibCursor field_nxt_2628 = deref_2615 + 1;
            uintptr_t tagged_tmpcur_54 = *(uintptr_t *) field_nxt_2628;
            GibCursor tmpcur_2998 = GIB_UNTAG(tagged_tmpcur_54);
            GibCursor tmpaftercur_2999 = field_nxt_2628 + 8;
            uint16_t tmptag_3000 = GIB_GET_TAG(tagged_tmpcur_54);
            
            *(GibCursor *) soa_field_4_2614 = tmpcur_2998;
            
            GibCursor end_from_tagged_fld_redir_2634 = tmpcur_2998 +
                      tmptag_3000;
            GibCursor indr_1320[6] = {tmpcur_2983, tmpcur_2986, tmpcur_2989,
                                      tmpcur_2992, tmpcur_2995, tmpcur_2998};
            GibCursor chk_end_2639 = cursor_ptr_2491[0];
            GibBool chk_2640 = deref_dcon_var_2495 < chk_end_2639;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            unsigned char call_1333 =
                           _traverse_MultiList(arg_86_180_268, arg_86_180_268);
            GibCursor loc_cursor_ptr_2635[6];
            
            memcpy(loc_cursor_ptr_2635, arg_86_180_268, sizeof(GibCursor [6]));
            return call_1333;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2953");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_60 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_2745 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_835 = region_2745.start;
    GibCursor end_r_835 = region_2745.end;
    GibChunk region_2746 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_836 = region_2746.start;
    GibCursor end_r_836 = region_2746.end;
    GibChunk region_2747 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_837 = region_2747.start;
    GibCursor end_r_837 = region_2747.end;
    GibChunk region_2748 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_838 = region_2748.start;
    GibCursor end_r_838 = region_2748.end;
    GibChunk region_2749 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_839 = region_2749.start;
    GibCursor end_r_839 = region_2749.end;
    GibChunk region_2750 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_840 = region_2750.start;
    GibCursor end_r_840 = region_2750.end;
    GibCursor reg_ptr_2642[6] = {r_835, r_836, r_837, r_838, r_839, r_840};
    GibCursor reg_cursor_ptr_2643[6] = {end_r_835, end_r_836, end_r_837,
                                        end_r_838, end_r_839, end_r_840};
    GibCursor cursor_ptr_2644[6];
    
    memcpy(cursor_ptr_2644, reg_ptr_2642, sizeof(GibCursor [6]));
    
    GibCursor chk_loc_2662 = cursor_ptr_2644[0];
    GibCursor chk_end_2663 = reg_cursor_ptr_2643[0];
    GibBool chk_2664 = chk_loc_2662 < chk_end_2663;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2659 = cursor_ptr_2644[1];
    GibCursor chk_end_2660 = reg_cursor_ptr_2643[1];
    GibBool chk_2661 = chk_loc_2659 < chk_end_2660;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2656 = cursor_ptr_2644[2];
    GibCursor chk_end_2657 = reg_cursor_ptr_2643[2];
    GibBool chk_2658 = chk_loc_2656 < chk_end_2657;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2653 = cursor_ptr_2644[3];
    GibCursor chk_end_2654 = reg_cursor_ptr_2643[3];
    GibBool chk_2655 = chk_loc_2653 < chk_end_2654;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2650 = cursor_ptr_2644[4];
    GibCursor chk_end_2651 = reg_cursor_ptr_2643[4];
    GibBool chk_2652 = chk_loc_2650 < chk_end_2651;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2647 = cursor_ptr_2644[5];
    GibCursor chk_end_2648 = reg_cursor_ptr_2643[5];
    GibBool chk_2649 = chk_loc_2647 < chk_end_2648;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    unsigned char tup_packed_2665 =
                   mkMultiList(reg_cursor_ptr_2643, cursor_ptr_2644,
                               SCALAR_COUNT_MULTI_LIST_LEN);
    GibCursor end_xs_27_122_199[6];
    
    memcpy(end_xs_27_122_199, cursor_ptr_2644, sizeof(GibCursor [6]));

    int add1_iters = SCALAR_COUNT_MULTI_BENCH_ITERS;
    GibCursor recursive_reg_ptr[6] = {0};
    GibCursor recursive_reg_end[6] = {0};
    GibCursor loop_scalar_reg_ptr[6] = {0};
    GibCursor loop_scalar_reg_end[6] = {0};
    GibCursor indir_loop_scalar_reg_ptr[6] = {0};
    GibCursor indir_loop_scalar_reg_end[6] = {0};
    GibCursor indir_auto_reg_ptr[6] = {0};
    GibCursor indir_auto_reg_end[6] = {0};
    GibCursor indir_vector_reg_ptr[6] = {0};
    GibCursor indir_vector_reg_end[6] = {0};

    if (add1_iters <= 0) {
        fprintf(stderr, "SCALAR_COUNT_MULTI_BENCH_ITERS must be positive\n");
        exit(1);
    }

    double scalar_add1_seconds =
        manual_time_add1_multilist(add1MultiList,
                                   reg_cursor_ptr_2643,
                                   reg_ptr_2642,
                                   add1_iters,
                                   recursive_reg_ptr,
                                   recursive_reg_end);
    manual_loop_timing_reset_many(loop_scalar_hot_loop_timings,
                                  MANUAL_MULTI_INT_FIELDS);
    double loop_scalar_add1_seconds =
        manual_time_add1_multilist(manual_copy_scalar_add1MultiList,
                                   reg_cursor_ptr_2643,
                                   reg_ptr_2642,
                                   add1_iters,
                                   loop_scalar_reg_ptr,
                                   loop_scalar_reg_end);
    manual_loop_timing_reset_many(indir_loop_scalar_hot_loop_timings,
                                  MANUAL_MULTI_INT_FIELDS);
    double indir_loop_scalar_add1_seconds =
        manual_time_add1_multilist(manual_indir_scalar_add1MultiList,
                                   reg_cursor_ptr_2643,
                                   reg_ptr_2642,
                                   add1_iters,
                                   indir_loop_scalar_reg_ptr,
                                   indir_loop_scalar_reg_end);
    manual_loop_timing_reset_many(indir_loop_auto_hot_loop_timings,
                                  MANUAL_MULTI_INT_FIELDS);
    double indir_auto_add1_seconds =
        manual_time_add1_multilist(manual_indir_auto_add1MultiList,
                                   reg_cursor_ptr_2643,
                                   reg_ptr_2642,
                                   add1_iters,
                                   indir_auto_reg_ptr,
                                   indir_auto_reg_end);
    manual_loop_timing_reset_many(indir_loop_vectorized_hot_loop_timings,
                                  MANUAL_MULTI_INT_FIELDS);
    double indir_vector_add1_seconds =
        manual_time_add1_multilist(manual_vectorized_add1MultiList,
                                   reg_cursor_ptr_2643,
                                   reg_ptr_2642,
                                   add1_iters,
                                   indir_vector_reg_ptr,
                                   indir_vector_reg_end);
    GibInt scalar_sum =
        manual_sum_multilist_result(recursive_reg_end, recursive_reg_ptr);
    GibInt loop_scalar_sum =
        manual_sum_multilist_result(loop_scalar_reg_end, loop_scalar_reg_ptr);
    GibInt indir_loop_scalar_sum =
        manual_sum_multilist_result(indir_loop_scalar_reg_end,
                                    indir_loop_scalar_reg_ptr);
    GibInt indir_auto_sum =
        manual_sum_multilist_result(indir_auto_reg_end, indir_auto_reg_ptr);
    GibInt indir_vector_sum =
        manual_sum_multilist_result(indir_vector_reg_end, indir_vector_reg_ptr);
    GibInt expected_sum =
        (2 * (GibInt) SCALAR_COUNT_MULTI_LIST_LEN *
         (GibInt) SCALAR_COUNT_MULTI_LIST_LEN) +
        (12 * (GibInt) SCALAR_COUNT_MULTI_LIST_LEN);
    double loop_scalar_over_recursive =
        loop_scalar_add1_seconds > 0.0
            ? scalar_add1_seconds / loop_scalar_add1_seconds
            : 0.0;
    double indir_loop_scalar_over_recursive =
        indir_loop_scalar_add1_seconds > 0.0
            ? scalar_add1_seconds / indir_loop_scalar_add1_seconds
            : 0.0;
    double indir_auto_over_recursive =
        indir_auto_add1_seconds > 0.0
            ? scalar_add1_seconds / indir_auto_add1_seconds
            : 0.0;
    double indir_auto_over_indir_loop_scalar =
        indir_auto_add1_seconds > 0.0
            ? indir_loop_scalar_add1_seconds / indir_auto_add1_seconds
            : 0.0;
    double indir_vectorized_over_recursive =
        indir_vector_add1_seconds > 0.0
            ? scalar_add1_seconds / indir_vector_add1_seconds
            : 0.0;
    double indir_vectorized_over_indir_loop_scalar =
        indir_vector_add1_seconds > 0.0
            ? indir_loop_scalar_add1_seconds / indir_vector_add1_seconds
            : 0.0;
    double hot_loop_measurement_overhead_seconds =
        manual_measure_empty_timing_overhead(20000);
    double loop_scalar_hot_loop_total_raw_seconds =
        manual_loop_timing_total_seconds(loop_scalar_hot_loop_timings,
                                         MANUAL_MULTI_INT_FIELDS);
    double indir_loop_scalar_hot_loop_total_raw_seconds =
        manual_loop_timing_total_seconds(indir_loop_scalar_hot_loop_timings,
                                         MANUAL_MULTI_INT_FIELDS);
    double indir_auto_hot_loop_total_raw_seconds =
        manual_loop_timing_total_seconds(indir_loop_auto_hot_loop_timings,
                                         MANUAL_MULTI_INT_FIELDS);
    double indir_vectorized_hot_loop_total_raw_seconds =
        manual_loop_timing_total_seconds(indir_loop_vectorized_hot_loop_timings,
                                         MANUAL_MULTI_INT_FIELDS);
    uint64_t loop_scalar_hot_loop_total_calls =
        manual_loop_timing_total_calls(loop_scalar_hot_loop_timings,
                                       MANUAL_MULTI_INT_FIELDS);
    uint64_t indir_loop_scalar_hot_loop_total_calls =
        manual_loop_timing_total_calls(indir_loop_scalar_hot_loop_timings,
                                       MANUAL_MULTI_INT_FIELDS);
    uint64_t indir_auto_hot_loop_total_calls =
        manual_loop_timing_total_calls(indir_loop_auto_hot_loop_timings,
                                       MANUAL_MULTI_INT_FIELDS);
    uint64_t indir_vectorized_hot_loop_total_calls =
        manual_loop_timing_total_calls(indir_loop_vectorized_hot_loop_timings,
                                       MANUAL_MULTI_INT_FIELDS);
    uint64_t loop_scalar_hot_loop_total_elements =
        manual_loop_timing_total_elements(loop_scalar_hot_loop_timings,
                                          MANUAL_MULTI_INT_FIELDS);
    uint64_t indir_loop_scalar_hot_loop_total_elements =
        manual_loop_timing_total_elements(indir_loop_scalar_hot_loop_timings,
                                          MANUAL_MULTI_INT_FIELDS);
    uint64_t indir_auto_hot_loop_total_elements =
        manual_loop_timing_total_elements(indir_loop_auto_hot_loop_timings,
                                          MANUAL_MULTI_INT_FIELDS);
    uint64_t indir_vectorized_hot_loop_total_elements =
        manual_loop_timing_total_elements(indir_loop_vectorized_hot_loop_timings,
                                          MANUAL_MULTI_INT_FIELDS);
    double loop_scalar_hot_loop_total_seconds =
        loop_scalar_hot_loop_total_raw_seconds -
        ((double) loop_scalar_hot_loop_total_calls *
         hot_loop_measurement_overhead_seconds);
    double indir_loop_scalar_hot_loop_total_seconds =
        indir_loop_scalar_hot_loop_total_raw_seconds -
        ((double) indir_loop_scalar_hot_loop_total_calls *
         hot_loop_measurement_overhead_seconds);
    double indir_auto_hot_loop_total_seconds =
        indir_auto_hot_loop_total_raw_seconds -
        ((double) indir_auto_hot_loop_total_calls *
         hot_loop_measurement_overhead_seconds);
    double indir_vectorized_hot_loop_total_seconds =
        indir_vectorized_hot_loop_total_raw_seconds -
        ((double) indir_vectorized_hot_loop_total_calls *
         hot_loop_measurement_overhead_seconds);

    if (loop_scalar_hot_loop_total_seconds < 0.0) {
        loop_scalar_hot_loop_total_seconds = 0.0;
    }
    if (indir_loop_scalar_hot_loop_total_seconds < 0.0) {
        indir_loop_scalar_hot_loop_total_seconds = 0.0;
    }
    if (indir_auto_hot_loop_total_seconds < 0.0) {
        indir_auto_hot_loop_total_seconds = 0.0;
    }
    if (indir_vectorized_hot_loop_total_seconds < 0.0) {
        indir_vectorized_hot_loop_total_seconds = 0.0;
    }

    ManualLoopTiming loop_scalar_hot_loop_total = {
        loop_scalar_hot_loop_total_seconds,
        loop_scalar_hot_loop_total_calls,
        loop_scalar_hot_loop_total_elements,
    };
    ManualLoopTiming indir_loop_scalar_hot_loop_total = {
        indir_loop_scalar_hot_loop_total_seconds,
        indir_loop_scalar_hot_loop_total_calls,
        indir_loop_scalar_hot_loop_total_elements,
    };
    ManualLoopTiming indir_auto_hot_loop_total = {
        indir_auto_hot_loop_total_seconds,
        indir_auto_hot_loop_total_calls,
        indir_auto_hot_loop_total_elements,
    };
    ManualLoopTiming indir_vectorized_hot_loop_total = {
        indir_vectorized_hot_loop_total_seconds,
        indir_vectorized_hot_loop_total_calls,
        indir_vectorized_hot_loop_total_elements,
    };
    double indir_auto_hot_loop_over_indir_loop_scalar =
        indir_auto_hot_loop_total_seconds > 0.0
            ? indir_loop_scalar_hot_loop_total_seconds /
                  indir_auto_hot_loop_total_seconds
            : 0.0;
    double indir_vectorized_hot_loop_over_indir_loop_scalar =
        indir_vectorized_hot_loop_total_seconds > 0.0
            ? indir_loop_scalar_hot_loop_total_seconds /
                  indir_vectorized_hot_loop_total_seconds
            : 0.0;

    printf("program=multi-list\n");
    printf("multi_add1_len=%d\n", SCALAR_COUNT_MULTI_LIST_LEN);
    printf("multi_add1_inner_iters=%d\n", add1_iters);
    printf("multi_expected_sum=%ld\n", expected_sum);
    printf("recursive_sum=%ld\n", scalar_sum);
    printf("loop_scalar_sum=%ld\n", loop_scalar_sum);
    printf("indir_loop_scalar_sum=%ld\n", indir_loop_scalar_sum);
    printf("indir_loop_auto_sum=%ld\n", indir_auto_sum);
    printf("indir_loop_vectorized_sum=%ld\n", indir_vector_sum);
    printf("hot_loop_measurement_overhead_seconds=%.12f\n",
           hot_loop_measurement_overhead_seconds);
    printf("recursive_add1_seconds=%.9f\n", scalar_add1_seconds);
    printf("loop_scalar_add1_seconds=%.9f\n", loop_scalar_add1_seconds);
    printf("loop_scalar_hot_loop_total_raw_seconds=%.9f\n",
           loop_scalar_hot_loop_total_raw_seconds);
    printf("loop_scalar_hot_loop_total_seconds=%.9f\n",
           loop_scalar_hot_loop_total_seconds);
    printf("loop_scalar_hot_loop_total_calls=%" PRIu64 "\n",
           loop_scalar_hot_loop_total_calls);
    printf("loop_scalar_hot_loop_total_elements=%" PRIu64 "\n",
           loop_scalar_hot_loop_total_elements);
    printf("loop_scalar_hot_loop_total_ns_per_element=%.3f\n",
           manual_loop_timing_ns_per_elem(&loop_scalar_hot_loop_total));
    printf("indir_loop_scalar_add1_seconds=%.9f\n",
           indir_loop_scalar_add1_seconds);
    printf("indir_loop_scalar_hot_loop_total_raw_seconds=%.9f\n",
           indir_loop_scalar_hot_loop_total_raw_seconds);
    printf("indir_loop_scalar_hot_loop_total_seconds=%.9f\n",
           indir_loop_scalar_hot_loop_total_seconds);
    printf("indir_loop_scalar_hot_loop_total_calls=%" PRIu64 "\n",
           indir_loop_scalar_hot_loop_total_calls);
    printf("indir_loop_scalar_hot_loop_total_elements=%" PRIu64 "\n",
           indir_loop_scalar_hot_loop_total_elements);
    printf("indir_loop_scalar_hot_loop_total_ns_per_element=%.3f\n",
           manual_loop_timing_ns_per_elem(&indir_loop_scalar_hot_loop_total));
    printf("indir_loop_auto_add1_seconds=%.9f\n",
           indir_auto_add1_seconds);
    printf("indir_loop_auto_hot_loop_total_raw_seconds=%.9f\n",
           indir_auto_hot_loop_total_raw_seconds);
    printf("indir_loop_auto_hot_loop_total_seconds=%.9f\n",
           indir_auto_hot_loop_total_seconds);
    printf("indir_loop_auto_hot_loop_total_calls=%" PRIu64 "\n",
           indir_auto_hot_loop_total_calls);
    printf("indir_loop_auto_hot_loop_total_elements=%" PRIu64 "\n",
           indir_auto_hot_loop_total_elements);
    printf("indir_loop_auto_hot_loop_total_ns_per_element=%.3f\n",
           manual_loop_timing_ns_per_elem(&indir_auto_hot_loop_total));
    printf("indir_loop_vectorized_add1_seconds=%.9f\n",
           indir_vector_add1_seconds);
    printf("indir_loop_vectorized_hot_loop_total_raw_seconds=%.9f\n",
           indir_vectorized_hot_loop_total_raw_seconds);
    printf("indir_loop_vectorized_hot_loop_total_seconds=%.9f\n",
           indir_vectorized_hot_loop_total_seconds);
    printf("indir_loop_vectorized_hot_loop_total_calls=%" PRIu64 "\n",
           indir_vectorized_hot_loop_total_calls);
    printf("indir_loop_vectorized_hot_loop_total_elements=%" PRIu64 "\n",
           indir_vectorized_hot_loop_total_elements);
    printf("indir_loop_vectorized_hot_loop_total_ns_per_element=%.3f\n",
           manual_loop_timing_ns_per_elem(&indir_vectorized_hot_loop_total));
    printf("speedup_loop_scalar_over_recursive=%.3fx\n",
           loop_scalar_over_recursive);
    printf("speedup_indir_loop_scalar_over_recursive=%.3fx\n",
           indir_loop_scalar_over_recursive);
    printf("speedup_indir_loop_auto_over_recursive=%.3fx\n",
           indir_auto_over_recursive);
    printf("speedup_indir_loop_auto_over_indir_loop_scalar=%.3fx\n",
           indir_auto_over_indir_loop_scalar);
    printf("speedup_indir_loop_auto_hot_loop_over_indir_loop_scalar=%.3fx\n",
           indir_auto_hot_loop_over_indir_loop_scalar);
    printf("speedup_indir_loop_vectorized_over_recursive=%.3fx\n",
           indir_vectorized_over_recursive);
    printf("speedup_indir_loop_vectorized_over_indir_loop_scalar=%.3fx\n",
           indir_vectorized_over_indir_loop_scalar);
    printf("speedup_indir_loop_vectorized_hot_loop_over_indir_loop_scalar=%.3fx\n",
           indir_vectorized_hot_loop_over_indir_loop_scalar);
    for (int field_ix = 0; field_ix < MANUAL_MULTI_INT_FIELDS; field_ix++) {
        double loop_scalar_field_seconds =
            manual_loop_timing_adjusted_seconds(
                &loop_scalar_hot_loop_timings[field_ix],
                hot_loop_measurement_overhead_seconds);
        double indir_loop_scalar_field_seconds =
            manual_loop_timing_adjusted_seconds(
                &indir_loop_scalar_hot_loop_timings[field_ix],
                hot_loop_measurement_overhead_seconds);
        double indir_loop_auto_field_seconds =
            manual_loop_timing_adjusted_seconds(
                &indir_loop_auto_hot_loop_timings[field_ix],
                hot_loop_measurement_overhead_seconds);
        double indir_loop_vectorized_field_seconds =
            manual_loop_timing_adjusted_seconds(
                &indir_loop_vectorized_hot_loop_timings[field_ix],
                hot_loop_measurement_overhead_seconds);
        printf("loop_scalar_hot_loop_field%d_raw_seconds=%.9f\n",
               field_ix, loop_scalar_hot_loop_timings[field_ix].seconds);
        printf("loop_scalar_hot_loop_field%d_seconds=%.9f\n",
               field_ix, loop_scalar_field_seconds);
        printf("loop_scalar_hot_loop_field%d_calls=%" PRIu64 "\n",
               field_ix, loop_scalar_hot_loop_timings[field_ix].calls);
        printf("loop_scalar_hot_loop_field%d_elements=%" PRIu64 "\n",
               field_ix, loop_scalar_hot_loop_timings[field_ix].elements);
        printf("loop_scalar_hot_loop_field%d_ns_per_element=%.3f\n",
               field_ix,
               manual_loop_timing_ns_per_elem_for_seconds(
                   &loop_scalar_hot_loop_timings[field_ix],
                   loop_scalar_field_seconds));
        printf("indir_loop_scalar_hot_loop_field%d_raw_seconds=%.9f\n",
               field_ix, indir_loop_scalar_hot_loop_timings[field_ix].seconds);
        printf("indir_loop_scalar_hot_loop_field%d_seconds=%.9f\n",
               field_ix, indir_loop_scalar_field_seconds);
        printf("indir_loop_scalar_hot_loop_field%d_calls=%" PRIu64 "\n",
               field_ix, indir_loop_scalar_hot_loop_timings[field_ix].calls);
        printf("indir_loop_scalar_hot_loop_field%d_elements=%" PRIu64 "\n",
               field_ix, indir_loop_scalar_hot_loop_timings[field_ix].elements);
        printf("indir_loop_scalar_hot_loop_field%d_ns_per_element=%.3f\n",
               field_ix,
               manual_loop_timing_ns_per_elem_for_seconds(
                   &indir_loop_scalar_hot_loop_timings[field_ix],
                   indir_loop_scalar_field_seconds));
        printf("indir_loop_auto_hot_loop_field%d_raw_seconds=%.9f\n",
               field_ix, indir_loop_auto_hot_loop_timings[field_ix].seconds);
        printf("indir_loop_auto_hot_loop_field%d_seconds=%.9f\n",
               field_ix, indir_loop_auto_field_seconds);
        printf("indir_loop_auto_hot_loop_field%d_calls=%" PRIu64 "\n",
               field_ix, indir_loop_auto_hot_loop_timings[field_ix].calls);
        printf("indir_loop_auto_hot_loop_field%d_elements=%" PRIu64 "\n",
               field_ix, indir_loop_auto_hot_loop_timings[field_ix].elements);
        printf("indir_loop_auto_hot_loop_field%d_ns_per_element=%.3f\n",
               field_ix,
               manual_loop_timing_ns_per_elem_for_seconds(
                   &indir_loop_auto_hot_loop_timings[field_ix],
                   indir_loop_auto_field_seconds));
        printf("indir_loop_vectorized_hot_loop_field%d_raw_seconds=%.9f\n",
               field_ix, indir_loop_vectorized_hot_loop_timings[field_ix].seconds);
        printf("indir_loop_vectorized_hot_loop_field%d_seconds=%.9f\n",
               field_ix, indir_loop_vectorized_field_seconds);
        printf("indir_loop_vectorized_hot_loop_field%d_calls=%" PRIu64 "\n",
               field_ix, indir_loop_vectorized_hot_loop_timings[field_ix].calls);
        printf("indir_loop_vectorized_hot_loop_field%d_elements=%" PRIu64 "\n",
               field_ix, indir_loop_vectorized_hot_loop_timings[field_ix].elements);
        printf("indir_loop_vectorized_hot_loop_field%d_ns_per_element=%.3f\n",
               field_ix,
               manual_loop_timing_ns_per_elem_for_seconds(
                   &indir_loop_vectorized_hot_loop_timings[field_ix],
                   indir_loop_vectorized_field_seconds));
    }
    printf("sums_match=%s\n",
           scalar_sum == expected_sum &&
           loop_scalar_sum == expected_sum &&
           indir_loop_scalar_sum == expected_sum &&
           indir_auto_sum == expected_sum &&
           indir_vector_sum == expected_sum
               ? "yes" : "no");

    int bench_exit_61 = gib_exit();

    return bench_exit_61;
    
    GibChunk region_2751 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_829 = region_2751.start;
    GibCursor end_r_829 = region_2751.end;
    GibChunk region_2752 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_830 = region_2752.start;
    GibCursor end_r_830 = region_2752.end;
    GibChunk region_2753 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_831 = region_2753.start;
    GibCursor end_r_831 = region_2753.end;
    GibChunk region_2754 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_832 = region_2754.start;
    GibCursor end_r_832 = region_2754.end;
    GibChunk region_2755 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_833 = region_2755.start;
    GibCursor end_r_833 = region_2755.end;
    GibChunk region_2756 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_834 = region_2756.start;
    GibCursor end_r_834 = region_2756.end;
    GibCursor reg_ptr_2667[6] = {r_829, r_830, r_831, r_832, r_833, r_834};
    GibCursor reg_cursor_ptr_2668[6] = {end_r_829, end_r_830, end_r_831,
                                        end_r_832, end_r_833, end_r_834};
    GibCursor cursor_ptr_2669[6];
    
    memcpy(cursor_ptr_2669, reg_ptr_2667, sizeof(GibCursor [6]));
    
    GibCursor chk_loc_2709 = cursor_ptr_2644[0];
    GibCursor chk_end_2710 = reg_cursor_ptr_2643[0];
    GibBool chk_2711 = chk_loc_2709 < chk_end_2710;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2706 = cursor_ptr_2644[1];
    GibCursor chk_end_2707 = reg_cursor_ptr_2643[1];
    GibBool chk_2708 = chk_loc_2706 < chk_end_2707;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2703 = cursor_ptr_2644[2];
    GibCursor chk_end_2704 = reg_cursor_ptr_2643[2];
    GibBool chk_2705 = chk_loc_2703 < chk_end_2704;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2700 = cursor_ptr_2644[3];
    GibCursor chk_end_2701 = reg_cursor_ptr_2643[3];
    GibBool chk_2702 = chk_loc_2700 < chk_end_2701;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2697 = cursor_ptr_2644[4];
    GibCursor chk_end_2698 = reg_cursor_ptr_2643[4];
    GibBool chk_2699 = chk_loc_2697 < chk_end_2698;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2694 = cursor_ptr_2644[5];
    GibCursor chk_end_2695 = reg_cursor_ptr_2643[5];
    GibBool chk_2696 = chk_loc_2694 < chk_end_2695;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2691 = cursor_ptr_2669[0];
    GibCursor chk_end_2692 = reg_cursor_ptr_2668[0];
    GibBool chk_2693 = chk_loc_2691 < chk_end_2692;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2688 = cursor_ptr_2669[1];
    GibCursor chk_end_2689 = reg_cursor_ptr_2668[1];
    GibBool chk_2690 = chk_loc_2688 < chk_end_2689;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2685 = cursor_ptr_2669[2];
    GibCursor chk_end_2686 = reg_cursor_ptr_2668[2];
    GibBool chk_2687 = chk_loc_2685 < chk_end_2686;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2682 = cursor_ptr_2669[3];
    GibCursor chk_end_2683 = reg_cursor_ptr_2668[3];
    GibBool chk_2684 = chk_loc_2682 < chk_end_2683;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2679 = cursor_ptr_2669[4];
    GibCursor chk_end_2680 = reg_cursor_ptr_2668[4];
    GibBool chk_2681 = chk_loc_2679 < chk_end_2680;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2676 = cursor_ptr_2669[5];
    GibCursor chk_end_2677 = reg_cursor_ptr_2668[5];
    GibBool chk_2678 = chk_loc_2676 < chk_end_2677;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor copy_address_2675[6];
    
    memcpy(copy_address_2675, reg_ptr_2642, sizeof(GibCursor [6]));
    
    unsigned char tup_packed_2712 =
                   add1MultiList(reg_cursor_ptr_2643, reg_cursor_ptr_2668, cursor_ptr_2669, copy_address_2675);
    GibCursor end_xs__28_123_200[6];
    
    memcpy(end_xs__28_123_200, cursor_ptr_2669, sizeof(GibCursor [6]));
    
    GibCursor chk_loc_2733 = cursor_ptr_2669[0];
    GibCursor chk_end_2734 = reg_cursor_ptr_2668[0];
    GibBool chk_2735 = chk_loc_2733 < chk_end_2734;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2730 = cursor_ptr_2669[1];
    GibCursor chk_end_2731 = reg_cursor_ptr_2668[1];
    GibBool chk_2732 = chk_loc_2730 < chk_end_2731;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2727 = cursor_ptr_2669[2];
    GibCursor chk_end_2728 = reg_cursor_ptr_2668[2];
    GibBool chk_2729 = chk_loc_2727 < chk_end_2728;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2724 = cursor_ptr_2669[3];
    GibCursor chk_end_2725 = reg_cursor_ptr_2668[3];
    GibBool chk_2726 = chk_loc_2724 < chk_end_2725;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2721 = cursor_ptr_2669[4];
    GibCursor chk_end_2722 = reg_cursor_ptr_2668[4];
    GibBool chk_2723 = chk_loc_2721 < chk_end_2722;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor chk_loc_2718 = cursor_ptr_2669[5];
    GibCursor chk_end_2719 = reg_cursor_ptr_2668[5];
    GibBool chk_2720 = chk_loc_2718 < chk_end_2719;
    
    #ifdef _GIBBON_DEBUG
    #endif
    
    GibCursor copy_address_2717[6];
    
    memcpy(copy_address_2717, reg_ptr_2667, sizeof(GibCursor [6]));
    
    GibInt tailapp_1196 =  sumMultiList(reg_cursor_ptr_2668, copy_address_2717);
    
    printf("%ld", tailapp_1196);
    printf("\n");
    
    int exit_61 = gib_exit();
    
    return exit_61;
}
