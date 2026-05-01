#include <errno.h>
#include <immintrin.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(SIMPLE_INT_WIDTH) && SIMPLE_INT_WIDTH == 32
typedef int IntType;
#else
typedef long IntType;
#endif

typedef struct footer {
    IntType length;
    void *next;
} Footer;

typedef struct prod2 {
    IntType *start;
    Footer *end;
} Prod2;

typedef struct config {
    IntType list_len;
    int iterations;
    bool print_arrays;
} Config;

typedef struct benchmark_result {
    const char *name;
    double total_seconds;
    double avg_seconds;
    double hot_loop_raw_seconds;
    double hot_loop_measurement_overhead_seconds;
    double hot_loop_seconds;
    double hot_loop_avg_seconds;
    double hot_loop_ns_per_element;
    double hot_loop_calls;
    double hot_loop_elements;
    long sum;
    bool ok;
    bool enabled;
} BenchmarkResult;

typedef Prod2 *(*Add1Fn)(const Prod2 *prod);
typedef void (*ChunkKernel)(IntType *out, const IntType *in, size_t count);

typedef struct variant_spec {
    const char *name;
    Add1Fn fn;
    bool enabled;
} VariantSpec;

#if defined(__GNUC__)
#define NOINLINE __attribute__((noinline))
#define NO_TREE_VECTORIZE __attribute__((optimize("no-tree-vectorize")))
#define TARGET_SSE2 __attribute__((target("sse2")))
#define TARGET_AVX2 __attribute__((target("avx2")))
#else
#define NOINLINE
#define NO_TREE_VECTORIZE
#define TARGET_SSE2
#define TARGET_AVX2
#endif

#define DEFAULT_LIST_LEN 100000
#define DEFAULT_ITERATIONS 30
#define INITIAL_CHUNK_SIZE 10
#define CHUNK_GROWTH_FACTOR 2

static void parse_args(int argc, char **argv, Config *cfg);
static void print_usage(const char *progname);
static double now_seconds(void);
static long expected_sum_after_add1(IntType list_len);
static size_t chunk_payload_bytes(size_t elem_count);
static Prod2 *build_chunked_array(IntType total_list_size);
static void free_chunked_array(Prod2 *prod);
static void print_chunked_array(const Prod2 *prod);
static long sum_chunked_array(const Prod2 *prod);
static Prod2 *map_chunked_array(const Prod2 *prod,
                                ChunkKernel kernel,
                                BenchmarkResult *result,
                                bool record_time);
static Prod2 *add1_chunked_arr_scalar(const Prod2 *prod);
static Prod2 *add1_chunked_arr_auto(const Prod2 *prod);
static Prod2 *add1_chunked_arr_vectorized_sse2(const Prod2 *prod);
static Prod2 *add1_chunked_arr_vectorized_avx2(const Prod2 *prod);
static NOINLINE NO_TREE_VECTORIZE void add1_scalar_kernel(IntType *out, const IntType *in, size_t count);
static NOINLINE void add1_auto_kernel(IntType *out, const IntType *in, size_t count);
static TARGET_SSE2 NOINLINE void add1_sse2_kernel(IntType *out, const IntType *in, size_t count);
static TARGET_AVX2 NOINLINE void add1_avx2_kernel(IntType *out, const IntType *in, size_t count);
static bool run_variant_once(BenchmarkResult *result,
                             Add1Fn fn,
                             const Prod2 *input,
                             long expected_sum,
                             bool record_time);
static void finalize_benchmark_results(BenchmarkResult *results, size_t count, int iterations);
static double measure_empty_timing_overhead(size_t calls);

static double now_seconds(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        perror("clock_gettime");
        exit(1);
    }
    return (double) ts.tv_sec + ((double) ts.tv_nsec / 1000000000.0);
}

static long expected_sum_after_add1(IntType list_len) {
    long n = (long) list_len;
    return (n * (n + 1)) / 2;
}

static size_t chunk_payload_bytes(size_t elem_count) {
    return (elem_count * sizeof(IntType)) + sizeof(Footer);
}

static void parse_args(int argc, char **argv, Config *cfg) {
    cfg->list_len = DEFAULT_LIST_LEN;
    cfg->iterations = DEFAULT_ITERATIONS;
    cfg->print_arrays = false;

    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--list-len") == 0) {
            if (i + 1 >= argc) {
                fprintf(stderr, "--list-len requires an integer\n");
                exit(1);
            }
            cfg->list_len = strtol(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--iterations") == 0) {
            if (i + 1 >= argc) {
                fprintf(stderr, "--iterations requires an integer\n");
                exit(1);
            }
            cfg->iterations = (int) strtol(argv[++i], NULL, 10);
        } else if (strcmp(argv[i], "--print") == 0) {
            cfg->print_arrays = true;
        } else if (strcmp(argv[i], "--help") == 0 || strcmp(argv[i], "-h") == 0) {
            print_usage(argv[0]);
            exit(0);
        } else {
            fprintf(stderr, "Unknown argument: %s\n", argv[i]);
            print_usage(argv[0]);
            exit(1);
        }
    }

    if (cfg->list_len <= 0) {
        fprintf(stderr, "--list-len must be positive\n");
        exit(1);
    }
    if (cfg->iterations <= 0) {
        fprintf(stderr, "--iterations must be positive\n");
        exit(1);
    }
}

static void print_usage(const char *progname) {
    fprintf(stderr,
            "Usage: %s [--list-len N] [--iterations N] [--print]\n",
            progname);
}

static Prod2 *build_chunked_array(IntType total_list_size) {
    Prod2 *prod = (Prod2 *) malloc(sizeof(Prod2));
    Footer *prev_footer = NULL;
    IntType first_chunk_size = 0;
    IntType num_elements_written = 0;
    IntType next_alloc_size = INITIAL_CHUNK_SIZE;
    IntType elem_id = 0;

    if (prod == NULL) {
        perror("malloc prod");
        return NULL;
    }

    prod->start = NULL;
    prod->end = NULL;

    while (num_elements_written < total_list_size) {
        IntType current_chunk_size = next_alloc_size;
        IntType remaining = total_list_size - num_elements_written;
        if (current_chunk_size > remaining) {
            current_chunk_size = remaining;
        }
        if (current_chunk_size <= 0) {
            break;
        }

        IntType *arr = (IntType *) malloc(chunk_payload_bytes((size_t) current_chunk_size));
        if (arr == NULL) {
            perror("malloc chunk");
            free_chunked_array(prod);
            return NULL;
        }

        if (prev_footer != NULL) {
            prev_footer->next = arr;
        }
        if (prod->start == NULL) {
            prod->start = arr;
            first_chunk_size = current_chunk_size;
        }

        for (IntType i = 0; i < current_chunk_size; i++) {
            arr[i] = elem_id++;
        }

        num_elements_written += current_chunk_size;
        next_alloc_size *= CHUNK_GROWTH_FACTOR;

        IntType length_for_footer = 0;
        if (num_elements_written < total_list_size) {
            IntType next_remaining = total_list_size - num_elements_written;
            length_for_footer = next_alloc_size;
            if (length_for_footer > next_remaining) {
                length_for_footer = next_remaining;
            }
        }

        Footer *current_footer = (Footer *) (arr + current_chunk_size);
        current_footer->length = length_for_footer;
        current_footer->next = NULL;
        prod->end = current_footer;
        prev_footer = current_footer;
    }

    if (prod->end != NULL) {
        prod->end->length = first_chunk_size;
    }

    return prod;
}

static void free_chunked_array(Prod2 *prod) {
    if (prod == NULL) {
        return;
    }
    if (prod->start == NULL) {
        free(prod);
        return;
    }

    IntType *current_chunk = prod->start;
    IntType size = prod->end->length;

    while (current_chunk != NULL) {
        Footer *footer = (Footer *) (current_chunk + size);
        IntType next_size = footer->length;
        IntType *next_chunk = (IntType *) footer->next;
        free(current_chunk);
        current_chunk = next_chunk;
        size = next_size;
    }

    free(prod);
}

static void print_chunked_array(const Prod2 *prod) {
    if (prod == NULL || prod->start == NULL) {
        printf("<empty>\n");
        return;
    }

    const IntType *current_chunk = prod->start;
    IntType size = prod->end->length;
    while (current_chunk != NULL) {
        for (IntType i = 0; i < size; i++) {
            printf("%ld ", (long) current_chunk[i]);
        }
        printf("--F--");
        const Footer *footer = (const Footer *) (current_chunk + size);
        size = footer->length;
        current_chunk = (const IntType *) footer->next;
    }
    printf("\n");
}

static long sum_chunked_array(const Prod2 *prod) {
    if (prod == NULL || prod->start == NULL) {
        return 0;
    }

    const IntType *current_chunk = prod->start;
    IntType size = prod->end->length;
    long sum = 0;

    while (current_chunk != NULL) {
        for (IntType i = 0; i < size; i++) {
            sum += current_chunk[i];
        }
        const Footer *footer = (const Footer *) (current_chunk + size);
        size = footer->length;
        current_chunk = (const IntType *) footer->next;
    }

    return sum;
}

static Prod2 *map_chunked_array(const Prod2 *prod,
                                ChunkKernel kernel,
                                BenchmarkResult *result,
                                bool record_time) {
    if (prod == NULL || prod->start == NULL) {
        return NULL;
    }

    Prod2 *out_prod = (Prod2 *) malloc(sizeof(Prod2));
    Footer *prev_footer = NULL;
    const IntType *current_chunk = prod->start;
    IntType size = prod->end->length;

    if (out_prod == NULL) {
        perror("malloc out_prod");
        return NULL;
    }

    out_prod->start = NULL;
    out_prod->end = NULL;

    while (current_chunk != NULL) {
        IntType *out_chunk = (IntType *) malloc(chunk_payload_bytes((size_t) size));
        if (out_chunk == NULL) {
            perror("malloc out_chunk");
            free_chunked_array(out_prod);
            return NULL;
        }

        if (out_prod->start == NULL) {
            out_prod->start = out_chunk;
        }
        if (prev_footer != NULL) {
            prev_footer->next = out_chunk;
        }

        if (record_time) {
            double start = now_seconds();
            kernel(out_chunk, current_chunk, (size_t) size);
            double end = now_seconds();
            result->hot_loop_raw_seconds += end - start;
            result->hot_loop_calls += 1.0;
            result->hot_loop_elements += (double) size;
        } else {
            kernel(out_chunk, current_chunk, (size_t) size);
        }

        const Footer *in_footer = (const Footer *) (current_chunk + size);
        Footer *out_footer = (Footer *) (out_chunk + size);
        out_footer->length = in_footer->length;
        out_footer->next = NULL;

        out_prod->end = out_footer;
        prev_footer = out_footer;

        size = in_footer->length;
        current_chunk = (const IntType *) in_footer->next;
    }

    return out_prod;
}

static Prod2 *add1_chunked_arr_scalar(const Prod2 *prod) {
    return map_chunked_array(prod, add1_scalar_kernel, NULL, false);
}

static Prod2 *add1_chunked_arr_auto(const Prod2 *prod) {
    return map_chunked_array(prod, add1_auto_kernel, NULL, false);
}

static Prod2 *add1_chunked_arr_vectorized_sse2(const Prod2 *prod) {
    return map_chunked_array(prod, add1_sse2_kernel, NULL, false);
}

static Prod2 *add1_chunked_arr_vectorized_avx2(const Prod2 *prod) {
    return map_chunked_array(prod, add1_avx2_kernel, NULL, false);
}

static NOINLINE NO_TREE_VECTORIZE void add1_scalar_kernel(IntType *out,
                                                          const IntType *in,
                                                          size_t count) {
    for (size_t i = 0; i < count; i++) {
        out[i] = in[i] + 1;
    }
}

static NOINLINE void add1_auto_kernel(IntType *out,
                                      const IntType *in,
                                      size_t count) {
    for (size_t i = 0; i < count; i++) {
        out[i] = in[i] + 1;
    }
}

static TARGET_SSE2 NOINLINE void add1_sse2_kernel(IntType *out,
                                                  const IntType *in,
                                                  size_t count) {
    size_t i = 0;
    if (sizeof(IntType) == sizeof(int)) {
        const __m128i ones = _mm_set1_epi32(1);
        for (; i + 3 < count; i += 4) {
            __m128i vals = _mm_loadu_si128((const __m128i *) (in + i));
            vals = _mm_add_epi32(vals, ones);
            _mm_storeu_si128((__m128i *) (out + i), vals);
        }
    } else {
        const __m128i ones = _mm_set1_epi64x(1);
        for (; i + 1 < count; i += 2) {
            __m128i vals = _mm_loadu_si128((const __m128i *) (in + i));
            vals = _mm_add_epi64(vals, ones);
            _mm_storeu_si128((__m128i *) (out + i), vals);
        }
    }

    for (; i < count; i++) {
        out[i] = in[i] + 1;
    }
}

static TARGET_AVX2 NOINLINE void add1_avx2_kernel(IntType *out,
                                                  const IntType *in,
                                                  size_t count) {
    size_t i = 0;
    if (sizeof(IntType) == sizeof(int)) {
        const __m256i ones = _mm256_set1_epi32(1);
        for (; i + 7 < count; i += 8) {
            __m256i vals = _mm256_loadu_si256((const __m256i *) (in + i));
            vals = _mm256_add_epi32(vals, ones);
            _mm256_storeu_si256((__m256i *) (out + i), vals);
        }
    } else {
        const __m256i ones = _mm256_set1_epi64x(1);
        for (; i + 3 < count; i += 4) {
            __m256i vals = _mm256_loadu_si256((const __m256i *) (in + i));
            vals = _mm256_add_epi64(vals, ones);
            _mm256_storeu_si256((__m256i *) (out + i), vals);
        }
    }

    for (; i < count; i++) {
        out[i] = in[i] + 1;
    }

    _mm256_zeroupper();
}

static double measure_empty_timing_overhead(size_t calls) {
    double total = 0.0;
    for (size_t i = 0; i < calls; i++) {
        double start = now_seconds();
        double end = now_seconds();
        total += end - start;
    }
    return total;
}

static bool run_variant_once(BenchmarkResult *result,
                             Add1Fn fn,
                             const Prod2 *input,
                             long expected_sum,
                             bool record_time) {
    double start = 0.0;
    double end = 0.0;
    Prod2 *out = NULL;
    if (record_time) {
        start = now_seconds();
        if (fn == add1_chunked_arr_scalar) {
            out = map_chunked_array(input, add1_scalar_kernel, result, true);
        } else if (fn == add1_chunked_arr_auto) {
            out = map_chunked_array(input, add1_auto_kernel, result, true);
        } else if (fn == add1_chunked_arr_vectorized_sse2) {
            out = map_chunked_array(input, add1_sse2_kernel, result, true);
        } else if (fn == add1_chunked_arr_vectorized_avx2) {
            out = map_chunked_array(input, add1_avx2_kernel, result, true);
        } else {
            out = fn(input);
        }
        end = now_seconds();
    } else {
        out = fn(input);
    }
    if (out == NULL) {
        result->ok = false;
        return false;
    }

    long sum = sum_chunked_array(out);
    if (sum != expected_sum) {
        result->ok = false;
    }

    result->sum = sum;
    if (record_time) {
        result->total_seconds += end - start;
    }

    free_chunked_array(out);
    return result->ok;
}

static void finalize_benchmark_results(BenchmarkResult *results,
                                       size_t count,
                                       int iterations) {
    for (size_t i = 0; i < count; i++) {
        if (!results[i].enabled) {
            continue;
        }
        if (results[i].ok) {
            results[i].avg_seconds = results[i].total_seconds / (double) iterations;
            results[i].hot_loop_measurement_overhead_seconds =
                measure_empty_timing_overhead((size_t) results[i].hot_loop_calls);
            results[i].hot_loop_seconds =
                results[i].hot_loop_raw_seconds - results[i].hot_loop_measurement_overhead_seconds;
            if (results[i].hot_loop_seconds < 0.0) {
                results[i].hot_loop_seconds = 0.0;
            }
            results[i].hot_loop_avg_seconds = results[i].hot_loop_seconds / (double) iterations;
            if (results[i].hot_loop_elements > 0.0) {
                results[i].hot_loop_ns_per_element =
                    (results[i].hot_loop_seconds * 1000000000.0) / results[i].hot_loop_elements;
            }
            results[i].hot_loop_calls /= (double) iterations;
            results[i].hot_loop_elements /= (double) iterations;
        }
    }
}

int main(int argc, char **argv) {
    Config cfg;
    parse_args(argc, argv, &cfg);

    Prod2 *input = build_chunked_array(cfg.list_len);
    if (input == NULL) {
        return 1;
    }

    if (cfg.print_arrays) {
        Prod2 *preview = add1_chunked_arr_scalar(input);
        print_chunked_array(input);
        print_chunked_array(preview);
        free_chunked_array(preview);
    }

    const long expected_sum = expected_sum_after_add1(cfg.list_len);
    const bool avx2_supported = __builtin_cpu_supports("avx2");

    VariantSpec specs[] = {
        {"scalar", add1_chunked_arr_scalar, true},
        {"auto", add1_chunked_arr_auto, true},
        {"sse2", add1_chunked_arr_vectorized_sse2, true},
        {"avx2", add1_chunked_arr_vectorized_avx2, avx2_supported},
    };
    BenchmarkResult results[4];
    size_t enabled_count = 0;

    for (size_t i = 0; i < 4; i++) {
        results[i].name = specs[i].name;
        results[i].total_seconds = 0.0;
        results[i].avg_seconds = 0.0;
        results[i].hot_loop_raw_seconds = 0.0;
        results[i].hot_loop_measurement_overhead_seconds = 0.0;
        results[i].hot_loop_seconds = 0.0;
        results[i].hot_loop_avg_seconds = 0.0;
        results[i].hot_loop_ns_per_element = 0.0;
        results[i].hot_loop_calls = 0.0;
        results[i].hot_loop_elements = 0.0;
        results[i].sum = 0;
        results[i].ok = specs[i].enabled;
        results[i].enabled = specs[i].enabled;
        if (specs[i].enabled) {
            enabled_count++;
        }
    }

    for (size_t i = 0; i < 4; i++) {
        if (!specs[i].enabled) {
            continue;
        }
        if (!run_variant_once(&results[i], specs[i].fn, input, expected_sum, false)) {
            break;
        }
    }

    if (enabled_count > 0) {
        for (int iter = 0; iter < cfg.iterations; iter++) {
            size_t start_ix = (size_t) iter % enabled_count;
            size_t seen = 0;
            for (size_t offset = 0; offset < 4; offset++) {
                size_t idx = (start_ix + offset) % 4;
                if (!specs[idx].enabled) {
                    continue;
                }
                if (!run_variant_once(&results[idx], specs[idx].fn, input, expected_sum, true)) {
                    break;
                }
                seen++;
                if (seen == enabled_count) {
                    break;
                }
            }
        }
    }

    finalize_benchmark_results(results, 4, cfg.iterations);

    BenchmarkResult scalar_result = results[0];
    BenchmarkResult auto_result = results[1];
    BenchmarkResult sse2_result = results[2];
    BenchmarkResult avx2_result = results[3];

    const bool sums_match =
        scalar_result.ok &&
        auto_result.ok &&
        sse2_result.ok &&
        (!avx2_supported || avx2_result.ok) &&
        scalar_result.sum == expected_sum &&
        auto_result.sum == expected_sum &&
        sse2_result.sum == expected_sum &&
        (!avx2_supported || avx2_result.sum == expected_sum);

    printf("list_len=%ld\n", (long) cfg.list_len);
    printf("iterations=%d\n", cfg.iterations);
    printf("int_size_bits=%zu\n", sizeof(IntType) * 8);
    printf("expected_sum=%ld\n", expected_sum);
    printf("avx2_supported=%s\n", avx2_supported ? "yes" : "no");
    printf("scalar_seconds=%.9f\n", scalar_result.avg_seconds);
    printf("auto_seconds=%.9f\n", auto_result.avg_seconds);
    printf("sse2_seconds=%.9f\n", sse2_result.avg_seconds);
    if (avx2_supported) {
        printf("avx2_seconds=%.9f\n", avx2_result.avg_seconds);
    }
    printf("scalar_sum=%ld\n", (long) scalar_result.sum);
    printf("auto_sum=%ld\n", (long) auto_result.sum);
    printf("sse2_sum=%ld\n", (long) sse2_result.sum);
    if (avx2_supported) {
        printf("avx2_sum=%ld\n", (long) avx2_result.sum);
    }
    printf("scalar_hot_loop_measurement_overhead_seconds=%.9f\n",
           scalar_result.hot_loop_measurement_overhead_seconds / (double) cfg.iterations);
    printf("scalar_hot_loop_raw_seconds=%.9f\n",
           scalar_result.hot_loop_raw_seconds / (double) cfg.iterations);
    printf("scalar_hot_loop_seconds=%.9f\n", scalar_result.hot_loop_avg_seconds);
    printf("scalar_hot_loop_ns_per_element=%.9f\n", scalar_result.hot_loop_ns_per_element);
    printf("scalar_hot_loop_calls=%.0f\n", scalar_result.hot_loop_calls);
    printf("scalar_hot_loop_elements=%.0f\n", scalar_result.hot_loop_elements);
    printf("auto_hot_loop_measurement_overhead_seconds=%.9f\n",
           auto_result.hot_loop_measurement_overhead_seconds / (double) cfg.iterations);
    printf("auto_hot_loop_raw_seconds=%.9f\n",
           auto_result.hot_loop_raw_seconds / (double) cfg.iterations);
    printf("auto_hot_loop_seconds=%.9f\n", auto_result.hot_loop_avg_seconds);
    printf("auto_hot_loop_ns_per_element=%.9f\n", auto_result.hot_loop_ns_per_element);
    printf("auto_hot_loop_calls=%.0f\n", auto_result.hot_loop_calls);
    printf("auto_hot_loop_elements=%.0f\n", auto_result.hot_loop_elements);
    printf("sse2_hot_loop_measurement_overhead_seconds=%.9f\n",
           sse2_result.hot_loop_measurement_overhead_seconds / (double) cfg.iterations);
    printf("sse2_hot_loop_raw_seconds=%.9f\n",
           sse2_result.hot_loop_raw_seconds / (double) cfg.iterations);
    printf("sse2_hot_loop_seconds=%.9f\n", sse2_result.hot_loop_avg_seconds);
    printf("sse2_hot_loop_ns_per_element=%.9f\n", sse2_result.hot_loop_ns_per_element);
    printf("sse2_hot_loop_calls=%.0f\n", sse2_result.hot_loop_calls);
    printf("sse2_hot_loop_elements=%.0f\n", sse2_result.hot_loop_elements);
    if (avx2_supported) {
        printf("avx2_hot_loop_measurement_overhead_seconds=%.9f\n",
               avx2_result.hot_loop_measurement_overhead_seconds / (double) cfg.iterations);
        printf("avx2_hot_loop_raw_seconds=%.9f\n",
               avx2_result.hot_loop_raw_seconds / (double) cfg.iterations);
        printf("avx2_hot_loop_seconds=%.9f\n", avx2_result.hot_loop_avg_seconds);
        printf("avx2_hot_loop_ns_per_element=%.9f\n", avx2_result.hot_loop_ns_per_element);
        printf("avx2_hot_loop_calls=%.0f\n", avx2_result.hot_loop_calls);
        printf("avx2_hot_loop_elements=%.0f\n", avx2_result.hot_loop_elements);
    }
    printf("sums_match=%s\n", sums_match ? "yes" : "no");

    free_chunked_array(input);
    return sums_match ? 0 : 1;
}
