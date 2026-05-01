#include <immintrin.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#if defined(SIMPLE_INT_WIDTH) && SIMPLE_INT_WIDTH == 32
typedef int IntTy;
#else
typedef long IntTy;
#endif

typedef struct config {
    long list_len;
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

typedef IntTy *(*Add1Fn)(const IntTy *in, size_t length);

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

static void parse_args(int argc, char **argv, Config *cfg);
static void print_usage(const char *progname);
static double now_seconds(void);
static double measure_empty_timing_overhead(size_t calls);
static long expected_sum_after_add1(long length);
static IntTy *generate_array(size_t length);
static void print_array(const IntTy *in, size_t length);
static long sum_array(const IntTy *in, size_t length);
static IntTy *run_add1_kernel(const IntTy *in,
                              size_t length,
                              void (*kernel)(IntTy *, size_t),
                              BenchmarkResult *result,
                              bool record_time);
static IntTy *add1_scalar(const IntTy *in, size_t length);
static IntTy *add1_auto(const IntTy *in, size_t length);
static IntTy *add1_sse2(const IntTy *in, size_t length);
static IntTy *add1_avx2(const IntTy *in, size_t length);
static NOINLINE NO_TREE_VECTORIZE void add1_scalar_kernel(IntTy *in, size_t length);
static NOINLINE void add1_auto_kernel(IntTy *in, size_t length);
static TARGET_SSE2 NOINLINE void add1_sse2_kernel(IntTy *in, size_t length);
static TARGET_AVX2 NOINLINE void add1_avx2_kernel(IntTy *in, size_t length);
static bool run_variant_once(BenchmarkResult *result,
                             Add1Fn fn,
                             const IntTy *input,
                             size_t length,
                             long expected_sum,
                             bool record_time);
static void finalize_benchmark_results(BenchmarkResult *results, size_t count, int iterations);

static double now_seconds(void) {
    struct timespec ts;
    if (clock_gettime(CLOCK_MONOTONIC, &ts) != 0) {
        perror("clock_gettime");
        exit(1);
    }
    return (double) ts.tv_sec + ((double) ts.tv_nsec / 1000000000.0);
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
    fprintf(stderr, "Usage: %s [--list-len N] [--iterations N] [--print]\n", progname);
}

static long expected_sum_after_add1(long length) {
    return (length * (length + 1)) / 2;
}

static IntTy *generate_array(size_t length) {
    IntTy *out = (IntTy *) malloc(sizeof(IntTy) * length);
    if (out == NULL) {
        perror("malloc generate_array");
        return NULL;
    }
    for (size_t i = 0; i < length; i++) {
        out[i] = (IntTy) i;
    }
    return out;
}

static void print_array(const IntTy *in, size_t length) {
    for (size_t i = 0; i < length; i++) {
        printf("%ld ", (long) in[i]);
    }
    printf("END\n");
}

static long sum_array(const IntTy *in, size_t length) {
    long sum = 0;
    for (size_t i = 0; i < length; i++) {
        sum += in[i];
    }
    return sum;
}

static IntTy *run_add1_kernel(const IntTy *in,
                              size_t length,
                              void (*kernel)(IntTy *, size_t),
                              BenchmarkResult *result,
                              bool record_time) {
    IntTy *out = (IntTy *) malloc(sizeof(IntTy) * length);
    if (out == NULL) {
        perror("malloc add1 work buffer");
        return NULL;
    }
    memcpy(out, in, sizeof(IntTy) * length);

    if (record_time) {
        double start = now_seconds();
        kernel(out, length);
        double end = now_seconds();
        result->hot_loop_raw_seconds += end - start;
        result->hot_loop_calls += 1.0;
        result->hot_loop_elements += (double) length;
    } else {
        kernel(out, length);
    }

    return out;
}

static IntTy *add1_scalar(const IntTy *in, size_t length) {
    return run_add1_kernel(in, length, add1_scalar_kernel, NULL, false);
}

static IntTy *add1_auto(const IntTy *in, size_t length) {
    return run_add1_kernel(in, length, add1_auto_kernel, NULL, false);
}

static IntTy *add1_sse2(const IntTy *in, size_t length) {
    return run_add1_kernel(in, length, add1_sse2_kernel, NULL, false);
}

static IntTy *add1_avx2(const IntTy *in, size_t length) {
    return run_add1_kernel(in, length, add1_avx2_kernel, NULL, false);
}

static NOINLINE NO_TREE_VECTORIZE void add1_scalar_kernel(IntTy *in,
                                                          size_t length) {
    for (size_t i = 0; i < length; i++) {
        in[i] += 1;
    }
}

static NOINLINE void add1_auto_kernel(IntTy *in,
                                      size_t length) {
    for (size_t i = 0; i < length; i++) {
        in[i] += 1;
    }
}

static TARGET_SSE2 NOINLINE void add1_sse2_kernel(IntTy *in,
                                                  size_t length) {
    size_t i = 0;
    if (sizeof(IntTy) == sizeof(int)) {
        const __m128i ones = _mm_set1_epi32(1);
        for (; i + 3 < length; i += 4) {
            __m128i vals = _mm_loadu_si128((const __m128i *) (in + i));
            vals = _mm_add_epi32(vals, ones);
            _mm_storeu_si128((__m128i *) (in + i), vals);
        }
    } else if (sizeof(IntTy) == sizeof(long)) {
        const __m128i ones = _mm_set1_epi64x(1);
        for (; i + 1 < length; i += 2) {
            __m128i vals = _mm_loadu_si128((const __m128i *) (in + i));
            vals = _mm_add_epi64(vals, ones);
            _mm_storeu_si128((__m128i *) (in + i), vals);
        }
    }
    for (; i < length; i++) {
        in[i] += 1;
    }
}

static TARGET_AVX2 NOINLINE void add1_avx2_kernel(IntTy *in,
                                                  size_t length) {
    size_t i = 0;
    if (sizeof(IntTy) == sizeof(int)) {
        const __m256i ones = _mm256_set1_epi32(1);
        for (; i + 7 < length; i += 8) {
            __m256i vals = _mm256_loadu_si256((const __m256i *) (in + i));
            vals = _mm256_add_epi32(vals, ones);
            _mm256_storeu_si256((__m256i *) (in + i), vals);
        }
    } else if (sizeof(IntTy) == sizeof(long)) {
        const __m256i ones = _mm256_set1_epi64x(1);
        for (; i + 3 < length; i += 4) {
            __m256i vals = _mm256_loadu_si256((const __m256i *) (in + i));
            vals = _mm256_add_epi64(vals, ones);
            _mm256_storeu_si256((__m256i *) (in + i), vals);
        }
    }
    for (; i < length; i++) {
        in[i] += 1;
    }
    _mm256_zeroupper();
}

static bool run_variant_once(BenchmarkResult *result,
                             Add1Fn fn,
                             const IntTy *input,
                             size_t length,
                             long expected_sum,
                             bool record_time) {
    double start = 0.0;
    double end = 0.0;
    IntTy *out = NULL;

    if (record_time) {
        start = now_seconds();
        if (fn == add1_scalar) {
            out = run_add1_kernel(input, length, add1_scalar_kernel, result, true);
        } else if (fn == add1_auto) {
            out = run_add1_kernel(input, length, add1_auto_kernel, result, true);
        } else if (fn == add1_sse2) {
            out = run_add1_kernel(input, length, add1_sse2_kernel, result, true);
        } else if (fn == add1_avx2) {
            out = run_add1_kernel(input, length, add1_avx2_kernel, result, true);
        } else {
            out = fn(input, length);
        }
        end = now_seconds();
    } else {
        out = fn(input, length);
    }

    if (out == NULL) {
        result->ok = false;
        return false;
    }

    long sum = sum_array(out, length);
    if (sum != expected_sum) {
        result->ok = false;
    }
    result->sum = sum;
    if (record_time) {
        result->total_seconds += end - start;
    }

    free(out);
    return result->ok;
}

static void finalize_benchmark_results(BenchmarkResult *results, size_t count, int iterations) {
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

    const size_t length = (size_t) cfg.list_len;
    IntTy *input = generate_array(length);
    if (input == NULL) {
        return 1;
    }

    if (cfg.print_arrays) {
        IntTy *preview = add1_scalar(input, length);
        if (preview == NULL) {
            free(input);
            return 1;
        }
        print_array(input, length);
        print_array(preview, length);
        free(preview);
    }

    const long expected_sum = expected_sum_after_add1(cfg.list_len);
    const bool avx2_supported = __builtin_cpu_supports("avx2");

    VariantSpec specs[] = {
        {"scalar", add1_scalar, true},
        {"auto", add1_auto, true},
        {"sse2", add1_sse2, true},
        {"avx2", add1_avx2, avx2_supported},
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
        if (!run_variant_once(&results[i], specs[i].fn, input, length, expected_sum, false)) {
            free(input);
            return 1;
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
                if (!run_variant_once(&results[idx], specs[idx].fn, input, length, expected_sum, true)) {
                    free(input);
                    return 1;
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

    printf("list_len=%ld\n", cfg.list_len);
    printf("iterations=%d\n", cfg.iterations);
    printf("int_size_bits=%zu\n", sizeof(IntTy) * 8);
    printf("expected_sum=%ld\n", expected_sum);
    printf("avx2_supported=%s\n", avx2_supported ? "yes" : "no");
    printf("scalar_seconds=%.9f\n", scalar_result.avg_seconds);
    printf("auto_seconds=%.9f\n", auto_result.avg_seconds);
    printf("sse2_seconds=%.9f\n", sse2_result.avg_seconds);
    if (avx2_supported) {
        printf("avx2_seconds=%.9f\n", avx2_result.avg_seconds);
    }
    printf("scalar_sum=%ld\n", scalar_result.sum);
    printf("auto_sum=%ld\n", auto_result.sum);
    printf("sse2_sum=%ld\n", sse2_result.sum);
    if (avx2_supported) {
        printf("avx2_sum=%ld\n", avx2_result.sum);
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

    free(input);
    return sums_match ? 0 : 1;
}
