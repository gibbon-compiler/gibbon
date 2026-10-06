// Cost of an 8-byte load by alignment class on the machine running the
// benchmarks, data resident in L1.  Used by the --pldi-kperf-counters phase to
// put a measured penalty beside the counted 64-byte-crossing accesses.
//
//   aligned           offset 0 of a 128-byte block
//   unaligned_in_64B  offset 3       (inside one 64-byte half)
//   cross_64B         offset 60      (bytes 60..67: crosses a 64-byte boundary)
//   cross_128B_line   offset 124     (bytes 124..131: into the next 128-byte block)
//
// latency:    a dependent chain (each load's value is the next load's position)
// throughput: independent loads, summed
// Output: CSV `class,latency_ns,throughput_ns`, median of 3.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#ifdef __APPLE__
#include <pthread.h>
#include <sys/qos.h>
#endif

#define BLOCKS 256                  /* 256 x 128 B = 32 KB, inside L1D */
#define STEPS  (100L * 1000 * 1000)

static double now(void)
{
    struct timespec t;
    clock_gettime(CLOCK_MONOTONIC, &t);
    return t.tv_sec + t.tv_nsec * 1e-9;
}

static int cmpd(const void *a, const void *b)
{
    double x = *(const double *) a, y = *(const double *) b;
    return (x > y) - (x < y);
}

static inline uint64_t ld(const unsigned char *p)
{
    uint64_t v;
    memcpy(&v, p, 8);
    return v;
}

int main(void)
{
#ifdef __APPLE__
    pthread_set_qos_class_self_np(QOS_CLASS_USER_INTERACTIVE, 0);
#endif
    const char *names[] = {"aligned", "unaligned_in_64B", "cross_64B", "cross_128B_line"};
    const size_t offs[] = {0, 3, 60, 124};
    unsigned char *buf = aligned_alloc(128, (BLOCKS + 1) * 128);
    size_t order[BLOCKS];
    uint64_t rng = 0x9E3779B97F4A7C15ull;
    if (buf == NULL) return 1;
    for (size_t i = 0; i < BLOCKS; i++) order[i] = i;
    for (size_t i = BLOCKS - 1; i > 0; i--) {
        rng ^= rng << 13; rng ^= rng >> 7; rng ^= rng << 17;
        size_t j = rng % i, t = order[i];
        order[i] = order[j];
        order[j] = t;
    }
    printf("class,latency_ns,throughput_ns\n");
    for (int c = 0; c < 4; c++) {
        memset(buf, 0, (BLOCKS + 1) * 128);
        for (size_t i = 0; i < BLOCKS; i++) {
            uint64_t next = order[(i + 1) % BLOCKS] * 128 + offs[c];
            memcpy(buf + order[i] * 128 + offs[c], &next, 8);
        }
        double lat[3], thr[3];
        for (int k = 0; k < 3; k++) {
            uint64_t p = order[0] * 128 + offs[c];
            double t0 = now();
            for (long i = 0; i < STEPS; i++) p = ld(buf + p);
            lat[k] = (now() - t0) * 1e9 / STEPS;
            if (p == 1) puts("");
            uint64_t s = 0;
            t0 = now();
            for (long r = 0; r < STEPS / BLOCKS; r++)
                for (size_t i = 0; i < BLOCKS; i++) s += ld(buf + i * 128 + offs[c]);
            thr[k] = (now() - t0) * 1e9 / ((double) (STEPS / BLOCKS) * BLOCKS);
            if (s == 1) puts("");
        }
        qsort(lat, 3, sizeof lat[0], cmpd);
        qsort(thr, 3, sizeof thr[0], cmpd);
        printf("%s,%.3f,%.3f\n", names[c], lat[1], thr[1]);
    }
    free(buf);
    return 0;
}
