/*
 * Deferred scalar counts: equivalence test.
 *
 * Runs each scenario with the per-element bump AND with the deferred counter
 * against the real RTS, and compares the resulting footer chains.  The claim
 * under test is that the two schemes count the same events, so checking
 * against hand-written expected numbers would be weaker.
 *
 * Built into a PRIVATE temp directory by run_scalar_count_deferred_tests.sh.
 */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdbool.h>
#include "gibbon_rts.h"

static int failures = 0;
static int checks = 0;

#define CHECK(cond, ...)                                                    \
    do { checks++;                                                          \
         if (!(cond)) { failures++; printf("  FAIL: "); printf(__VA_ARGS__);\
                        printf("   [%s:%d]\n", __func__, __LINE__); } } while (0)

#define CHUNK 1024
#define MAX_CHUNKS 32
#define MAX_BUFFERS 4

/* What the RTS ended up storing, walked off the chain. */
typedef struct {
    int      n;
    uint64_t count[MAX_CHUNKS];
    bool     truncated;
} Chain;

static void chain_read(Chain *out, char *any_footer)
{
    memset(out, 0, sizeof(*out));
    char *f = gib_scalar_count_first_footer(any_footer);
    if (f == NULL) { out->truncated = true; return; }

    while (f != NULL && out->n < MAX_CHUNKS) {
        out->count[out->n++] = gib_scalar_count_footer_get(f);
        f = gib_scalar_count_footer_next(f);
    }
    if (f != NULL) out->truncated = true;
}

static bool chain_eq(const Chain *a, const Chain *b)
{
    if (a->n != b->n || a->truncated != b->truncated) return false;
    for (int i = 0; i < a->n; i++) if (a->count[i] != b->count[i]) return false;
    return true;
}

static void chain_print(const char *label, const Chain *c)
{
    printf("     %-9s n=%d [", label, c->n);
    for (int i = 0; i < c->n; i++)
        printf("%s%llu", i ? ", " : "", (unsigned long long) c->count[i]);
    printf("]%s\n", c->truncated ? " (truncated)" : "");
}

/* A scenario: `nbuf` buffers, `nchunks` chunks, elems[b][k] elements of buffer
 * b in chunk k.  Every buffer grows together, which is what the SoA producer
 * does -- all buffers in a group share one bounds check. */
typedef struct {
    const char *name;
    int      nbuf;
    int      nchunks;
    uint64_t elems[MAX_BUFFERS][MAX_CHUNKS];
} Scenario;

/* Run `sc` with the per-element bump (the scheme being replaced), or with the
 * deferred counter, and report each buffer's resulting chain. */
static void run_scenario(const Scenario *sc, bool deferred, size_t base, Chain *chains)
{
    char *writeloc[MAX_BUFFERS];
    char *footer[MAX_BUFFERS];
    char *first_footer[MAX_BUFFERS];

    gib_scalar_count_footer_begin();

    for (int b = 0; b < sc->nbuf; b++) {
        /* Each SoA buffer is its own region -- that 1:1 slot/region mapping is
         * what lets on_grow find a slot from reg_info alone. */
        GibChunk c = gib_alloc_region_on_heap(CHUNK);
        writeloc[b] = c.start;
        footer[b]   = c.end;
        first_footer[b] = c.end;
    }

    if (deferred) {
        gib_scalar_count_bind(first_footer, base, sc->nbuf);
    }

    for (int k = 0; k < sc->nchunks; k++) {
        for (int b = 0; b < sc->nbuf; b++) {
            for (uint64_t i = 0; i < sc->elems[b][k]; i++) {
                if (deferred) {
                    gib_scalar_count_pending[base + (size_t) b]++;
                } else {
                    gib_scalar_count_footer_bump(footer[b]);
                }
            }
        }
        if (k + 1 < sc->nchunks) {
            for (int b = 0; b < sc->nbuf; b++) {
                char *old_footer = footer[b];
                gib_grow_region(&writeloc[b], &footer[b]);
                gib_scalar_count_on_grow(old_footer, footer[b]);
            }
        }
    }

    if (deferred) {
        gib_scalar_count_finalize(footer, base, sc->nbuf);
    }

    for (int b = 0; b < sc->nbuf; b++) chain_read(&chains[b], footer[b]);

    gib_scalar_count_footer_end(sc->name);
}

static void check_scenario(const Scenario *sc, size_t base)
{
    Chain bumped[MAX_BUFFERS];
    Chain deferred[MAX_BUFFERS];

    run_scenario(sc, false, base, bumped);
    run_scenario(sc, true,  base, deferred);

    bool all_eq = true;
    for (int b = 0; b < sc->nbuf; b++) {
        if (!chain_eq(&bumped[b], &deferred[b])) {
            all_eq = false;
            printf("  buffer %d diverged:\n", b);
            chain_print("bumped", &bumped[b]);
            chain_print("deferred", &deferred[b]);
        }
    }
    CHECK(all_eq, "%s: deferred counts differ from the per-element bumps", sc->name);

    /* Equality with a scheme that is itself wrong would prove nothing, so also
     * assert the chains carry the right TOTAL -- the one number both schemes
     * must agree with the scenario on. */
    for (int b = 0; b < sc->nbuf; b++) {
        uint64_t want = 0, got = 0;
        for (int k = 0; k < sc->nchunks; k++) want += sc->elems[b][k];
        for (int i = 0; i < deferred[b].n; i++) got += deferred[b].count[i];
        CHECK(want == got, "%s buffer %d: total should be %llu, chain sums to %llu",
              sc->name, b, (unsigned long long) want, (unsigned long long) got);
    }

    if (all_eq) printf("  ok: %s\n", sc->name);
}

int main(void)
{
    gib_init(0, NULL);
    printf("scalar_count_deferred_test\n");

    /* Single chunk: nothing ever grows, so the whole count is delivered by the
     * finalize.  This is the case a growth-time-only hook would have missed. */
    check_scenario(&(Scenario){ "single chunk, 1 buffer, 7 elements",
                                1, 1, {{7}} }, 0);

    /* Zero elements: the footer must stay UNTOUCHED, not be set to a genuine
     * zero -- a flush of 0 has to be a no-op for the two to stay
     * distinguishable (see test 3 of scalar_count_footer_test.c). */
    check_scenario(&(Scenario){ "single chunk, 1 buffer, 0 elements",
                                1, 1, {{0}} }, 0);

    /* One growth: the cyclic convention, driven through the deferred path. */
    check_scenario(&(Scenario){ "one growth (3 then 5)",
                                1, 2, {{3, 5}} }, 0);

    /* Repeated growth, same sequence scalar_count_footer_test.c pins. */
    check_scenario(&(Scenario){ "repeated growth {2,7,1,4}",
                                1, 4, {{2, 7, 1, 4}} }, 0);

    /* Several buffers with DIFFERENT per-chunk counts, which is what an SoA
     * producer actually does: mkTree's Node branch bumps only the tag buffer
     * while Leaf bumps both, so the counts genuinely diverge per buffer. */
    check_scenario(&(Scenario){ "3 buffers, divergent counts",
                                3, 3, {{5, 0, 2}, {1, 9, 3}, {0, 0, 0}} }, 0);

    /* A non-zero slot base, as a nested or second producer would get. */
    check_scenario(&(Scenario){ "non-zero slot base",
                                2, 3, {{4, 6, 1}, {2, 0, 8}} }, 64);

    /* Two producers live at once: distinct bases must not interfere.  Program-
     * global slot assignment is what makes this safe. */
    {
        Scenario outer = { "nested: outer", 1, 2, {{3, 4}} };
        Scenario inner = { "nested: inner", 1, 2, {{9, 2}} };
        char *ow, *of, *iw, *if_;

        gib_scalar_count_footer_begin();
        GibChunk oc = gib_alloc_region_on_heap(CHUNK);
        ow = oc.start; of = oc.end;
        GibChunk ic = gib_alloc_region_on_heap(CHUNK);
        iw = ic.start; if_ = ic.end;

        char *ofs[1] = { of };
        char *ifs[1] = { if_ };
        gib_scalar_count_bind(ofs, 0, 1);
        gib_scalar_count_bind(ifs, 8, 1);

        /* Interleaved, as a producer calling another producer would be. */
        for (uint64_t i = 0; i < outer.elems[0][0]; i++) gib_scalar_count_pending[0]++;
        for (uint64_t i = 0; i < inner.elems[0][0]; i++) gib_scalar_count_pending[8]++;
        { char *o = of; gib_grow_region(&ow, &of); gib_scalar_count_on_grow(o, of); }
        { char *o = if_; gib_grow_region(&iw, &if_); gib_scalar_count_on_grow(o, if_); }
        for (uint64_t i = 0; i < outer.elems[0][1]; i++) gib_scalar_count_pending[0]++;
        for (uint64_t i = 0; i < inner.elems[0][1]; i++) gib_scalar_count_pending[8]++;

        gib_scalar_count_finalize(ofs, 0, 1);
        gib_scalar_count_finalize(ifs, 8, 1);

        Chain och, ich;
        chain_read(&och, of);
        chain_read(&ich, if_);
        uint64_t osum = 0, isum = 0;
        for (int i = 0; i < och.n; i++) osum += och.count[i];
        for (int i = 0; i < ich.n; i++) isum += ich.count[i];
        CHECK(osum == 7, "nested outer total should be 7, got %llu", (unsigned long long) osum);
        CHECK(isum == 11, "nested inner total should be 11, got %llu", (unsigned long long) isum);
        gib_scalar_count_footer_end("nested");
        if (osum == 7 && isum == 11)
            printf("  ok: two producers live at once keep separate slot bases\n");
    }

    /* The debug bracket is emitted as the FIRST statement of a producer, so the
     * caller's bind has already run when it opens, and the caller's finalize
     * has not yet run when it closes.  The bracket exists to print footers; it
     * must leave counting state alone.  Above, run_scenario opens the bracket
     * BEFORE the bind, which is the one ordering the generated code never
     * produces. */
    {
        char *w, *f;
        GibChunk c = gib_alloc_region_on_heap(CHUNK);
        w = c.start; f = c.end;

        char *fs[1] = { f };
        gib_scalar_count_bind(fs, 0, 1);

        gib_scalar_count_footer_begin();
        for (uint64_t i = 0; i < 3; i++) gib_scalar_count_pending[0]++;
        { char *o = f; gib_grow_region(&w, &f); gib_scalar_count_on_grow(o, f); }
        for (uint64_t i = 0; i < 4; i++) gib_scalar_count_pending[0]++;
        gib_scalar_count_footer_end("bracket after bind");

        char *ffs[1] = { f };
        gib_scalar_count_finalize(ffs, 0, 1);

        Chain ch; chain_read(&ch, f);
        uint64_t sum = 0;
        for (int i = 0; i < ch.n; i++) sum += ch.count[i];
        CHECK(sum == 7, "bracket opened after bind: total should be 7, got %llu",
              (unsigned long long) sum);
        if (sum == 7) printf("  ok: a bracket opened after the bind keeps the binding\n");
    }

    /* A producer calling another producer nests the brackets, so the inner
     * bracket opens and closes while the outer producer's slot is still live
     * and its region has already grown once.  Closing the inner bracket must
     * not discard the outer region's accumulated state. */
    {
        char *ow, *of, *iw, *if_;
        GibChunk oc = gib_alloc_region_on_heap(CHUNK);
        ow = oc.start; of = oc.end;

        char *ofs[1] = { of };
        gib_scalar_count_bind(ofs, 0, 1);
        gib_scalar_count_footer_begin();

        for (uint64_t i = 0; i < 3; i++) gib_scalar_count_pending[0]++;
        { char *o = of; gib_grow_region(&ow, &of); gib_scalar_count_on_grow(o, of); }

        GibChunk ic = gib_alloc_region_on_heap(CHUNK);
        iw = ic.start; if_ = ic.end;
        char *ifs[1] = { if_ };
        gib_scalar_count_bind(ifs, 8, 1);
        gib_scalar_count_footer_begin();
        for (uint64_t i = 0; i < 9; i++) gib_scalar_count_pending[8]++;
        { char *o = if_; gib_grow_region(&iw, &if_); gib_scalar_count_on_grow(o, if_); }
        for (uint64_t i = 0; i < 2; i++) gib_scalar_count_pending[8]++;
        gib_scalar_count_footer_end("inner producer");
        char *iffs[1] = { if_ };
        gib_scalar_count_finalize(iffs, 8, 1);

        for (uint64_t i = 0; i < 4; i++) gib_scalar_count_pending[0]++;
        { char *o = of; gib_grow_region(&ow, &of); gib_scalar_count_on_grow(o, of); }
        gib_scalar_count_footer_end("outer producer");
        char *offs[1] = { of };
        gib_scalar_count_finalize(offs, 0, 1);

        Chain och, ich;
        chain_read(&och, of);
        chain_read(&ich, if_);
        uint64_t osum = 0, isum = 0;
        for (int i = 0; i < och.n; i++) osum += och.count[i];
        for (int i = 0; i < ich.n; i++) isum += ich.count[i];
        CHECK(osum == 7, "nested bracket, outer total should be 7, got %llu",
              (unsigned long long) osum);
        CHECK(isum == 11, "nested bracket, inner total should be 11, got %llu",
              (unsigned long long) isum);
        if (osum == 7 && isum == 11)
            printf("  ok: an inner producer's bracket leaves the outer one's counts alone\n");
    }

    printf("\n%d checks, %d failures\n", checks, failures);
    return failures == 0 ? 0 : 1;
}
