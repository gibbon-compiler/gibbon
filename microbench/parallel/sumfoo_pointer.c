#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <utlist.h>
#include <uthash.h>
#include <time.h>
#include <cilk/cilk.h>

/* -------------------------------------------------------------------------- */

#define KB (1 * 1000lu)
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

// Some types we need.
typedef long long IntTy;

int compare(const void *a, const void *b) {
    if (*(double*)a > *(double*)b) {
        return 1;
    }
    else if (*(double*)a < *(double*)b) {
        return -1;
    }
    else {
        return 0;
    }
}

double difftimespecs(struct timespec* t0, struct timespec* t1)
{
    return (double)(t1->tv_sec - t0->tv_sec)
      + ((double)(t1->tv_nsec - t0->tv_nsec) / 1000000000.0);
}

double median(int len, double *nums) {
    qsort(nums, len, sizeof(double), compare);
    return nums[len/2];
}

double mean(int len, double *nums) {
    double sum = 0;
    for (int i = 0; i < len ; i++) {
        sum += nums[i];
    }
    return (double) (sum / len);
}

void print_size(char* msg, double size) {
    if (size > (1 * MB)) {
        printf("%s %.0lfM\n", msg, (double) (size / (1 * MB)));
    } else if (size > (1 * KB)) {
        printf("%s %.0lfK\n", msg, (double) (size / (1 * KB)));
    } else {
        printf("%s %.0lf bytes\n", msg, size);
    }
}

/* --------------------------------------------------------------------------

data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo

         | B_big Ptr Foo Foo
         | C_big Ptr Ptr Foo Foo Foo



mkFoo :: Int -> Foo
mkFoo n
  | n < 0     = A 10
  | n == 1    = B n (mkFoo (n-1)) (mkFoo (n-2))
  | otherwise = C n (mkFoo (n-1)) (mkFoo (n-2)) (mkFoo (n-3))


sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i          -> i
    B n f1 f2    -> n + sumFoo f1 + sumFoo f2
    C n f1 f2 f3 -> n + sumFoo f1 + sumFoo f2 + sumFoo f3

-------------------------------------------------------------------------- */

enum Type { A, B, C };

typedef struct Foo {
    enum Type tag;
    union {
      struct { IntTy a_elem; };
      struct { IntTy b_elem;
               struct Foo* b_f1;
               struct Foo* b_f2; };
      struct { IntTy c_elem;
               struct Foo* c_f1;
               struct Foo* c_f2;
               struct Foo* c_f3; };
    };
} Foo;

/* ------------------------------------------------------------------------- */

void printFoo(Foo* foo) {
    if (foo->tag == A) {
        printf("(A ");
        printf("%lld", foo->a_elem);
        printf(") ");
        return;
    } else if (foo->tag == B) {
        printf("(B ");
        printf("%lld ", foo->b_elem);
        printFoo(foo->b_f1);
        printFoo(foo->b_f2);
        printf(")");
        return;
    } else {
        printf("(C ");
        printf("%lld ", foo->c_elem);
        printFoo(foo->c_f1);
        printFoo(foo->c_f2);
        printFoo(foo->c_f3);
        printf(")");
        return;
    }
}

Foo* mkFoo(int n) {
    Foo* foo = (Foo*) malloc(sizeof(Foo));
    if (n <= 0) {
        foo->tag = A;
        foo->a_elem = 10;
    } else if (n == 1) {
        foo->tag = B;
        foo->b_elem = n;
        foo->b_f1 = mkFoo(n-1);
        foo->b_f2 = mkFoo(n-2);
    } else {
        foo->tag = C;
        foo->c_elem = n;
        foo->c_f1 = mkFoo(n-1);
        foo->c_f2 = mkFoo(n-2);
        foo->c_f3 = mkFoo(n-3);
    }
    return foo;
}

IntTy sumFoo_seq(Foo* foo) {
    if (foo->tag == A) {
        return foo->a_elem;
    } else if (foo->tag == B) {
        IntTy n = sumFoo_seq(foo->b_f1);
        IntTy m = sumFoo_seq(foo->b_f2);
        return (foo->b_elem + n + m);
    } else {
        IntTy n = sumFoo_seq(foo->c_f1);
        IntTy m = sumFoo_seq(foo->c_f2);
        IntTy o = sumFoo_seq(foo->c_f3);
        return (foo->c_elem + n + m + o);
    }
}

#define PAR_SIZE_THRESHOLD 10

IntTy sumFoo(Foo* foo) {
    if (foo->tag == A) {
        return foo->a_elem;
    } else if (foo->tag == B) {
        IntTy n = sumFoo(foo->b_f1);
        IntTy m = sumFoo(foo->b_f2);
        return (foo->b_elem + n + m);
    } else {
        IntTy height = foo->c_elem;
        if (height <= PAR_SIZE_THRESHOLD) {
            return sumFoo_seq(foo);
        }
        IntTy n = sumFoo(foo->c_f1);
        IntTy m = cilk_spawn sumFoo(foo->c_f2);
        IntTy o = cilk_spawn sumFoo(foo->c_f3);
        cilk_sync;
        return (height + n + m + o);
    }
}

int main(int argc, char** argv) {
    if (argc < 1) {
        printf("USAGE: sumtree.exe SIZE");
        exit(1);
    }
    IntTy tree_depth = atoll(argv[1]);

    // Things for benchmarking.
    int iters = 9;
    double nums[iters];
    double selftimed;
    struct timespec begin_timed;
    struct timespec end_timed;

    Foo* foo;
    for (int i = 0; i < iters; i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
        foo = mkFoo(tree_depth);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
        selftimed = difftimespecs(&begin_timed, &end_timed);
        nums[i] = selftimed;
    }
    printf("mkFoo\n");
    printf("=====\n");
    printf("Tree Depth: %lld\n", tree_depth);
    printf("Median of 9: %lf\n", median(iters, nums));
    printf("Mean of 9: %lf\n", mean(iters, nums));
    // printFoo(foo);
    // printf("\n");

    IntTy total_sum = 0;
    IntTy sum = 0;
    for (int i = 0; i < iters; i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
        sum = sumFoo(foo);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
        total_sum += sum;
        selftimed = difftimespecs(&begin_timed, &end_timed);
        nums[i] = selftimed;
    }
    printf("\nsumFoo\n");
    printf("=======\n");
    printf("Tree Depth: %lld\n", tree_depth);
    printf("Median of 9: %lf\n", median(iters, nums));
    printf("Mean of 9: %lf\n", mean(iters, nums));
    printf("Sum: %lld\n", total_sum / iters);

    total_sum = 0;
    for (int i = 0; i < iters; i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
        sum = sumFoo_seq(foo);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
        total_sum += sum;
        selftimed = difftimespecs(&begin_timed, &end_timed);
        nums[i] = selftimed;
    }
    printf("\nsumFoo_seq\n");
    printf("===========\n");
    printf("Tree Depth: %lld\n", tree_depth);
    printf("Median of 9: %lf\n", median(iters, nums));
    printf("Mean of 9: %lf\n", mean(iters, nums));
    printf("Sum: %lld\n", total_sum / iters);


    return 0;
}
