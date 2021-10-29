// Gibbon program.

#include "gibbon.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
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
 * Program starts here
 * ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 */


/*
 *

 * The nursery is set to 4MiB and every alloc_region requests space
 * just under 2*MiB. Therefore the third allocation on every thread should
 * be malloc'd, indicated on the stdout by MALLOC!!!.


 * Compile:
 * ~~~~~~~~~~


1) Compile the Rust RTS:

cd $GIBBONDIR/gibbon-rts && cargo build --release


2) Compile the C RTS:

gcc -std=gnu11  -fcilkplus -D_GIBBON_PARALLEL  -Wno-unused-variable -Wno-unused-label -Wall -Wextra -Wpedantic  -O3  -flto \
-I $GIBBONDIR/gibbon-compiler/cbits  -L$GIBBONDIR/gibbon-rts/target/release -Wl,-rpath=$GIBBONDIR/gibbon-rts/target/release \
-c $GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.c -o $GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.o  -lm -lgibbon_rts


3) Compile this program:

gcc -std=gnu11  -fcilkplus -D_GIBBON_PARALLEL  -Wno-unused-variable -Wno-unused-label -Wall -Wextra -Wpedantic  -O3  -flto \
$GIBBONDIR/gibbon-compiler/cbits/gibbon_rts.o -I$GIBBONDIR/gibbon-compiler/cbits  -L$GIBBONDIR/gibbon-rts/target/release \
-Wl,-rpath=$GIBBONDIR/gibbon-rts/target/release $GIBBONDIR/gibbon-compiler/examples/test_new_rts.c \
-o $GIBBONDIR/gibbon-compiler/examples/test_new_rts.exe -lm -lgibbon_rts


 * Run:
 * ~~~~~~~~~~

CILK_NWORKERS=3 $GIBBONDIR/gibbon-compiler/examples/test_new_rts.exe


 */

GibInt fib_seq(GibInt n)
{
    if (n == 0) {
        return 0;
    } else {
        if (n == 1) {
            return 1;
        } else {
            GibInt x =  fib_seq(n - 1);
            GibInt y =  fib_seq(n - 2);
            return (x + y);
        }
    }
}

void alloc_region(void)
{
    int worker;
#ifdef _GIBBON_PARALLEL
     worker = __cilkrts_get_worker_number();
#else
     worker = 0;
#endif

    // A dummy computation to make Cilk schedule this function on
    // different threads.
    GibInt x = fib_seq(20);
    // Allocate a region.
    GibCursorsPair *cursors = gib_alloc_region2(2*MB-1);
    printf("alloc_region: worker=%d, start=%p, end=%p, x=%lld\n", worker, cursors->cp_start, cursors->cp_end, x);
    return;
}

void test_alloc_region(void)
{
    // sequential.
    printf("\nSequential.\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    alloc_region();
    alloc_region();
    alloc_region();

    // reset.
    printf("\nResetting the nursery.\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n\n");
    gib_reset_nursery();

    // parallel.
    printf("\nParallel.\n~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~\n");
    cilk_spawn alloc_region();
    cilk_spawn alloc_region();
    cilk_spawn alloc_region();
    cilk_spawn alloc_region();
    cilk_spawn alloc_region();
    cilk_spawn alloc_region();

    alloc_region();
    alloc_region();
    alloc_region();

    cilk_sync;

    return;
}

int gib_main_expr(void) {
    test_alloc_region();

    return 0;
}
