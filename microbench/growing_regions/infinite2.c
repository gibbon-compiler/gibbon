#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>
#include <malloc.h>
#include <sys/resource.h>
#include <math.h>
#include "rts.h"

/*
  Infinite - regions consist of a linked list of buffers, spread throughout memory
  (though possible constrained to 4GB regions). Writing into these regions requires
  bounds-checking. The buffers can start very small at the head of the list, but
  probably grow geometrically in size, making the cost of traversing all of them
  logarithmic.

*/

/* -------------------------------------------------------------------------------- */

CursorTy write_tag(CursorTy cur, TagTyPacked tag) {
    *(TagTyPacked *) cur = tag;
    return cur + 1;
}

CursorTy write_int(CursorTy cur, IntTy i) {
    *(IntTy *) cur = i;
    return cur + sizeof(IntTy);
}

void write_cursor(CursorTy at, CursorTy val) {
    *(CursorTy *) at = val;
}

/* -------------------------------------------------------------------------------- */

IntTy max(IntTy a, IntTy b) {
    return (a > b ? a : b);
}

CursorTy alloc_buf_malloc (IntTy buf_size) {
    CursorTy buf_ptr;
    buf_ptr = (CursorTy) malloc(buf_size);
    if (buf_ptr == NULL) {
        fprintf(stderr, "Error: malloc failed: %s\n", strerror(errno));
        abort();
    }
    return buf_ptr;
}

RegionTy alloc_first_infinite_region() {
    CursorTy reg_start = alloc_buf_malloc(INF_REG_INIT_SIZE);
    return (RegionTy) {reg_start, INF_REG_INIT_SIZE};
}

RegionTy alloc_infinite_region(RegionTy old) {
    IntTy newsize;
    IntTy newsize_maybe = old.size * 2;
    if (newsize_maybe > INF_REG_MAX_SIZE) {
        newsize = old.size;
    } else {
        newsize = newsize_maybe;
    }
    CursorTy reg_start = alloc_buf_malloc(newsize);
    return (RegionTy) {reg_start, newsize};
}

RegionCursorProd bounds_check(IntTy size_scalars, RegionTy reg, CursorTy cur) {
    // size of redirection node
    // need to come up with something better here

    IntTy required = max(size_scalars, REDIRECTION_SIZE);
    IntTy space_left = (reg.start + reg.size) - cur;

    if (space_left > required) {
        return (RegionCursorProd) {reg, cur};
    } else {
        // allocate
        RegionTy reg1 = alloc_infinite_region(reg);

        // redirect
        CursorTy redir = write_tag(cur, REDIRECTION_TAG);
        write_cursor(redir, reg1.start);
        return (RegionCursorProd) {reg1, reg1.start};
    }
}

/* -------------------------------------------------------------------------------- */

RegionCursorCursorProd buildTree(RegionTy reg, CursorTy pvrtmp2, IntTy pvrtmp3) {
    CursorTy lout272 = (CursorTy) pvrtmp2;
    IntTy i270 = (IntTy) pvrtmp3;
    IntTy b279 = i270 == (IntTy) 0;

    switch (b279) {

    case 0:
    {
        IntTy i273 = i270 - (IntTy) 1;
        CursorTy l274 = lout272 + (IntTy) 1;
        RegionCursorCursorProd tmp_struct0 = buildTree(reg, l274, i273);
        RegionTy reg1 = (RegionTy) tmp_struct0.field0;
        CursorTy pvrtmp6 = tmp_struct0.field1;
        CursorTy pvrtmp7 = tmp_struct0.field2;

        CursorTy x275 = (CursorTy) pvrtmp6;
        CursorTy end_x275 = (CursorTy) pvrtmp7;

        IntTy sizeof_x275 = end_x275 - x275;
        CursorTy l276 = l274 + sizeof_x275;
        RegionCursorCursorProd tmp_struct1 = buildTree(reg1, l276, i273);
        RegionTy reg2 = (RegionTy) tmp_struct1.field0;
        CursorTy pvrtmp8 = tmp_struct1.field1;
        CursorTy pvrtmp9 = tmp_struct1.field2;
        CursorTy y277 = (CursorTy) pvrtmp8;
        CursorTy end_y277 = (CursorTy) pvrtmp9;

        // write tag
        *(TagTyPacked *) lout272 = 1;
        CursorTy writetag8 = lout272 + 1;

        CursorTy writecur9 = (CursorTy) end_x275;
        CursorTy writecur10 = (CursorTy) end_y277;
        CursorTy pvrtmp11 = (CursorTy) writecur10;
        CursorTy pvrtmp10 = (CursorTy) lout272;
        CursorTy a278 = (CursorTy) pvrtmp10;
        CursorTy end_a278 = (CursorTy) pvrtmp11;

        return (RegionCursorCursorProd) {reg2, a278, end_a278};
        break;
    }

    case 1:
    {
        IntTy size_scalars = 9;
        /* RegionCursorProd tmp_struct2 = bounds_check(size_scalars, reg, lout272); */
        /* RegionTy reg3 = tmp_struct2.field0; */
        /* CursorTy lout273 = tmp_struct2.field1; */

        // -------------------- */
        // BOUNDS CHECK
        // ~~~~~~~~~~~~~~~~~~~~
        RegionTy reg3;
        CursorTy lout273;

        IntTy required = MAX(size_scalars, REDIRECTION_SIZE);
        IntTy space_left = (reg.start + reg.size) - lout272;
        if (space_left > required) {
            reg3 = reg;
            lout273 = lout272;
        } else {
            // allocate
            reg3 = alloc_infinite_region(reg);

            // redirect
            CursorTy redir = write_tag(lout272, REDIRECTION_TAG);
            write_cursor(redir, reg3.start);
            lout273 = reg3.start;
        }
        /* -------------------- */


        // write tag
        *(TagTyPacked *) lout273 = 0;
        CursorTy writetag3 = lout273 + 1;

        // write int
        *(IntTy *) writetag3 = (IntTy) 1;
        CursorTy writecur4 = writetag3 + sizeof(IntTy);

        CursorTy pvrtmp5 = (CursorTy) writecur4;
        CursorTy pvrtmp4 = (CursorTy) lout273;
        CursorTy taildc0 = (CursorTy) pvrtmp4;
        CursorTy end_taildc0 = (CursorTy) pvrtmp5;
        return (RegionCursorCursorProd) {reg3, taildc0, end_taildc0};
    }
    }
}

Int64CursorProd sumTree (CursorTy in_cur) {
    CursorTy lin = (CursorTy) in_cur;
    CursorTy tail = lin + sizeof(TagTyPacked);

    TagTyPacked tmpval = *lin;

    switch(tmpval) {
    case 0: {
        IntTy val = *(IntTy *) tail;
        CursorTy tail2 = tail + sizeof(IntTy);
        return (Int64CursorProd) {val, tail2};
    }
    case 1: {

        Int64CursorProd tmp_struct1 = sumTree(tail);
        IntTy vleft = tmp_struct1.field0;
        CursorTy end_left = tmp_struct1.field1;

        Int64CursorProd tmp_struct2 = sumTree(end_left);
        IntTy vright = tmp_struct2.field0;
        CursorTy end_right = tmp_struct2.field1;

        IntTy final = vleft + vright;

        return (Int64CursorProd) {final, end_right};
    }

    case REDIRECTION_TAG: {
        CursorTy next = *(CursorTy *) tail;
        return sumTree(next);
    }
    }
}

CursorTy print_Tree(CursorTy p23)
{
    TagTyPacked tag24 = *(TagTyPacked *) p23;
    CursorTy tail25 = p23 + sizeof(TagTyPacked);

    switch (tag24) {

    case 0:
    {
        fputs("(Leaf ", stdout);
        IntTy val26 = *(IntTy *) tail25;
        CursorTy tail27 = tail25 + sizeof(IntTy);
        printf("%lld", val26);
        fputs(")", stdout);
        return tail27;
        break;
    }
    case 1:
    {
        fputs("(Node ", stdout);
        CursorTy end_left = print_Tree(tail25);
        fputs(" ", stdout);
        CursorTy end_right = print_Tree(end_left);
        fputs(")", stdout);
        return end_right;
    }
    case REDIRECTION_TAG:
    {
        printf("-> ");
        CursorTy next = *(CursorTy *) tail25;
        print_Tree(next);
    }
    }
}

void print_space_required(int depth) {
    IntTy nodes = (1 << depth) - 1;
    IntTy leaves = nodes + 1;
    IntTy reqd = nodes + leaves + (leaves * 8);
    printf("Space Required: %lld bytes.\n", reqd);
}

int main(int argc, char *argv[]) {

    int depth;
    depth = atoi(argv[1]);

    // buildTree and sumTree allocations
    RegionTy reg;
    CursorTy lout;
    reg = alloc_first_infinite_region();
    lout = reg.start;

    RegionCursorCursorProd tmp_struct8;
    CursorTy tailapp1;
    Int64CursorProd tmp_struct9;
    IntTy val;

    if (strcmp(argv[2],"debug") == 0) {
        reg = alloc_first_infinite_region();
        lout = reg.start;
        tmp_struct8 = buildTree(reg, lout, depth);
        tailapp1 = tmp_struct8.field1;
        /* print_Tree(tailapp1); */
        tmp_struct9 = sumTree(tailapp1);
        val = tmp_struct9.field0;
        printf("%lld\n", val);
    } else {

        // criterion-interactive
        // ~~~~~~~~~~~~~~~~~~~~~

        size_t input_size = 32;
        size_t input_len;
        IntTy iters;
        char* input     = (char *) malloc(input_size * sizeof(char));
        char* iters_str = (char *) malloc(input_size * sizeof(char));
        int i;

        // Indicate that we're ready to run benchmarks
        fprintf(stdout,"READY\n");
        fflush(stdout);

        // Read criterion `START_BENCH N`
        input_len = getline(&input,&input_size,stdin);

        //
        while (strcmp(input,"EXIT\n") != 0) {

            // Extract the N ... len(START_BENCH) = 11
            strncpy(iters_str, input+11, input_len-11);
            iters = atoll(iters_str);

            // ***BENCHMARK***
            // Run the benchmark N times
            for(i = 0; i < iters; i++) {
                tmp_struct8 = buildTree(reg, lout, depth);
                tailapp1 = tmp_struct8.field1;
                /* print_Tree(tailapp1); */
                tmp_struct9 = sumTree(tailapp1);
                val = tmp_struct9.field0;
                /* printf("%lld\n", val);x */
            }

            // Mark the end of 1 criterion run
            /* fprintf(stdout,"%lld\n",iters); */
            fprintf(stdout, "END_BENCH\n");
            fflush(stdout);

            // Recur
            input_len = getline(&input,&input_size,stdin);
        }
    }
    /* print_space_required(depth); */
}
