#include <stdlib.h>
#include <stdio.h>
#include <string.h>
#include <sys/mman.h>
#include <errno.h>
#include <malloc.h>
#include "rts.h"
#include <sys/resource.h>

/* -------------------------------------------------------------------------------- */

void print_space_required(int depth) {
    IntTy nodes = (1 << depth) - 1;
    IntTy leaves = nodes + 1;
    IntTy reqd = nodes + leaves + (leaves * 8);
    printf("Space Required: %lld bytes.\n", reqd);
}

CursorTy alloc_buf_malloc(IntTy buf_size) {
    CursorTy buf_ptr;
    buf_ptr = (CursorTy) malloc(buf_size);
    if (buf_ptr == NULL) {
        fprintf(stderr, "Error: malloc failed: %s\n", strerror(errno));
        abort();
    }
    return buf_ptr;
}

/* -------------------------------------------------------------------------------- */

CursorCursorCursorProd bounds_check(CursorTy reg, CursorTy end_reg, CursorTy cur) {
    if ((end_reg - cur) <= REDIRECTION_SIZE) {
        // update the region size and allocate...
        size_t reg_sz = (end_reg - reg) * 2;

        if (reg_sz > 409600) {
            reg_sz = reg_sz / 2;
        }
        /* printf("Allocating a new region with size: %ld\n", reg_sz); */
        CursorTy new_reg = alloc_buf_malloc(reg_sz);
        CursorTy new_reg_loc = new_reg;

        // write the indirection node
        *(TagTyPacked *) cur = REDIRECTION_TAG;
        CursorTy writetag_indr = cur + 1;
        *(CursorTy *) writetag_indr = new_reg_loc;

        return (CursorCursorCursorProd) {new_reg,new_reg + reg_sz,new_reg_loc};

    } else {
        return (CursorCursorCursorProd) {reg,end_reg,cur};
    }
}

/* -------------------------------------------------------------------------------- */

CursorCursorCursorCursorProd buildTree(CursorTy reg1, CursorTy end_reg1, CursorTy pvrtmp2, IntTy pvrtmp3) {
    CursorTy lout272 = (CursorTy) pvrtmp2;
    IntTy i270 = (IntTy) pvrtmp3;
    IntTy b279 = i270 == (IntTy) 0;

    switch (b279) {

    case 0:
    {
        IntTy i273 = i270 - (IntTy) 1;
        CursorTy l274 = lout272 + (IntTy) 1;
        CursorCursorCursorCursorProd tmp_struct0 = buildTree(reg1, end_reg1, l274, i273);
        CursorTy pvrtmp20 = tmp_struct0.field0;
        CursorTy pvrtmp21 = tmp_struct0.field1;
        CursorTy pvrtmp6 = tmp_struct0.field2;
        CursorTy pvrtmp7 = tmp_struct0.field3;

        CursorTy reg2 = (CursorTy) pvrtmp20;
        CursorTy end_reg2 = (CursorTy) pvrtmp21;
        CursorTy x275 = (CursorTy) pvrtmp6;
        CursorTy end_x275 = (CursorTy) pvrtmp7;

        /* IntTy sizeof_x275 = end_x275 - x275; */
        CursorTy l276 = end_x275;
        CursorCursorCursorCursorProd tmp_struct1 = buildTree(reg2, end_reg2, l276, i273);
        CursorTy pvrtmp22 = tmp_struct1.field0;
        CursorTy pvrtmp23 = tmp_struct1.field1;
        CursorTy pvrtmp8 = tmp_struct1.field2;
        CursorTy pvrtmp9 = tmp_struct1.field3;
        CursorTy y277 = (CursorTy) pvrtmp8;
        CursorTy end_y277 = (CursorTy) pvrtmp9;
        CursorTy reg3 = (CursorTy) pvrtmp22;
        CursorTy end_reg3 = (CursorTy) pvrtmp23;

        // write tag
        *(TagTyPacked *) lout272 = 1;
        CursorTy writetag8 = lout272 + 1;

        CursorTy writecur9 = (CursorTy) end_x275;
        CursorTy writecur10 = (CursorTy) end_y277;
        CursorTy pvrtmp11 = (CursorTy) writecur10;
        CursorTy pvrtmp10 = (CursorTy) lout272;
        CursorTy a278 = (CursorTy) pvrtmp10;
        CursorTy end_a278 = (CursorTy) pvrtmp11;

        return (CursorCursorCursorCursorProd) {reg3, end_reg3, a278, end_a278};
        break;
    }

    case 1:
    {
        // bounds check
        /* CursorCursorCursorProd tmp_struct23 = bounds_check(reg1, end_reg1, lout272); */
        /* CursorTy reg4 = tmp_struct23.field0; */
        /* CursorTy end_reg4 = tmp_struct23.field1; */
        /* CursorTy lout273 = tmp_struct23.field2; */

        /* -------------------- */
        /* BOUNDS CHECK         */
        /* ~~~~~~~~~~~~~~~~~~~~ */

        int size_scalars = 9;

        if ((end_reg1 - lout272) <= MAX(size_scalars, REDIRECTION_SIZE)) {
            IntTy newsize = (end_reg1 - reg1) * 2;
            reg1 = alloc_buf_malloc(newsize);
            end_reg1 = reg1 + newsize;

            // write redirection tag
            *(TagTyPacked *) lout272 =  REDIRECTION_TAG;
            CursorTy redir = lout272 + 1;
            *(CursorTy *) redir = reg1;

            lout272 = (CursorTy) reg1;
        }

        /* -------------------- */

        // write tag
        *(TagTyPacked *) lout272 = 0;
        CursorTy writetag3 = lout272 + 1;

        // write int
        *(IntTy *) writetag3 = (IntTy) 1;
        CursorTy writecur4 = writetag3 + sizeof(IntTy);

        CursorTy pvrtmp5 = (CursorTy) writecur4;
        CursorTy pvrtmp4 = (CursorTy) lout272;
        CursorTy taildc0 = (CursorTy) pvrtmp4;
        CursorTy end_taildc0 = (CursorTy) pvrtmp5;

        return (CursorCursorCursorCursorProd) {reg1, end_reg1, taildc0, end_taildc0};
    }
    }
}

/* -------------------------------------------------------------------------------- */

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

int main (int argc, char* argv[]) {

    int depth;
    depth = atoi(argv[1]);

    CursorTy reg1 = alloc_buf_malloc(INF_REG_INIT_SIZE);
    CursorTy end_reg1 = reg1 + INF_REG_INIT_SIZE;
    CursorTy lout = reg1;

    //
    CursorCursorCursorCursorProd tmp_struct8;
    CursorTy tailapp1;
    CursorTy end_tailapp1;
    Int64CursorProd tmp_struct9;
    IntTy val;

    if ((strcmp(argv[2], "debug")) == 0) {
        tmp_struct8 = buildTree(reg1, end_reg1, lout, depth);
        tailapp1 = tmp_struct8.field2;
        /* print_Tree(tailapp1); */
        end_tailapp1 = tmp_struct8.field3;
        tmp_struct9 = sumTree(tailapp1);
        val = tmp_struct9.field0;
        printf("%lld\n",val);
    } else {
        // criterion-interactive
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


        while (strcmp(input,"EXIT\n") != 0) {

            // Extract the N ... len(START_BENCH) = 11
            strncpy(iters_str, input+11, input_len-11);
            iters = atoll(iters_str);

            // ***BENCHMARK***
            // Run the benchmark N times
            for(i = 0; i < iters; i++) {
                tmp_struct8 = buildTree(reg1, end_reg1, lout, depth);
                tailapp1 = tmp_struct8.field2;
                /* end_tailapp1 = tmp_struct8.field3; */
                tmp_struct9 = sumTree(tailapp1);
                val = tmp_struct9.field0;
                /* printf("%lld\n",val); */
            }

            // Mark the end of 1 criterion run
            /* fprintf(stdout,"%lld\n",iters); */
            fprintf(stdout, "END_BENCH\n");
            fflush(stdout);

            // Recur
            input_len = getline(&input,&input_size,stdin);
        }
    }

    return 0;
}
