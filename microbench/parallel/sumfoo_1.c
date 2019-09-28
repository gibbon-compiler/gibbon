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

// A region with this refcount has already been garbage collected.
#define REG_FREED -100

#define ALLOC_PACKED(n) malloc(n)

// Maximum size of a chunk, see GitHub #110.
long long global_inf_buf_max_chunk_size = 1 * GB;

// Some types we need.
typedef long long IntTy;
typedef char* CursorTy;
typedef char TagTyPacked;

typedef struct CursorCursorCursorIntProd_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
    IntTy    field3;
} CursorCursorCursorIntProd;

typedef struct CursorIntProd_struct {
    CursorTy field0;
    IntTy    field1;
} CursorIntProd;

typedef struct CursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
} CursorCursorProd;

typedef struct Outset_elem {
    CursorTy ref;
    struct Outset_elem *prev;
    struct Outset_elem *next;
} Outset_elem;

typedef struct RegionTy_struct {
    int refcount;
    CursorTy start_ptr;
    Outset_elem *outset;
} RegionTy;

typedef struct RegionFooter_struct {
    // This sequence number is not strictly required, but helps with debugging
    // and error messages.
    int seq_no;
    IntTy size;
    int *refcount_ptr;
    Outset_elem *outset_ptr;
    CursorTy next;
    CursorTy prev;
} RegionFooter;

RegionTy *alloc_region(IntTy size) {
    // Allocate the first chunk
    IntTy total_size = size + sizeof(RegionFooter);
    CursorTy start = ALLOC_PACKED(total_size);
    CursorTy end = start + size;

    RegionTy *reg = malloc(sizeof(RegionTy));
    reg->refcount = 0;
    reg->start_ptr = start;
    reg->outset = NULL;

    // Write the footer
    RegionFooter* footer = (RegionFooter *) end;
    footer->seq_no = 1;
    footer->size = size;
    footer->refcount_ptr = &(reg->refcount);
    footer->outset_ptr = reg->outset;
    footer->next = NULL;
    footer->prev = NULL;
    *(RegionFooter *) end = *footer;

    return reg;
}

typedef struct ChunkTy_struct {
    CursorTy start_ptr;
    CursorTy end_ptr;
} ChunkTy;

ChunkTy alloc_chunk(CursorTy end_old_chunk) {
    // Get size from current footer
    RegionFooter *footer = (RegionFooter *) end_old_chunk;
    IntTy newsize = footer->size * 2;
    // See #110.
    if (newsize > global_inf_buf_max_chunk_size) {
        newsize = global_inf_buf_max_chunk_size;
    }
    IntTy total_size = newsize + sizeof(RegionFooter);

    // Allocate
    CursorTy start = ALLOC_PACKED(total_size);
    CursorTy end = start + newsize;

    #ifdef DEBUG
    printf("Allocated a chunk: %lld bytes.\n", total_size);
    #endif

    // Link the next chunk's footer
    footer->next = end;

    // Write the footer
    RegionFooter* new_footer = (RegionFooter *) end;
    new_footer->seq_no = footer->seq_no + 1;
    new_footer->size = newsize;
    new_footer->refcount_ptr = footer->refcount_ptr;
    new_footer->outset_ptr = footer->outset_ptr;
    new_footer->next = NULL;
    new_footer->prev = end_old_chunk;

    return (ChunkTy) {start , end};
}

RegionFooter* trav_to_first_chunk(RegionFooter *footer) {
    if (footer->seq_no == 1) {
        return footer;
    } else if (footer->prev == NULL) {
        fprintf(stderr, "No previous chunk found at seq_no: %d", footer->seq_no);
        return NULL;
    } else {
        trav_to_first_chunk((RegionFooter*) footer->prev);
    }
}

int get_ref_count(CursorTy end_ptr) {
    RegionFooter footer = *(RegionFooter *) end_ptr;
    return *(footer.refcount_ptr);
}

// B is the pointer, and A is the pointee (i.e B -> A) --
// bump A's refcount, and update B's outset ptr.
IntTy bump_ref_count(CursorTy end_b, CursorTy end_a) {
    // Bump refcount
    RegionFooter *footer_a = (RegionFooter *) end_a;
    int refcount = *(footer_a->refcount_ptr);
    int new_refcount = refcount + 1;
    *(footer_a->refcount_ptr) = new_refcount;

    // Grab B's outset
    RegionFooter *footer_b = (RegionFooter *) end_b;
    Outset_elem *head = footer_b->outset_ptr;

    #ifdef DEBUG
    Outset_elem *elt;
    int count;
    DL_COUNT(head, elt, count);
    printf("bump_ref_count: old-refcount=%d, old-outset-len=%d:\n", refcount, count);
    assert(refcount == count);
    #endif

    // Add A to B's outset
    Outset_elem *add = malloc(sizeof(Outset_elem));
    add->ref = end_a;
    add->next = NULL;
    add->prev = NULL;
    DL_APPEND(head, add);

    // As far as I can tell, DL_APPEND updates "head" after an append. Or maybe
    // only after the first one, possibly to change NULL to some struct.
    // In any case, we update outset_ptr here.
    footer_b->outset_ptr = head;

    #ifdef DEBUG
    int new_count;
    DL_COUNT(head, elt, new_count);
    printf("bump_ref_count: new-refcount=%d, new-outset-len=%d:\n", new_refcount, new_count);
    assert(new_refcount == new_count);
    #endif

    return refcount;
}

void free_region(CursorTy end_reg) {
    RegionFooter footer = *(RegionFooter *) end_reg;
    CursorTy first_chunk = end_reg - footer.size;
    CursorTy next_chunk = footer.next;

    // Decrement refcounts of all regions `reg` points to
    if (footer.outset_ptr != NULL) {
        // Grab the outset, and decrement refcounts.
        Outset_elem *elt, *tmp;
        Outset_elem *head = (footer.outset_ptr);

        #ifdef DEBUG
        int count;
        DL_COUNT(head, elt, count);
        printf("free_region: outset-len: %d\n", count);
        #endif

        // Decrement refcounts, free regions with refcount==0 and also free
        // elements of the outset.
        DL_FOREACH_SAFE(head,elt,tmp) {
            RegionFooter *elt_footer = (RegionFooter *) elt->ref;
            *(elt_footer->refcount_ptr) = *(elt_footer->refcount_ptr) - 1;
            if (*(elt_footer->refcount_ptr) == 0) {
                // See [Why is it a doubly linked-list?] above
                RegionFooter *first_chunk = trav_to_first_chunk(elt_footer);
                if (first_chunk != NULL) {
                    free_region((CursorTy) first_chunk);
                }
            }
            DL_DELETE(head,elt);
            free(elt);
        }
    }

    // Free all chunks if recount is 0
    if (*(footer.refcount_ptr) == 0) {

        #ifdef DEBUG
        // Bookkeeping
        int num_chunks = 1;
        IntTy total_bytesize = footer.size;
        #endif

        // Indicate that this region has been garbage collected.
        *(footer.refcount_ptr) = REG_FREED;

        // Free the first chunk
        free(first_chunk);

        // Now, all the others
        while (next_chunk != NULL) {
            footer = *(RegionFooter *) next_chunk;
            free(next_chunk - footer.size);
            next_chunk = footer.next;

            #ifdef DEBUG
            num_chunks++;
            total_bytesize = total_bytesize + footer.size;
            #endif
        }

        #ifdef DEBUG
        printf("GC: Freed %lld bytes across %d chunks.\n",total_bytesize,num_chunks);
        #endif
    } else {
        #ifdef DEBUG
        printf("free_region: non-zero refcount: %d.\n", *(footer.refcount_ptr));
        #endif
    }
}

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

    B_big _ f1 f2 -> let p = sumFoo f1 .||. sumFoo f2
                     in fst p + snd p

    C_big _ f1 f2 f3 -> let t = sumFoo f1 .||. (sumFoo f2 .||. sumFoo f3)
                          in fst3 t + snd3 t + thd3 t

-------------------------------------------------------------------------- */

CursorTy printFoo(CursorTy cur) {
    if (*cur == 0) {
        printf("(A ");
        cur++;
        IntTy val = *(IntTy *) cur;
        cur += 8;
        printf("%lld",val);
        printf(") ");
        return cur;
    } else if (*cur == 1) {
        printf("(B ");
        cur++;
        IntTy val = *(IntTy *) cur;
        cur += 8;
        printf("%lld ", val);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 2) {
        printf("(C ");
        cur++;
        IntTy val = *(IntTy *) cur;
        cur += 8;
        printf("%lld ", val);
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 3) {
        printf("(C_big PTR ");
        cur += 9;
        IntTy val = *(IntTy *) cur;
        cur += 8;
        printf("%lld ", val);
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 4) {
        printf("(C_tmp _ ");
        cur += 9;
        IntTy val = *(IntTy *) cur;
        cur += 8;
        printf("%lld ", val);
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
    } else if (*cur == 100) {
        // redirection
        printf("R -> ");
        cur++;
        CursorTy new_cur = *(CursorTy*) cur;
        cur = printFoo(new_cur);
        return cur;
    } else if (*cur = 90) {
        // indirection
        printf("I -> ");
        cur++;
        CursorTy new_cur = *(CursorTy*) cur;
        cur = printFoo(new_cur);
        return cur;
    }
}

// Data over this threshold will be processed in parallel
#define PAR_SIZE_THRESHOLD 8 * KB

CursorCursorCursorIntProd mkFoo (CursorTy end_chunk, CursorTy out, CursorTy out_ran, IntTy n) {
    CursorCursorCursorIntProd tmp;
    if (n <= 0) {
        // A

        // start bounds check
        if ((end_chunk - out) <= 30) {
            ChunkTy new_chunk    = alloc_chunk(end_chunk);
            CursorTy chunk_start = new_chunk.start_ptr;
            CursorTy chunk_end   = new_chunk.end_ptr;

            end_chunk = chunk_end;
            *(TagTyPacked *) out = 100;
            CursorTy redir = out + 1;
            *(CursorTy *) redir = chunk_start;
            out = chunk_start;
        }
        // end bounds check
        *out = 0;
        out++;
        *(IntTy *) out = 10;
        out += 8;
        return (CursorCursorCursorIntProd) {end_chunk, out, out_ran, 9};
    } else if (n == 1) {
        // B

        // start bounds check
        if ((end_chunk - out) <= 30) {
            ChunkTy new_chunk    = alloc_chunk(end_chunk);
            CursorTy chunk_start = new_chunk.start_ptr;
            CursorTy chunk_end   = new_chunk.end_ptr;

            end_chunk = chunk_end;
            *(TagTyPacked *) out = 100;
            CursorTy redir = out + 1;
            *(CursorTy *) redir = chunk_start;
            out = chunk_start;
        }

        // n
        CursorTy out0 = out + 1;
        *(IntTy *) out0 = n;
        out0 += 8;

        // rec1
        tmp = mkFoo(end_chunk, out0, out_ran, (n-1));
        CursorTy end_chunk1 = tmp.field0;
        CursorTy out1 = tmp.field1;
        CursorTy out_ran1 = tmp.field2;
        IntTy size1 = tmp.field3;

        // rec2
        tmp = mkFoo(end_chunk1, out1, out_ran1, (n-2));
        CursorTy end_chunk2 = tmp.field0;
        CursorTy out2 = tmp.field1;
        CursorTy out_ran2 = tmp.field2;
        IntTy size2 = tmp.field3;

        *out = 1;

        return (CursorCursorCursorIntProd) {end_chunk2, out2, out_ran2, (size1 + size2 + 1)};
    } else {
        // C_tmp

        // start bounds check
        if ((end_chunk - out) <= 30) {
            ChunkTy new_chunk    = alloc_chunk(end_chunk);
            CursorTy chunk_start = new_chunk.start_ptr;
            CursorTy chunk_end   = new_chunk.end_ptr;

            end_chunk = chunk_end;
            *(TagTyPacked *) out = 100;
            CursorTy redir = out + 1;
            *(CursorTy *) redir = chunk_start;
            out = chunk_start;
        }

        // n
        CursorTy out0 = out + 9;
        *(IntTy *) out0 = n;
        out0 += 8;

        // rec1
        tmp = mkFoo(end_chunk, out0, out_ran, (n-1));
        CursorTy end_chunk1 = tmp.field0;
        CursorTy out1 = tmp.field1;
        CursorTy out_ran1 = tmp.field2;
        IntTy size1 = tmp.field3;

        // rec2
        tmp = mkFoo(end_chunk1, out1, out_ran1, (n-2));
        CursorTy end_chunk2 = tmp.field0;
        CursorTy out2 = tmp.field1;
        CursorTy out_ran2 = tmp.field2;
        IntTy size2 = tmp.field3;

        // rec3
        tmp = mkFoo(end_chunk2, out2, out_ran2, (n-3));
        CursorTy end_chunk3 = tmp.field0;
        CursorTy out3 = tmp.field1;
        CursorTy out_ran3 = tmp.field2;
        IntTy size3 = tmp.field3;

        // Conditionally write a BIG node
        if ((size1 + size2 + size3 + 1) > PAR_SIZE_THRESHOLD) {
            *out = 3;
            out++;
            *(CursorTy *) out = out_ran3;
            *(CursorTy *) out_ran3 = out1;
            out_ran3 += 8;
            *(CursorTy *) out_ran3 = out2;
            out_ran3 += 8;
        } else {
            *out = 4;
        }

        return (CursorCursorCursorIntProd) {end_chunk3, out3, out_ran3, (size1 + size2 + size3 + 1)};
    }
}

CursorIntProd sumFoo_seq(CursorTy in) {
    TagTyPacked tag = *in;
    CursorTy next = in + 1;

    sumFoo_switch:
    if (tag == 0) {
        // A
        IntTy n = *(IntTy *) next;
        CursorTy next1 = next + 8;
        return (CursorIntProd) {next1, n};
    } else if (tag == 1) {
        // B
        IntTy p = *(IntTy *) next;
        next += 8;

        CursorIntProd tmp1 = sumFoo_seq(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo_seq(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        return (CursorIntProd) {next2, n+m+p};
    } else if (tag == 4) {
        // C_tmp
        next += 8;

        IntTy p = *(IntTy *) next;
        next += 8;

        CursorIntProd tmp1 = sumFoo_seq(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo_seq(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        CursorIntProd tmp3 = sumFoo_seq(next2);
        CursorTy next3 = tmp3.field0;
        IntTy o = tmp3.field1;

        return (CursorIntProd) {next3, (p+n+m+o)};

    } else if (tag == 90) {
        CursorTy tmpcur = *(CursorTy *) next;
        TagTyPacked new_tag = *tmpcur;
        CursorTy new_next = tmpcur + 1;

        tag = new_tag;
        next = new_next;
        goto sumFoo_switch;

    } else if (tag == 100) {
        CursorTy tmpcur = *(CursorTy *) next;
        TagTyPacked new_tag = *tmpcur;
        CursorTy new_next = tmpcur + 1;

        tag = new_tag;
        next = new_next;
        goto sumFoo_switch;

    } else {
        printf("sumFoo: couldn't match tag: %c", tag);
        exit(1);
    }

}

CursorIntProd sumFoo(CursorTy in) {
    TagTyPacked tag = *in;
    CursorTy next = in + 1;

    sumFoo_switch:
    if (tag == 0) {
        // A
        IntTy n = *(IntTy *) next;
        CursorTy next1 = next + 8;
        return (CursorIntProd) {next1, n};
    } else if (tag == 1) {
        // B
        IntTy p = *(IntTy *) next;
        next += 8;

        CursorIntProd tmp1 = sumFoo(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        return (CursorIntProd) {next2, n+m+p};
    } else if (tag == 3) {
        // C_big

        CursorTy ran_storage = *(CursorTy *) next;
        next += 8;

        IntTy p = *(IntTy *) next;
        next += 8;

        CursorTy ran1 = *(CursorTy *) ran_storage;
        ran_storage += 8;
        CursorTy ran2 = *(CursorTy *) ran_storage;
        ran_storage += 8;

        CursorIntProd tmp1 = sumFoo(next);
        CursorIntProd tmp2 = cilk_spawn sumFoo(ran1);
        CursorIntProd tmp3 = cilk_spawn sumFoo(ran2);
        cilk_sync;

        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;
        CursorTy next3 = tmp3.field0;
        IntTy o = tmp3.field1;

        return (CursorIntProd) {next3, (p+n+m+o)};

    } else if (tag == 4) {

        return sumFoo_seq(in);

    } else if (tag == 90) {
        CursorTy tmpcur = *(CursorTy *) next;
        TagTyPacked new_tag = *tmpcur;
        CursorTy new_next = tmpcur + 1;

        tag = new_tag;
        next = new_next;
        goto sumFoo_switch;

    } else if (tag == 100) {
        CursorTy tmpcur = *(CursorTy *) next;
        TagTyPacked new_tag = *tmpcur;
        CursorTy new_next = tmpcur + 1;

        tag = new_tag;
        next = new_next;
        goto sumFoo_switch;

    } else {
        printf("sumFoo: couldn't match tag: %c", tag);
        exit(1);
    }

}

int main (int argc, char** argv) {

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

    // Allocate region for mkFoo.
    RegionTy *region1 = alloc_region(1 * MB);
    CursorTy r1 = region1->start_ptr;
    CursorTy end_r1 = r1 + (1 * MB);
    // For the offset table.
    RegionTy *region2 = alloc_region(2 * GB);
    CursorTy r2 = region2->start_ptr;
    CursorTy end_r2 = r2 + (1 * GB);


    CursorCursorCursorIntProd foo;
    for (int i = 0; i < iters; i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
        foo = mkFoo(end_r1, r1, r2, tree_depth);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
        selftimed = difftimespecs(&begin_timed, &end_timed);
        nums[i] = selftimed;
    }
    printf("mkFoo\n");
    printf("=====\n");
    printf("Tree Depth: %lld\n", tree_depth);
    printf("Median of 9: %lf\n", median(iters, nums));
    printf("Mean of 9: %lf\n", mean(iters, nums));
    // printFoo(r1);
    // printf("\n");

    IntTy tree_size = foo.field3;
    if (tree_size > (1 * MB)) {
        printf("Total size: %.0lfM\n", (double) (tree_size / (1 * MB)));
    } else if (tree_size > (1 * KB)) {
        printf("Total size: %.0lfK\n", (double) (tree_size / (1 * KB)));
    } else {
        printf("Total size: %.0lld bytes\n", tree_size);
    }

    CursorIntProd sum;

    IntTy total_sum = 0;
    for (int i = 0; i < iters; i++) {
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed);
        sum = sumFoo(r1);
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed);
        total_sum += sum.field1;
        selftimed = difftimespecs(&begin_timed, &end_timed);
        nums[i] = selftimed;
    }
    printf("\nsumFoo\n");
    printf("=======\n");
    printf("Tree Depth: %lld\n", tree_depth);
    printf("Median of 9: %lf\n", median(iters, nums));
    printf("Mean of 9: %lf\n", mean(iters, nums));
    printf("Sum: %lld\n", total_sum / iters);
}
