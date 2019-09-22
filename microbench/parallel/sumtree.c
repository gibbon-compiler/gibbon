#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>
#include <utlist.h>
#include <uthash.h>

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

typedef struct CursorCursorIntProd_struct {
    CursorTy field0;
    CursorTy field1;
    IntTy    field2;
} CursorCursorIntProd;

typedef struct CursorIntProd_struct {
    CursorTy field0;
    IntTy    field1;
} CursorIntProd;

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
        trav_to_first_chunk(footer->prev);
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
                    free_region(first_chunk);
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

/* --------------------------------------------------------------------------

data Foo = A Int
         | B Foo Foo
         | C Foo Foo Foo

         | B_big Ptr Foo Foo
         | C_big Ptr Ptr Foo Foo Foo



mkFoo :: Int -> Foo
mkFoo n
  | n < 0     = A 10
  | n == 1    = B (mkFoo (n-1)) (mkFoo (n-2))
  | otherwise = C (mkFoo (n-1)) (mkFoo (n-2)) (mkFoo (n-3))


sumFoo :: Foo -> Int
sumFoo foo =
  case foo of
    A i        -> i
    B f1 f2    -> sumFoo f1 + sumFoo f2
    C f1 f2 f3 -> sumFoo f1 + sumFoo f2 + sumFoo f3

    B_big _ f1 f2 -> let p = sumFoo f1 .||. sumFoo f2
                     in fst p + snd p

    C_big _ _ f1 f2 f3 -> let t = sumFoo f1 .||. (sumFoo f2 .||. sumFoo f3)
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
        printf("(B _ ");
        cur += 9;
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 2) {
        printf("(C _ _ ");
        cur += 17;
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 3) {
        printf("(B_big PTR ");
        cur += 9;
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    }  else if (*cur == 4) {
        printf("(C_big PTR PTR ");
        cur += 17;
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
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
#define PAR_SIZE_THRESHOLD 4000

CursorCursorIntProd mkFoo (CursorTy end_chunk, CursorTy out, IntTy n) {
    CursorCursorIntProd tmp;
    if (n <= 0) {
        // start bounds check
        if ((end_chunk - out) <= 20) {
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
        return (CursorCursorIntProd) {end_chunk, out, 9};
    } else if (n == 1) {
        // rec1
        CursorTy left_out = out + 9;
        tmp = mkFoo(end_chunk, left_out, (n-1));
        CursorTy end_chunk1 = tmp.field0;
        CursorTy out1 = tmp.field1;
        IntTy size1 = tmp.field2;

        // rec2
        tmp = mkFoo(end_chunk1, out1, (n-2));
        CursorTy end_chunk2 = tmp.field0;
        CursorTy out2 = tmp.field1;
        IntTy size2 = tmp.field2;

        // Conditionally write a BIG node
        if ((size1 + size2 + 1) > PAR_SIZE_THRESHOLD) {
            *out = 3;
            out++;
            *(CursorTy *) out = out1;
        } else {
            *out = 1;
        }
        return (CursorCursorIntProd) {end_chunk2, out2, (size1 + size2 + 1)};
    } else {
        CursorTy left = out + 17;

        // rec1
        tmp = mkFoo(end_chunk, left, (n-1));
        CursorTy end_chunk1 = tmp.field0;
        CursorTy out1 = tmp.field1;
        IntTy size1 = tmp.field2;

        // rec2
        tmp = mkFoo(end_chunk1, out1, (n-2));
        CursorTy end_chunk2 = tmp.field0;
        CursorTy out2 = tmp.field1;
        IntTy size2 = tmp.field2;

        // rec3
        tmp = mkFoo(end_chunk2, out2, (n-3));
        CursorTy end_chunk3 = tmp.field0;
        CursorTy out3 = tmp.field1;
        IntTy size3 = tmp.field2;

        // Conditionally write a BIG node
        if ((size1 + size2 + size3 + 1) > PAR_SIZE_THRESHOLD) {
            *out = 4;
            out++;
            *(CursorTy *) out = out1;
            out += 8;
            *(CursorTy *) out = out2;
        } else {
            *out = 2;
        }

        return (CursorCursorIntProd) {end_chunk3, out3, (size1 + size2 + size3 + 1)};
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
        next += 8;
        CursorIntProd tmp1 = sumFoo(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        return (CursorIntProd) {next2, (n+m)};
    } else if (tag == 2) {
        // C
        next += 16;
        CursorIntProd tmp1 = sumFoo(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        CursorIntProd tmp3 = sumFoo(next2);
        CursorTy next3 = tmp3.field0;
        IntTy o = tmp3.field1;

        return (CursorIntProd) {next3, (n+m+o)};

    } else if (tag == 3) {
        // B_big
        next += 8;

        CursorIntProd tmp1 = sumFoo(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        return (CursorIntProd) {next2, (n+m)};

    } else if (tag == 4) {
        // C_big
        next += 16;

        CursorIntProd tmp1 = sumFoo(next);
        CursorTy next1 = tmp1.field0;
        IntTy n = tmp1.field1;

        CursorIntProd tmp2 = sumFoo(next1);
        CursorTy next2 = tmp2.field0;
        IntTy m = tmp2.field1;

        CursorIntProd tmp3 = sumFoo(next2);
        CursorTy next3 = tmp3.field0;
        IntTy o = tmp3.field1;

        return (CursorIntProd) {next3, (n+m+o)};

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
    int reg_size = 100;
    IntTy tree_size = atoll(argv[1]);

    RegionTy *region1 = alloc_region(reg_size);
    CursorTy r1 = region1->start_ptr;
    CursorTy end_r1 = r1 + reg_size;

    CursorCursorIntProd foo;
    foo = mkFoo(end_r1, r1, tree_size);
    printFoo(r1);
    printf("\n");
    printf("Foo size: %lld\n", foo.field2);
    CursorIntProd sum = sumFoo(r1);
    printf("Sum: %lld\n", sum.field1);
}
