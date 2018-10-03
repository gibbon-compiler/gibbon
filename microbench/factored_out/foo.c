#include <stdio.h>
#include <stdlib.h>
#include <errno.h>
#include <string.h>

/*

Running example:

    data Foo = A Int
             | B Foo Foo
             | C Foo Foo Foo
      deriving (Show)

    mkFoo :: Int -> Foo
    mkFoo n
      | n <= 0    = A 10
      | n == 1    = B (mkFoo (n-1)) (mkFoo (n-2))
      | otherwise = C (mkFoo (n-1)) (mkFoo (n-2)) (mkFoo (n-3))

    rightmost :: Foo -> Int
    rightmost foo =
      case foo of
        A i     -> i
        B _ b   -> rightmost b
        C _ _ c -> rightmost c

 */

#define KB (1 * 1000lu)
#define MB (KB * 1000lu)
#define GB (MB * 1000lu)

// Space required to store 1 offset pair (INT,INT)
#define OFFSET_SIZE 16

// Some types we need.
typedef long long IntTy;
typedef char* CursorTy;
typedef struct CursorCursorProd_struct {
    CursorTy field0;
    CursorTy field1;
} CursorCursorProd;
typedef struct CursorCursorCursorIntProd_struct {
    CursorTy field0;
    CursorTy field1;
    CursorTy field2;
    IntTy    field3;
} CursorCursorCursorIntProd;

// --------------------------------------------------------------------------------

typedef struct RegionTy_struct {
    int refcount;
    CursorTy start_ptr;
} RegionTy;

typedef struct RegionFooter_struct {
    IntTy size;
    IntTy data_size;
    CursorTy refcount_ptr;
    CursorTy outset_ptr;
    CursorTy next;
} RegionFooter;

RegionTy* alloc_region(IntTy size) {
    // Allocate the first chunk
    IntTy total_size = size + sizeof(RegionFooter);
    CursorTy start = malloc(total_size);
    CursorTy end = start + size;

    RegionTy* reg = malloc(sizeof(RegionTy));
    reg->refcount = 0;
    reg->start_ptr = start;

    // Write the footer
    RegionFooter* footer = (RegionFooter *) end;
    footer->size = size;
    footer->data_size = 0;
    footer->refcount_ptr = (CursorTy) &(reg->refcount);
    footer->outset_ptr = NULL;
    footer-> next = NULL;
    *(RegionFooter *) end = *footer;

    return reg;
}

typedef struct ChunkTy_struct {
    CursorTy start_ptr;
    CursorTy end_ptr;
} ChunkTy;

ChunkTy alloc_chunk(CursorTy end_ptr) {
    // Get size from current footer
    RegionFooter* footer = (RegionFooter *) end_ptr;
    IntTy newsize = footer->size * 2;
    IntTy total_size = newsize + sizeof(RegionFooter);

    // Allocate
    CursorTy start = malloc(total_size);
    CursorTy end = start + newsize;

    #ifdef DEBUG
    printf("Allocated a chunk: %lld bytes.\n", total_size);
    #endif

    // Link the next chunk's footer
    footer->next = end;

    // Write the footer
    RegionFooter* new_footer = (RegionFooter *) end;
    new_footer->size = newsize;
    new_footer->data_size = 0;
    new_footer->refcount_ptr = footer->refcount_ptr;
    new_footer->outset_ptr = NULL;
    new_footer->next = NULL;

    return (ChunkTy) {start , end};
}

int get_ref_count(CursorTy end_ptr) {
    RegionFooter footer = *(RegionFooter *) end_ptr;
    return *(footer.refcount_ptr);
}

// If B -> A, bump A's refcount, and update B's offset ptr
IntTy bump_ref_count(CursorTy end_b, CursorTy end_a) {
    // Bump refcount
    RegionFooter footer_a = *(RegionFooter *) end_a;
    int refcount = *(footer_a.refcount_ptr);
    *(int *) footer_a.refcount_ptr = refcount + 1;

    // Add A to B's outset
    RegionFooter* footer_b = (RegionFooter *) end_b;
    if (footer_b->outset_ptr == NULL) {
        footer_b->outset_ptr = end_a;
    } else if (footer_b->outset_ptr != end_a) {
        printf("Outset isn't a real set yet..\n");
    }

    return refcount;
}

CursorTy printFoo(CursorTy cur);

// Returns 'cur+n', but can skip whole chunks if required (as opposed to doing it one byte at a time)
CursorCursorProd skip_bytes(CursorTy end_reg, CursorTy cur, IntTy n) {
    // Current region's footer.
    RegionFooter footer = *(RegionFooter *) end_reg;

    // Sometimes we eagerly start using a fresh region without fully using the current one, because
    //     (1) There's not enough space to write all the scalars of the current data constructor *and*
    //         the redirection nodes after it.
    // Essentially, #bytes between the last written data, and the start of the region footer.
    IntTy unused_space = footer.size - footer.data_size;

    // #bytes of data in the current region, serialized *after* the cursor 'cur'
    IntTy data_after_cur = (end_reg - unused_space) - cur;

    if (n == 0) {
        return (CursorCursorProd) {end_reg, cur};
    }
    // This is the last chunk in the region, the data better be in it.
    if (footer.data_size == 0) {
        return (CursorCursorProd) {end_reg, cur + n};
    }
    // The current chunk has enough data to skip 'n' bytes.
    else if (data_after_cur > n) {
        return (CursorCursorProd) {end_reg,cur + n};
    }
    // Otherwise, skip whatever #bytes can in the current chunk, and the rest in the next one.
    else {
        RegionFooter next_footer = *(RegionFooter *) footer.next;
        CursorTy next_end = footer.next;
        IntTy next_size = next_footer.size;
        CursorTy next_start = next_end - next_size;
        return skip_bytes(next_end, next_start, (n-data_after_cur));
    }
}

CursorTy check_footers(CursorTy end_reg) {
    RegionFooter footer = *(RegionFooter *) end_reg;
    printf("Size: %lld. Data : %lld\n", footer.size, footer.data_size);

    while(footer.next != NULL) {
        CursorTy next = footer.next;
        footer = *(RegionFooter *) next;
        printf("Size: %lld. Data : %lld\n", footer.size, footer.data_size);
    }
}

// --------------------------------------------------------------------------------

CursorCursorCursorIntProd mkFoo (CursorTy end_reg, CursorTy out, CursorTy ran_reg, IntTy n) {
    CursorCursorCursorIntProd tmp;
    IntTy size;

    if (n <= 0) {

        // ***start bounds-check
        // A redirection node would require 19 bytes
        if ((end_reg - out) <= 30) {

            ChunkTy new_chunk = alloc_chunk(end_reg);
            CursorTy chunk_start = new_chunk.start_ptr;
            CursorTy chunk_end = new_chunk.end_ptr;

            // Write the indirection pointing to the next chunk.
            RegionFooter* footer = (RegionFooter *) end_reg;
            footer->data_size = footer->size - (end_reg - out);

            *out = 110;
            out++;
            *(CursorTy *) out = chunk_start;
            out += 8;
            *(CursorTy *) out = chunk_end;
            out += 8;

            // Mutate the current cursor, and end_reg.
            out = chunk_start;
            end_reg = chunk_end;
        }
        // ***end   bounds-check

        *out = 0;
        out++;
        *(IntTy *) out = rand() % 20;
        out += 8;
        return (CursorCursorCursorIntProd) {end_reg,out,ran_reg,9};
    } else if (n == 1) {
        *out = 1;
        out++;

        // rec1
        tmp = mkFoo(end_reg, out, (ran_reg + OFFSET_SIZE), (n-1));
        CursorTy end_reg1 = tmp.field0;
        CursorTy out1 = tmp.field1;
        CursorTy ran_reg1 = tmp.field2;
        IntTy size1 = tmp.field3;

        // rec2
        tmp = mkFoo(end_reg1, out1, ran_reg1, (n-2));
        CursorTy end_reg2 = tmp.field0;
        CursorTy out2 = tmp.field1;
        CursorTy ran_reg2 = tmp.field2;
        IntTy size2 = tmp.field3;

        // write offset table (factored out).
        *(IntTy*) ran_reg = size1;
        ran_reg += 8;
        *(IntTy*) ran_reg = (ran_reg1 - ran_reg - 8);
        ran_reg += 8;

        return (CursorCursorCursorIntProd) {end_reg2,out2,ran_reg2,(size2 + size1 + 1)};
    } else {
        *out = 2;
        out++;

        // rec1
        tmp = mkFoo(end_reg, out, (ran_reg + OFFSET_SIZE + OFFSET_SIZE), (n-1));
        CursorTy end_reg1 = tmp.field0;
        CursorTy out1 = tmp.field1;
        CursorTy ran_reg1 = tmp.field2;
        IntTy size1 = tmp.field3;

        // rec2
        tmp = mkFoo(end_reg1, out1, ran_reg1, (n-2));
        CursorTy end_reg2 = tmp.field0;
        CursorTy out2 = tmp.field1;
        CursorTy ran_reg2 = tmp.field2;
        IntTy size2 = tmp.field3;

        // rec3
        tmp = mkFoo(end_reg2, out2, ran_reg2, (n-3));
        CursorTy end_reg3 = tmp.field0;
        CursorTy out3 = tmp.field1;
        CursorTy ran_reg3 = tmp.field2;
        IntTy size3 = tmp.field3;

        // write offset table (factored out).
        *(IntTy*) ran_reg = size1;
        ran_reg += 8;
        *(IntTy*) ran_reg = (ran_reg1 - ran_reg - 8);
        ran_reg += 8;
        *(IntTy*) ran_reg = size1 + size2;
        ran_reg += 8;
        *(IntTy*) ran_reg = (ran_reg2 - ran_reg - 8);
        ran_reg += 8;

        return (CursorCursorCursorIntProd) {end_reg3,out3,ran_reg3,(1 + size1 + size2 + size3)};
    }
}

IntTy rightmost(CursorTy end_reg, CursorTy in, CursorTy ran_reg) {
if1:;
    if (*in == 0) {
        in++;
        IntTy val = *(IntTy *) in;
        return val;
    } else if (*in == 1) {
        in++;

        IntTy data_offset = *(IntTy *) ran_reg;
        ran_reg += 8;
        IntTy ran_offset = *(IntTy *) ran_reg;
        ran_reg += 8;
        ran_offset = (ran_offset) == 0 ? 1 : ran_offset;

        CursorCursorProd tmp = skip_bytes(end_reg, in, data_offset);
        CursorTy end_reg1 = tmp.field0;
        CursorTy in1 = tmp.field1;
        CursorTy ran_reg1 = ran_reg + ran_offset;

        return rightmost(end_reg1, in1, ran_reg1);

    } else if (*in == 2) {
        in++;

        IntTy data_offset1 = *(IntTy *) ran_reg;
        ran_reg += 8;
        IntTy ran_offset1 = *(IntTy *) ran_reg;
        ran_reg += 8;
        IntTy data_offset2 = *(IntTy *) ran_reg;
        ran_reg += 8;
        IntTy ran_offset2 = *(IntTy *) ran_reg;
        ran_reg += 8;
        ran_offset2 = (ran_offset2) == 0 ? 1 : ran_offset2;

        CursorCursorProd tmp = skip_bytes(end_reg, in, data_offset2);
        CursorTy end_reg1 = tmp.field0;
        CursorTy in1 = tmp.field1;
        CursorTy ran_reg1 = ran_reg + ran_offset2;

        return rightmost(end_reg1, in1, ran_reg1);

    } else if (*in == 100) {
        // indirection
        in++;
        CursorTy in1 = *(CursorTy *) in;

        in = in1;
        goto if1;
    } else if (*in == 110) {
        // region end
        in++;
        CursorTy in1 = *(CursorTy *) in;
        in += 8;
        CursorTy end1 = *(CursorTy *) in;
        in += 8;

        return rightmost(end1, in1, ran_reg);

    }
}

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
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 2) {
        printf("(C ");
        cur++;
        cur = printFoo(cur);
        cur = printFoo(cur);
        cur = printFoo(cur);
        printf(") ");
        return cur;
    } else if (*cur == 100) {
        // indirection
        printf("-> ");
        cur++;
        CursorTy new_cur = *(CursorTy*) cur;
        printFoo(new_cur);
    } else if (*cur = 110) {
        // region end
        printf("=> ");
        cur++;
        CursorTy new_cur = *(CursorTy*) cur;
        printFoo(new_cur);
    }
}

void printOffsets(CursorTy start, CursorTy end) {
    IntTy val;
    while (start < end) {
        val = *(IntTy *) start;
        printf("(%lld,", val);
        start += 8;
        val = *(IntTy *) start;
        printf("%lld) ", val);
        start += 8;
    }
}


int main () {
    // something small so that the layout has indirections even for small trees.
    IntTy reg_size = 30;

    RegionTy *region_reg = alloc_region(reg_size);
    CursorTy reg = region_reg->start_ptr;
    CursorTy end_reg = reg + reg_size;
    CursorTy out = reg;

    // A place to store offset information.
    CursorTy ran_reg = malloc(1 * MB);

    /* // TODO: Add some error checks around malloc in the main RTS */
    /* // */
    /* if (ran_reg == NULL) { */
    /*     fprintf(stderr, "Malloc failed: %s\n", strerror(errno)); */
    /*     exit(1); */
    /* } */

    CursorCursorCursorIntProd tmp;
    tmp = mkFoo(end_reg, out, ran_reg, 11);
    /* printFoo(out); */
    /* printf("\n"); */
    /* check_footers(end_reg); */
    /* printf("\n"); */
    IntTy n = rightmost(end_reg, out,ran_reg);
    printf("rightmost: %lld\n", n);

    printf("------------\n");
    printf("Size: %lld\n", tmp.field3);
    /* printf("Offsets: "); */
    /* printOffsets(ran_reg,tmp.field2); */
    printf("\n");

    return 0;
}
