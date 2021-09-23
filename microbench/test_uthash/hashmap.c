#include <stdio.h>
#include <stdlib.h>
#include <uthash.h>

/* -------------------------------------------------------------------------- */

#define BUFFER_SIZE 1024

typedef struct Outset_elem {
    // the key
    char *outset_ref;
    UT_hash_handle hh;
} Outset_elem;

typedef struct RegionFooter_struct {
    int rf_id;
    Outset_elem *rf_outset_ptr;
} RegionFooter;

typedef struct RegionTy_struct {
    int reg_id;
    Outset_elem *reg_outset;
} RegionTy;

/* -------------------------------------------------------------------------- */

void access_outset(char *end) {
    RegionFooter *footer = (RegionFooter *) end;

    Outset_elem *elt, *tmp;
    RegionFooter *fetch_footer;
    printf("iterating:\n");
    HASH_ITER(hh, footer->rf_outset_ptr, elt, tmp) {
        fetch_footer = (RegionFooter *) elt->outset_ref;
        printf("id=%d\n", fetch_footer->rf_id);
    }
}

void add_to_outset(char *end_a, char *end_b) {
    RegionFooter *footer_a = (RegionFooter *) end_a;
    RegionFooter *footer_b = (RegionFooter *) end_b;

    Outset_elem *add = (Outset_elem*) malloc(sizeof(Outset_elem));
    add->outset_ref = end_b;
    HASH_ADD_PTR(footer_a->rf_outset_ptr, outset_ref, add);
}

void test1() {
    // Region one.
    RegionTy *reg1 = malloc(sizeof(RegionTy));
    reg1->reg_id = 1;
    reg1->reg_outset = NULL;

    // Footer one.
    char *start1, *end1;
    start1 = (char*) malloc(BUFFER_SIZE + sizeof(RegionFooter));
    end1 = start1 + BUFFER_SIZE;
    RegionFooter *footer_reg1 = (RegionFooter *) end1;
    footer_reg1->rf_id = 1;
    footer_reg1->rf_outset_ptr = reg1->reg_outset;

    // Region two.
    RegionTy *reg2 = malloc(sizeof(RegionTy));
    reg2->reg_id = 2;
    reg2->reg_outset = NULL;

    // Footer two.
    char *start2, *end2;
    start2 = (char*) malloc(BUFFER_SIZE + sizeof(RegionFooter));
    end2 = start2 + BUFFER_SIZE;
    RegionFooter *footer_reg2 = (RegionFooter *) end2;
    footer_reg2->rf_id = 2;
    footer_reg2->rf_outset_ptr = reg2->reg_outset;

    // Footer three.
    char *start3, *end3;
    start3 = (char*) malloc(BUFFER_SIZE + sizeof(RegionFooter));
    end3 = start3 + BUFFER_SIZE;
    RegionFooter *footer_reg3 = (RegionFooter *) end3;
    footer_reg3->rf_id = 3;
    footer_reg3->rf_outset_ptr = NULL;

    // Add footers to first's outset.
    add_to_outset(end1, end2);
    add_to_outset(end2, end3);

    // test.
    printf("test1\n====================\n");
    access_outset(end1);
    access_outset(end2);
}

int main() {
    test1();
    return 0;
}
