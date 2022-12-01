/* Gibbon program. */

#include "gibbon_rts.h"

#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <inttypes.h>
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

typedef struct GibIntProd_struct {
            GibInt field0;
        } GibIntProd;
typedef struct GibIntGibCursorProd_struct {
            GibInt field0;
            GibCursor field1;
        } GibIntGibCursorProd;
typedef struct GibBoolProd_struct {
            GibBool field0;
        } GibBoolProd;
typedef struct GibPackedTagGibCursorProd_struct {
            GibPackedTag field0;
            GibCursor field1;
        } GibPackedTagGibCursorProd;
typedef struct GibCursorProd_struct {
            GibCursor field0;
        } GibCursorProd;
typedef struct GibCursorGibIntProd_struct {
            GibCursor field0;
            GibInt field1;
        } GibCursorGibIntProd;
typedef struct GibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
        } GibCursorGibCursorProd;
typedef struct GibCursorGibCursorGibIntProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibInt field2;
        } GibCursorGibCursorGibIntProd;
typedef struct GibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
        } GibCursorGibCursorGibCursorProd;
typedef struct GibCursorGibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
            GibCursor field3;
        } GibCursorGibCursorGibCursorGibCursorProd;
typedef struct GibCursorGibCursorGibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
            GibCursor field3;
            GibCursor field4;
        } GibCursorGibCursorGibCursorGibCursorGibCursorProd;
typedef struct GibVectorProd_struct {
            GibVector *field0;
        } GibVectorProd;
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1401, GibCursor loc_1400,
                                       GibInt s_81_756_919,
                                       GibInt e_82_757_920);
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1404,
                                              GibCursor end_r_1405,
                                              GibCursor loc_1403,
                                              GibVector *nums_86_761_930,
                                              GibInt idx_87_762_931,
                                              GibCursor tr_88_763_932,
                                              GibInt n_89_764_933);
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1408,
                                                    GibCursor end_r_1409,
                                                    GibCursor loc_1407,
                                                    GibCursor tr_92_767_950,
                                                    GibInt n_93_768_951);
GibCursorGibIntProd minTree(GibCursor end_r_1411, GibCursor tr_99_774_966);
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1414,
                                                    GibCursor end_r_1415,
                                                    GibCursor loc_1413,
                                                    GibCursor tr_108_779_971,
                                                    GibInt n_109_780_972);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1417,
                                        GibCursor tr_119_790_991);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_1420, GibCursor end_r_1421, GibCursor loc_1419,
                 GibCursor arg_708_816_999);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_1424, GibCursor end_r_1425,
                              GibCursor loc_1423, GibCursor arg_717_825_1008);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1427,
                                            GibCursor arg_726_834_1017);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1429,
                                         GibCursor arg_735_841_1024);
GibCursorGibIntProd caseFn_750(GibCursor end_r_1431,
                               GibCursor l_102_751_856_1039,
                               GibInt n_101_752_857_1040);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            SearchTree_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[3];

    error = gib_info_table_insert_packed_dcon(SearchTree_T, 1, 8, 0, 1, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 1);
        exit(1);
    }
    field_tys[0] = SearchTree_T;
    field_tys[1] = SearchTree_T;
    error = gib_info_table_insert_packed_dcon(SearchTree_T, 2, 8, 0, 1, 2,
                                              field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 2);
        exit(1);
    }
    field_tys[0] = SearchTree_T;
    field_tys[1] = SearchTree_T;
    error = gib_info_table_insert_packed_dcon(SearchTree_T, 3, 8, 1, 1, 2,
                                              field_tys, 2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 3);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(SearchTree_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, SearchTree_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(2736, ")");
    gib_add_symbol(2737, "(Null ");
    gib_add_symbol(2738, "(Node ");
    gib_add_symbol(2739, "(Leaf ");
    gib_add_symbol(2740, " ->r ");
    gib_add_symbol(2741, " ->i ");
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1401, GibCursor loc_1400,
                                       GibInt s_81_756_919, GibInt e_82_757_920)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1400 + 26 > end_r_1401) {
        gib_grow_region(&loc_1400, &end_r_1401);
    }

    GibBool fltIf_868_921 = e_82_757_920 < s_81_756_919;

    if (fltIf_868_921) {
        *(GibPackedTag *) loc_1400 = 0;

        GibCursor writetag_2006 = loc_1400 + 1;
        GibCursor after_tag_2007 = loc_1400 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_1401, loc_1400,
                                                  after_tag_2007};
    } else {
        GibBool fltIf_869_922 = s_81_756_919 == e_82_757_920;

        if (fltIf_869_922) {
            *(GibPackedTag *) loc_1400 = 1;

            GibCursor writetag_2013 = loc_1400 + 1;
            GibCursor after_tag_2014 = loc_1400 + 1;

            *(GibInt *) after_tag_2014 = s_81_756_919;

            GibCursor writecur_2018 = after_tag_2014 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_1401, loc_1400,
                                                      writecur_2018};
        } else {
            GibInt fltPrm_871_923 = e_82_757_920 - s_81_756_919;
            GibInt fltPrm_870_924 = fltPrm_871_923 / 2;
            GibInt m_83_758_925 = fltPrm_870_924 + s_81_756_919;
            GibInt fltAppE_873_926 = m_83_758_925 - 1;
            GibCursor loc_1452 = loc_1400 + 17;

            *(GibPackedTag *) loc_1400 = 3;

            GibCursor writetag_2025 = loc_1400 + 1;

            gib_shadowstack_push(rstack, loc_1400, end_r_1401, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_1401, loc_1452, s_81_756_919, fltAppE_873_926);
            GibCursor pvrtmp_2782 = tmp_struct_0.field0;
            GibCursor pvrtmp_2783 = tmp_struct_0.field1;
            GibCursor pvrtmp_2784 = tmp_struct_0.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_1400 = frame->ptr;
            end_r_1401 = frame->endptr;

            GibInt fltAppE_875_928 = m_83_758_925 + 1;

            gib_shadowstack_push(rstack, loc_1400, pvrtmp_2782, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2782, pvrtmp_2784, fltAppE_875_928, e_82_757_920);
            GibCursor pvrtmp_2789 = tmp_struct_1.field0;
            GibCursor pvrtmp_2790 = tmp_struct_1.field1;
            GibCursor pvrtmp_2791 = tmp_struct_1.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_1400 = frame->ptr;
            pvrtmp_2782 = frame->endptr;

            uint16_t offset_2 = pvrtmp_2782 - pvrtmp_2784;
            uintptr_t ran_1345 = GIB_STORE_TAG(pvrtmp_2784, offset_2);
            GibCursor after_tag_2026 = loc_1400 + 1;

            *(uintptr_t *) after_tag_2026 = ran_1345;

            GibCursor writecur_2030 = after_tag_2026 + 8;

            *(GibInt *) writecur_2030 = m_83_758_925;

            GibCursor writecur_2031 = writecur_2030 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2789, loc_1400,
                                                      pvrtmp_2791};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1404,
                                              GibCursor end_r_1405,
                                              GibCursor loc_1403,
                                              GibVector *nums_86_761_930,
                                              GibInt idx_87_762_931,
                                              GibCursor tr_88_763_932,
                                              GibInt n_89_764_933)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1403 + 26 > end_r_1405) {
        gib_grow_region(&loc_1403, &end_r_1405);
    }

    GibBool fltIf_876_934 = n_89_764_933 == 0;

    if (fltIf_876_934) {
        if (loc_1403 + 18 > end_r_1405) {
            gib_grow_region(&loc_1403, &end_r_1405);
        }
        gib_indirection_barrier(loc_1403, end_r_1405, tr_88_763_932, end_r_1404,
                                SearchTree_T);

        GibCursor end_2038 = loc_1403 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1404,
                                                           end_r_1405, loc_1403,
                                                           end_2038};
    } else {
        GibInt fltPrm_879_936 = gib_vector_length(nums_86_761_930);
        GibInt fltPrm_878_937 = fltPrm_879_936 - 1;
        GibBool fltIf_877_938 = idx_87_762_931 == fltPrm_878_937;
        GibInt idx1_90_765_939;

        if (fltIf_877_938) {
            idx1_90_765_939 = 0;
        } else {
            GibInt flt_2804 = idx_87_762_931 + 1;

            idx1_90_765_939 = flt_2804;
        }

        GibInt *tmp_13;

        tmp_13 = (GibInt *) gib_vector_nth(nums_86_761_930, idx1_90_765_939);

        GibInt j_91_766_942 = *tmp_13;
        // GibInt j_91_766_942 = rand() % 20;
        // GibInt j_91_766_942 = rand() % 400;
        GibInt fltPrm_881_943 = j_91_766_942 % 2;
        GibBool fltIf_880_944 = fltPrm_881_943 == 0;

        if (fltIf_880_944) {
            gib_shadowstack_push(rstack, tr_88_763_932, end_r_1404, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                 SearchTree_T);

            GibChunk region_2805 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1469 = region_2805.start;
            GibCursor end_r_1469 = region_2805.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1403 = frame->ptr;
            end_r_1405 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_88_763_932 = frame->ptr;
            end_r_1404 = frame->endptr;
            gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_9 =
                                                      treeInsert(end_r_1404, end_r_1469, r_1469, tr_88_763_932, j_91_766_942);
            GibCursor pvrtmp_2806 = tmp_struct_9.field0;
            GibCursor pvrtmp_2807 = tmp_struct_9.field1;
            GibCursor pvrtmp_2808 = tmp_struct_9.field2;
            GibCursor pvrtmp_2809 = tmp_struct_9.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_1403 = frame->ptr;
            end_r_1405 = frame->endptr;

            GibInt fltAppE_883_946 = n_89_764_933 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_10 =
                                                      loop(pvrtmp_2807, end_r_1405, loc_1403, nums_86_761_930, idx1_90_765_939, pvrtmp_2808, fltAppE_883_946);
            GibCursor pvrtmp_2814 = tmp_struct_10.field0;
            GibCursor pvrtmp_2815 = tmp_struct_10.field1;
            GibCursor pvrtmp_2816 = tmp_struct_10.field2;
            GibCursor pvrtmp_2817 = tmp_struct_10.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2806,
                                                               pvrtmp_2815,
                                                               pvrtmp_2816,
                                                               pvrtmp_2817};
        } else {
            GibInt fltAppE_885_947 = j_91_766_942 - 1;

            gib_shadowstack_push(rstack, tr_88_763_932, end_r_1404, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                 SearchTree_T);

            GibChunk region_2824 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1478 = region_2824.start;
            GibCursor end_r_1478 = region_2824.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1403 = frame->ptr;
            end_r_1405 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_88_763_932 = frame->ptr;
            end_r_1404 = frame->endptr;
            gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                                                      treeDelete(end_r_1404, end_r_1478, r_1478, tr_88_763_932, fltAppE_885_947);
            GibCursor pvrtmp_2825 = tmp_struct_11.field0;
            GibCursor pvrtmp_2826 = tmp_struct_11.field1;
            GibCursor pvrtmp_2827 = tmp_struct_11.field2;
            GibCursor pvrtmp_2828 = tmp_struct_11.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_1403 = frame->ptr;
            end_r_1405 = frame->endptr;

            GibInt fltAppE_886_949 = n_89_764_933 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                      loop(pvrtmp_2826, end_r_1405, loc_1403, nums_86_761_930, idx1_90_765_939, pvrtmp_2827, fltAppE_886_949);
            GibCursor pvrtmp_2833 = tmp_struct_12.field0;
            GibCursor pvrtmp_2834 = tmp_struct_12.field1;
            GibCursor pvrtmp_2835 = tmp_struct_12.field2;
            GibCursor pvrtmp_2836 = tmp_struct_12.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2825,
                                                               pvrtmp_2834,
                                                               pvrtmp_2835,
                                                               pvrtmp_2836};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop2(GibCursor end_r_1404,
                                              GibCursor end_r_1405,
                                              GibCursor loc_1403,
                                              GibVector *nums_86_761_930,
                                              GibInt idx_87_762_931,
                                              GibCursor tr_88_763_932,
                                              GibInt n_89_764_933)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    while (n_89_764_933 > 0) {
        GibBool fltIf_876_934 = n_89_764_933 == 0;

        if (fltIf_876_934) {
            if (loc_1403 + 18 > end_r_1405) {
                gib_grow_region(&loc_1403, &end_r_1405);
            }
            gib_indirection_barrier(loc_1403, end_r_1405, tr_88_763_932, end_r_1404,
                                    SearchTree_T);

            GibCursor end_2038 = loc_1403 + 9;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1404,
                        end_r_1405, loc_1403,
                        end_2038};
        } else {
            GibInt fltPrm_879_936 = gib_vector_length(nums_86_761_930);
            GibInt fltPrm_878_937 = fltPrm_879_936 - 1;
            GibBool fltIf_877_938 = idx_87_762_931 == fltPrm_878_937;
            GibInt idx1_90_765_939;

            if (fltIf_877_938) {
                idx1_90_765_939 = 0;
            } else {
                GibInt flt_2804 = idx_87_762_931 + 1;
                idx1_90_765_939 = flt_2804;
            }

            GibInt *tmp_13;

            tmp_13 = (GibInt *) gib_vector_nth(nums_86_761_930, idx1_90_765_939);

            GibInt j_91_766_942 = *tmp_13;
            GibInt fltPrm_881_943 = j_91_766_942 % 2;
            GibBool fltIf_880_944 = fltPrm_881_943 == 0;

            if (fltIf_880_944) {
                gib_shadowstack_push(rstack, tr_88_763_932, end_r_1404, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                     SearchTree_T);

                GibChunk region_2805 =
                        gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_1469 = region_2805.start;
                GibCursor end_r_1469 = region_2805.end;

                frame = gib_shadowstack_pop(wstack);
                loc_1403 = frame->ptr;
                end_r_1405 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tr_88_763_932 = frame->ptr;
                end_r_1404 = frame->endptr;
                gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_9 =
                        treeInsert(end_r_1404, end_r_1469, r_1469, tr_88_763_932, j_91_766_942);
                GibCursor pvrtmp_2806 = tmp_struct_9.field0;
                GibCursor pvrtmp_2807 = tmp_struct_9.field1;
                GibCursor pvrtmp_2808 = tmp_struct_9.field2;
                GibCursor pvrtmp_2809 = tmp_struct_9.field3;

                frame = gib_shadowstack_pop(wstack);
                loc_1403 = frame->ptr;
                end_r_1405 = frame->endptr;

                // update
                GibInt fltAppE_883_946 = n_89_764_933 - 1;
                end_r_1404 = pvrtmp_2807;
                idx_87_762_931 = idx1_90_765_939;
                tr_88_763_932 = pvrtmp_2808;
                n_89_764_933 = fltAppE_883_946;

                // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_10 =
                //         loop(pvrtmp_2807, end_r_1405, loc_1403, nums_86_761_930, idx1_90_765_939, pvrtmp_2808, fltAppE_883_946);
                // GibCursor pvrtmp_2814 = tmp_struct_10.field0;
                // GibCursor pvrtmp_2815 = tmp_struct_10.field1;
                // GibCursor pvrtmp_2816 = tmp_struct_10.field2;
                // GibCursor pvrtmp_2817 = tmp_struct_10.field3;

                // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2806,
                //             pvrtmp_2815,
                //             pvrtmp_2816,
                //             pvrtmp_2817};
            } else {
                GibInt fltAppE_885_947 = j_91_766_942 - 1;

                gib_shadowstack_push(rstack, tr_88_763_932, end_r_1404, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                     SearchTree_T);

                GibChunk region_2824 =
                        gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_1478 = region_2824.start;
                GibCursor end_r_1478 = region_2824.end;

                frame = gib_shadowstack_pop(wstack);
                loc_1403 = frame->ptr;
                end_r_1405 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tr_88_763_932 = frame->ptr;
                end_r_1404 = frame->endptr;
                gib_shadowstack_push(wstack, loc_1403, end_r_1405, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                        treeDelete(end_r_1404, end_r_1478, r_1478, tr_88_763_932, fltAppE_885_947);
                GibCursor pvrtmp_2825 = tmp_struct_11.field0;
                GibCursor pvrtmp_2826 = tmp_struct_11.field1;
                GibCursor pvrtmp_2827 = tmp_struct_11.field2;
                GibCursor pvrtmp_2828 = tmp_struct_11.field3;

                frame = gib_shadowstack_pop(wstack);
                loc_1403 = frame->ptr;
                end_r_1405 = frame->endptr;

                // update.
                GibInt fltAppE_886_949 = n_89_764_933 - 1;
                end_r_1404 = pvrtmp_2826;
                idx_87_762_931 = idx1_90_765_939;
                tr_88_763_932 = pvrtmp_2827;
                n_89_764_933 = fltAppE_886_949;

                // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                //         loop(pvrtmp_2826, end_r_1405, loc_1403, nums_86_761_930, idx1_90_765_939, pvrtmp_2827, fltAppE_886_949);
                // GibCursor pvrtmp_2833 = tmp_struct_12.field0;
                // GibCursor pvrtmp_2834 = tmp_struct_12.field1;
                // GibCursor pvrtmp_2835 = tmp_struct_12.field2;
                // GibCursor pvrtmp_2836 = tmp_struct_12.field3;

                // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2825,
                //             pvrtmp_2834,
                //             pvrtmp_2835,
                //             pvrtmp_2836};
            }
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1408,
                                                    GibCursor end_r_1409,
                                                    GibCursor loc_1407,
                                                    GibCursor tr_92_767_950,
                                                    GibInt n_93_768_951)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1407 + 26 > end_r_1409) {
        gib_grow_region(&loc_1407, &end_r_1409);
    }

    GibPackedTag tmpval_2843 = *(GibPackedTag *) tr_92_767_950;
    GibCursor tmpcur_2844 = tr_92_767_950 + 1;


  switch_2934:
    ;
    switch (tmpval_2843) {

      case 0:
        {
            *(GibPackedTag *) loc_1407 = 0;

            GibCursor writetag_2053 = loc_1407 + 1;
            GibCursor after_tag_2054 = loc_1407 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                               end_r_1409,
                                                               loc_1407,
                                                               after_tag_2054};
            break;
        }

      case 1:
        {
            GibInt tmpval_2849 = *(GibInt *) tmpcur_2844;
            GibCursor tmpcur_2850 = tmpcur_2844 + sizeof(GibInt);
            GibBool fltIf_887_953 = tmpval_2849 == n_93_768_951;

            if (fltIf_887_953) {
                *(GibPackedTag *) loc_1407 = 0;

                GibCursor writetag_2062 = loc_1407 + 1;
                GibCursor after_tag_2063 = loc_1407 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                                   end_r_1409,
                                                                   loc_1407,
                                                                   after_tag_2063};
            } else {
                *(GibPackedTag *) loc_1407 = 1;

                GibCursor writetag_2069 = loc_1407 + 1;
                GibCursor after_tag_2070 = loc_1407 + 1;

                *(GibInt *) after_tag_2070 = tmpval_2849;

                GibCursor writecur_2074 = after_tag_2070 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                                   end_r_1409,
                                                                   loc_1407,
                                                                   writecur_2074};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) tmpcur_2844;
            GibCursor tmpcur_2859 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_2860 = tmpcur_2844 + 8;
            uint16_t tmptag_2861 = GIB_GET_TAG(tagged_tmpcur_33);
            GibCursor end_from_tagged_absran_1349 = tmpcur_2859 + tmptag_2861;
            GibInt tmpval_2862 = *(GibInt *) tmpaftercur_2860;
            GibCursor tmpcur_2863 = tmpaftercur_2860 + sizeof(GibInt);
            GibBool fltIf_888_957 = tmpval_2862 == n_93_768_951;

            if (fltIf_888_957) {
                gib_shadowstack_push(rstack, tmpcur_2859, end_r_1408, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2863, end_r_1408, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_1407, end_r_1409, Stk,
                                     SearchTree_T);

                GibCursorGibIntProd tmp_struct_17 =
                                     minTree(end_from_tagged_absran_1349, tmpcur_2859);
                GibCursor pvrtmp_2864 = tmp_struct_17.field0;
                GibInt pvrtmp_2865 = tmp_struct_17.field1;

                frame = gib_shadowstack_pop(wstack);
                loc_1407 = frame->ptr;
                end_r_1409 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2863 = frame->ptr;
                end_r_1408 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2859 = frame->ptr;
                end_r_1408 = frame->endptr;

                GibCursor loc_1501 = loc_1407 + 17;

                *(GibPackedTag *) loc_1407 = 3;

                GibCursor writetag_2088 = loc_1407 + 1;

                if (loc_1501 + 18 > end_r_1409) {
                    gib_grow_region(&loc_1501, &end_r_1409);
                }
                gib_indirection_barrier(loc_1501, end_r_1409, tmpcur_2863,
                                        end_r_1408, SearchTree_T);

                GibCursor end_2083 = loc_1501 + 9;

                gib_shadowstack_push(rstack, loc_1407, end_r_1409, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_18 =
                                                          treeDelete(end_from_tagged_absran_1349, end_r_1409, end_2083, tmpcur_2859, pvrtmp_2865);
                GibCursor pvrtmp_2868 = tmp_struct_18.field0;
                GibCursor pvrtmp_2869 = tmp_struct_18.field1;
                GibCursor pvrtmp_2870 = tmp_struct_18.field2;
                GibCursor pvrtmp_2871 = tmp_struct_18.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_1407 = frame->ptr;
                end_r_1409 = frame->endptr;

                uint16_t offset_19 = end_r_1409 - end_2083;
                uintptr_t ran_1352 = GIB_STORE_TAG(end_2083, offset_19);
                GibCursor after_tag_2089 = loc_1407 + 1;

                *(uintptr_t *) after_tag_2089 = ran_1352;

                GibCursor writecur_2093 = after_tag_2089 + 8;

                *(GibInt *) writecur_2093 = pvrtmp_2865;

                GibCursor writecur_2094 = writecur_2093 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2868,
                                                                   pvrtmp_2869,
                                                                   loc_1407,
                                                                   pvrtmp_2871};
            } else {
                GibBool fltIf_891_961 = tmpval_2862 < n_93_768_951;

                if (fltIf_891_961) {
                    GibCursor loc_1517 = loc_1407 + 17;

                    *(GibPackedTag *) loc_1407 = 3;

                    GibCursor writetag_2106 = loc_1407 + 1;

                    if (loc_1517 + 18 > end_r_1409) {
                        gib_grow_region(&loc_1517, &end_r_1409);
                    }
                    gib_indirection_barrier(loc_1517, end_r_1409, tmpcur_2863,
                                            end_r_1408, SearchTree_T);

                    GibCursor end_2101 = loc_1517 + 9;

                    gib_shadowstack_push(rstack, loc_1407, end_r_1409, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_23 =
                                                              treeDelete(end_from_tagged_absran_1349, end_r_1409, end_2101, tmpcur_2859, n_93_768_951);
                    GibCursor pvrtmp_2882 = tmp_struct_23.field0;
                    GibCursor pvrtmp_2883 = tmp_struct_23.field1;
                    GibCursor pvrtmp_2884 = tmp_struct_23.field2;
                    GibCursor pvrtmp_2885 = tmp_struct_23.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_1407 = frame->ptr;
                    end_r_1409 = frame->endptr;

                    uint16_t offset_24 = end_r_1409 - end_2101;
                    uintptr_t ran_1353 = GIB_STORE_TAG(end_2101, offset_24);
                    GibCursor after_tag_2107 = loc_1407 + 1;

                    *(uintptr_t *) after_tag_2107 = ran_1353;

                    GibCursor writecur_2111 = after_tag_2107 + 8;

                    *(GibInt *) writecur_2111 = tmpval_2862;

                    GibCursor writecur_2112 = writecur_2111 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2882,
                                                                       pvrtmp_2883,
                                                                       loc_1407,
                                                                       pvrtmp_2885};
                } else {
                    GibCursor loc_1533 = loc_1407 + 17;

                    *(GibPackedTag *) loc_1407 = 3;

                    GibCursor writetag_2124 = loc_1407 + 1;

                    gib_shadowstack_push(rstack, loc_1407, end_r_1409, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2859, end_r_1408, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                              treeDelete(end_r_1408, end_r_1409, loc_1533, tmpcur_2863, n_93_768_951);
                    GibCursor pvrtmp_2894 = tmp_struct_28.field0;
                    GibCursor pvrtmp_2895 = tmp_struct_28.field1;
                    GibCursor pvrtmp_2896 = tmp_struct_28.field2;
                    GibCursor pvrtmp_2897 = tmp_struct_28.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2859 = frame->ptr;
                    end_r_1408 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_1407 = frame->ptr;
                    end_r_1409 = frame->endptr;
                    if (pvrtmp_2897 + 18 > pvrtmp_2895) {
                        gib_grow_region(&pvrtmp_2897, &pvrtmp_2895);
                    }
                    gib_indirection_barrier(pvrtmp_2897, pvrtmp_2895,
                                            tmpcur_2859,
                                            end_from_tagged_absran_1349,
                                            SearchTree_T);

                    GibCursor end_2122 = pvrtmp_2897 + 9;
                    uint16_t offset_29 = pvrtmp_2895 - pvrtmp_2897;
                    uintptr_t ran_1354 = GIB_STORE_TAG(pvrtmp_2897, offset_29);
                    GibCursor after_tag_2125 = loc_1407 + 1;

                    *(uintptr_t *) after_tag_2125 = ran_1354;

                    GibCursor writecur_2129 = after_tag_2125 + 8;

                    *(GibInt *) writecur_2129 = tmpval_2862;

                    GibCursor writecur_2130 = writecur_2129 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2894,
                                                                       pvrtmp_2895,
                                                                       loc_1407,
                                                                       end_2122};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_2844;
            GibCursor tmpcur_2908 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_2909 = tmpcur_2844 + 8;
            uint16_t tmptag_2910 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_indr_1855 = tmpcur_2908 + tmptag_2910;
            GibCursor jump_1857 = tmpcur_2844 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_34 =
                                                      treeDelete(end_from_tagged_indr_1855, end_r_1409, loc_1407, tmpcur_2908, n_93_768_951);
            GibCursor pvrtmp_2911 = tmp_struct_34.field0;
            GibCursor pvrtmp_2912 = tmp_struct_34.field1;
            GibCursor pvrtmp_2913 = tmp_struct_34.field2;
            GibCursor pvrtmp_2914 = tmp_struct_34.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                               pvrtmp_2912,
                                                               pvrtmp_2913,
                                                               pvrtmp_2914};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_37 = *(uintptr_t *) tmpcur_2844;
            GibCursor tmpcur_2921 = GIB_UNTAG(tagged_tmpcur_37);
            GibCursor tmpaftercur_2922 = tmpcur_2844 + 8;
            uint16_t tmptag_2923 = GIB_GET_TAG(tagged_tmpcur_37);
            GibCursor end_from_tagged_indr_1855 = tmpcur_2921 + tmptag_2923;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_36 =
                                                      treeDelete(end_from_tagged_indr_1855, end_r_1409, loc_1407, tmpcur_2921, n_93_768_951);
            GibCursor pvrtmp_2924 = tmp_struct_36.field0;
            GibCursor pvrtmp_2925 = tmp_struct_36.field1;
            GibCursor pvrtmp_2926 = tmp_struct_36.field2;
            GibCursor pvrtmp_2927 = tmp_struct_36.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2924,
                                                               pvrtmp_2925,
                                                               pvrtmp_2926,
                                                               pvrtmp_2927};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2843");
            exit(1);
        }
    }
}
GibCursorGibIntProd minTree(GibCursor end_r_1411, GibCursor tr_99_774_966)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2935 = *(GibPackedTag *) tr_99_774_966;
    GibCursor tmpcur_2936 = tr_99_774_966 + 1;


  switch_2956:
    ;
    switch (tmpval_2935) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1411, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2937 = *(GibInt *) tmpcur_2936;
            GibCursor tmpcur_2938 = tmpcur_2936 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1411, tmpval_2937};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_2936;
            GibCursor tmpcur_2939 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_2940 = tmpcur_2936 + 8;
            uint16_t tmptag_2941 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_absran_1358 = tmpcur_2939 + tmptag_2941;
            GibInt tmpval_2942 = *(GibInt *) tmpaftercur_2940;
            GibCursor tmpcur_2943 = tmpaftercur_2940 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_41 =
                                 caseFn_750(end_r_1411, tmpcur_2943, tmpval_2942);
            GibCursor pvrtmp_2944 = tmp_struct_41.field0;
            GibInt pvrtmp_2945 = tmp_struct_41.field1;

            return (GibCursorGibIntProd) {pvrtmp_2944, pvrtmp_2945};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_44 = *(uintptr_t *) tmpcur_2936;
            GibCursor tmpcur_2946 = GIB_UNTAG(tagged_tmpcur_44);
            GibCursor tmpaftercur_2947 = tmpcur_2936 + 8;
            uint16_t tmptag_2948 = GIB_GET_TAG(tagged_tmpcur_44);
            GibCursor end_from_tagged_indr_1860 = tmpcur_2946 + tmptag_2948;
            GibCursor jump_1862 = tmpcur_2936 + 8;
            GibCursorGibIntProd tmp_struct_43 =
                                 minTree(end_from_tagged_indr_1860, tmpcur_2946);
            GibCursor pvrtmp_2949 = tmp_struct_43.field0;
            GibInt pvrtmp_2950 = tmp_struct_43.field1;

            return (GibCursorGibIntProd) {end_r_1411, pvrtmp_2950};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_46 = *(uintptr_t *) tmpcur_2936;
            GibCursor tmpcur_2951 = GIB_UNTAG(tagged_tmpcur_46);
            GibCursor tmpaftercur_2952 = tmpcur_2936 + 8;
            uint16_t tmptag_2953 = GIB_GET_TAG(tagged_tmpcur_46);
            GibCursor end_from_tagged_indr_1860 = tmpcur_2951 + tmptag_2953;
            GibCursorGibIntProd tmp_struct_45 =
                                 minTree(end_from_tagged_indr_1860, tmpcur_2951);
            GibCursor pvrtmp_2954 = tmp_struct_45.field0;
            GibInt pvrtmp_2955 = tmp_struct_45.field1;

            return (GibCursorGibIntProd) {pvrtmp_2954, pvrtmp_2955};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2935");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1414,
                                                    GibCursor end_r_1415,
                                                    GibCursor loc_1413,
                                                    GibCursor tr_108_779_971,
                                                    GibInt n_109_780_972)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1413 + 26 > end_r_1415) {
        gib_grow_region(&loc_1413, &end_r_1415);
    }

    GibPackedTag tmpval_2957 = *(GibPackedTag *) tr_108_779_971;
    GibCursor tmpcur_2958 = tr_108_779_971 + 1;


  switch_3052:
    ;
    switch (tmpval_2957) {

      case 0:
        {
            *(GibPackedTag *) loc_1413 = 1;

            GibCursor writetag_2163 = loc_1413 + 1;
            GibCursor after_tag_2164 = loc_1413 + 1;

            *(GibInt *) after_tag_2164 = n_109_780_972;

            GibCursor writecur_2168 = after_tag_2164 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1414,
                                                               end_r_1415,
                                                               loc_1413,
                                                               writecur_2168};
            break;
        }

      case 1:
        {
            GibInt tmpval_2963 = *(GibInt *) tmpcur_2958;
            GibCursor tmpcur_2964 = tmpcur_2958 + sizeof(GibInt);
            GibBool fltIf_896_974 = n_109_780_972 == tmpval_2963;

            if (fltIf_896_974) {
                *(GibPackedTag *) loc_1413 = 1;

                GibCursor writetag_2173 = loc_1413 + 1;
                GibCursor after_tag_2174 = loc_1413 + 1;

                *(GibInt *) after_tag_2174 = tmpval_2963;

                GibCursor writecur_2178 = after_tag_2174 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1414,
                                                                   end_r_1415,
                                                                   loc_1413,
                                                                   writecur_2178};
            } else {
                GibBool fltIf_897_975 = n_109_780_972 < tmpval_2963;

                if (fltIf_897_975) {
                    GibCursor loc_1570 = loc_1413 + 17;

                    *(GibPackedTag *) loc_1413 = 3;

                    GibCursor writetag_2196 = loc_1413 + 1;

                    *(GibPackedTag *) loc_1570 = 1;

                    GibCursor writetag_2181 = loc_1570 + 1;
                    GibCursor after_tag_2182 = loc_1570 + 1;

                    *(GibInt *) after_tag_2182 = n_109_780_972;

                    GibCursor writecur_2186 = after_tag_2182 + sizeof(GibInt);

                    *(GibPackedTag *) writecur_2186 = 0;

                    GibCursor writetag_2189 = writecur_2186 + 1;
                    GibCursor after_tag_2190 = writecur_2186 + 1;
                    uint16_t offset_47 = end_r_1415 - writecur_2186;
                    uintptr_t ran_1361 = GIB_STORE_TAG(writecur_2186,
                                                       offset_47);
                    GibCursor after_tag_2197 = loc_1413 + 1;

                    *(uintptr_t *) after_tag_2197 = ran_1361;

                    GibCursor writecur_2201 = after_tag_2197 + 8;

                    *(GibInt *) writecur_2201 = tmpval_2963;

                    GibCursor writecur_2202 = writecur_2201 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1414,
                                                                       end_r_1415,
                                                                       loc_1413,
                                                                       after_tag_2190};
                } else {
                    GibCursor loc_1586 = loc_1413 + 17;

                    *(GibPackedTag *) loc_1413 = 3;

                    GibCursor writetag_2223 = loc_1413 + 1;

                    *(GibPackedTag *) loc_1586 = 0;

                    GibCursor writetag_2208 = loc_1586 + 1;
                    GibCursor after_tag_2209 = loc_1586 + 1;

                    *(GibPackedTag *) after_tag_2209 = 1;

                    GibCursor writetag_2215 = after_tag_2209 + 1;
                    GibCursor after_tag_2216 = after_tag_2209 + 1;

                    *(GibInt *) after_tag_2216 = n_109_780_972;

                    GibCursor writecur_2220 = after_tag_2216 + sizeof(GibInt);
                    uint16_t offset_48 = end_r_1415 - after_tag_2209;
                    uintptr_t ran_1362 = GIB_STORE_TAG(after_tag_2209,
                                                       offset_48);
                    GibCursor after_tag_2224 = loc_1413 + 1;

                    *(uintptr_t *) after_tag_2224 = ran_1362;

                    GibCursor writecur_2228 = after_tag_2224 + 8;

                    *(GibInt *) writecur_2228 = tmpval_2963;

                    GibCursor writecur_2229 = writecur_2228 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1414,
                                                                       end_r_1415,
                                                                       loc_1413,
                                                                       writecur_2220};
                }
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_66 = *(uintptr_t *) tmpcur_2958;
            GibCursor tmpcur_2985 = GIB_UNTAG(tagged_tmpcur_66);
            GibCursor tmpaftercur_2986 = tmpcur_2958 + 8;
            uint16_t tmptag_2987 = GIB_GET_TAG(tagged_tmpcur_66);
            GibCursor end_from_tagged_absran_1366 = tmpcur_2985 + tmptag_2987;
            GibInt tmpval_2988 = *(GibInt *) tmpaftercur_2986;
            GibCursor tmpcur_2989 = tmpaftercur_2986 + sizeof(GibInt);
            GibBool fltIf_902_983 = tmpval_2988 == n_109_780_972;

            if (fltIf_902_983) {
                GibCursor loc_1606 = loc_1413 + 17;

                *(GibPackedTag *) loc_1413 = 3;

                GibCursor writetag_2244 = loc_1413 + 1;

                if (loc_1606 + 18 > end_r_1415) {
                    gib_grow_region(&loc_1606, &end_r_1415);
                }
                gib_indirection_barrier(loc_1606, end_r_1415, tmpcur_2989,
                                        end_r_1414, SearchTree_T);

                GibCursor end_2239 = loc_1606 + 9;

                if (end_2239 + 18 > end_r_1415) {
                    gib_grow_region(&end_2239, &end_r_1415);
                }
                gib_indirection_barrier(end_2239, end_r_1415, tmpcur_2985,
                                        end_from_tagged_absran_1366,
                                        SearchTree_T);

                GibCursor end_2242 = end_2239 + 9;
                uint16_t offset_49 = end_r_1415 - end_2239;
                uintptr_t ran_1369 = GIB_STORE_TAG(end_2239, offset_49);
                GibCursor after_tag_2245 = loc_1413 + 1;

                *(uintptr_t *) after_tag_2245 = ran_1369;

                GibCursor writecur_2249 = after_tag_2245 + 8;

                *(GibInt *) writecur_2249 = tmpval_2988;

                GibCursor writecur_2250 = writecur_2249 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1414,
                                                                   end_r_1415,
                                                                   loc_1413,
                                                                   end_2242};
            } else {
                GibBool fltIf_905_986 = n_109_780_972 < tmpval_2988;

                if (fltIf_905_986) {
                    GibCursor loc_1622 = loc_1413 + 17;

                    *(GibPackedTag *) loc_1413 = 3;

                    GibCursor writetag_2262 = loc_1413 + 1;

                    if (loc_1622 + 18 > end_r_1415) {
                        gib_grow_region(&loc_1622, &end_r_1415);
                    }
                    gib_indirection_barrier(loc_1622, end_r_1415, tmpcur_2989,
                                            end_r_1414, SearchTree_T);

                    GibCursor end_2257 = loc_1622 + 9;

                    gib_shadowstack_push(rstack, loc_1413, end_r_1415, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_56 =
                                                              treeInsert(end_from_tagged_absran_1366, end_r_1415, end_2257, tmpcur_2985, n_109_780_972);
                    GibCursor pvrtmp_3000 = tmp_struct_56.field0;
                    GibCursor pvrtmp_3001 = tmp_struct_56.field1;
                    GibCursor pvrtmp_3002 = tmp_struct_56.field2;
                    GibCursor pvrtmp_3003 = tmp_struct_56.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_1413 = frame->ptr;
                    end_r_1415 = frame->endptr;

                    uint16_t offset_57 = end_r_1415 - end_2257;
                    uintptr_t ran_1370 = GIB_STORE_TAG(end_2257, offset_57);
                    GibCursor after_tag_2263 = loc_1413 + 1;

                    *(uintptr_t *) after_tag_2263 = ran_1370;

                    GibCursor writecur_2267 = after_tag_2263 + 8;

                    *(GibInt *) writecur_2267 = tmpval_2988;

                    GibCursor writecur_2268 = writecur_2267 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3000,
                                                                       pvrtmp_3001,
                                                                       loc_1413,
                                                                       pvrtmp_3003};
                } else {
                    GibCursor loc_1638 = loc_1413 + 17;

                    *(GibPackedTag *) loc_1413 = 3;

                    GibCursor writetag_2280 = loc_1413 + 1;

                    gib_shadowstack_push(rstack, loc_1413, end_r_1415, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2985, end_r_1414, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_61 =
                                                              treeInsert(end_r_1414, end_r_1415, loc_1638, tmpcur_2989, n_109_780_972);
                    GibCursor pvrtmp_3012 = tmp_struct_61.field0;
                    GibCursor pvrtmp_3013 = tmp_struct_61.field1;
                    GibCursor pvrtmp_3014 = tmp_struct_61.field2;
                    GibCursor pvrtmp_3015 = tmp_struct_61.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2985 = frame->ptr;
                    end_r_1414 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_1413 = frame->ptr;
                    end_r_1415 = frame->endptr;
                    if (pvrtmp_3015 + 18 > pvrtmp_3013) {
                        gib_grow_region(&pvrtmp_3015, &pvrtmp_3013);
                    }
                    gib_indirection_barrier(pvrtmp_3015, pvrtmp_3013,
                                            tmpcur_2985,
                                            end_from_tagged_absran_1366,
                                            SearchTree_T);

                    GibCursor end_2278 = pvrtmp_3015 + 9;
                    uint16_t offset_62 = pvrtmp_3013 - pvrtmp_3015;
                    uintptr_t ran_1371 = GIB_STORE_TAG(pvrtmp_3015, offset_62);
                    GibCursor after_tag_2281 = loc_1413 + 1;

                    *(uintptr_t *) after_tag_2281 = ran_1371;

                    GibCursor writecur_2285 = after_tag_2281 + 8;

                    *(GibInt *) writecur_2285 = tmpval_2988;

                    GibCursor writecur_2286 = writecur_2285 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3012,
                                                                       pvrtmp_3013,
                                                                       loc_1413,
                                                                       end_2278};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_68 = *(uintptr_t *) tmpcur_2958;
            GibCursor tmpcur_3026 = GIB_UNTAG(tagged_tmpcur_68);
            GibCursor tmpaftercur_3027 = tmpcur_2958 + 8;
            uint16_t tmptag_3028 = GIB_GET_TAG(tagged_tmpcur_68);
            GibCursor end_from_tagged_indr_1865 = tmpcur_3026 + tmptag_3028;
            GibCursor jump_1867 = tmpcur_2958 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                      treeInsert(end_from_tagged_indr_1865, end_r_1415, loc_1413, tmpcur_3026, n_109_780_972);
            GibCursor pvrtmp_3029 = tmp_struct_67.field0;
            GibCursor pvrtmp_3030 = tmp_struct_67.field1;
            GibCursor pvrtmp_3031 = tmp_struct_67.field2;
            GibCursor pvrtmp_3032 = tmp_struct_67.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1414,
                                                               pvrtmp_3030,
                                                               pvrtmp_3031,
                                                               pvrtmp_3032};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_70 = *(uintptr_t *) tmpcur_2958;
            GibCursor tmpcur_3039 = GIB_UNTAG(tagged_tmpcur_70);
            GibCursor tmpaftercur_3040 = tmpcur_2958 + 8;
            uint16_t tmptag_3041 = GIB_GET_TAG(tagged_tmpcur_70);
            GibCursor end_from_tagged_indr_1865 = tmpcur_3039 + tmptag_3041;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_69 =
                                                      treeInsert(end_from_tagged_indr_1865, end_r_1415, loc_1413, tmpcur_3039, n_109_780_972);
            GibCursor pvrtmp_3042 = tmp_struct_69.field0;
            GibCursor pvrtmp_3043 = tmp_struct_69.field1;
            GibCursor pvrtmp_3044 = tmp_struct_69.field2;
            GibCursor pvrtmp_3045 = tmp_struct_69.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3042,
                                                               pvrtmp_3043,
                                                               pvrtmp_3044,
                                                               pvrtmp_3045};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2957");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1417,
                                        GibCursor tr_119_790_991)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3053 = *(GibPackedTag *) tr_119_790_991;
    GibCursor tmpcur_3054 = tr_119_790_991 + 1;


  switch_3080:
    ;
    switch (tmpval_3053) {

      case 0:
        {
            GibCursor jump_1803 = tr_119_790_991 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_1417, jump_1803, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_3055 = *(GibInt *) tmpcur_3054;
            GibCursor tmpcur_3056 = tmpcur_3054 + sizeof(GibInt);
            GibCursor jump_1804 = tmpcur_3054 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_1417, jump_1804, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_3054;
            GibCursor tmpcur_3057 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_3058 = tmpcur_3054 + 8;
            uint16_t tmptag_3059 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_absran_1375 = tmpcur_3057 + tmptag_3059;
            GibInt tmpval_3060 = *(GibInt *) tmpaftercur_3058;
            GibCursor tmpcur_3061 = tmpaftercur_3058 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_3057, end_r_1417, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibIntProd tmp_struct_74 =
                                          countnodes(end_r_1417, tmpcur_3061);
            GibCursor pvrtmp_3062 = tmp_struct_74.field0;
            GibCursor pvrtmp_3063 = tmp_struct_74.field1;
            GibInt pvrtmp_3064 = tmp_struct_74.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3057 = frame->ptr;
            end_r_1417 = frame->endptr;

            GibInt fltPrm_910_997 = 1 + pvrtmp_3064;
            GibCursorGibCursorGibIntProd tmp_struct_75 =
                                          countnodes(end_from_tagged_absran_1375, tmpcur_3057);
            GibCursor pvrtmp_3065 = tmp_struct_75.field0;
            GibCursor pvrtmp_3066 = tmp_struct_75.field1;
            GibInt pvrtmp_3067 = tmp_struct_75.field2;
            GibInt tailprim_1809 = fltPrm_910_997 + pvrtmp_3067;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3065, pvrtmp_3066,
                                                   tailprim_1809};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_78 = *(uintptr_t *) tmpcur_3054;
            GibCursor tmpcur_3068 = GIB_UNTAG(tagged_tmpcur_78);
            GibCursor tmpaftercur_3069 = tmpcur_3054 + 8;
            uint16_t tmptag_3070 = GIB_GET_TAG(tagged_tmpcur_78);
            GibCursor end_from_tagged_indr_1870 = tmpcur_3068 + tmptag_3070;
            GibCursor jump_1872 = tmpcur_3054 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_77 =
                                          countnodes(end_from_tagged_indr_1870, tmpcur_3068);
            GibCursor pvrtmp_3071 = tmp_struct_77.field0;
            GibCursor pvrtmp_3072 = tmp_struct_77.field1;
            GibInt pvrtmp_3073 = tmp_struct_77.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_1417, jump_1872,
                                                   pvrtmp_3073};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_80 = *(uintptr_t *) tmpcur_3054;
            GibCursor tmpcur_3074 = GIB_UNTAG(tagged_tmpcur_80);
            GibCursor tmpaftercur_3075 = tmpcur_3054 + 8;
            uint16_t tmptag_3076 = GIB_GET_TAG(tagged_tmpcur_80);
            GibCursor end_from_tagged_indr_1870 = tmpcur_3074 + tmptag_3076;
            GibCursorGibCursorGibIntProd tmp_struct_79 =
                                          countnodes(end_from_tagged_indr_1870, tmpcur_3074);
            GibCursor pvrtmp_3077 = tmp_struct_79.field0;
            GibCursor pvrtmp_3078 = tmp_struct_79.field1;
            GibInt pvrtmp_3079 = tmp_struct_79.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3077, pvrtmp_3078,
                                                   pvrtmp_3079};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3053");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_1420,
                                                                   GibCursor end_r_1421,
                                                                   GibCursor loc_1419,
                                                                   GibCursor arg_708_816_999)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1419 + 26 > end_r_1421) {
        gib_grow_region(&loc_1419, &end_r_1421);
    }

    GibPackedTag tmpval_3081 = *(GibPackedTag *) arg_708_816_999;
    GibCursor tmpcur_3082 = arg_708_816_999 + 1;


  switch_3148:
    ;
    switch (tmpval_3081) {

      case 0:
        {
            GibCursor jump_1810 = arg_708_816_999 + 1;

            *(GibPackedTag *) loc_1419 = 0;

            GibCursor writetag_2321 = loc_1419 + 1;
            GibCursor after_tag_2322 = loc_1419 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                                        end_r_1421,
                                                                        jump_1810,
                                                                        loc_1419,
                                                                        after_tag_2322};
            break;
        }

      case 1:
        {
            GibInt tmpval_3087 = *(GibInt *) tmpcur_3082;
            GibCursor tmpcur_3088 = tmpcur_3082 + sizeof(GibInt);
            GibCursor jump_1812 = tmpcur_3082 + 8;

            *(GibPackedTag *) loc_1419 = 1;

            GibCursor writetag_2330 = loc_1419 + 1;
            GibCursor after_tag_2331 = loc_1419 + 1;

            *(GibInt *) after_tag_2331 = tmpval_3087;

            GibCursor writecur_2335 = after_tag_2331 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                                        end_r_1421,
                                                                        jump_1812,
                                                                        loc_1419,
                                                                        writecur_2335};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_3082;
            GibCursor tmpcur_3093 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_3094 = tmpcur_3082 + 8;
            uint16_t tmptag_3095 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_absran_1379 = tmpcur_3093 + tmptag_3095;
            GibInt tmpval_3096 = *(GibInt *) tmpaftercur_3094;
            GibCursor tmpcur_3097 = tmpaftercur_3094 + sizeof(GibInt);
            GibCursor loc_1681 = loc_1419 + 17;

            *(GibPackedTag *) loc_1419 = 3;

            GibCursor writetag_2347 = loc_1419 + 1;

            gib_shadowstack_push(rstack, loc_1419, end_r_1421, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_3093, end_r_1420, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_r_1420, end_r_1421, loc_1681, tmpcur_3097);
            GibCursor pvrtmp_3098 = tmp_struct_81.field0;
            GibCursor pvrtmp_3099 = tmp_struct_81.field1;
            GibCursor pvrtmp_3100 = tmp_struct_81.field2;
            GibCursor pvrtmp_3101 = tmp_struct_81.field3;
            GibCursor pvrtmp_3102 = tmp_struct_81.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3093 = frame->ptr;
            end_r_1420 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_1419 = frame->ptr;
            end_r_1421 = frame->endptr;
            gib_shadowstack_push(rstack, loc_1419, pvrtmp_3099, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_82 =
                                                               _copy_SearchTree(end_from_tagged_absran_1379, pvrtmp_3099, pvrtmp_3102, tmpcur_3093);
            GibCursor pvrtmp_3107 = tmp_struct_82.field0;
            GibCursor pvrtmp_3108 = tmp_struct_82.field1;
            GibCursor pvrtmp_3109 = tmp_struct_82.field2;
            GibCursor pvrtmp_3110 = tmp_struct_82.field3;
            GibCursor pvrtmp_3111 = tmp_struct_82.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_1419 = frame->ptr;
            pvrtmp_3099 = frame->endptr;

            uint16_t offset_83 = pvrtmp_3099 - pvrtmp_3102;
            uintptr_t ran_1382 = GIB_STORE_TAG(pvrtmp_3102, offset_83);
            GibCursor after_tag_2348 = loc_1419 + 1;

            *(uintptr_t *) after_tag_2348 = ran_1382;

            GibCursor writecur_2352 = after_tag_2348 + 8;

            *(GibInt *) writecur_2352 = tmpval_3096;

            GibCursor writecur_2353 = writecur_2352 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3107,
                                                                        pvrtmp_3108,
                                                                        pvrtmp_3109,
                                                                        loc_1419,
                                                                        pvrtmp_3111};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_3082;
            GibCursor tmpcur_3120 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_3121 = tmpcur_3082 + 8;
            uint16_t tmptag_3122 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1876 = tmpcur_3120 + tmptag_3122;
            GibCursor jump_1878 = tmpcur_3082 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_85 =
                                                               _copy_SearchTree(end_from_tagged_indr_1876, end_r_1421, loc_1419, tmpcur_3120);
            GibCursor pvrtmp_3123 = tmp_struct_85.field0;
            GibCursor pvrtmp_3124 = tmp_struct_85.field1;
            GibCursor pvrtmp_3125 = tmp_struct_85.field2;
            GibCursor pvrtmp_3126 = tmp_struct_85.field3;
            GibCursor pvrtmp_3127 = tmp_struct_85.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                                        pvrtmp_3124,
                                                                        jump_1878,
                                                                        pvrtmp_3126,
                                                                        pvrtmp_3127};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3082;
            GibCursor tmpcur_3134 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3135 = tmpcur_3082 + 8;
            uint16_t tmptag_3136 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1876 = tmpcur_3134 + tmptag_3136;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_SearchTree(end_from_tagged_indr_1876, end_r_1421, loc_1419, tmpcur_3134);
            GibCursor pvrtmp_3137 = tmp_struct_87.field0;
            GibCursor pvrtmp_3138 = tmp_struct_87.field1;
            GibCursor pvrtmp_3139 = tmp_struct_87.field2;
            GibCursor pvrtmp_3140 = tmp_struct_87.field3;
            GibCursor pvrtmp_3141 = tmp_struct_87.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3137,
                                                                        pvrtmp_3138,
                                                                        pvrtmp_3139,
                                                                        pvrtmp_3140,
                                                                        pvrtmp_3141};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3081");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_1424,
                                                                                GibCursor end_r_1425,
                                                                                GibCursor loc_1423,
                                                                                GibCursor arg_717_825_1008)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3149 = *(GibPackedTag *) arg_717_825_1008;
    GibCursor tmpcur_3150 = arg_717_825_1008 + 1;


  switch_3216:
    ;
    switch (tmpval_3149) {

      case 0:
        {
            GibCursor jump_1819 = arg_717_825_1008 + 1;

            *(GibPackedTag *) loc_1423 = 0;

            GibCursor writetag_2370 = loc_1423 + 1;
            GibCursor after_tag_2371 = loc_1423 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1424,
                                                                        end_r_1425,
                                                                        jump_1819,
                                                                        loc_1423,
                                                                        after_tag_2371};
            break;
        }

      case 1:
        {
            GibInt tmpval_3155 = *(GibInt *) tmpcur_3150;
            GibCursor tmpcur_3156 = tmpcur_3150 + sizeof(GibInt);
            GibCursor jump_1821 = tmpcur_3150 + 8;

            *(GibPackedTag *) loc_1423 = 1;

            GibCursor writetag_2379 = loc_1423 + 1;
            GibCursor after_tag_2380 = loc_1423 + 1;

            *(GibInt *) after_tag_2380 = tmpval_3155;

            GibCursor writecur_2384 = after_tag_2380 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1424,
                                                                        end_r_1425,
                                                                        jump_1821,
                                                                        loc_1423,
                                                                        writecur_2384};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_94 = *(uintptr_t *) tmpcur_3150;
            GibCursor tmpcur_3161 = GIB_UNTAG(tagged_tmpcur_94);
            GibCursor tmpaftercur_3162 = tmpcur_3150 + 8;
            uint16_t tmptag_3163 = GIB_GET_TAG(tagged_tmpcur_94);
            GibCursor end_from_tagged_absran_1384 = tmpcur_3161 + tmptag_3163;
            GibInt tmpval_3164 = *(GibInt *) tmpaftercur_3162;
            GibCursor tmpcur_3165 = tmpaftercur_3162 + sizeof(GibInt);
            GibCursor loc_1708 = loc_1423 + 9;

            *(GibPackedTag *) loc_1423 = 2;

            GibCursor writetag_2396 = loc_1423 + 1;
            GibCursor after_tag_2397 = loc_1423 + 1;

            *(GibInt *) after_tag_2397 = tmpval_3164;

            GibCursor writecur_2401 = after_tag_2397 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_1423, end_r_1425, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_3161, end_r_1424, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_r_1424, end_r_1425, loc_1708, tmpcur_3165);
            GibCursor pvrtmp_3166 = tmp_struct_92.field0;
            GibCursor pvrtmp_3167 = tmp_struct_92.field1;
            GibCursor pvrtmp_3168 = tmp_struct_92.field2;
            GibCursor pvrtmp_3169 = tmp_struct_92.field3;
            GibCursor pvrtmp_3170 = tmp_struct_92.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3161 = frame->ptr;
            end_r_1424 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_1423 = frame->ptr;
            end_r_1425 = frame->endptr;
            gib_shadowstack_push(rstack, loc_1423, pvrtmp_3167, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_93 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_1384, pvrtmp_3167, pvrtmp_3170, tmpcur_3161);
            GibCursor pvrtmp_3175 = tmp_struct_93.field0;
            GibCursor pvrtmp_3176 = tmp_struct_93.field1;
            GibCursor pvrtmp_3177 = tmp_struct_93.field2;
            GibCursor pvrtmp_3178 = tmp_struct_93.field3;
            GibCursor pvrtmp_3179 = tmp_struct_93.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_1423 = frame->ptr;
            pvrtmp_3167 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3175,
                                                                        pvrtmp_3176,
                                                                        pvrtmp_3177,
                                                                        loc_1423,
                                                                        pvrtmp_3179};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_96 = *(uintptr_t *) tmpcur_3150;
            GibCursor tmpcur_3188 = GIB_UNTAG(tagged_tmpcur_96);
            GibCursor tmpaftercur_3189 = tmpcur_3150 + 8;
            uint16_t tmptag_3190 = GIB_GET_TAG(tagged_tmpcur_96);
            GibCursor end_from_tagged_indr_1882 = tmpcur_3188 + tmptag_3190;
            GibCursor jump_1884 = tmpcur_3150 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_95 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1882, end_r_1425, loc_1423, tmpcur_3188);
            GibCursor pvrtmp_3191 = tmp_struct_95.field0;
            GibCursor pvrtmp_3192 = tmp_struct_95.field1;
            GibCursor pvrtmp_3193 = tmp_struct_95.field2;
            GibCursor pvrtmp_3194 = tmp_struct_95.field3;
            GibCursor pvrtmp_3195 = tmp_struct_95.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1424,
                                                                        pvrtmp_3192,
                                                                        jump_1884,
                                                                        pvrtmp_3194,
                                                                        pvrtmp_3195};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_98 = *(uintptr_t *) tmpcur_3150;
            GibCursor tmpcur_3202 = GIB_UNTAG(tagged_tmpcur_98);
            GibCursor tmpaftercur_3203 = tmpcur_3150 + 8;
            uint16_t tmptag_3204 = GIB_GET_TAG(tagged_tmpcur_98);
            GibCursor end_from_tagged_indr_1882 = tmpcur_3202 + tmptag_3204;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_97 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1882, end_r_1425, loc_1423, tmpcur_3202);
            GibCursor pvrtmp_3205 = tmp_struct_97.field0;
            GibCursor pvrtmp_3206 = tmp_struct_97.field1;
            GibCursor pvrtmp_3207 = tmp_struct_97.field2;
            GibCursor pvrtmp_3208 = tmp_struct_97.field3;
            GibCursor pvrtmp_3209 = tmp_struct_97.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3205,
                                                                        pvrtmp_3206,
                                                                        pvrtmp_3207,
                                                                        pvrtmp_3208,
                                                                        pvrtmp_3209};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3149");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1427,
                                            GibCursor arg_726_834_1017)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3217 = *(GibPackedTag *) arg_726_834_1017;
    GibCursor tmpcur_3218 = arg_726_834_1017 + 1;


  switch_3240:
    ;
    switch (tmpval_3217) {

      case 0:
        {
            GibCursor jump_1828 = arg_726_834_1017 + 1;

            return (GibCursorGibCursorProd) {end_r_1427, jump_1828};
            break;
        }

      case 1:
        {
            GibInt tmpval_3219 = *(GibInt *) tmpcur_3218;
            GibCursor tmpcur_3220 = tmpcur_3218 + sizeof(GibInt);
            GibCursor jump_1830 = tmpcur_3218 + 8;

            return (GibCursorGibCursorProd) {end_r_1427, jump_1830};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_3218;
            GibCursor tmpcur_3221 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_3222 = tmpcur_3218 + 8;
            uint16_t tmptag_3223 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_absran_1387 = tmpcur_3221 + tmptag_3223;
            GibInt tmpval_3224 = *(GibInt *) tmpaftercur_3222;
            GibCursor tmpcur_3225 = tmpaftercur_3222 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_3221, end_r_1427, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_r_1427, tmpcur_3225);
            GibCursor pvrtmp_3226 = tmp_struct_99.field0;
            GibCursor pvrtmp_3227 = tmp_struct_99.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3221 = frame->ptr;
            end_r_1427 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_100 =
                                    _traverse_SearchTree(end_from_tagged_absran_1387, tmpcur_3221);
            GibCursor pvrtmp_3228 = tmp_struct_100.field0;
            GibCursor pvrtmp_3229 = tmp_struct_100.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3228, pvrtmp_3229};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_3218;
            GibCursor tmpcur_3230 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_3231 = tmpcur_3218 + 8;
            uint16_t tmptag_3232 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_1888 = tmpcur_3230 + tmptag_3232;
            GibCursor jump_1890 = tmpcur_3218 + 8;
            GibCursorGibCursorProd tmp_struct_102 =
                                    _traverse_SearchTree(end_from_tagged_indr_1888, tmpcur_3230);
            GibCursor pvrtmp_3233 = tmp_struct_102.field0;
            GibCursor pvrtmp_3234 = tmp_struct_102.field1;

            return (GibCursorGibCursorProd) {end_r_1427, jump_1890};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) tmpcur_3218;
            GibCursor tmpcur_3235 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_3236 = tmpcur_3218 + 8;
            uint16_t tmptag_3237 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_indr_1888 = tmpcur_3235 + tmptag_3237;
            GibCursorGibCursorProd tmp_struct_104 =
                                    _traverse_SearchTree(end_from_tagged_indr_1888, tmpcur_3235);
            GibCursor pvrtmp_3238 = tmp_struct_104.field0;
            GibCursor pvrtmp_3239 = tmp_struct_104.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3238, pvrtmp_3239};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3217");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1429,
                                         GibCursor arg_735_841_1024)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3241 = *(GibPackedTag *) arg_735_841_1024;
    GibCursor tmpcur_3242 = arg_735_841_1024 + 1;


  switch_3264:
    ;
    switch (tmpval_3241) {

      case 0:
        {
            GibCursor jump_1837 = arg_735_841_1024 + 1;
            unsigned char wildcard_736_842_1025 = gib_print_symbol(2737);
            unsigned char wildcard_737_843_1026 = gib_print_symbol(2736);

            return (GibCursorGibCursorProd) {end_r_1429, jump_1837};
            break;
        }

      case 1:
        {
            GibInt tmpval_3243 = *(GibInt *) tmpcur_3242;
            GibCursor tmpcur_3244 = tmpcur_3242 + sizeof(GibInt);
            GibCursor jump_1839 = tmpcur_3242 + 8;
            unsigned char wildcard_740_845_1028 = gib_print_symbol(2739);
            unsigned char y_739_846_1029 = printf("%ld", tmpval_3243);
            unsigned char wildcard_741_847_1030 = gib_print_symbol(2736);

            return (GibCursorGibCursorProd) {end_r_1429, jump_1839};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_108 = *(uintptr_t *) tmpcur_3242;
            GibCursor tmpcur_3245 = GIB_UNTAG(tagged_tmpcur_108);
            GibCursor tmpaftercur_3246 = tmpcur_3242 + 8;
            uint16_t tmptag_3247 = GIB_GET_TAG(tagged_tmpcur_108);
            GibCursor end_from_tagged_absran_1390 = tmpcur_3245 + tmptag_3247;
            GibInt tmpval_3248 = *(GibInt *) tmpaftercur_3246;
            GibCursor tmpcur_3249 = tmpaftercur_3246 + sizeof(GibInt);
            unsigned char wildcard_748_851_1034 = gib_print_symbol(2738);
            unsigned char y_745_852_1035 = printf("%ld", tmpval_3248);

            gib_shadowstack_push(rstack, tmpcur_3245, end_r_1429, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_r_1429, tmpcur_3249);
            GibCursor pvrtmp_3250 = tmp_struct_106.field0;
            GibCursor pvrtmp_3251 = tmp_struct_106.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3245 = frame->ptr;
            end_r_1429 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_107 =
                                    _print_SearchTree(end_from_tagged_absran_1390, tmpcur_3245);
            GibCursor pvrtmp_3252 = tmp_struct_107.field0;
            GibCursor pvrtmp_3253 = tmp_struct_107.field1;
            unsigned char wildcard_749_855_1038 = gib_print_symbol(2736);

            return (GibCursorGibCursorProd) {pvrtmp_3252, pvrtmp_3253};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_3242;
            GibCursor tmpcur_3254 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_3255 = tmpcur_3242 + 8;
            uint16_t tmptag_3256 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_1894 = tmpcur_3254 + tmptag_3256;
            GibCursor jump_1896 = tmpcur_3242 + 8;
            unsigned char wildcard_1899 = gib_print_symbol(2741);
            GibCursorGibCursorProd tmp_struct_109 =
                                    _print_SearchTree(end_from_tagged_indr_1894, tmpcur_3254);
            GibCursor pvrtmp_3257 = tmp_struct_109.field0;
            GibCursor pvrtmp_3258 = tmp_struct_109.field1;

            return (GibCursorGibCursorProd) {end_r_1429, jump_1896};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_3242;
            GibCursor tmpcur_3259 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_3260 = tmpcur_3242 + 8;
            uint16_t tmptag_3261 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_1894 = tmpcur_3259 + tmptag_3261;
            unsigned char wildcard_1899 = gib_print_symbol(2740);
            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_SearchTree(end_from_tagged_indr_1894, tmpcur_3259);
            GibCursor pvrtmp_3262 = tmp_struct_111.field0;
            GibCursor pvrtmp_3263 = tmp_struct_111.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3262, pvrtmp_3263};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3241");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_750(GibCursor end_r_1431,
                               GibCursor l_102_751_856_1039,
                               GibInt n_101_752_857_1040)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3265 = *(GibPackedTag *) l_102_751_856_1039;
    GibCursor tmpcur_3266 = l_102_751_856_1039 + 1;


  switch_3286:
    ;
    switch (tmpval_3265) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1431, n_101_752_857_1040};
            break;
        }

      case 1:
        {
            GibInt tmpval_3267 = *(GibInt *) tmpcur_3266;
            GibCursor tmpcur_3268 = tmpcur_3266 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1431, tmpval_3267};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_3266;
            GibCursor tmpcur_3269 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_3270 = tmpcur_3266 + 8;
            uint16_t tmptag_3271 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_absran_1393 = tmpcur_3269 + tmptag_3271;
            GibInt tmpval_3272 = *(GibInt *) tmpaftercur_3270;
            GibCursor tmpcur_3273 = tmpaftercur_3270 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_113 =
                                 minTree(end_r_1431, tmpcur_3273);
            GibCursor pvrtmp_3274 = tmp_struct_113.field0;
            GibInt pvrtmp_3275 = tmp_struct_113.field1;

            return (GibCursorGibIntProd) {pvrtmp_3274, pvrtmp_3275};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_116 = *(uintptr_t *) tmpcur_3266;
            GibCursor tmpcur_3276 = GIB_UNTAG(tagged_tmpcur_116);
            GibCursor tmpaftercur_3277 = tmpcur_3266 + 8;
            uint16_t tmptag_3278 = GIB_GET_TAG(tagged_tmpcur_116);
            GibCursor end_from_tagged_indr_1900 = tmpcur_3276 + tmptag_3278;
            GibCursor jump_1902 = tmpcur_3266 + 8;
            GibCursorGibIntProd tmp_struct_115 =
                                 caseFn_750(end_from_tagged_indr_1900, tmpcur_3276, n_101_752_857_1040);
            GibCursor pvrtmp_3279 = tmp_struct_115.field0;
            GibInt pvrtmp_3280 = tmp_struct_115.field1;

            return (GibCursorGibIntProd) {end_r_1431, pvrtmp_3280};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_118 = *(uintptr_t *) tmpcur_3266;
            GibCursor tmpcur_3281 = GIB_UNTAG(tagged_tmpcur_118);
            GibCursor tmpaftercur_3282 = tmpcur_3266 + 8;
            uint16_t tmptag_3283 = GIB_GET_TAG(tagged_tmpcur_118);
            GibCursor end_from_tagged_indr_1900 = tmpcur_3281 + tmptag_3283;
            GibCursorGibIntProd tmp_struct_117 =
                                 caseFn_750(end_from_tagged_indr_1900, tmpcur_3281, n_101_752_857_1040);
            GibCursor pvrtmp_3284 = tmp_struct_117.field0;
            GibInt pvrtmp_3285 = tmp_struct_117.field1;

            return (GibCursorGibIntProd) {pvrtmp_3284, pvrtmp_3285};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3265");
            exit(1);
        }
    }
}
int gib_main_expr(void)
{
    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_2742 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1443 = region_2742.start;
    GibCursor end_r_1443 = region_2742.end;
    GibChunk region_2743 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1440 = region_2743.start;
    GibCursor end_r_1440 = region_2743.end;
    GibVector *pts_78_753_913 =
              gib_vector_alloc(gib_read_arrayfile_length_param(),
                               sizeof(GibInt));
    GibInt arr_elem_127;

    FILE * fp_128;

    char *line_129 = NULL;

    size_t(len_130);
    len_130 = 0;
    ssize_t(read_131);
    fp_128 = fopen(gib_read_arrayfile_param(), "r");
    if (fp_128 == NULL) {
        fprintf(stderr, "fopen failed\n");
        abort();
    }

    GibInt tmp_133;
    GibInt i_132 = 0;

    while ((read_131 = getline(&line_129, &len_130, fp_128)) != -1) {
        int xxxx = sscanf(line_129, "%ld", &tmp_133);

        arr_elem_127 = tmp_133;
        gib_vector_inplace_update(pts_78_753_913, i_132, &arr_elem_127);
        i_132++;
    }

    GibInt n_79_754_914 = gib_get_size_param();
    GibCursor pvrtmp_2761;
    GibCursor pvrtmp_2762;
    GibCursor pvrtmp_2763;
    GibVector *times_124 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2761;
    struct timespec end_pvrtmp_2761;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(2);

    for (long long iters_pvrtmp_2761 = 0; iters_pvrtmp_2761 <
         gib_get_iters_param(); iters_pvrtmp_2761++) {
        if (iters_pvrtmp_2761 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_gc_save_state(snapshot, 2, region_2742.end, region_2743.end);
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2761);

        GibCursorGibCursorGibCursorProd tmp_struct_119 =
                                         helper(end_r_1440, r_1440, 0, 3);
        GibCursor pvrtmp_2744 = tmp_struct_119.field0;
        GibCursor pvrtmp_2745 = tmp_struct_119.field1;
        GibCursor pvrtmp_2746 = tmp_struct_119.field2;
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                  loop(pvrtmp_2744, end_r_1443, r_1443, pts_78_753_913, 0, pvrtmp_2745, n_79_754_914);
        GibCursor pvrtmp_2751 = tmp_struct_120.field0;
        GibCursor pvrtmp_2752 = tmp_struct_120.field1;
        GibCursor pvrtmp_2753 = tmp_struct_120.field2;
        GibCursor pvrtmp_2754 = tmp_struct_120.field3;

        pvrtmp_2761 = pvrtmp_2752;
        pvrtmp_2762 = pvrtmp_2753;
        pvrtmp_2763 = pvrtmp_2754;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2761);

        if (iters_pvrtmp_2761 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_gc_restore_state(snapshot);
        }

        double itertime_121 = gib_difftimespecs(&begin_pvrtmp_2761,
                                                &end_pvrtmp_2761);

        printf("itertime: %lf\n", itertime_121);
        gib_vector_inplace_update(times_124, iters_pvrtmp_2761, &itertime_121);
    }
    gib_vector_inplace_sort(times_124, gib_compare_doubles);

    double *tmp_125 = (double *) gib_vector_nth(times_124,
                                                gib_get_iters_param() / 2);
    double selftimed_123 = *tmp_125;
    double batchtime_122 = gib_sum_timing_array(times_124);

    gib_print_timing_array(times_124);
    gib_vector_free(times_124);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_122);
    printf("SELFTIMED: %e\n", selftimed_123);

    GibCursorGibCursorGibIntProd tmp_struct_126 =
                                  countnodes(end_r_1443, pvrtmp_2762);
    GibCursor pvrtmp_2771 = tmp_struct_126.field0;
    GibCursor pvrtmp_2772 = tmp_struct_126.field1;
    GibInt pvrtmp_2773 = tmp_struct_126.field2;

    printf("%ld", pvrtmp_2773);
    printf("\n");
    return 0;
}
