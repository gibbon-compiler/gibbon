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
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1389, GibCursor loc_1388,
                                       GibInt s_81_751_907,
                                       GibInt e_82_752_908);
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1392,
                                              GibCursor end_r_1393,
                                              GibCursor loc_1391,
                                              GibVector *nums_84_754_918,
                                              GibInt idx_85_755_919,
                                              GibCursor tr_86_756_920,
                                              GibInt n_87_757_921);
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1396,
                                                    GibCursor end_r_1397,
                                                    GibCursor loc_1395,
                                                    GibCursor tr_90_760_938,
                                                    GibInt n_91_761_939);
GibCursorGibIntProd minTree(GibCursor end_r_1399, GibCursor tr_97_767_954);
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1402,
                                                    GibCursor end_r_1403,
                                                    GibCursor loc_1401,
                                                    GibCursor tr_106_772_959,
                                                    GibInt n_107_773_960);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1405,
                                        GibCursor tr_117_783_979);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_1408, GibCursor end_r_1409, GibCursor loc_1407,
                 GibCursor arg_702_809_987);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_1412, GibCursor end_r_1413,
                              GibCursor loc_1411, GibCursor arg_711_818_996);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1415,
                                            GibCursor arg_720_827_1005);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1417,
                                         GibCursor arg_729_834_1012);
GibCursorGibIntProd caseFn_744(GibCursor end_r_1419,
                               GibCursor l_100_745_849_1027,
                               GibInt n_99_746_850_1028);
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
    gib_add_symbol(2723, ")");
    gib_add_symbol(2724, "(Null ");
    gib_add_symbol(2725, "(Node ");
    gib_add_symbol(2726, "(Leaf ");
    gib_add_symbol(2727, " ->r ");
    gib_add_symbol(2728, " ->i ");
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1389, GibCursor loc_1388,
                                       GibInt s_81_751_907, GibInt e_82_752_908)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1388 + 26 > end_r_1389) {
        gib_grow_region(&loc_1388, &end_r_1389);
    }

    GibBool fltIf_858_909 = e_82_752_908 < s_81_751_907;

    if (fltIf_858_909) {
        *(GibPackedTag *) loc_1388 = 0;

        GibCursor writetag_1993 = loc_1388 + 1;
        GibCursor after_tag_1994 = loc_1388 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_1389, loc_1388,
                                                  after_tag_1994};
    } else {
        GibBool fltIf_859_910 = s_81_751_907 == e_82_752_908;

        if (fltIf_859_910) {
            *(GibPackedTag *) loc_1388 = 1;

            GibCursor writetag_2000 = loc_1388 + 1;
            GibCursor after_tag_2001 = loc_1388 + 1;

            *(GibInt *) after_tag_2001 = s_81_751_907;

            GibCursor writecur_2005 = after_tag_2001 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_1389, loc_1388,
                                                      writecur_2005};
        } else {
            GibInt fltPrm_861_911 = e_82_752_908 - s_81_751_907;
            GibInt fltPrm_860_912 = fltPrm_861_911 / 2;
            GibInt m_83_753_913 = fltPrm_860_912 + s_81_751_907;
            GibInt fltAppE_863_914 = m_83_753_913 - 1;
            GibCursor loc_1440 = loc_1388 + 17;

            *(GibPackedTag *) loc_1388 = 3;

            GibCursor writetag_2012 = loc_1388 + 1;

            gib_shadowstack_push(rstack, loc_1388, end_r_1389, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_0 =
                                             helper(end_r_1389, loc_1440, s_81_751_907, fltAppE_863_914);
            GibCursor pvrtmp_2769 = tmp_struct_0.field0;
            GibCursor pvrtmp_2770 = tmp_struct_0.field1;
            GibCursor pvrtmp_2771 = tmp_struct_0.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_1388 = frame->ptr;
            end_r_1389 = frame->endptr;

            GibInt fltAppE_865_916 = m_83_753_913 + 1;

            gib_shadowstack_push(rstack, loc_1388, pvrtmp_2769, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorProd tmp_struct_1 =
                                             helper(pvrtmp_2769, pvrtmp_2771, fltAppE_865_916, e_82_752_908);
            GibCursor pvrtmp_2776 = tmp_struct_1.field0;
            GibCursor pvrtmp_2777 = tmp_struct_1.field1;
            GibCursor pvrtmp_2778 = tmp_struct_1.field2;

            frame = gib_shadowstack_pop(rstack);
            loc_1388 = frame->ptr;
            pvrtmp_2769 = frame->endptr;

            uint16_t offset_2 = pvrtmp_2769 - pvrtmp_2771;
            uintptr_t ran_1333 = GIB_STORE_TAG(pvrtmp_2771, offset_2);
            GibCursor after_tag_2013 = loc_1388 + 1;

            *(uintptr_t *) after_tag_2013 = ran_1333;

            GibCursor writecur_2017 = after_tag_2013 + 8;

            *(GibInt *) writecur_2017 = m_83_753_913;

            GibCursor writecur_2018 = writecur_2017 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_2776, loc_1388,
                                                      pvrtmp_2778};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1392,
                                              GibCursor end_r_1393,
                                              GibCursor loc_1391,
                                              GibVector *nums_84_754_918,
                                              GibInt idx_85_755_919,
                                              GibCursor tr_86_756_920,
                                              GibInt n_87_757_921)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1391 + 26 > end_r_1393) {
        gib_grow_region(&loc_1391, &end_r_1393);
    }

    GibBool fltIf_866_922 = n_87_757_921 == 0;

    if (fltIf_866_922) {
        if (loc_1391 + 18 > end_r_1393) {
            gib_grow_region(&loc_1391, &end_r_1393);
        }
        gib_indirection_barrier(loc_1391, end_r_1393, tr_86_756_920, end_r_1392,
                                SearchTree_T);

        GibCursor end_2025 = loc_1391 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1392,
                                                           end_r_1393, loc_1391,
                                                           end_2025};
    } else {
        GibInt fltPrm_869_924 = gib_vector_length(nums_84_754_918);
        GibInt fltPrm_868_925 = fltPrm_869_924 - 1;
        GibBool fltIf_867_926 = idx_85_755_919 == fltPrm_868_925;
        GibInt idx1_88_758_927;

        if (fltIf_867_926) {
            idx1_88_758_927 = 0;
        } else {
            GibInt flt_2791 = idx_85_755_919 + 1;

            idx1_88_758_927 = flt_2791;
        }

        GibInt *tmp_13;

        tmp_13 = (GibInt *) gib_vector_nth(nums_84_754_918, idx1_88_758_927);

        GibInt j_89_759_930 = *tmp_13;
        GibInt fltPrm_871_931 = j_89_759_930 % 2;
        GibBool fltIf_870_932 = fltPrm_871_931 == 0;

        if (fltIf_870_932) {
            gib_shadowstack_push(rstack, tr_86_756_920, end_r_1392, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibChunk region_2792 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1457 = region_2792.start;
            GibCursor end_r_1457 = region_2792.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_86_756_920 = frame->ptr;
            end_r_1392 = frame->endptr;
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_9 =
                                                      treeInsert(end_r_1392, end_r_1457, r_1457, tr_86_756_920, j_89_759_930);
            GibCursor pvrtmp_2793 = tmp_struct_9.field0;
            GibCursor pvrtmp_2794 = tmp_struct_9.field1;
            GibCursor pvrtmp_2795 = tmp_struct_9.field2;
            GibCursor pvrtmp_2796 = tmp_struct_9.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;

            GibInt fltAppE_873_934 = n_87_757_921 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_10 =
                                                      loop(pvrtmp_2794, end_r_1393, loc_1391, nums_84_754_918, idx1_88_758_927, pvrtmp_2795, fltAppE_873_934);
            GibCursor pvrtmp_2801 = tmp_struct_10.field0;
            GibCursor pvrtmp_2802 = tmp_struct_10.field1;
            GibCursor pvrtmp_2803 = tmp_struct_10.field2;
            GibCursor pvrtmp_2804 = tmp_struct_10.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2793,
                                                               pvrtmp_2802,
                                                               pvrtmp_2803,
                                                               pvrtmp_2804};
        } else {
            GibInt fltAppE_875_935 = j_89_759_930 - 1;

            gib_shadowstack_push(rstack, tr_86_756_920, end_r_1392, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibChunk region_2811 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1466 = region_2811.start;
            GibCursor end_r_1466 = region_2811.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_86_756_920 = frame->ptr;
            end_r_1392 = frame->endptr;
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                                                      treeDelete(end_r_1392, end_r_1466, r_1466, tr_86_756_920, fltAppE_875_935);
            GibCursor pvrtmp_2812 = tmp_struct_11.field0;
            GibCursor pvrtmp_2813 = tmp_struct_11.field1;
            GibCursor pvrtmp_2814 = tmp_struct_11.field2;
            GibCursor pvrtmp_2815 = tmp_struct_11.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;

            GibInt fltAppE_876_937 = n_87_757_921 - 1;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                      loop(pvrtmp_2813, end_r_1393, loc_1391, nums_84_754_918, idx1_88_758_927, pvrtmp_2814, fltAppE_876_937);
            GibCursor pvrtmp_2820 = tmp_struct_12.field0;
            GibCursor pvrtmp_2821 = tmp_struct_12.field1;
            GibCursor pvrtmp_2822 = tmp_struct_12.field2;
            GibCursor pvrtmp_2823 = tmp_struct_12.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2812,
                                                               pvrtmp_2821,
                                                               pvrtmp_2822,
                                                               pvrtmp_2823};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd loop2(GibCursor end_r_1392,
                                              GibCursor end_r_1393,
                                              GibCursor loc_1391,
                                              GibVector *nums_84_754_918,
                                              GibInt idx_85_755_919,
                                              GibCursor tr_86_756_920,
                                              GibInt n_87_757_921)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    // if (loc_1391 + 26 > end_r_1393) {
    //     gib_grow_region(&loc_1391, &end_r_1393);
    // }
    while (n_87_757_921 > 0) {
        GibInt fltPrm_869_924 = gib_vector_length(nums_84_754_918);
        GibInt fltPrm_868_925 = fltPrm_869_924 - 1;
        GibBool fltIf_867_926 = idx_85_755_919 == fltPrm_868_925;
        GibInt idx1_88_758_927;

        if (fltIf_867_926) {
            idx1_88_758_927 = 0;
        } else {
            GibInt flt_2791 = idx_85_755_919 + 1;

            idx1_88_758_927 = flt_2791;
        }

        GibInt *tmp_13;

        tmp_13 = (GibInt *) gib_vector_nth(nums_84_754_918, idx1_88_758_927);

        GibInt j_89_759_930 = *tmp_13;
        GibInt fltPrm_871_931 = j_89_759_930 % 2;
        GibBool fltIf_870_932 = fltPrm_871_931 == 0;

        if (fltIf_870_932) {
            gib_shadowstack_push(rstack, tr_86_756_920, end_r_1392, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibChunk region_2792 =
                    gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1457 = region_2792.start;
            GibCursor end_r_1457 = region_2792.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_86_756_920 = frame->ptr;
            end_r_1392 = frame->endptr;
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_9 =
                    treeInsert(end_r_1392, end_r_1457, r_1457, tr_86_756_920, j_89_759_930);
            GibCursor pvrtmp_2793 = tmp_struct_9.field0;
            GibCursor pvrtmp_2794 = tmp_struct_9.field1;
            GibCursor pvrtmp_2795 = tmp_struct_9.field2;
            GibCursor pvrtmp_2796 = tmp_struct_9.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;

            GibInt fltAppE_873_934 = n_87_757_921 - 1;

            // update.
            end_r_1392 = pvrtmp_2794;
            idx_85_755_919 = idx1_88_758_927;
            tr_86_756_920 = pvrtmp_2795;
            n_87_757_921 = fltAppE_873_934;

            // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_10 =
            //                                           loop(pvrtmp_2794, end_r_1393, loc_1391, nums_84_754_918, idx1_88_758_927, pvrtmp_2795, fltAppE_873_934);
            // GibCursor pvrtmp_2801 = tmp_struct_10.field0;
            // GibCursor pvrtmp_2802 = tmp_struct_10.field1;
            // GibCursor pvrtmp_2803 = tmp_struct_10.field2;
            // GibCursor pvrtmp_2804 = tmp_struct_10.field3;


            // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2793,
            //                                                    pvrtmp_2802,
            //                                                    pvrtmp_2803,
            //                                                    pvrtmp_2804};
        } else {
            GibInt fltAppE_875_935 = j_89_759_930 - 1;

            gib_shadowstack_push(rstack, tr_86_756_920, end_r_1392, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibChunk region_2811 =
                    gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1466 = region_2811.start;
            GibCursor end_r_1466 = region_2811.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_86_756_920 = frame->ptr;
            end_r_1392 = frame->endptr;
            gib_shadowstack_push(wstack, loc_1391, end_r_1393, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_11 =
                    treeDelete(end_r_1392, end_r_1466, r_1466, tr_86_756_920, fltAppE_875_935);
            GibCursor pvrtmp_2812 = tmp_struct_11.field0;
            GibCursor pvrtmp_2813 = tmp_struct_11.field1;
            GibCursor pvrtmp_2814 = tmp_struct_11.field2;
            GibCursor pvrtmp_2815 = tmp_struct_11.field3;

            frame = gib_shadowstack_pop(wstack);
            loc_1391 = frame->ptr;
            end_r_1393 = frame->endptr;

            GibInt fltAppE_876_937 = n_87_757_921 - 1;
            end_r_1392 = pvrtmp_2813;
            idx_85_755_919 = idx1_88_758_927;
            tr_86_756_920 = pvrtmp_2814;
            n_87_757_921 = fltAppE_876_937;

            // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
            //                                           loop(pvrtmp_2813, end_r_1393, loc_1391, nums_84_754_918, idx1_88_758_927, pvrtmp_2814, fltAppE_876_937);
            // GibCursor pvrtmp_2820 = tmp_struct_12.field0;
            // GibCursor pvrtmp_2821 = tmp_struct_12.field1;
            // GibCursor pvrtmp_2822 = tmp_struct_12.field2;
            // GibCursor pvrtmp_2823 = tmp_struct_12.field3;

            // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2812,
            //                                                    pvrtmp_2821,
            //                                                    pvrtmp_2822,
            //                                                    pvrtmp_2823};
        }
    }


    if (loc_1391 + 18 > end_r_1393) {
        gib_grow_region(&loc_1391, &end_r_1393);
    }
    gib_indirection_barrier(loc_1391, end_r_1393, tr_86_756_920, end_r_1392,
                            SearchTree_T);

    GibCursor end_2025 = loc_1391 + 9;

    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1392,
                end_r_1393, loc_1391,
                end_2025};
}
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1396,
                                                    GibCursor end_r_1397,
                                                    GibCursor loc_1395,
                                                    GibCursor tr_90_760_938,
                                                    GibInt n_91_761_939)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1395 + 26 > end_r_1397) {
        gib_grow_region(&loc_1395, &end_r_1397);
    }

    GibPackedTag tmpval_2830 = *(GibPackedTag *) tr_90_760_938;
    GibCursor tmpcur_2831 = tr_90_760_938 + 1;


  switch_2921:
    ;
    switch (tmpval_2830) {

      case 0:
        {
            *(GibPackedTag *) loc_1395 = 0;

            GibCursor writetag_2040 = loc_1395 + 1;
            GibCursor after_tag_2041 = loc_1395 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1396,
                                                               end_r_1397,
                                                               loc_1395,
                                                               after_tag_2041};
            break;
        }

      case 1:
        {
            GibInt tmpval_2836 = *(GibInt *) tmpcur_2831;
            GibCursor tmpcur_2837 = tmpcur_2831 + sizeof(GibInt);
            GibBool fltIf_877_941 = tmpval_2836 == n_91_761_939;

            if (fltIf_877_941) {
                *(GibPackedTag *) loc_1395 = 0;

                GibCursor writetag_2049 = loc_1395 + 1;
                GibCursor after_tag_2050 = loc_1395 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1396,
                                                                   end_r_1397,
                                                                   loc_1395,
                                                                   after_tag_2050};
            } else {
                *(GibPackedTag *) loc_1395 = 1;

                GibCursor writetag_2056 = loc_1395 + 1;
                GibCursor after_tag_2057 = loc_1395 + 1;

                *(GibInt *) after_tag_2057 = tmpval_2836;

                GibCursor writecur_2061 = after_tag_2057 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1396,
                                                                   end_r_1397,
                                                                   loc_1395,
                                                                   writecur_2061};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) tmpcur_2831;
            GibCursor tmpcur_2846 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_2847 = tmpcur_2831 + 8;
            uint16_t tmptag_2848 = GIB_GET_TAG(tagged_tmpcur_33);
            GibCursor end_from_tagged_absran_1337 = tmpcur_2846 + tmptag_2848;
            GibInt tmpval_2849 = *(GibInt *) tmpaftercur_2847;
            GibCursor tmpcur_2850 = tmpaftercur_2847 + sizeof(GibInt);
            GibBool fltIf_878_945 = tmpval_2849 == n_91_761_939;

            if (fltIf_878_945) {
                gib_shadowstack_push(rstack, tmpcur_2846, end_r_1396, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(rstack, tmpcur_2850, end_r_1396, Stk,
                                     SearchTree_T);
                gib_shadowstack_push(wstack, loc_1395, end_r_1397, Stk,
                                     SearchTree_T);

                GibCursorGibIntProd tmp_struct_17 =
                                     minTree(end_from_tagged_absran_1337, tmpcur_2846);
                GibCursor pvrtmp_2851 = tmp_struct_17.field0;
                GibInt pvrtmp_2852 = tmp_struct_17.field1;

                frame = gib_shadowstack_pop(wstack);
                loc_1395 = frame->ptr;
                end_r_1397 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2850 = frame->ptr;
                end_r_1396 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                tmpcur_2846 = frame->ptr;
                end_r_1396 = frame->endptr;

                GibCursor loc_1489 = loc_1395 + 17;

                *(GibPackedTag *) loc_1395 = 3;

                GibCursor writetag_2075 = loc_1395 + 1;

                if (loc_1489 + 18 > end_r_1397) {
                    gib_grow_region(&loc_1489, &end_r_1397);
                }
                gib_indirection_barrier(loc_1489, end_r_1397, tmpcur_2850,
                                        end_r_1396, SearchTree_T);

                GibCursor end_2070 = loc_1489 + 9;

                gib_shadowstack_push(rstack, loc_1395, end_r_1397, Stk,
                                     SearchTree_T);

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_18 =
                                                          treeDelete(end_from_tagged_absran_1337, end_r_1397, end_2070, tmpcur_2846, pvrtmp_2852);
                GibCursor pvrtmp_2855 = tmp_struct_18.field0;
                GibCursor pvrtmp_2856 = tmp_struct_18.field1;
                GibCursor pvrtmp_2857 = tmp_struct_18.field2;
                GibCursor pvrtmp_2858 = tmp_struct_18.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_1395 = frame->ptr;
                end_r_1397 = frame->endptr;

                uint16_t offset_19 = end_r_1397 - end_2070;
                uintptr_t ran_1340 = GIB_STORE_TAG(end_2070, offset_19);
                GibCursor after_tag_2076 = loc_1395 + 1;

                *(uintptr_t *) after_tag_2076 = ran_1340;

                GibCursor writecur_2080 = after_tag_2076 + 8;

                *(GibInt *) writecur_2080 = pvrtmp_2852;

                GibCursor writecur_2081 = writecur_2080 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2855,
                                                                   pvrtmp_2856,
                                                                   loc_1395,
                                                                   pvrtmp_2858};
            } else {
                GibBool fltIf_881_949 = tmpval_2849 < n_91_761_939;

                if (fltIf_881_949) {
                    GibCursor loc_1505 = loc_1395 + 17;

                    *(GibPackedTag *) loc_1395 = 3;

                    GibCursor writetag_2093 = loc_1395 + 1;

                    if (loc_1505 + 18 > end_r_1397) {
                        gib_grow_region(&loc_1505, &end_r_1397);
                    }
                    gib_indirection_barrier(loc_1505, end_r_1397, tmpcur_2850,
                                            end_r_1396, SearchTree_T);

                    GibCursor end_2088 = loc_1505 + 9;

                    gib_shadowstack_push(rstack, loc_1395, end_r_1397, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_23 =
                                                              treeDelete(end_from_tagged_absran_1337, end_r_1397, end_2088, tmpcur_2846, n_91_761_939);
                    GibCursor pvrtmp_2869 = tmp_struct_23.field0;
                    GibCursor pvrtmp_2870 = tmp_struct_23.field1;
                    GibCursor pvrtmp_2871 = tmp_struct_23.field2;
                    GibCursor pvrtmp_2872 = tmp_struct_23.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_1395 = frame->ptr;
                    end_r_1397 = frame->endptr;

                    uint16_t offset_24 = end_r_1397 - end_2088;
                    uintptr_t ran_1341 = GIB_STORE_TAG(end_2088, offset_24);
                    GibCursor after_tag_2094 = loc_1395 + 1;

                    *(uintptr_t *) after_tag_2094 = ran_1341;

                    GibCursor writecur_2098 = after_tag_2094 + 8;

                    *(GibInt *) writecur_2098 = tmpval_2849;

                    GibCursor writecur_2099 = writecur_2098 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2869,
                                                                       pvrtmp_2870,
                                                                       loc_1395,
                                                                       pvrtmp_2872};
                } else {
                    GibCursor loc_1521 = loc_1395 + 17;

                    *(GibPackedTag *) loc_1395 = 3;

                    GibCursor writetag_2111 = loc_1395 + 1;

                    gib_shadowstack_push(rstack, loc_1395, end_r_1397, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2846, end_r_1396, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                              treeDelete(end_r_1396, end_r_1397, loc_1521, tmpcur_2850, n_91_761_939);
                    GibCursor pvrtmp_2881 = tmp_struct_28.field0;
                    GibCursor pvrtmp_2882 = tmp_struct_28.field1;
                    GibCursor pvrtmp_2883 = tmp_struct_28.field2;
                    GibCursor pvrtmp_2884 = tmp_struct_28.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2846 = frame->ptr;
                    end_r_1396 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_1395 = frame->ptr;
                    end_r_1397 = frame->endptr;
                    if (pvrtmp_2884 + 18 > pvrtmp_2882) {
                        gib_grow_region(&pvrtmp_2884, &pvrtmp_2882);
                    }
                    gib_indirection_barrier(pvrtmp_2884, pvrtmp_2882,
                                            tmpcur_2846,
                                            end_from_tagged_absran_1337,
                                            SearchTree_T);

                    GibCursor end_2109 = pvrtmp_2884 + 9;
                    uint16_t offset_29 = pvrtmp_2882 - pvrtmp_2884;
                    uintptr_t ran_1342 = GIB_STORE_TAG(pvrtmp_2884, offset_29);
                    GibCursor after_tag_2112 = loc_1395 + 1;

                    *(uintptr_t *) after_tag_2112 = ran_1342;

                    GibCursor writecur_2116 = after_tag_2112 + 8;

                    *(GibInt *) writecur_2116 = tmpval_2849;

                    GibCursor writecur_2117 = writecur_2116 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2881,
                                                                       pvrtmp_2882,
                                                                       loc_1395,
                                                                       end_2109};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_2831;
            GibCursor tmpcur_2895 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_2896 = tmpcur_2831 + 8;
            uint16_t tmptag_2897 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_indr_1843 = tmpcur_2895 + tmptag_2897;
            GibCursor jump_1845 = tmpcur_2831 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_34 =
                                                      treeDelete(end_from_tagged_indr_1843, end_r_1397, loc_1395, tmpcur_2895, n_91_761_939);
            GibCursor pvrtmp_2898 = tmp_struct_34.field0;
            GibCursor pvrtmp_2899 = tmp_struct_34.field1;
            GibCursor pvrtmp_2900 = tmp_struct_34.field2;
            GibCursor pvrtmp_2901 = tmp_struct_34.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1396,
                                                               pvrtmp_2899,
                                                               pvrtmp_2900,
                                                               pvrtmp_2901};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_37 = *(uintptr_t *) tmpcur_2831;
            GibCursor tmpcur_2908 = GIB_UNTAG(tagged_tmpcur_37);
            GibCursor tmpaftercur_2909 = tmpcur_2831 + 8;
            uint16_t tmptag_2910 = GIB_GET_TAG(tagged_tmpcur_37);
            GibCursor end_from_tagged_indr_1843 = tmpcur_2908 + tmptag_2910;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_36 =
                                                      treeDelete(end_from_tagged_indr_1843, end_r_1397, loc_1395, tmpcur_2908, n_91_761_939);
            GibCursor pvrtmp_2911 = tmp_struct_36.field0;
            GibCursor pvrtmp_2912 = tmp_struct_36.field1;
            GibCursor pvrtmp_2913 = tmp_struct_36.field2;
            GibCursor pvrtmp_2914 = tmp_struct_36.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2911,
                                                               pvrtmp_2912,
                                                               pvrtmp_2913,
                                                               pvrtmp_2914};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2830");
            exit(1);
        }
    }
}
GibCursorGibIntProd minTree(GibCursor end_r_1399, GibCursor tr_97_767_954)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2922 = *(GibPackedTag *) tr_97_767_954;
    GibCursor tmpcur_2923 = tr_97_767_954 + 1;


  switch_2943:
    ;
    switch (tmpval_2922) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1399, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2924 = *(GibInt *) tmpcur_2923;
            GibCursor tmpcur_2925 = tmpcur_2923 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1399, tmpval_2924};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_2923;
            GibCursor tmpcur_2926 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_2927 = tmpcur_2923 + 8;
            uint16_t tmptag_2928 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_absran_1346 = tmpcur_2926 + tmptag_2928;
            GibInt tmpval_2929 = *(GibInt *) tmpaftercur_2927;
            GibCursor tmpcur_2930 = tmpaftercur_2927 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_41 =
                                 caseFn_744(end_r_1399, tmpcur_2930, tmpval_2929);
            GibCursor pvrtmp_2931 = tmp_struct_41.field0;
            GibInt pvrtmp_2932 = tmp_struct_41.field1;

            return (GibCursorGibIntProd) {pvrtmp_2931, pvrtmp_2932};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_44 = *(uintptr_t *) tmpcur_2923;
            GibCursor tmpcur_2933 = GIB_UNTAG(tagged_tmpcur_44);
            GibCursor tmpaftercur_2934 = tmpcur_2923 + 8;
            uint16_t tmptag_2935 = GIB_GET_TAG(tagged_tmpcur_44);
            GibCursor end_from_tagged_indr_1848 = tmpcur_2933 + tmptag_2935;
            GibCursor jump_1850 = tmpcur_2923 + 8;
            GibCursorGibIntProd tmp_struct_43 =
                                 minTree(end_from_tagged_indr_1848, tmpcur_2933);
            GibCursor pvrtmp_2936 = tmp_struct_43.field0;
            GibInt pvrtmp_2937 = tmp_struct_43.field1;

            return (GibCursorGibIntProd) {end_r_1399, pvrtmp_2937};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_46 = *(uintptr_t *) tmpcur_2923;
            GibCursor tmpcur_2938 = GIB_UNTAG(tagged_tmpcur_46);
            GibCursor tmpaftercur_2939 = tmpcur_2923 + 8;
            uint16_t tmptag_2940 = GIB_GET_TAG(tagged_tmpcur_46);
            GibCursor end_from_tagged_indr_1848 = tmpcur_2938 + tmptag_2940;
            GibCursorGibIntProd tmp_struct_45 =
                                 minTree(end_from_tagged_indr_1848, tmpcur_2938);
            GibCursor pvrtmp_2941 = tmp_struct_45.field0;
            GibInt pvrtmp_2942 = tmp_struct_45.field1;

            return (GibCursorGibIntProd) {pvrtmp_2941, pvrtmp_2942};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2922");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1402,
                                                    GibCursor end_r_1403,
                                                    GibCursor loc_1401,
                                                    GibCursor tr_106_772_959,
                                                    GibInt n_107_773_960)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1401 + 26 > end_r_1403) {
        gib_grow_region(&loc_1401, &end_r_1403);
    }

    GibPackedTag tmpval_2944 = *(GibPackedTag *) tr_106_772_959;
    GibCursor tmpcur_2945 = tr_106_772_959 + 1;


  switch_3039:
    ;
    switch (tmpval_2944) {

      case 0:
        {
            *(GibPackedTag *) loc_1401 = 1;

            GibCursor writetag_2150 = loc_1401 + 1;
            GibCursor after_tag_2151 = loc_1401 + 1;

            *(GibInt *) after_tag_2151 = n_107_773_960;

            GibCursor writecur_2155 = after_tag_2151 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1402,
                                                               end_r_1403,
                                                               loc_1401,
                                                               writecur_2155};
            break;
        }

      case 1:
        {
            GibInt tmpval_2950 = *(GibInt *) tmpcur_2945;
            GibCursor tmpcur_2951 = tmpcur_2945 + sizeof(GibInt);
            GibBool fltIf_886_962 = n_107_773_960 == tmpval_2950;

            if (fltIf_886_962) {
                *(GibPackedTag *) loc_1401 = 1;

                GibCursor writetag_2160 = loc_1401 + 1;
                GibCursor after_tag_2161 = loc_1401 + 1;

                *(GibInt *) after_tag_2161 = tmpval_2950;

                GibCursor writecur_2165 = after_tag_2161 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1402,
                                                                   end_r_1403,
                                                                   loc_1401,
                                                                   writecur_2165};
            } else {
                GibBool fltIf_887_963 = n_107_773_960 < tmpval_2950;

                if (fltIf_887_963) {
                    GibCursor loc_1558 = loc_1401 + 17;

                    *(GibPackedTag *) loc_1401 = 3;

                    GibCursor writetag_2183 = loc_1401 + 1;

                    *(GibPackedTag *) loc_1558 = 1;

                    GibCursor writetag_2168 = loc_1558 + 1;
                    GibCursor after_tag_2169 = loc_1558 + 1;

                    *(GibInt *) after_tag_2169 = n_107_773_960;

                    GibCursor writecur_2173 = after_tag_2169 + sizeof(GibInt);

                    *(GibPackedTag *) writecur_2173 = 0;

                    GibCursor writetag_2176 = writecur_2173 + 1;
                    GibCursor after_tag_2177 = writecur_2173 + 1;
                    uint16_t offset_47 = end_r_1403 - writecur_2173;
                    uintptr_t ran_1349 = GIB_STORE_TAG(writecur_2173,
                                                       offset_47);
                    GibCursor after_tag_2184 = loc_1401 + 1;

                    *(uintptr_t *) after_tag_2184 = ran_1349;

                    GibCursor writecur_2188 = after_tag_2184 + 8;

                    *(GibInt *) writecur_2188 = tmpval_2950;

                    GibCursor writecur_2189 = writecur_2188 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1402,
                                                                       end_r_1403,
                                                                       loc_1401,
                                                                       after_tag_2177};
                } else {
                    GibCursor loc_1574 = loc_1401 + 17;

                    *(GibPackedTag *) loc_1401 = 3;

                    GibCursor writetag_2210 = loc_1401 + 1;

                    *(GibPackedTag *) loc_1574 = 0;

                    GibCursor writetag_2195 = loc_1574 + 1;
                    GibCursor after_tag_2196 = loc_1574 + 1;

                    *(GibPackedTag *) after_tag_2196 = 1;

                    GibCursor writetag_2202 = after_tag_2196 + 1;
                    GibCursor after_tag_2203 = after_tag_2196 + 1;

                    *(GibInt *) after_tag_2203 = n_107_773_960;

                    GibCursor writecur_2207 = after_tag_2203 + sizeof(GibInt);
                    uint16_t offset_48 = end_r_1403 - after_tag_2196;
                    uintptr_t ran_1350 = GIB_STORE_TAG(after_tag_2196,
                                                       offset_48);
                    GibCursor after_tag_2211 = loc_1401 + 1;

                    *(uintptr_t *) after_tag_2211 = ran_1350;

                    GibCursor writecur_2215 = after_tag_2211 + 8;

                    *(GibInt *) writecur_2215 = tmpval_2950;

                    GibCursor writecur_2216 = writecur_2215 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1402,
                                                                       end_r_1403,
                                                                       loc_1401,
                                                                       writecur_2207};
                }
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_66 = *(uintptr_t *) tmpcur_2945;
            GibCursor tmpcur_2972 = GIB_UNTAG(tagged_tmpcur_66);
            GibCursor tmpaftercur_2973 = tmpcur_2945 + 8;
            uint16_t tmptag_2974 = GIB_GET_TAG(tagged_tmpcur_66);
            GibCursor end_from_tagged_absran_1354 = tmpcur_2972 + tmptag_2974;
            GibInt tmpval_2975 = *(GibInt *) tmpaftercur_2973;
            GibCursor tmpcur_2976 = tmpaftercur_2973 + sizeof(GibInt);
            GibBool fltIf_892_971 = tmpval_2975 == n_107_773_960;

            if (fltIf_892_971) {
                GibCursor loc_1594 = loc_1401 + 17;

                *(GibPackedTag *) loc_1401 = 3;

                GibCursor writetag_2231 = loc_1401 + 1;

                if (loc_1594 + 18 > end_r_1403) {
                    gib_grow_region(&loc_1594, &end_r_1403);
                }
                gib_indirection_barrier(loc_1594, end_r_1403, tmpcur_2976,
                                        end_r_1402, SearchTree_T);

                GibCursor end_2226 = loc_1594 + 9;

                if (end_2226 + 18 > end_r_1403) {
                    gib_grow_region(&end_2226, &end_r_1403);
                }
                gib_indirection_barrier(end_2226, end_r_1403, tmpcur_2972,
                                        end_from_tagged_absran_1354,
                                        SearchTree_T);

                GibCursor end_2229 = end_2226 + 9;
                uint16_t offset_49 = end_r_1403 - end_2226;
                uintptr_t ran_1357 = GIB_STORE_TAG(end_2226, offset_49);
                GibCursor after_tag_2232 = loc_1401 + 1;

                *(uintptr_t *) after_tag_2232 = ran_1357;

                GibCursor writecur_2236 = after_tag_2232 + 8;

                *(GibInt *) writecur_2236 = tmpval_2975;

                GibCursor writecur_2237 = writecur_2236 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1402,
                                                                   end_r_1403,
                                                                   loc_1401,
                                                                   end_2229};
            } else {
                GibBool fltIf_895_974 = n_107_773_960 < tmpval_2975;

                if (fltIf_895_974) {
                    GibCursor loc_1610 = loc_1401 + 17;

                    *(GibPackedTag *) loc_1401 = 3;

                    GibCursor writetag_2249 = loc_1401 + 1;

                    if (loc_1610 + 18 > end_r_1403) {
                        gib_grow_region(&loc_1610, &end_r_1403);
                    }
                    gib_indirection_barrier(loc_1610, end_r_1403, tmpcur_2976,
                                            end_r_1402, SearchTree_T);

                    GibCursor end_2244 = loc_1610 + 9;

                    gib_shadowstack_push(rstack, loc_1401, end_r_1403, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_56 =
                                                              treeInsert(end_from_tagged_absran_1354, end_r_1403, end_2244, tmpcur_2972, n_107_773_960);
                    GibCursor pvrtmp_2987 = tmp_struct_56.field0;
                    GibCursor pvrtmp_2988 = tmp_struct_56.field1;
                    GibCursor pvrtmp_2989 = tmp_struct_56.field2;
                    GibCursor pvrtmp_2990 = tmp_struct_56.field3;

                    frame = gib_shadowstack_pop(rstack);
                    loc_1401 = frame->ptr;
                    end_r_1403 = frame->endptr;

                    uint16_t offset_57 = end_r_1403 - end_2244;
                    uintptr_t ran_1358 = GIB_STORE_TAG(end_2244, offset_57);
                    GibCursor after_tag_2250 = loc_1401 + 1;

                    *(uintptr_t *) after_tag_2250 = ran_1358;

                    GibCursor writecur_2254 = after_tag_2250 + 8;

                    *(GibInt *) writecur_2254 = tmpval_2975;

                    GibCursor writecur_2255 = writecur_2254 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2987,
                                                                       pvrtmp_2988,
                                                                       loc_1401,
                                                                       pvrtmp_2990};
                } else {
                    GibCursor loc_1626 = loc_1401 + 17;

                    *(GibPackedTag *) loc_1401 = 3;

                    GibCursor writetag_2267 = loc_1401 + 1;

                    gib_shadowstack_push(rstack, loc_1401, end_r_1403, Stk,
                                         SearchTree_T);
                    gib_shadowstack_push(rstack, tmpcur_2972, end_r_1402, Stk,
                                         SearchTree_T);

                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_61 =
                                                              treeInsert(end_r_1402, end_r_1403, loc_1626, tmpcur_2976, n_107_773_960);
                    GibCursor pvrtmp_2999 = tmp_struct_61.field0;
                    GibCursor pvrtmp_3000 = tmp_struct_61.field1;
                    GibCursor pvrtmp_3001 = tmp_struct_61.field2;
                    GibCursor pvrtmp_3002 = tmp_struct_61.field3;

                    frame = gib_shadowstack_pop(rstack);
                    tmpcur_2972 = frame->ptr;
                    end_r_1402 = frame->endptr;
                    frame = gib_shadowstack_pop(rstack);
                    loc_1401 = frame->ptr;
                    end_r_1403 = frame->endptr;
                    if (pvrtmp_3002 + 18 > pvrtmp_3000) {
                        gib_grow_region(&pvrtmp_3002, &pvrtmp_3000);
                    }
                    gib_indirection_barrier(pvrtmp_3002, pvrtmp_3000,
                                            tmpcur_2972,
                                            end_from_tagged_absran_1354,
                                            SearchTree_T);

                    GibCursor end_2265 = pvrtmp_3002 + 9;
                    uint16_t offset_62 = pvrtmp_3000 - pvrtmp_3002;
                    uintptr_t ran_1359 = GIB_STORE_TAG(pvrtmp_3002, offset_62);
                    GibCursor after_tag_2268 = loc_1401 + 1;

                    *(uintptr_t *) after_tag_2268 = ran_1359;

                    GibCursor writecur_2272 = after_tag_2268 + 8;

                    *(GibInt *) writecur_2272 = tmpval_2975;

                    GibCursor writecur_2273 = writecur_2272 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2999,
                                                                       pvrtmp_3000,
                                                                       loc_1401,
                                                                       end_2265};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_68 = *(uintptr_t *) tmpcur_2945;
            GibCursor tmpcur_3013 = GIB_UNTAG(tagged_tmpcur_68);
            GibCursor tmpaftercur_3014 = tmpcur_2945 + 8;
            uint16_t tmptag_3015 = GIB_GET_TAG(tagged_tmpcur_68);
            GibCursor end_from_tagged_indr_1853 = tmpcur_3013 + tmptag_3015;
            GibCursor jump_1855 = tmpcur_2945 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                      treeInsert(end_from_tagged_indr_1853, end_r_1403, loc_1401, tmpcur_3013, n_107_773_960);
            GibCursor pvrtmp_3016 = tmp_struct_67.field0;
            GibCursor pvrtmp_3017 = tmp_struct_67.field1;
            GibCursor pvrtmp_3018 = tmp_struct_67.field2;
            GibCursor pvrtmp_3019 = tmp_struct_67.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1402,
                                                               pvrtmp_3017,
                                                               pvrtmp_3018,
                                                               pvrtmp_3019};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_70 = *(uintptr_t *) tmpcur_2945;
            GibCursor tmpcur_3026 = GIB_UNTAG(tagged_tmpcur_70);
            GibCursor tmpaftercur_3027 = tmpcur_2945 + 8;
            uint16_t tmptag_3028 = GIB_GET_TAG(tagged_tmpcur_70);
            GibCursor end_from_tagged_indr_1853 = tmpcur_3026 + tmptag_3028;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_69 =
                                                      treeInsert(end_from_tagged_indr_1853, end_r_1403, loc_1401, tmpcur_3026, n_107_773_960);
            GibCursor pvrtmp_3029 = tmp_struct_69.field0;
            GibCursor pvrtmp_3030 = tmp_struct_69.field1;
            GibCursor pvrtmp_3031 = tmp_struct_69.field2;
            GibCursor pvrtmp_3032 = tmp_struct_69.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3029,
                                                               pvrtmp_3030,
                                                               pvrtmp_3031,
                                                               pvrtmp_3032};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2944");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1405,
                                        GibCursor tr_117_783_979)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3040 = *(GibPackedTag *) tr_117_783_979;
    GibCursor tmpcur_3041 = tr_117_783_979 + 1;


  switch_3067:
    ;
    switch (tmpval_3040) {

      case 0:
        {
            GibCursor jump_1791 = tr_117_783_979 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_1405, jump_1791, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_3042 = *(GibInt *) tmpcur_3041;
            GibCursor tmpcur_3043 = tmpcur_3041 + sizeof(GibInt);
            GibCursor jump_1792 = tmpcur_3041 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_1405, jump_1792, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_3041;
            GibCursor tmpcur_3044 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_3045 = tmpcur_3041 + 8;
            uint16_t tmptag_3046 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_absran_1363 = tmpcur_3044 + tmptag_3046;
            GibInt tmpval_3047 = *(GibInt *) tmpaftercur_3045;
            GibCursor tmpcur_3048 = tmpaftercur_3045 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_3044, end_r_1405, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibIntProd tmp_struct_74 =
                                          countnodes(end_r_1405, tmpcur_3048);
            GibCursor pvrtmp_3049 = tmp_struct_74.field0;
            GibCursor pvrtmp_3050 = tmp_struct_74.field1;
            GibInt pvrtmp_3051 = tmp_struct_74.field2;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3044 = frame->ptr;
            end_r_1405 = frame->endptr;

            GibInt fltPrm_900_985 = 1 + pvrtmp_3051;
            GibCursorGibCursorGibIntProd tmp_struct_75 =
                                          countnodes(end_from_tagged_absran_1363, tmpcur_3044);
            GibCursor pvrtmp_3052 = tmp_struct_75.field0;
            GibCursor pvrtmp_3053 = tmp_struct_75.field1;
            GibInt pvrtmp_3054 = tmp_struct_75.field2;
            GibInt tailprim_1797 = fltPrm_900_985 + pvrtmp_3054;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3052, pvrtmp_3053,
                                                   tailprim_1797};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_78 = *(uintptr_t *) tmpcur_3041;
            GibCursor tmpcur_3055 = GIB_UNTAG(tagged_tmpcur_78);
            GibCursor tmpaftercur_3056 = tmpcur_3041 + 8;
            uint16_t tmptag_3057 = GIB_GET_TAG(tagged_tmpcur_78);
            GibCursor end_from_tagged_indr_1858 = tmpcur_3055 + tmptag_3057;
            GibCursor jump_1860 = tmpcur_3041 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_77 =
                                          countnodes(end_from_tagged_indr_1858, tmpcur_3055);
            GibCursor pvrtmp_3058 = tmp_struct_77.field0;
            GibCursor pvrtmp_3059 = tmp_struct_77.field1;
            GibInt pvrtmp_3060 = tmp_struct_77.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_1405, jump_1860,
                                                   pvrtmp_3060};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_80 = *(uintptr_t *) tmpcur_3041;
            GibCursor tmpcur_3061 = GIB_UNTAG(tagged_tmpcur_80);
            GibCursor tmpaftercur_3062 = tmpcur_3041 + 8;
            uint16_t tmptag_3063 = GIB_GET_TAG(tagged_tmpcur_80);
            GibCursor end_from_tagged_indr_1858 = tmpcur_3061 + tmptag_3063;
            GibCursorGibCursorGibIntProd tmp_struct_79 =
                                          countnodes(end_from_tagged_indr_1858, tmpcur_3061);
            GibCursor pvrtmp_3064 = tmp_struct_79.field0;
            GibCursor pvrtmp_3065 = tmp_struct_79.field1;
            GibInt pvrtmp_3066 = tmp_struct_79.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3064, pvrtmp_3065,
                                                   pvrtmp_3066};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3040");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_1408,
                                                                   GibCursor end_r_1409,
                                                                   GibCursor loc_1407,
                                                                   GibCursor arg_702_809_987)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1407 + 26 > end_r_1409) {
        gib_grow_region(&loc_1407, &end_r_1409);
    }

    GibPackedTag tmpval_3068 = *(GibPackedTag *) arg_702_809_987;
    GibCursor tmpcur_3069 = arg_702_809_987 + 1;


  switch_3135:
    ;
    switch (tmpval_3068) {

      case 0:
        {
            GibCursor jump_1798 = arg_702_809_987 + 1;

            *(GibPackedTag *) loc_1407 = 0;

            GibCursor writetag_2308 = loc_1407 + 1;
            GibCursor after_tag_2309 = loc_1407 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                                        end_r_1409,
                                                                        jump_1798,
                                                                        loc_1407,
                                                                        after_tag_2309};
            break;
        }

      case 1:
        {
            GibInt tmpval_3074 = *(GibInt *) tmpcur_3069;
            GibCursor tmpcur_3075 = tmpcur_3069 + sizeof(GibInt);
            GibCursor jump_1800 = tmpcur_3069 + 8;

            *(GibPackedTag *) loc_1407 = 1;

            GibCursor writetag_2317 = loc_1407 + 1;
            GibCursor after_tag_2318 = loc_1407 + 1;

            *(GibInt *) after_tag_2318 = tmpval_3074;

            GibCursor writecur_2322 = after_tag_2318 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                                        end_r_1409,
                                                                        jump_1800,
                                                                        loc_1407,
                                                                        writecur_2322};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_3069;
            GibCursor tmpcur_3080 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_3081 = tmpcur_3069 + 8;
            uint16_t tmptag_3082 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_absran_1367 = tmpcur_3080 + tmptag_3082;
            GibInt tmpval_3083 = *(GibInt *) tmpaftercur_3081;
            GibCursor tmpcur_3084 = tmpaftercur_3081 + sizeof(GibInt);
            GibCursor loc_1669 = loc_1407 + 17;

            *(GibPackedTag *) loc_1407 = 3;

            GibCursor writetag_2334 = loc_1407 + 1;

            gib_shadowstack_push(rstack, loc_1407, end_r_1409, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_3080, end_r_1408, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_r_1408, end_r_1409, loc_1669, tmpcur_3084);
            GibCursor pvrtmp_3085 = tmp_struct_81.field0;
            GibCursor pvrtmp_3086 = tmp_struct_81.field1;
            GibCursor pvrtmp_3087 = tmp_struct_81.field2;
            GibCursor pvrtmp_3088 = tmp_struct_81.field3;
            GibCursor pvrtmp_3089 = tmp_struct_81.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3080 = frame->ptr;
            end_r_1408 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_1407 = frame->ptr;
            end_r_1409 = frame->endptr;
            gib_shadowstack_push(rstack, loc_1407, pvrtmp_3086, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_82 =
                                                               _copy_SearchTree(end_from_tagged_absran_1367, pvrtmp_3086, pvrtmp_3089, tmpcur_3080);
            GibCursor pvrtmp_3094 = tmp_struct_82.field0;
            GibCursor pvrtmp_3095 = tmp_struct_82.field1;
            GibCursor pvrtmp_3096 = tmp_struct_82.field2;
            GibCursor pvrtmp_3097 = tmp_struct_82.field3;
            GibCursor pvrtmp_3098 = tmp_struct_82.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_1407 = frame->ptr;
            pvrtmp_3086 = frame->endptr;

            uint16_t offset_83 = pvrtmp_3086 - pvrtmp_3089;
            uintptr_t ran_1370 = GIB_STORE_TAG(pvrtmp_3089, offset_83);
            GibCursor after_tag_2335 = loc_1407 + 1;

            *(uintptr_t *) after_tag_2335 = ran_1370;

            GibCursor writecur_2339 = after_tag_2335 + 8;

            *(GibInt *) writecur_2339 = tmpval_3083;

            GibCursor writecur_2340 = writecur_2339 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3094,
                                                                        pvrtmp_3095,
                                                                        pvrtmp_3096,
                                                                        loc_1407,
                                                                        pvrtmp_3098};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_3069;
            GibCursor tmpcur_3107 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_3108 = tmpcur_3069 + 8;
            uint16_t tmptag_3109 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1864 = tmpcur_3107 + tmptag_3109;
            GibCursor jump_1866 = tmpcur_3069 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_85 =
                                                               _copy_SearchTree(end_from_tagged_indr_1864, end_r_1409, loc_1407, tmpcur_3107);
            GibCursor pvrtmp_3110 = tmp_struct_85.field0;
            GibCursor pvrtmp_3111 = tmp_struct_85.field1;
            GibCursor pvrtmp_3112 = tmp_struct_85.field2;
            GibCursor pvrtmp_3113 = tmp_struct_85.field3;
            GibCursor pvrtmp_3114 = tmp_struct_85.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1408,
                                                                        pvrtmp_3111,
                                                                        jump_1866,
                                                                        pvrtmp_3113,
                                                                        pvrtmp_3114};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3069;
            GibCursor tmpcur_3121 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3122 = tmpcur_3069 + 8;
            uint16_t tmptag_3123 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1864 = tmpcur_3121 + tmptag_3123;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_SearchTree(end_from_tagged_indr_1864, end_r_1409, loc_1407, tmpcur_3121);
            GibCursor pvrtmp_3124 = tmp_struct_87.field0;
            GibCursor pvrtmp_3125 = tmp_struct_87.field1;
            GibCursor pvrtmp_3126 = tmp_struct_87.field2;
            GibCursor pvrtmp_3127 = tmp_struct_87.field3;
            GibCursor pvrtmp_3128 = tmp_struct_87.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3124,
                                                                        pvrtmp_3125,
                                                                        pvrtmp_3126,
                                                                        pvrtmp_3127,
                                                                        pvrtmp_3128};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3068");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_1412,
                                                                                GibCursor end_r_1413,
                                                                                GibCursor loc_1411,
                                                                                GibCursor arg_711_818_996)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3136 = *(GibPackedTag *) arg_711_818_996;
    GibCursor tmpcur_3137 = arg_711_818_996 + 1;


  switch_3203:
    ;
    switch (tmpval_3136) {

      case 0:
        {
            GibCursor jump_1807 = arg_711_818_996 + 1;

            *(GibPackedTag *) loc_1411 = 0;

            GibCursor writetag_2357 = loc_1411 + 1;
            GibCursor after_tag_2358 = loc_1411 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1412,
                                                                        end_r_1413,
                                                                        jump_1807,
                                                                        loc_1411,
                                                                        after_tag_2358};
            break;
        }

      case 1:
        {
            GibInt tmpval_3142 = *(GibInt *) tmpcur_3137;
            GibCursor tmpcur_3143 = tmpcur_3137 + sizeof(GibInt);
            GibCursor jump_1809 = tmpcur_3137 + 8;

            *(GibPackedTag *) loc_1411 = 1;

            GibCursor writetag_2366 = loc_1411 + 1;
            GibCursor after_tag_2367 = loc_1411 + 1;

            *(GibInt *) after_tag_2367 = tmpval_3142;

            GibCursor writecur_2371 = after_tag_2367 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1412,
                                                                        end_r_1413,
                                                                        jump_1809,
                                                                        loc_1411,
                                                                        writecur_2371};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_94 = *(uintptr_t *) tmpcur_3137;
            GibCursor tmpcur_3148 = GIB_UNTAG(tagged_tmpcur_94);
            GibCursor tmpaftercur_3149 = tmpcur_3137 + 8;
            uint16_t tmptag_3150 = GIB_GET_TAG(tagged_tmpcur_94);
            GibCursor end_from_tagged_absran_1372 = tmpcur_3148 + tmptag_3150;
            GibInt tmpval_3151 = *(GibInt *) tmpaftercur_3149;
            GibCursor tmpcur_3152 = tmpaftercur_3149 + sizeof(GibInt);
            GibCursor loc_1696 = loc_1411 + 9;

            *(GibPackedTag *) loc_1411 = 2;

            GibCursor writetag_2383 = loc_1411 + 1;
            GibCursor after_tag_2384 = loc_1411 + 1;

            *(GibInt *) after_tag_2384 = tmpval_3151;

            GibCursor writecur_2388 = after_tag_2384 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_1411, end_r_1413, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(rstack, tmpcur_3148, end_r_1412, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_r_1412, end_r_1413, loc_1696, tmpcur_3152);
            GibCursor pvrtmp_3153 = tmp_struct_92.field0;
            GibCursor pvrtmp_3154 = tmp_struct_92.field1;
            GibCursor pvrtmp_3155 = tmp_struct_92.field2;
            GibCursor pvrtmp_3156 = tmp_struct_92.field3;
            GibCursor pvrtmp_3157 = tmp_struct_92.field4;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3148 = frame->ptr;
            end_r_1412 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            loc_1411 = frame->ptr;
            end_r_1413 = frame->endptr;
            gib_shadowstack_push(rstack, loc_1411, pvrtmp_3154, Stk,
                                 SearchTree_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_93 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_1372, pvrtmp_3154, pvrtmp_3157, tmpcur_3148);
            GibCursor pvrtmp_3162 = tmp_struct_93.field0;
            GibCursor pvrtmp_3163 = tmp_struct_93.field1;
            GibCursor pvrtmp_3164 = tmp_struct_93.field2;
            GibCursor pvrtmp_3165 = tmp_struct_93.field3;
            GibCursor pvrtmp_3166 = tmp_struct_93.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_1411 = frame->ptr;
            pvrtmp_3154 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3162,
                                                                        pvrtmp_3163,
                                                                        pvrtmp_3164,
                                                                        loc_1411,
                                                                        pvrtmp_3166};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_96 = *(uintptr_t *) tmpcur_3137;
            GibCursor tmpcur_3175 = GIB_UNTAG(tagged_tmpcur_96);
            GibCursor tmpaftercur_3176 = tmpcur_3137 + 8;
            uint16_t tmptag_3177 = GIB_GET_TAG(tagged_tmpcur_96);
            GibCursor end_from_tagged_indr_1870 = tmpcur_3175 + tmptag_3177;
            GibCursor jump_1872 = tmpcur_3137 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_95 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1870, end_r_1413, loc_1411, tmpcur_3175);
            GibCursor pvrtmp_3178 = tmp_struct_95.field0;
            GibCursor pvrtmp_3179 = tmp_struct_95.field1;
            GibCursor pvrtmp_3180 = tmp_struct_95.field2;
            GibCursor pvrtmp_3181 = tmp_struct_95.field3;
            GibCursor pvrtmp_3182 = tmp_struct_95.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1412,
                                                                        pvrtmp_3179,
                                                                        jump_1872,
                                                                        pvrtmp_3181,
                                                                        pvrtmp_3182};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_98 = *(uintptr_t *) tmpcur_3137;
            GibCursor tmpcur_3189 = GIB_UNTAG(tagged_tmpcur_98);
            GibCursor tmpaftercur_3190 = tmpcur_3137 + 8;
            uint16_t tmptag_3191 = GIB_GET_TAG(tagged_tmpcur_98);
            GibCursor end_from_tagged_indr_1870 = tmpcur_3189 + tmptag_3191;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_97 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1870, end_r_1413, loc_1411, tmpcur_3189);
            GibCursor pvrtmp_3192 = tmp_struct_97.field0;
            GibCursor pvrtmp_3193 = tmp_struct_97.field1;
            GibCursor pvrtmp_3194 = tmp_struct_97.field2;
            GibCursor pvrtmp_3195 = tmp_struct_97.field3;
            GibCursor pvrtmp_3196 = tmp_struct_97.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3192,
                                                                        pvrtmp_3193,
                                                                        pvrtmp_3194,
                                                                        pvrtmp_3195,
                                                                        pvrtmp_3196};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3136");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1415,
                                            GibCursor arg_720_827_1005)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3204 = *(GibPackedTag *) arg_720_827_1005;
    GibCursor tmpcur_3205 = arg_720_827_1005 + 1;


  switch_3227:
    ;
    switch (tmpval_3204) {

      case 0:
        {
            GibCursor jump_1816 = arg_720_827_1005 + 1;

            return (GibCursorGibCursorProd) {end_r_1415, jump_1816};
            break;
        }

      case 1:
        {
            GibInt tmpval_3206 = *(GibInt *) tmpcur_3205;
            GibCursor tmpcur_3207 = tmpcur_3205 + sizeof(GibInt);
            GibCursor jump_1818 = tmpcur_3205 + 8;

            return (GibCursorGibCursorProd) {end_r_1415, jump_1818};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_3205;
            GibCursor tmpcur_3208 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_3209 = tmpcur_3205 + 8;
            uint16_t tmptag_3210 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_absran_1375 = tmpcur_3208 + tmptag_3210;
            GibInt tmpval_3211 = *(GibInt *) tmpaftercur_3209;
            GibCursor tmpcur_3212 = tmpaftercur_3209 + sizeof(GibInt);

            gib_shadowstack_push(rstack, tmpcur_3208, end_r_1415, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_r_1415, tmpcur_3212);
            GibCursor pvrtmp_3213 = tmp_struct_99.field0;
            GibCursor pvrtmp_3214 = tmp_struct_99.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3208 = frame->ptr;
            end_r_1415 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_100 =
                                    _traverse_SearchTree(end_from_tagged_absran_1375, tmpcur_3208);
            GibCursor pvrtmp_3215 = tmp_struct_100.field0;
            GibCursor pvrtmp_3216 = tmp_struct_100.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3215, pvrtmp_3216};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_3205;
            GibCursor tmpcur_3217 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_3218 = tmpcur_3205 + 8;
            uint16_t tmptag_3219 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_1876 = tmpcur_3217 + tmptag_3219;
            GibCursor jump_1878 = tmpcur_3205 + 8;
            GibCursorGibCursorProd tmp_struct_102 =
                                    _traverse_SearchTree(end_from_tagged_indr_1876, tmpcur_3217);
            GibCursor pvrtmp_3220 = tmp_struct_102.field0;
            GibCursor pvrtmp_3221 = tmp_struct_102.field1;

            return (GibCursorGibCursorProd) {end_r_1415, jump_1878};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) tmpcur_3205;
            GibCursor tmpcur_3222 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_3223 = tmpcur_3205 + 8;
            uint16_t tmptag_3224 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_indr_1876 = tmpcur_3222 + tmptag_3224;
            GibCursorGibCursorProd tmp_struct_104 =
                                    _traverse_SearchTree(end_from_tagged_indr_1876, tmpcur_3222);
            GibCursor pvrtmp_3225 = tmp_struct_104.field0;
            GibCursor pvrtmp_3226 = tmp_struct_104.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3225, pvrtmp_3226};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3204");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1417,
                                         GibCursor arg_729_834_1012)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3228 = *(GibPackedTag *) arg_729_834_1012;
    GibCursor tmpcur_3229 = arg_729_834_1012 + 1;


  switch_3251:
    ;
    switch (tmpval_3228) {

      case 0:
        {
            GibCursor jump_1825 = arg_729_834_1012 + 1;
            unsigned char wildcard_730_835_1013 = gib_print_symbol(2724);
            unsigned char wildcard_731_836_1014 = gib_print_symbol(2723);

            return (GibCursorGibCursorProd) {end_r_1417, jump_1825};
            break;
        }

      case 1:
        {
            GibInt tmpval_3230 = *(GibInt *) tmpcur_3229;
            GibCursor tmpcur_3231 = tmpcur_3229 + sizeof(GibInt);
            GibCursor jump_1827 = tmpcur_3229 + 8;
            unsigned char wildcard_734_838_1016 = gib_print_symbol(2726);
            unsigned char y_733_839_1017 = printf("%ld", tmpval_3230);
            unsigned char wildcard_735_840_1018 = gib_print_symbol(2723);

            return (GibCursorGibCursorProd) {end_r_1417, jump_1827};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_108 = *(uintptr_t *) tmpcur_3229;
            GibCursor tmpcur_3232 = GIB_UNTAG(tagged_tmpcur_108);
            GibCursor tmpaftercur_3233 = tmpcur_3229 + 8;
            uint16_t tmptag_3234 = GIB_GET_TAG(tagged_tmpcur_108);
            GibCursor end_from_tagged_absran_1378 = tmpcur_3232 + tmptag_3234;
            GibInt tmpval_3235 = *(GibInt *) tmpaftercur_3233;
            GibCursor tmpcur_3236 = tmpaftercur_3233 + sizeof(GibInt);
            unsigned char wildcard_742_844_1022 = gib_print_symbol(2725);
            unsigned char y_739_845_1023 = printf("%ld", tmpval_3235);

            gib_shadowstack_push(rstack, tmpcur_3232, end_r_1417, Stk,
                                 SearchTree_T);

            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_r_1417, tmpcur_3236);
            GibCursor pvrtmp_3237 = tmp_struct_106.field0;
            GibCursor pvrtmp_3238 = tmp_struct_106.field1;

            frame = gib_shadowstack_pop(rstack);
            tmpcur_3232 = frame->ptr;
            end_r_1417 = frame->endptr;

            GibCursorGibCursorProd tmp_struct_107 =
                                    _print_SearchTree(end_from_tagged_absran_1378, tmpcur_3232);
            GibCursor pvrtmp_3239 = tmp_struct_107.field0;
            GibCursor pvrtmp_3240 = tmp_struct_107.field1;
            unsigned char wildcard_743_848_1026 = gib_print_symbol(2723);

            return (GibCursorGibCursorProd) {pvrtmp_3239, pvrtmp_3240};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_3229;
            GibCursor tmpcur_3241 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_3242 = tmpcur_3229 + 8;
            uint16_t tmptag_3243 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_1882 = tmpcur_3241 + tmptag_3243;
            GibCursor jump_1884 = tmpcur_3229 + 8;
            unsigned char wildcard_1887 = gib_print_symbol(2728);
            GibCursorGibCursorProd tmp_struct_109 =
                                    _print_SearchTree(end_from_tagged_indr_1882, tmpcur_3241);
            GibCursor pvrtmp_3244 = tmp_struct_109.field0;
            GibCursor pvrtmp_3245 = tmp_struct_109.field1;

            return (GibCursorGibCursorProd) {end_r_1417, jump_1884};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_3229;
            GibCursor tmpcur_3246 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_3247 = tmpcur_3229 + 8;
            uint16_t tmptag_3248 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_1882 = tmpcur_3246 + tmptag_3248;
            unsigned char wildcard_1887 = gib_print_symbol(2727);
            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_SearchTree(end_from_tagged_indr_1882, tmpcur_3246);
            GibCursor pvrtmp_3249 = tmp_struct_111.field0;
            GibCursor pvrtmp_3250 = tmp_struct_111.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3249, pvrtmp_3250};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3228");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_744(GibCursor end_r_1419,
                               GibCursor l_100_745_849_1027,
                               GibInt n_99_746_850_1028)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3252 = *(GibPackedTag *) l_100_745_849_1027;
    GibCursor tmpcur_3253 = l_100_745_849_1027 + 1;


  switch_3273:
    ;
    switch (tmpval_3252) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1419, n_99_746_850_1028};
            break;
        }

      case 1:
        {
            GibInt tmpval_3254 = *(GibInt *) tmpcur_3253;
            GibCursor tmpcur_3255 = tmpcur_3253 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1419, tmpval_3254};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_3253;
            GibCursor tmpcur_3256 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_3257 = tmpcur_3253 + 8;
            uint16_t tmptag_3258 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_absran_1381 = tmpcur_3256 + tmptag_3258;
            GibInt tmpval_3259 = *(GibInt *) tmpaftercur_3257;
            GibCursor tmpcur_3260 = tmpaftercur_3257 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_113 =
                                 minTree(end_r_1419, tmpcur_3260);
            GibCursor pvrtmp_3261 = tmp_struct_113.field0;
            GibInt pvrtmp_3262 = tmp_struct_113.field1;

            return (GibCursorGibIntProd) {pvrtmp_3261, pvrtmp_3262};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_116 = *(uintptr_t *) tmpcur_3253;
            GibCursor tmpcur_3263 = GIB_UNTAG(tagged_tmpcur_116);
            GibCursor tmpaftercur_3264 = tmpcur_3253 + 8;
            uint16_t tmptag_3265 = GIB_GET_TAG(tagged_tmpcur_116);
            GibCursor end_from_tagged_indr_1888 = tmpcur_3263 + tmptag_3265;
            GibCursor jump_1890 = tmpcur_3253 + 8;
            GibCursorGibIntProd tmp_struct_115 =
                                 caseFn_744(end_from_tagged_indr_1888, tmpcur_3263, n_99_746_850_1028);
            GibCursor pvrtmp_3266 = tmp_struct_115.field0;
            GibInt pvrtmp_3267 = tmp_struct_115.field1;

            return (GibCursorGibIntProd) {end_r_1419, pvrtmp_3267};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_118 = *(uintptr_t *) tmpcur_3253;
            GibCursor tmpcur_3268 = GIB_UNTAG(tagged_tmpcur_118);
            GibCursor tmpaftercur_3269 = tmpcur_3253 + 8;
            uint16_t tmptag_3270 = GIB_GET_TAG(tagged_tmpcur_118);
            GibCursor end_from_tagged_indr_1888 = tmpcur_3268 + tmptag_3270;
            GibCursorGibIntProd tmp_struct_117 =
                                 caseFn_744(end_from_tagged_indr_1888, tmpcur_3268, n_99_746_850_1028);
            GibCursor pvrtmp_3271 = tmp_struct_117.field0;
            GibInt pvrtmp_3272 = tmp_struct_117.field1;

            return (GibCursorGibIntProd) {pvrtmp_3271, pvrtmp_3272};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3252");
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
    GibChunk region_2729 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1431 = region_2729.start;
    GibCursor end_r_1431 = region_2729.end;
    GibChunk region_2730 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1430 = region_2730.start;
    GibCursor end_r_1430 = region_2730.end;
    GibVector *pts_77_747_903 =
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
        gib_vector_inplace_update(pts_77_747_903, i_132, &arr_elem_127);
        i_132++;
    }

    GibInt n_78_748_904 = gib_get_size_param();
    GibCursorGibCursorGibCursorProd tmp_struct_119 =
                                     helper(end_r_1431, r_1431, 0, 3);
    GibCursor pvrtmp_2731 = tmp_struct_119.field0;
    GibCursor pvrtmp_2732 = tmp_struct_119.field1;
    GibCursor pvrtmp_2733 = tmp_struct_119.field2;

    gib_shadowstack_push(rstack, r_1431, pvrtmp_2731, Stk, SearchTree_T);
    frame = gib_shadowstack_pop(rstack);
    r_1431 = frame->ptr;
    pvrtmp_2731 = frame->endptr;

    GibCursor pvrtmp_2748;
    GibCursor pvrtmp_2749;
    GibCursor pvrtmp_2750;
    GibVector *times_124 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2748;
    struct timespec end_pvrtmp_2748;


    GibGcStateSnapshot *snapshot = gib_gc_init_state(2);

    for (long long iters_pvrtmp_2748 = 0; iters_pvrtmp_2748 <
         gib_get_iters_param(); iters_pvrtmp_2748++) {
        if (iters_pvrtmp_2748 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 2, region_2729.end, region_2730.end);
            gib_list_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2748);

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                  loop2(pvrtmp_2731, end_r_1430, r_1430, pts_77_747_903, 0, pvrtmp_2732, n_78_748_904);
        GibCursor pvrtmp_2738 = tmp_struct_120.field0;
        GibCursor pvrtmp_2739 = tmp_struct_120.field1;
        GibCursor pvrtmp_2740 = tmp_struct_120.field2;
        GibCursor pvrtmp_2741 = tmp_struct_120.field3;

        pvrtmp_2748 = pvrtmp_2739;
        pvrtmp_2749 = pvrtmp_2740;
        pvrtmp_2750 = pvrtmp_2741;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2748);
        if (iters_pvrtmp_2748 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
        }

        double itertime_121 = gib_difftimespecs(&begin_pvrtmp_2748,
                                                &end_pvrtmp_2748);

        printf("itertime: %lf\n", itertime_121);
        gib_vector_inplace_update(times_124, iters_pvrtmp_2748, &itertime_121);
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
                                  countnodes(end_r_1430, pvrtmp_2749);
    GibCursor pvrtmp_2758 = tmp_struct_126.field0;
    GibCursor pvrtmp_2759 = tmp_struct_126.field1;
    GibInt pvrtmp_2760 = tmp_struct_126.field2;

    printf("%ld", pvrtmp_2760);
    printf("\n");
    return 0;
}
