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
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1416,
                                              GibCursor end_r_1417,
                                              GibCursor loc_1415,
                                              GibVector *nums_89_772_933,
                                              GibInt idx_90_773_934,
                                              GibCursor tr_91_774_935,
                                              GibInt n_92_775_936);
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1420,
                                                    GibCursor end_r_1421,
                                                    GibCursor loc_1419,
                                                    GibCursor tr_95_778_953,
                                                    GibInt n_96_779_954);
GibCursorGibIntProd minTree(GibCursor end_r_1423, GibCursor tr_102_785_969);
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1426,
                                                    GibCursor end_r_1427,
                                                    GibCursor loc_1425,
                                                    GibCursor tr_111_790_974,
                                                    GibInt n_112_791_975);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1429,
                                        GibCursor tr_122_801_994);
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1431, GibCursor loc_1430,
                                       GibInt s_127_806_1002,
                                       GibInt e_128_807_1003);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_1434, GibCursor end_r_1435, GibCursor loc_1433,
                 GibCursor arg_723_835_1013);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_1438, GibCursor end_r_1439,
                              GibCursor loc_1437, GibCursor arg_732_844_1022);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1441,
                                            GibCursor arg_741_853_1031);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1443,
                                         GibCursor arg_750_860_1038);
GibCursorGibIntProd caseFn_765(GibCursor end_r_1445,
                               GibCursor l_105_766_875_1053,
                               GibInt n_104_767_876_1054);
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
    gib_add_symbol(2809, ")");
    gib_add_symbol(2810, "(Null ");
    gib_add_symbol(2811, "(Node ");
    gib_add_symbol(2812, "(Leaf ");
    gib_add_symbol(2813, " ->r ");
    gib_add_symbol(2814, " ->i ");
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1416,
                                              GibCursor end_r_1417,
                                              GibCursor loc_1415,
                                              GibVector *nums_89_772_933,
                                              GibInt idx_90_773_934,
                                              GibCursor tr_91_774_935,
                                              GibInt n_92_775_936)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1415 + 26 > end_r_1417) {
        gib_grow_region(&loc_1415, &end_r_1417);
    }

    GibBool fltIf_884_937 = n_92_775_936 == 0;

    if (fltIf_884_937) {
        // if (loc_1415 + 18 > end_r_1417) {
        //     gib_grow_region(&loc_1415, &end_r_1417);
        // }
        gib_indirection_barrier(loc_1415, end_r_1417, tr_91_774_935, end_r_1416,
                                SearchTree_T);

        GibCursor end_2080 = loc_1415 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1416,
                                                           end_r_1417, loc_1415,
                                                           end_2080};
    } else {
        GibInt fltPrm_887_939 = gib_vector_length(nums_89_772_933);
        GibInt fltPrm_886_940 = fltPrm_887_939 - 1;
        GibBool fltIf_885_941 = idx_90_773_934 == fltPrm_886_940;
        GibInt idx1_93_776_942;

        if (fltIf_885_941) {
            idx1_93_776_942 = 0;
        } else {
            GibInt flt_2851 = idx_90_773_934 + 1;

            idx1_93_776_942 = flt_2851;
        }

        GibInt *tmp_7;

        tmp_7 = (GibInt *) gib_vector_nth(nums_89_772_933, idx1_93_776_942);

        GibInt j_94_777_945 = *tmp_7;
        GibInt fltPrm_889_946 = j_94_777_945 % 2;
        GibBool fltIf_888_947 = fltPrm_889_946 == 0;

        if (fltIf_888_947) {
            gib_shadowstack_push(rstack, tr_91_774_935, end_r_1416, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1415, end_r_1417, Stk,
                                 SearchTree_T);

            GibChunk region_2852 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1466 = region_2852.start;
            GibCursor end_r_1466 = region_2852.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1415 = frame->ptr;
            end_r_1417 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_91_774_935 = frame->ptr;
            end_r_1416 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_3 =
                                                      treeInsert(end_r_1416, end_r_1466, r_1466, tr_91_774_935, j_94_777_945);
            GibCursor pvrtmp_2853 = tmp_struct_3.field0;
            GibCursor pvrtmp_2854 = tmp_struct_3.field1;
            GibCursor pvrtmp_2855 = tmp_struct_3.field2;
            GibCursor pvrtmp_2856 = tmp_struct_3.field3;
            GibInt fltAppE_891_949 = n_92_775_936 - 1;
            // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_4 =
                                                      return loop(pvrtmp_2854, end_r_1417, loc_1415, nums_89_772_933, idx1_93_776_942, pvrtmp_2855, fltAppE_891_949);
            // GibCursor pvrtmp_2861 = tmp_struct_4.field0;
            // GibCursor pvrtmp_2862 = tmp_struct_4.field1;
            // GibCursor pvrtmp_2863 = tmp_struct_4.field2;
            // GibCursor pvrtmp_2864 = tmp_struct_4.field3;

            // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2853,
            //                                                    pvrtmp_2862,
            //                                                    pvrtmp_2863,
            //                                                    pvrtmp_2864};
        } else {
            GibInt fltAppE_893_950 = j_94_777_945 - 1;

            gib_shadowstack_push(rstack, tr_91_774_935, end_r_1416, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1415, end_r_1417, Stk,
                                 SearchTree_T);

            GibChunk region_2871 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1475 = region_2871.start;
            GibCursor end_r_1475 = region_2871.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1415 = frame->ptr;
            end_r_1417 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_91_774_935 = frame->ptr;
            end_r_1416 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_5 =
                                                      treeDelete(end_r_1416, end_r_1475, r_1475, tr_91_774_935, fltAppE_893_950);
            GibCursor pvrtmp_2872 = tmp_struct_5.field0;
            GibCursor pvrtmp_2873 = tmp_struct_5.field1;
            GibCursor pvrtmp_2874 = tmp_struct_5.field2;
            GibCursor pvrtmp_2875 = tmp_struct_5.field3;
            GibInt fltAppE_894_952 = n_92_775_936 - 1;
            // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                      return loop(pvrtmp_2873, end_r_1417, loc_1415, nums_89_772_933, idx1_93_776_942, pvrtmp_2874, fltAppE_894_952);
            // GibCursor pvrtmp_2880 = tmp_struct_6.field0;
            // GibCursor pvrtmp_2881 = tmp_struct_6.field1;
            // GibCursor pvrtmp_2882 = tmp_struct_6.field2;
            // GibCursor pvrtmp_2883 = tmp_struct_6.field3;

            // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2872,
            //                                                    pvrtmp_2881,
            //                                                    pvrtmp_2882,
            //                                                    pvrtmp_2883};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1420,
                                                    GibCursor end_r_1421,
                                                    GibCursor loc_1419,
                                                    GibCursor tr_95_778_953,
                                                    GibInt n_96_779_954)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1419 + 26 > end_r_1421) {
        gib_grow_region(&loc_1419, &end_r_1421);
    }

    GibPackedTag tmpval_2890 = *(GibPackedTag *) tr_95_778_953;
    GibCursor tmpcur_2891 = tr_95_778_953 + 1;


  switch_2981:
    ;
    switch (tmpval_2890) {

      case 0:
        {
            *(GibPackedTag *) loc_1419 = 0;

            GibCursor writetag_2095 = loc_1419 + 1;
            GibCursor after_tag_2096 = loc_1419 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                               end_r_1421,
                                                               loc_1419,
                                                               after_tag_2096};
            break;
        }

      case 1:
        {
            GibInt tmpval_2896 = *(GibInt *) tmpcur_2891;
            GibCursor tmpcur_2897 = tmpcur_2891 + sizeof(GibInt);
            GibBool fltIf_895_956 = tmpval_2896 == n_96_779_954;

            if (fltIf_895_956) {
                *(GibPackedTag *) loc_1419 = 0;

                GibCursor writetag_2104 = loc_1419 + 1;
                GibCursor after_tag_2105 = loc_1419 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                                   end_r_1421,
                                                                   loc_1419,
                                                                   after_tag_2105};
            } else {
                *(GibPackedTag *) loc_1419 = 1;

                GibCursor writetag_2111 = loc_1419 + 1;
                GibCursor after_tag_2112 = loc_1419 + 1;

                *(GibInt *) after_tag_2112 = tmpval_2896;

                GibCursor writecur_2116 = after_tag_2112 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                                   end_r_1421,
                                                                   loc_1419,
                                                                   writecur_2116};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2891;
            GibCursor tmpcur_2906 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2907 = tmpcur_2891 + 8;
            uint16_t tmptag_2908 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_absran_1362 = tmpcur_2906 + tmptag_2908;
            GibInt tmpval_2909 = *(GibInt *) tmpaftercur_2907;
            GibCursor tmpcur_2910 = tmpaftercur_2907 + sizeof(GibInt);
            GibBool fltIf_896_960 = tmpval_2909 == n_96_779_954;

            if (fltIf_896_960) {
                GibCursorGibIntProd tmp_struct_11 =
                                     minTree(end_from_tagged_absran_1362, tmpcur_2906);
                GibCursor pvrtmp_2911 = tmp_struct_11.field0;
                GibInt pvrtmp_2912 = tmp_struct_11.field1;
                GibCursor loc_1498 = loc_1419 + 17;

                *(GibPackedTag *) loc_1419 = 3;

                GibCursor writetag_2130 = loc_1419 + 1;

                // if (loc_1498 + 18 > end_r_1421) {
                //     gib_grow_region(&loc_1498, &end_r_1421);
                // }
                gib_indirection_barrier(loc_1498, end_r_1421, tmpcur_2910,
                                        end_r_1420, SearchTree_T);

                GibCursor end_2125 = loc_1498 + 9;
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                          treeDelete(end_from_tagged_absran_1362, end_r_1421, end_2125, tmpcur_2906, pvrtmp_2912);
                GibCursor pvrtmp_2915 = tmp_struct_12.field0;
                GibCursor pvrtmp_2916 = tmp_struct_12.field1;
                GibCursor pvrtmp_2917 = tmp_struct_12.field2;
                GibCursor pvrtmp_2918 = tmp_struct_12.field3;
                uint16_t offset_13 = end_r_1421 - end_2125;
                uintptr_t ran_1365 = GIB_STORE_TAG(end_2125, offset_13);
                GibCursor after_tag_2131 = loc_1419 + 1;

                *(uintptr_t *) after_tag_2131 = ran_1365;

                GibCursor writecur_2135 = after_tag_2131 + 8;

                *(GibInt *) writecur_2135 = pvrtmp_2912;

                GibCursor writecur_2136 = writecur_2135 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2915,
                                                                   pvrtmp_2916,
                                                                   loc_1419,
                                                                   pvrtmp_2918};
            } else {
                GibBool fltIf_899_964 = tmpval_2909 < n_96_779_954;

                if (fltIf_899_964) {
                    GibCursor loc_1498 = loc_1419 + 17;

                    *(GibPackedTag *) loc_1419 = 3;

                    GibCursor writetag_2148 = loc_1419 + 1;

                    // if (loc_1498 + 18 > end_r_1421) {
                    //     gib_grow_region(&loc_1498, &end_r_1421);
                    // }
                    gib_indirection_barrier(loc_1498, end_r_1421, tmpcur_2910,
                                            end_r_1420, SearchTree_T);

                    GibCursor end_2143 = loc_1498 + 9;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_17 =
                                                              treeDelete(end_from_tagged_absran_1362, end_r_1421, end_2143, tmpcur_2906, n_96_779_954);
                    GibCursor pvrtmp_2929 = tmp_struct_17.field0;
                    GibCursor pvrtmp_2930 = tmp_struct_17.field1;
                    GibCursor pvrtmp_2931 = tmp_struct_17.field2;
                    GibCursor pvrtmp_2932 = tmp_struct_17.field3;
                    uint16_t offset_18 = end_r_1421 - end_2143;
                    uintptr_t ran_1366 = GIB_STORE_TAG(end_2143, offset_18);
                    GibCursor after_tag_2149 = loc_1419 + 1;

                    *(uintptr_t *) after_tag_2149 = ran_1366;

                    GibCursor writecur_2153 = after_tag_2149 + 8;

                    *(GibInt *) writecur_2153 = tmpval_2909;

                    GibCursor writecur_2154 = writecur_2153 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2929,
                                                                       pvrtmp_2930,
                                                                       loc_1419,
                                                                       pvrtmp_2932};
                } else {
                    GibCursor loc_1498 = loc_1419 + 17;

                    *(GibPackedTag *) loc_1419 = 3;

                    GibCursor writetag_2166 = loc_1419 + 1;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_22 =
                                                              treeDelete(end_r_1420, end_r_1421, loc_1498, tmpcur_2910, n_96_779_954);
                    GibCursor pvrtmp_2941 = tmp_struct_22.field0;
                    GibCursor pvrtmp_2942 = tmp_struct_22.field1;
                    GibCursor pvrtmp_2943 = tmp_struct_22.field2;
                    GibCursor pvrtmp_2944 = tmp_struct_22.field3;

                    // if (pvrtmp_2944 + 18 > pvrtmp_2942) {
                    //     gib_grow_region(&pvrtmp_2944, &pvrtmp_2942);
                    // }
                    gib_indirection_barrier(pvrtmp_2944, pvrtmp_2942,
                                            tmpcur_2906,
                                            end_from_tagged_absran_1362,
                                            SearchTree_T);

                    GibCursor end_2164 = pvrtmp_2944 + 9;
                    uint16_t offset_23 = pvrtmp_2942 - pvrtmp_2944;
                    uintptr_t ran_1367 = GIB_STORE_TAG(pvrtmp_2944, offset_23);
                    GibCursor after_tag_2167 = loc_1419 + 1;

                    *(uintptr_t *) after_tag_2167 = ran_1367;

                    GibCursor writecur_2171 = after_tag_2167 + 8;

                    *(GibInt *) writecur_2171 = tmpval_2909;

                    GibCursor writecur_2172 = writecur_2171 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2941,
                                                                       pvrtmp_2942,
                                                                       loc_1419,
                                                                       end_2164};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_2891;
            GibCursor tmpcur_2955 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_2956 = tmpcur_2891 + 8;
            uint16_t tmptag_2957 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_1869 = tmpcur_2955 + tmptag_2957;
            GibCursor jump_1871 = tmpcur_2891 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                      treeDelete(end_from_tagged_indr_1869, end_r_1421, loc_1419, tmpcur_2955, n_96_779_954);
            GibCursor pvrtmp_2958 = tmp_struct_28.field0;
            GibCursor pvrtmp_2959 = tmp_struct_28.field1;
            GibCursor pvrtmp_2960 = tmp_struct_28.field2;
            GibCursor pvrtmp_2961 = tmp_struct_28.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1420,
                                                               pvrtmp_2959,
                                                               pvrtmp_2960,
                                                               pvrtmp_2961};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_31 = *(uintptr_t *) tmpcur_2891;
            GibCursor tmpcur_2968 = GIB_UNTAG(tagged_tmpcur_31);
            GibCursor tmpaftercur_2969 = tmpcur_2891 + 8;
            uint16_t tmptag_2970 = GIB_GET_TAG(tagged_tmpcur_31);
            GibCursor end_from_tagged_indr_1869 = tmpcur_2968 + tmptag_2970;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_30 =
                                                      treeDelete(end_from_tagged_indr_1869, end_r_1421, loc_1419, tmpcur_2968, n_96_779_954);
            GibCursor pvrtmp_2971 = tmp_struct_30.field0;
            GibCursor pvrtmp_2972 = tmp_struct_30.field1;
            GibCursor pvrtmp_2973 = tmp_struct_30.field2;
            GibCursor pvrtmp_2974 = tmp_struct_30.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2971,
                                                               pvrtmp_2972,
                                                               pvrtmp_2973,
                                                               pvrtmp_2974};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2890");
            exit(1);
        }
    }
}
GibCursorGibIntProd minTree(GibCursor end_r_1423, GibCursor tr_102_785_969)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2982 = *(GibPackedTag *) tr_102_785_969;
    GibCursor tmpcur_2983 = tr_102_785_969 + 1;


  switch_3003:
    ;
    switch (tmpval_2982) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1423, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2984 = *(GibInt *) tmpcur_2983;
            GibCursor tmpcur_2985 = tmpcur_2983 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1423, tmpval_2984};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_2983;
            GibCursor tmpcur_2986 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_2987 = tmpcur_2983 + 8;
            uint16_t tmptag_2988 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_absran_1371 = tmpcur_2986 + tmptag_2988;
            GibInt tmpval_2989 = *(GibInt *) tmpaftercur_2987;
            GibCursor tmpcur_2990 = tmpaftercur_2987 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_35 =
                                 caseFn_765(end_r_1423, tmpcur_2990, tmpval_2989);
            GibCursor pvrtmp_2991 = tmp_struct_35.field0;
            GibInt pvrtmp_2992 = tmp_struct_35.field1;

            return (GibCursorGibIntProd) {pvrtmp_2991, pvrtmp_2992};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) tmpcur_2983;
            GibCursor tmpcur_2993 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_2994 = tmpcur_2983 + 8;
            uint16_t tmptag_2995 = GIB_GET_TAG(tagged_tmpcur_38);
            GibCursor end_from_tagged_indr_1874 = tmpcur_2993 + tmptag_2995;
            GibCursor jump_1876 = tmpcur_2983 + 8;
            GibCursorGibIntProd tmp_struct_37 =
                                 minTree(end_from_tagged_indr_1874, tmpcur_2993);
            GibCursor pvrtmp_2996 = tmp_struct_37.field0;
            GibInt pvrtmp_2997 = tmp_struct_37.field1;

            return (GibCursorGibIntProd) {end_r_1423, pvrtmp_2997};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_2983;
            GibCursor tmpcur_2998 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_2999 = tmpcur_2983 + 8;
            uint16_t tmptag_3000 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_1874 = tmpcur_2998 + tmptag_3000;
            GibCursorGibIntProd tmp_struct_39 =
                                 minTree(end_from_tagged_indr_1874, tmpcur_2998);
            GibCursor pvrtmp_3001 = tmp_struct_39.field0;
            GibInt pvrtmp_3002 = tmp_struct_39.field1;

            return (GibCursorGibIntProd) {pvrtmp_3001, pvrtmp_3002};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2982");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1426,
                                                    GibCursor end_r_1427,
                                                    GibCursor loc_1425,
                                                    GibCursor tr_111_790_974,
                                                    GibInt n_112_791_975)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1425 + 26 > end_r_1427) {
        gib_grow_region(&loc_1425, &end_r_1427);
    }

    GibPackedTag tmpval_3004 = *(GibPackedTag *) tr_111_790_974;
    GibCursor tmpcur_3005 = tr_111_790_974 + 1;


  switch_3099:
    ;
    switch (tmpval_3004) {

      case 0:
        {
            *(GibPackedTag *) loc_1425 = 1;

            GibCursor writetag_2205 = loc_1425 + 1;
            GibCursor after_tag_2206 = loc_1425 + 1;

            *(GibInt *) after_tag_2206 = n_112_791_975;

            GibCursor writecur_2210 = after_tag_2206 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1426,
                                                               end_r_1427,
                                                               loc_1425,
                                                               writecur_2210};
            break;
        }

      case 1:
        {
            GibInt tmpval_3010 = *(GibInt *) tmpcur_3005;
            GibCursor tmpcur_3011 = tmpcur_3005 + sizeof(GibInt);
            GibBool fltIf_904_977 = n_112_791_975 == tmpval_3010;

            if (fltIf_904_977) {
                *(GibPackedTag *) loc_1425 = 1;

                GibCursor writetag_2215 = loc_1425 + 1;
                GibCursor after_tag_2216 = loc_1425 + 1;

                *(GibInt *) after_tag_2216 = tmpval_3010;

                GibCursor writecur_2220 = after_tag_2216 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1426,
                                                                   end_r_1427,
                                                                   loc_1425,
                                                                   writecur_2220};
            } else {
                GibBool fltIf_905_978 = n_112_791_975 < tmpval_3010;

                if (fltIf_905_978) {
                    GibCursor loc_1567 = loc_1425 + 17;

                    *(GibPackedTag *) loc_1425 = 3;

                    GibCursor writetag_2238 = loc_1425 + 1;

                    *(GibPackedTag *) loc_1567 = 1;

                    GibCursor writetag_2223 = loc_1567 + 1;
                    GibCursor after_tag_2224 = loc_1567 + 1;

                    *(GibInt *) after_tag_2224 = n_112_791_975;

                    GibCursor writecur_2228 = after_tag_2224 + sizeof(GibInt);

                    *(GibPackedTag *) writecur_2228 = 0;

                    GibCursor writetag_2231 = writecur_2228 + 1;
                    GibCursor after_tag_2232 = writecur_2228 + 1;
                    uint16_t offset_41 = end_r_1427 - writecur_2228;
                    uintptr_t ran_1374 = GIB_STORE_TAG(writecur_2228,
                                                       offset_41);
                    GibCursor after_tag_2239 = loc_1425 + 1;

                    *(uintptr_t *) after_tag_2239 = ran_1374;

                    GibCursor writecur_2243 = after_tag_2239 + 8;

                    *(GibInt *) writecur_2243 = tmpval_3010;

                    GibCursor writecur_2244 = writecur_2243 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1426,
                                                                       end_r_1427,
                                                                       loc_1425,
                                                                       after_tag_2232};
                } else {
                    GibCursor loc_1567 = loc_1425 + 17;

                    *(GibPackedTag *) loc_1425 = 3;

                    GibCursor writetag_2265 = loc_1425 + 1;

                    *(GibPackedTag *) loc_1567 = 0;

                    GibCursor writetag_2250 = loc_1567 + 1;
                    GibCursor after_tag_2251 = loc_1567 + 1;

                    *(GibPackedTag *) after_tag_2251 = 1;

                    GibCursor writetag_2257 = after_tag_2251 + 1;
                    GibCursor after_tag_2258 = after_tag_2251 + 1;

                    *(GibInt *) after_tag_2258 = n_112_791_975;

                    GibCursor writecur_2262 = after_tag_2258 + sizeof(GibInt);
                    uint16_t offset_42 = end_r_1427 - after_tag_2251;
                    uintptr_t ran_1375 = GIB_STORE_TAG(after_tag_2251,
                                                       offset_42);
                    GibCursor after_tag_2266 = loc_1425 + 1;

                    *(uintptr_t *) after_tag_2266 = ran_1375;

                    GibCursor writecur_2270 = after_tag_2266 + 8;

                    *(GibInt *) writecur_2270 = tmpval_3010;

                    GibCursor writecur_2271 = writecur_2270 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1426,
                                                                       end_r_1427,
                                                                       loc_1425,
                                                                       writecur_2262};
                }
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_60 = *(uintptr_t *) tmpcur_3005;
            GibCursor tmpcur_3032 = GIB_UNTAG(tagged_tmpcur_60);
            GibCursor tmpaftercur_3033 = tmpcur_3005 + 8;
            uint16_t tmptag_3034 = GIB_GET_TAG(tagged_tmpcur_60);
            GibCursor end_from_tagged_absran_1379 = tmpcur_3032 + tmptag_3034;
            GibInt tmpval_3035 = *(GibInt *) tmpaftercur_3033;
            GibCursor tmpcur_3036 = tmpaftercur_3033 + sizeof(GibInt);
            GibBool fltIf_910_986 = tmpval_3035 == n_112_791_975;

            if (fltIf_910_986) {
                GibCursor loc_1567 = loc_1425 + 17;

                *(GibPackedTag *) loc_1425 = 3;

                GibCursor writetag_2286 = loc_1425 + 1;

                // if (loc_1567 + 18 > end_r_1427) {
                //     gib_grow_region(&loc_1567, &end_r_1427);
                // }
                gib_indirection_barrier(loc_1567, end_r_1427, tmpcur_3036,
                                        end_r_1426, SearchTree_T);

                GibCursor end_2281 = loc_1567 + 9;

                // if (end_2281 + 18 > end_r_1427) {
                //     gib_grow_region(&end_2281, &end_r_1427);
                // }
                gib_indirection_barrier(end_2281, end_r_1427, tmpcur_3032,
                                        end_from_tagged_absran_1379,
                                        SearchTree_T);

                GibCursor end_2284 = end_2281 + 9;
                uint16_t offset_43 = end_r_1427 - end_2281;
                uintptr_t ran_1382 = GIB_STORE_TAG(end_2281, offset_43);
                GibCursor after_tag_2287 = loc_1425 + 1;

                *(uintptr_t *) after_tag_2287 = ran_1382;

                GibCursor writecur_2291 = after_tag_2287 + 8;

                *(GibInt *) writecur_2291 = tmpval_3035;

                GibCursor writecur_2292 = writecur_2291 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1426,
                                                                   end_r_1427,
                                                                   loc_1425,
                                                                   end_2284};
            } else {
                GibBool fltIf_913_989 = n_112_791_975 < tmpval_3035;

                if (fltIf_913_989) {
                    GibCursor loc_1567 = loc_1425 + 17;

                    *(GibPackedTag *) loc_1425 = 3;

                    GibCursor writetag_2304 = loc_1425 + 1;

                    // if (loc_1567 + 18 > end_r_1427) {
                    //     gib_grow_region(&loc_1567, &end_r_1427);
                    // }
                    gib_indirection_barrier(loc_1567, end_r_1427, tmpcur_3036,
                                            end_r_1426, SearchTree_T);

                    GibCursor end_2299 = loc_1567 + 9;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                              treeInsert(end_from_tagged_absran_1379, end_r_1427, end_2299, tmpcur_3032, n_112_791_975);
                    GibCursor pvrtmp_3047 = tmp_struct_50.field0;
                    GibCursor pvrtmp_3048 = tmp_struct_50.field1;
                    GibCursor pvrtmp_3049 = tmp_struct_50.field2;
                    GibCursor pvrtmp_3050 = tmp_struct_50.field3;
                    uint16_t offset_51 = end_r_1427 - end_2299;
                    uintptr_t ran_1383 = GIB_STORE_TAG(end_2299, offset_51);
                    GibCursor after_tag_2305 = loc_1425 + 1;

                    *(uintptr_t *) after_tag_2305 = ran_1383;

                    GibCursor writecur_2309 = after_tag_2305 + 8;

                    *(GibInt *) writecur_2309 = tmpval_3035;

                    GibCursor writecur_2310 = writecur_2309 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3047,
                                                                       pvrtmp_3048,
                                                                       loc_1425,
                                                                       pvrtmp_3050};
                } else {
                    GibCursor loc_1567 = loc_1425 + 17;

                    *(GibPackedTag *) loc_1425 = 3;

                    GibCursor writetag_2322 = loc_1425 + 1;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_55 =
                                                              treeInsert(end_r_1426, end_r_1427, loc_1567, tmpcur_3036, n_112_791_975);
                    GibCursor pvrtmp_3059 = tmp_struct_55.field0;
                    GibCursor pvrtmp_3060 = tmp_struct_55.field1;
                    GibCursor pvrtmp_3061 = tmp_struct_55.field2;
                    GibCursor pvrtmp_3062 = tmp_struct_55.field3;

                    // if (pvrtmp_3062 + 18 > pvrtmp_3060) {
                    //     gib_grow_region(&pvrtmp_3062, &pvrtmp_3060);
                    // }
                    gib_indirection_barrier(pvrtmp_3062, pvrtmp_3060,
                                            tmpcur_3032,
                                            end_from_tagged_absran_1379,
                                            SearchTree_T);

                    GibCursor end_2320 = pvrtmp_3062 + 9;
                    uint16_t offset_56 = pvrtmp_3060 - pvrtmp_3062;
                    uintptr_t ran_1384 = GIB_STORE_TAG(pvrtmp_3062, offset_56);
                    GibCursor after_tag_2323 = loc_1425 + 1;

                    *(uintptr_t *) after_tag_2323 = ran_1384;

                    GibCursor writecur_2327 = after_tag_2323 + 8;

                    *(GibInt *) writecur_2327 = tmpval_3035;

                    GibCursor writecur_2328 = writecur_2327 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3059,
                                                                       pvrtmp_3060,
                                                                       loc_1425,
                                                                       end_2320};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_62 = *(uintptr_t *) tmpcur_3005;
            GibCursor tmpcur_3073 = GIB_UNTAG(tagged_tmpcur_62);
            GibCursor tmpaftercur_3074 = tmpcur_3005 + 8;
            uint16_t tmptag_3075 = GIB_GET_TAG(tagged_tmpcur_62);
            GibCursor end_from_tagged_indr_1879 = tmpcur_3073 + tmptag_3075;
            GibCursor jump_1881 = tmpcur_3005 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_61 =
                                                      treeInsert(end_from_tagged_indr_1879, end_r_1427, loc_1425, tmpcur_3073, n_112_791_975);
            GibCursor pvrtmp_3076 = tmp_struct_61.field0;
            GibCursor pvrtmp_3077 = tmp_struct_61.field1;
            GibCursor pvrtmp_3078 = tmp_struct_61.field2;
            GibCursor pvrtmp_3079 = tmp_struct_61.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1426,
                                                               pvrtmp_3077,
                                                               pvrtmp_3078,
                                                               pvrtmp_3079};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_64 = *(uintptr_t *) tmpcur_3005;
            GibCursor tmpcur_3086 = GIB_UNTAG(tagged_tmpcur_64);
            GibCursor tmpaftercur_3087 = tmpcur_3005 + 8;
            uint16_t tmptag_3088 = GIB_GET_TAG(tagged_tmpcur_64);
            GibCursor end_from_tagged_indr_1879 = tmpcur_3086 + tmptag_3088;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_63 =
                                                      treeInsert(end_from_tagged_indr_1879, end_r_1427, loc_1425, tmpcur_3086, n_112_791_975);
            GibCursor pvrtmp_3089 = tmp_struct_63.field0;
            GibCursor pvrtmp_3090 = tmp_struct_63.field1;
            GibCursor pvrtmp_3091 = tmp_struct_63.field2;
            GibCursor pvrtmp_3092 = tmp_struct_63.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3089,
                                                               pvrtmp_3090,
                                                               pvrtmp_3091,
                                                               pvrtmp_3092};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3004");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1429,
                                        GibCursor tr_122_801_994)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3100 = *(GibPackedTag *) tr_122_801_994;
    GibCursor tmpcur_3101 = tr_122_801_994 + 1;


  switch_3127:
    ;
    switch (tmpval_3100) {

      case 0:
        {
            GibCursor jump_1814 = tr_122_801_994 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_1429, jump_1814, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_3102 = *(GibInt *) tmpcur_3101;
            GibCursor tmpcur_3103 = tmpcur_3101 + sizeof(GibInt);
            GibCursor jump_1815 = tmpcur_3101 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_1429, jump_1815, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_70 = *(uintptr_t *) tmpcur_3101;
            GibCursor tmpcur_3104 = GIB_UNTAG(tagged_tmpcur_70);
            GibCursor tmpaftercur_3105 = tmpcur_3101 + 8;
            uint16_t tmptag_3106 = GIB_GET_TAG(tagged_tmpcur_70);
            GibCursor end_from_tagged_absran_1388 = tmpcur_3104 + tmptag_3106;
            GibInt tmpval_3107 = *(GibInt *) tmpaftercur_3105;
            GibCursor tmpcur_3108 = tmpaftercur_3105 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_68 =
                                          countnodes(end_r_1429, tmpcur_3108);
            GibCursor pvrtmp_3109 = tmp_struct_68.field0;
            GibCursor pvrtmp_3110 = tmp_struct_68.field1;
            GibInt pvrtmp_3111 = tmp_struct_68.field2;
            GibInt fltPrm_918_1000 = 1 + pvrtmp_3111;
            GibCursorGibCursorGibIntProd tmp_struct_69 =
                                          countnodes(end_from_tagged_absran_1388, tmpcur_3104);
            GibCursor pvrtmp_3112 = tmp_struct_69.field0;
            GibCursor pvrtmp_3113 = tmp_struct_69.field1;
            GibInt pvrtmp_3114 = tmp_struct_69.field2;
            GibInt tailprim_1820 = fltPrm_918_1000 + pvrtmp_3114;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3112, pvrtmp_3113,
                                                   tailprim_1820};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) tmpcur_3101;
            GibCursor tmpcur_3115 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_3116 = tmpcur_3101 + 8;
            uint16_t tmptag_3117 = GIB_GET_TAG(tagged_tmpcur_72);
            GibCursor end_from_tagged_indr_1884 = tmpcur_3115 + tmptag_3117;
            GibCursor jump_1886 = tmpcur_3101 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_71 =
                                          countnodes(end_from_tagged_indr_1884, tmpcur_3115);
            GibCursor pvrtmp_3118 = tmp_struct_71.field0;
            GibCursor pvrtmp_3119 = tmp_struct_71.field1;
            GibInt pvrtmp_3120 = tmp_struct_71.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_1429, jump_1886,
                                                   pvrtmp_3120};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_3101;
            GibCursor tmpcur_3121 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_3122 = tmpcur_3101 + 8;
            uint16_t tmptag_3123 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_1884 = tmpcur_3121 + tmptag_3123;
            GibCursorGibCursorGibIntProd tmp_struct_73 =
                                          countnodes(end_from_tagged_indr_1884, tmpcur_3121);
            GibCursor pvrtmp_3124 = tmp_struct_73.field0;
            GibCursor pvrtmp_3125 = tmp_struct_73.field1;
            GibInt pvrtmp_3126 = tmp_struct_73.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3124, pvrtmp_3125,
                                                   pvrtmp_3126};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3100");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1431, GibCursor loc_1430,
                                       GibInt s_127_806_1002,
                                       GibInt e_128_807_1003)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1430 + 26 > end_r_1431) {
        gib_grow_region(&loc_1430, &end_r_1431);
    }

    GibBool fltIf_921_1004 = e_128_807_1003 < s_127_806_1002;

    if (fltIf_921_1004) {
        *(GibPackedTag *) loc_1430 = 0;

        GibCursor writetag_2362 = loc_1430 + 1;
        GibCursor after_tag_2363 = loc_1430 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_1431, loc_1430,
                                                  after_tag_2363};
    } else {
        GibBool fltIf_922_1005 = s_127_806_1002 == e_128_807_1003;

        if (fltIf_922_1005) {
            *(GibPackedTag *) loc_1430 = 1;

            GibCursor writetag_2369 = loc_1430 + 1;
            GibCursor after_tag_2370 = loc_1430 + 1;

            *(GibInt *) after_tag_2370 = s_127_806_1002;

            GibCursor writecur_2374 = after_tag_2370 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_1431, loc_1430,
                                                      writecur_2374};
        } else {
            GibInt fltPrm_924_1006 = e_128_807_1003 - s_127_806_1002;
            GibInt fltPrm_923_1007 = fltPrm_924_1006 / 2;
            GibInt m_129_808_1008 = fltPrm_923_1007 + s_127_806_1002;
            GibInt fltAppE_926_1009 = m_129_808_1008 - 1;
            GibCursor loc_1667 = loc_1430 + 17;

            *(GibPackedTag *) loc_1430 = 3;

            GibCursor writetag_2381 = loc_1430 + 1;
            GibCursorGibCursorGibCursorProd tmp_struct_75 =
                                             helper(end_r_1431, loc_1667, s_127_806_1002, fltAppE_926_1009);
            GibCursor pvrtmp_3136 = tmp_struct_75.field0;
            GibCursor pvrtmp_3137 = tmp_struct_75.field1;
            GibCursor pvrtmp_3138 = tmp_struct_75.field2;
            GibInt fltAppE_928_1011 = m_129_808_1008 + 1;
            GibCursorGibCursorGibCursorProd tmp_struct_76 =
                                             helper(pvrtmp_3136, pvrtmp_3138, fltAppE_928_1011, e_128_807_1003);
            GibCursor pvrtmp_3143 = tmp_struct_76.field0;
            GibCursor pvrtmp_3144 = tmp_struct_76.field1;
            GibCursor pvrtmp_3145 = tmp_struct_76.field2;
            uint16_t offset_77 = pvrtmp_3136 - pvrtmp_3138;
            uintptr_t ran_1391 = GIB_STORE_TAG(pvrtmp_3138, offset_77);
            GibCursor after_tag_2382 = loc_1430 + 1;

            *(uintptr_t *) after_tag_2382 = ran_1391;

            GibCursor writecur_2386 = after_tag_2382 + 8;

            *(GibInt *) writecur_2386 = m_129_808_1008;

            GibCursor writecur_2387 = writecur_2386 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_3143, loc_1430,
                                                      pvrtmp_3145};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_1434,
                                                                   GibCursor end_r_1435,
                                                                   GibCursor loc_1433,
                                                                   GibCursor arg_723_835_1013)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1433 + 26 > end_r_1435) {
        gib_grow_region(&loc_1433, &end_r_1435);
    }

    GibPackedTag tmpval_3154 = *(GibPackedTag *) arg_723_835_1013;
    GibCursor tmpcur_3155 = arg_723_835_1013 + 1;


  switch_3221:
    ;
    switch (tmpval_3154) {

      case 0:
        {
            GibCursor jump_1824 = arg_723_835_1013 + 1;

            *(GibPackedTag *) loc_1433 = 0;

            GibCursor writetag_2394 = loc_1433 + 1;
            GibCursor after_tag_2395 = loc_1433 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1434,
                                                                        end_r_1435,
                                                                        jump_1824,
                                                                        loc_1433,
                                                                        after_tag_2395};
            break;
        }

      case 1:
        {
            GibInt tmpval_3160 = *(GibInt *) tmpcur_3155;
            GibCursor tmpcur_3161 = tmpcur_3155 + sizeof(GibInt);
            GibCursor jump_1826 = tmpcur_3155 + 8;

            *(GibPackedTag *) loc_1433 = 1;

            GibCursor writetag_2403 = loc_1433 + 1;
            GibCursor after_tag_2404 = loc_1433 + 1;

            *(GibInt *) after_tag_2404 = tmpval_3160;

            GibCursor writecur_2408 = after_tag_2404 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1434,
                                                                        end_r_1435,
                                                                        jump_1826,
                                                                        loc_1433,
                                                                        writecur_2408};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_3155;
            GibCursor tmpcur_3166 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_3167 = tmpcur_3155 + 8;
            uint16_t tmptag_3168 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_absran_1393 = tmpcur_3166 + tmptag_3168;
            GibInt tmpval_3169 = *(GibInt *) tmpaftercur_3167;
            GibCursor tmpcur_3170 = tmpaftercur_3167 + sizeof(GibInt);
            GibCursor loc_1695 = loc_1433 + 17;

            *(GibPackedTag *) loc_1433 = 3;

            GibCursor writetag_2420 = loc_1433 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_r_1434, end_r_1435, loc_1695, tmpcur_3170);
            GibCursor pvrtmp_3171 = tmp_struct_81.field0;
            GibCursor pvrtmp_3172 = tmp_struct_81.field1;
            GibCursor pvrtmp_3173 = tmp_struct_81.field2;
            GibCursor pvrtmp_3174 = tmp_struct_81.field3;
            GibCursor pvrtmp_3175 = tmp_struct_81.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_82 =
                                                               _copy_SearchTree(end_from_tagged_absran_1393, pvrtmp_3172, pvrtmp_3175, tmpcur_3166);
            GibCursor pvrtmp_3180 = tmp_struct_82.field0;
            GibCursor pvrtmp_3181 = tmp_struct_82.field1;
            GibCursor pvrtmp_3182 = tmp_struct_82.field2;
            GibCursor pvrtmp_3183 = tmp_struct_82.field3;
            GibCursor pvrtmp_3184 = tmp_struct_82.field4;
            uint16_t offset_83 = pvrtmp_3172 - pvrtmp_3175;
            uintptr_t ran_1396 = GIB_STORE_TAG(pvrtmp_3175, offset_83);
            GibCursor after_tag_2421 = loc_1433 + 1;

            *(uintptr_t *) after_tag_2421 = ran_1396;

            GibCursor writecur_2425 = after_tag_2421 + 8;

            *(GibInt *) writecur_2425 = tmpval_3169;

            GibCursor writecur_2426 = writecur_2425 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3180,
                                                                        pvrtmp_3181,
                                                                        pvrtmp_3182,
                                                                        loc_1433,
                                                                        pvrtmp_3184};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_3155;
            GibCursor tmpcur_3193 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_3194 = tmpcur_3155 + 8;
            uint16_t tmptag_3195 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1890 = tmpcur_3193 + tmptag_3195;
            GibCursor jump_1892 = tmpcur_3155 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_85 =
                                                               _copy_SearchTree(end_from_tagged_indr_1890, end_r_1435, loc_1433, tmpcur_3193);
            GibCursor pvrtmp_3196 = tmp_struct_85.field0;
            GibCursor pvrtmp_3197 = tmp_struct_85.field1;
            GibCursor pvrtmp_3198 = tmp_struct_85.field2;
            GibCursor pvrtmp_3199 = tmp_struct_85.field3;
            GibCursor pvrtmp_3200 = tmp_struct_85.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1434,
                                                                        pvrtmp_3197,
                                                                        jump_1892,
                                                                        pvrtmp_3199,
                                                                        pvrtmp_3200};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3155;
            GibCursor tmpcur_3207 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3208 = tmpcur_3155 + 8;
            uint16_t tmptag_3209 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1890 = tmpcur_3207 + tmptag_3209;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_SearchTree(end_from_tagged_indr_1890, end_r_1435, loc_1433, tmpcur_3207);
            GibCursor pvrtmp_3210 = tmp_struct_87.field0;
            GibCursor pvrtmp_3211 = tmp_struct_87.field1;
            GibCursor pvrtmp_3212 = tmp_struct_87.field2;
            GibCursor pvrtmp_3213 = tmp_struct_87.field3;
            GibCursor pvrtmp_3214 = tmp_struct_87.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3210,
                                                                        pvrtmp_3211,
                                                                        pvrtmp_3212,
                                                                        pvrtmp_3213,
                                                                        pvrtmp_3214};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3154");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_1438,
                                                                                GibCursor end_r_1439,
                                                                                GibCursor loc_1437,
                                                                                GibCursor arg_732_844_1022)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3222 = *(GibPackedTag *) arg_732_844_1022;
    GibCursor tmpcur_3223 = arg_732_844_1022 + 1;


  switch_3289:
    ;
    switch (tmpval_3222) {

      case 0:
        {
            GibCursor jump_1833 = arg_732_844_1022 + 1;

            *(GibPackedTag *) loc_1437 = 0;

            GibCursor writetag_2443 = loc_1437 + 1;
            GibCursor after_tag_2444 = loc_1437 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1438,
                                                                        end_r_1439,
                                                                        jump_1833,
                                                                        loc_1437,
                                                                        after_tag_2444};
            break;
        }

      case 1:
        {
            GibInt tmpval_3228 = *(GibInt *) tmpcur_3223;
            GibCursor tmpcur_3229 = tmpcur_3223 + sizeof(GibInt);
            GibCursor jump_1835 = tmpcur_3223 + 8;

            *(GibPackedTag *) loc_1437 = 1;

            GibCursor writetag_2452 = loc_1437 + 1;
            GibCursor after_tag_2453 = loc_1437 + 1;

            *(GibInt *) after_tag_2453 = tmpval_3228;

            GibCursor writecur_2457 = after_tag_2453 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1438,
                                                                        end_r_1439,
                                                                        jump_1835,
                                                                        loc_1437,
                                                                        writecur_2457};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_94 = *(uintptr_t *) tmpcur_3223;
            GibCursor tmpcur_3234 = GIB_UNTAG(tagged_tmpcur_94);
            GibCursor tmpaftercur_3235 = tmpcur_3223 + 8;
            uint16_t tmptag_3236 = GIB_GET_TAG(tagged_tmpcur_94);
            GibCursor end_from_tagged_absran_1398 = tmpcur_3234 + tmptag_3236;
            GibInt tmpval_3237 = *(GibInt *) tmpaftercur_3235;
            GibCursor tmpcur_3238 = tmpaftercur_3235 + sizeof(GibInt);
            GibCursor loc_1722 = loc_1437 + 9;

            *(GibPackedTag *) loc_1437 = 2;

            GibCursor writetag_2469 = loc_1437 + 1;
            GibCursor after_tag_2470 = loc_1437 + 1;

            *(GibInt *) after_tag_2470 = tmpval_3237;

            GibCursor writecur_2474 = after_tag_2470 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_r_1438, end_r_1439, loc_1722, tmpcur_3238);
            GibCursor pvrtmp_3239 = tmp_struct_92.field0;
            GibCursor pvrtmp_3240 = tmp_struct_92.field1;
            GibCursor pvrtmp_3241 = tmp_struct_92.field2;
            GibCursor pvrtmp_3242 = tmp_struct_92.field3;
            GibCursor pvrtmp_3243 = tmp_struct_92.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_93 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_1398, pvrtmp_3240, pvrtmp_3243, tmpcur_3234);
            GibCursor pvrtmp_3248 = tmp_struct_93.field0;
            GibCursor pvrtmp_3249 = tmp_struct_93.field1;
            GibCursor pvrtmp_3250 = tmp_struct_93.field2;
            GibCursor pvrtmp_3251 = tmp_struct_93.field3;
            GibCursor pvrtmp_3252 = tmp_struct_93.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3248,
                                                                        pvrtmp_3249,
                                                                        pvrtmp_3250,
                                                                        loc_1437,
                                                                        pvrtmp_3252};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_96 = *(uintptr_t *) tmpcur_3223;
            GibCursor tmpcur_3261 = GIB_UNTAG(tagged_tmpcur_96);
            GibCursor tmpaftercur_3262 = tmpcur_3223 + 8;
            uint16_t tmptag_3263 = GIB_GET_TAG(tagged_tmpcur_96);
            GibCursor end_from_tagged_indr_1896 = tmpcur_3261 + tmptag_3263;
            GibCursor jump_1898 = tmpcur_3223 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_95 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1896, end_r_1439, loc_1437, tmpcur_3261);
            GibCursor pvrtmp_3264 = tmp_struct_95.field0;
            GibCursor pvrtmp_3265 = tmp_struct_95.field1;
            GibCursor pvrtmp_3266 = tmp_struct_95.field2;
            GibCursor pvrtmp_3267 = tmp_struct_95.field3;
            GibCursor pvrtmp_3268 = tmp_struct_95.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1438,
                                                                        pvrtmp_3265,
                                                                        jump_1898,
                                                                        pvrtmp_3267,
                                                                        pvrtmp_3268};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_98 = *(uintptr_t *) tmpcur_3223;
            GibCursor tmpcur_3275 = GIB_UNTAG(tagged_tmpcur_98);
            GibCursor tmpaftercur_3276 = tmpcur_3223 + 8;
            uint16_t tmptag_3277 = GIB_GET_TAG(tagged_tmpcur_98);
            GibCursor end_from_tagged_indr_1896 = tmpcur_3275 + tmptag_3277;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_97 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1896, end_r_1439, loc_1437, tmpcur_3275);
            GibCursor pvrtmp_3278 = tmp_struct_97.field0;
            GibCursor pvrtmp_3279 = tmp_struct_97.field1;
            GibCursor pvrtmp_3280 = tmp_struct_97.field2;
            GibCursor pvrtmp_3281 = tmp_struct_97.field3;
            GibCursor pvrtmp_3282 = tmp_struct_97.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3278,
                                                                        pvrtmp_3279,
                                                                        pvrtmp_3280,
                                                                        pvrtmp_3281,
                                                                        pvrtmp_3282};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3222");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1441,
                                            GibCursor arg_741_853_1031)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3290 = *(GibPackedTag *) arg_741_853_1031;
    GibCursor tmpcur_3291 = arg_741_853_1031 + 1;


  switch_3313:
    ;
    switch (tmpval_3290) {

      case 0:
        {
            GibCursor jump_1842 = arg_741_853_1031 + 1;

            return (GibCursorGibCursorProd) {end_r_1441, jump_1842};
            break;
        }

      case 1:
        {
            GibInt tmpval_3292 = *(GibInt *) tmpcur_3291;
            GibCursor tmpcur_3293 = tmpcur_3291 + sizeof(GibInt);
            GibCursor jump_1844 = tmpcur_3291 + 8;

            return (GibCursorGibCursorProd) {end_r_1441, jump_1844};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_3291;
            GibCursor tmpcur_3294 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_3295 = tmpcur_3291 + 8;
            uint16_t tmptag_3296 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_absran_1401 = tmpcur_3294 + tmptag_3296;
            GibInt tmpval_3297 = *(GibInt *) tmpaftercur_3295;
            GibCursor tmpcur_3298 = tmpaftercur_3295 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_r_1441, tmpcur_3298);
            GibCursor pvrtmp_3299 = tmp_struct_99.field0;
            GibCursor pvrtmp_3300 = tmp_struct_99.field1;
            GibCursorGibCursorProd tmp_struct_100 =
                                    _traverse_SearchTree(end_from_tagged_absran_1401, tmpcur_3294);
            GibCursor pvrtmp_3301 = tmp_struct_100.field0;
            GibCursor pvrtmp_3302 = tmp_struct_100.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3301, pvrtmp_3302};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_3291;
            GibCursor tmpcur_3303 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_3304 = tmpcur_3291 + 8;
            uint16_t tmptag_3305 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_1902 = tmpcur_3303 + tmptag_3305;
            GibCursor jump_1904 = tmpcur_3291 + 8;
            GibCursorGibCursorProd tmp_struct_102 =
                                    _traverse_SearchTree(end_from_tagged_indr_1902, tmpcur_3303);
            GibCursor pvrtmp_3306 = tmp_struct_102.field0;
            GibCursor pvrtmp_3307 = tmp_struct_102.field1;

            return (GibCursorGibCursorProd) {end_r_1441, jump_1904};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) tmpcur_3291;
            GibCursor tmpcur_3308 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_3309 = tmpcur_3291 + 8;
            uint16_t tmptag_3310 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_indr_1902 = tmpcur_3308 + tmptag_3310;
            GibCursorGibCursorProd tmp_struct_104 =
                                    _traverse_SearchTree(end_from_tagged_indr_1902, tmpcur_3308);
            GibCursor pvrtmp_3311 = tmp_struct_104.field0;
            GibCursor pvrtmp_3312 = tmp_struct_104.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3311, pvrtmp_3312};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3290");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1443,
                                         GibCursor arg_750_860_1038)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3314 = *(GibPackedTag *) arg_750_860_1038;
    GibCursor tmpcur_3315 = arg_750_860_1038 + 1;


  switch_3337:
    ;
    switch (tmpval_3314) {

      case 0:
        {
            GibCursor jump_1851 = arg_750_860_1038 + 1;
            unsigned char wildcard_751_861_1039 = gib_print_symbol(2810);
            unsigned char wildcard_752_862_1040 = gib_print_symbol(2809);

            return (GibCursorGibCursorProd) {end_r_1443, jump_1851};
            break;
        }

      case 1:
        {
            GibInt tmpval_3316 = *(GibInt *) tmpcur_3315;
            GibCursor tmpcur_3317 = tmpcur_3315 + sizeof(GibInt);
            GibCursor jump_1853 = tmpcur_3315 + 8;
            unsigned char wildcard_755_864_1042 = gib_print_symbol(2812);
            unsigned char y_754_865_1043 = printf("%ld", tmpval_3316);
            unsigned char wildcard_756_866_1044 = gib_print_symbol(2809);

            return (GibCursorGibCursorProd) {end_r_1443, jump_1853};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_108 = *(uintptr_t *) tmpcur_3315;
            GibCursor tmpcur_3318 = GIB_UNTAG(tagged_tmpcur_108);
            GibCursor tmpaftercur_3319 = tmpcur_3315 + 8;
            uint16_t tmptag_3320 = GIB_GET_TAG(tagged_tmpcur_108);
            GibCursor end_from_tagged_absran_1404 = tmpcur_3318 + tmptag_3320;
            GibInt tmpval_3321 = *(GibInt *) tmpaftercur_3319;
            GibCursor tmpcur_3322 = tmpaftercur_3319 + sizeof(GibInt);
            unsigned char wildcard_763_870_1048 = gib_print_symbol(2811);
            unsigned char y_760_871_1049 = printf("%ld", tmpval_3321);
            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_r_1443, tmpcur_3322);
            GibCursor pvrtmp_3323 = tmp_struct_106.field0;
            GibCursor pvrtmp_3324 = tmp_struct_106.field1;
            GibCursorGibCursorProd tmp_struct_107 =
                                    _print_SearchTree(end_from_tagged_absran_1404, tmpcur_3318);
            GibCursor pvrtmp_3325 = tmp_struct_107.field0;
            GibCursor pvrtmp_3326 = tmp_struct_107.field1;
            unsigned char wildcard_764_874_1052 = gib_print_symbol(2809);

            return (GibCursorGibCursorProd) {pvrtmp_3325, pvrtmp_3326};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_3315;
            GibCursor tmpcur_3327 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_3328 = tmpcur_3315 + 8;
            uint16_t tmptag_3329 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_1908 = tmpcur_3327 + tmptag_3329;
            GibCursor jump_1910 = tmpcur_3315 + 8;
            unsigned char wildcard_1913 = gib_print_symbol(2814);
            GibCursorGibCursorProd tmp_struct_109 =
                                    _print_SearchTree(end_from_tagged_indr_1908, tmpcur_3327);
            GibCursor pvrtmp_3330 = tmp_struct_109.field0;
            GibCursor pvrtmp_3331 = tmp_struct_109.field1;

            return (GibCursorGibCursorProd) {end_r_1443, jump_1910};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_3315;
            GibCursor tmpcur_3332 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_3333 = tmpcur_3315 + 8;
            uint16_t tmptag_3334 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_1908 = tmpcur_3332 + tmptag_3334;
            unsigned char wildcard_1913 = gib_print_symbol(2813);
            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_SearchTree(end_from_tagged_indr_1908, tmpcur_3332);
            GibCursor pvrtmp_3335 = tmp_struct_111.field0;
            GibCursor pvrtmp_3336 = tmp_struct_111.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3335, pvrtmp_3336};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3314");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_765(GibCursor end_r_1445,
                               GibCursor l_105_766_875_1053,
                               GibInt n_104_767_876_1054)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3338 = *(GibPackedTag *) l_105_766_875_1053;
    GibCursor tmpcur_3339 = l_105_766_875_1053 + 1;


  switch_3359:
    ;
    switch (tmpval_3338) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1445, n_104_767_876_1054};
            break;
        }

      case 1:
        {
            GibInt tmpval_3340 = *(GibInt *) tmpcur_3339;
            GibCursor tmpcur_3341 = tmpcur_3339 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1445, tmpval_3340};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_3339;
            GibCursor tmpcur_3342 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_3343 = tmpcur_3339 + 8;
            uint16_t tmptag_3344 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_absran_1407 = tmpcur_3342 + tmptag_3344;
            GibInt tmpval_3345 = *(GibInt *) tmpaftercur_3343;
            GibCursor tmpcur_3346 = tmpaftercur_3343 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_113 =
                                 minTree(end_r_1445, tmpcur_3346);
            GibCursor pvrtmp_3347 = tmp_struct_113.field0;
            GibInt pvrtmp_3348 = tmp_struct_113.field1;

            return (GibCursorGibIntProd) {pvrtmp_3347, pvrtmp_3348};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_116 = *(uintptr_t *) tmpcur_3339;
            GibCursor tmpcur_3349 = GIB_UNTAG(tagged_tmpcur_116);
            GibCursor tmpaftercur_3350 = tmpcur_3339 + 8;
            uint16_t tmptag_3351 = GIB_GET_TAG(tagged_tmpcur_116);
            GibCursor end_from_tagged_indr_1914 = tmpcur_3349 + tmptag_3351;
            GibCursor jump_1916 = tmpcur_3339 + 8;
            GibCursorGibIntProd tmp_struct_115 =
                                 caseFn_765(end_from_tagged_indr_1914, tmpcur_3349, n_104_767_876_1054);
            GibCursor pvrtmp_3352 = tmp_struct_115.field0;
            GibInt pvrtmp_3353 = tmp_struct_115.field1;

            return (GibCursorGibIntProd) {end_r_1445, pvrtmp_3353};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_118 = *(uintptr_t *) tmpcur_3339;
            GibCursor tmpcur_3354 = GIB_UNTAG(tagged_tmpcur_118);
            GibCursor tmpaftercur_3355 = tmpcur_3339 + 8;
            uint16_t tmptag_3356 = GIB_GET_TAG(tagged_tmpcur_118);
            GibCursor end_from_tagged_indr_1914 = tmpcur_3354 + tmptag_3356;
            GibCursorGibIntProd tmp_struct_117 =
                                 caseFn_765(end_from_tagged_indr_1914, tmpcur_3354, n_104_767_876_1054);
            GibCursor pvrtmp_3357 = tmp_struct_117.field0;
            GibInt pvrtmp_3358 = tmp_struct_117.field1;

            return (GibCursorGibIntProd) {pvrtmp_3357, pvrtmp_3358};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3338");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_134 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibVector *pts_85_768_929 =
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
        gib_vector_inplace_update(pts_85_768_929, i_132, &arr_elem_127);
        i_132++;
    }

    GibInt n_86_769_930 = gib_get_size_param();
    GibChunk region_2815 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1457 = region_2815.start;
    GibCursor end_r_1457 = region_2815.end;
    GibCursorGibCursorGibCursorProd tmp_struct_119 =
                                     helper(end_r_1457, r_1457, 0, 3);
    GibCursor pvrtmp_2816 = tmp_struct_119.field0;
    GibCursor pvrtmp_2817 = tmp_struct_119.field1;
    GibCursor pvrtmp_2818 = tmp_struct_119.field2;

    gib_shadowstack_push(rstack, r_1457, pvrtmp_2816, Stk, SearchTree_T);

    GibChunk region_2823 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1456 = region_2823.start;
    GibCursor end_r_1456 = region_2823.end;

    frame = gib_shadowstack_pop(rstack);
    r_1457 = frame->ptr;
    pvrtmp_2816 = frame->endptr;

    GibCursor pvrtmp_2834;
    GibCursor pvrtmp_2835;
    GibCursor pvrtmp_2836;
    GibVector *times_124 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2834;
    struct timespec end_pvrtmp_2834;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(2);

    for (long long iters_pvrtmp_2834 = 0; iters_pvrtmp_2834 <
         gib_get_iters_param(); iters_pvrtmp_2834++) {
        if (iters_pvrtmp_2834 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 2, region_2823.end, region_2815.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2834);

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                  loop(pvrtmp_2816, end_r_1456, r_1456, pts_85_768_929, 0, pvrtmp_2817, n_86_769_930);
        GibCursor pvrtmp_2824 = tmp_struct_120.field0;
        GibCursor pvrtmp_2825 = tmp_struct_120.field1;
        GibCursor pvrtmp_2826 = tmp_struct_120.field2;
        GibCursor pvrtmp_2827 = tmp_struct_120.field3;

        pvrtmp_2834 = pvrtmp_2825;
        pvrtmp_2835 = pvrtmp_2826;
        pvrtmp_2836 = pvrtmp_2827;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2834);
        if (iters_pvrtmp_2834 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_121 = gib_difftimespecs(&begin_pvrtmp_2834,
                                                &end_pvrtmp_2834);

        printf("itertime: %lf\n", itertime_121);
        gib_vector_inplace_update(times_124, iters_pvrtmp_2834, &itertime_121);
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
                                  countnodes(end_r_1456, pvrtmp_2835);
    GibCursor pvrtmp_2844 = tmp_struct_126.field0;
    GibCursor pvrtmp_2845 = tmp_struct_126.field1;
    GibInt pvrtmp_2846 = tmp_struct_126.field2;

    printf("%ld", pvrtmp_2846);
    printf("\n");
    return 0;

    int exit_135 = gib_exit();

    return exit_135;
}
