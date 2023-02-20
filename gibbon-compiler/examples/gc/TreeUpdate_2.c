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
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1446,
                                              GibCursor end_r_1447,
                                              GibCursor loc_1445,
                                              GibVector *nums_89_780_952,
                                              GibInt idx_90_781_953,
                                              GibCursor tr_91_782_954,
                                              GibInt n_92_783_955);
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1450,
                                                    GibCursor end_r_1451,
                                                    GibCursor loc_1449,
                                                    GibCursor tr_95_786_971,
                                                    GibInt n_96_787_972);
GibCursorGibIntProd minTree(GibCursor end_r_1453, GibCursor tr_102_793_987);
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1456,
                                                    GibCursor end_r_1457,
                                                    GibCursor loc_1455,
                                                    GibCursor tr_111_798_992,
                                                    GibInt n_112_799_993);
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1459,
                                        GibCursor tr_122_809_1012);
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1461, GibCursor loc_1460,
                                       GibInt s_127_814_1020,
                                       GibInt e_128_815_1021);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_SearchTree(GibCursor end_r_1464, GibCursor end_r_1465, GibCursor loc_1463,
                 GibCursor arg_723_843_1031);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_SearchTree(GibCursor end_r_1468, GibCursor end_r_1469,
                              GibCursor loc_1467, GibCursor arg_732_852_1040);
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1471,
                                            GibCursor arg_741_861_1049);
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1473,
                                         GibCursor arg_750_868_1056);
GibCursorGibIntProd caseFn_773(GibCursor end_r_1475,
                               GibCursor l_105_774_895_1083,
                               GibInt n_104_775_896_1084);
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
    gib_add_symbol(2849, ")");
    gib_add_symbol(2850, "(Null");
    gib_add_symbol(2851, "(Node");
    gib_add_symbol(2852, "(Leaf");
    gib_add_symbol(2853, " ->r ");
    gib_add_symbol(2854, " ->i ");
    gib_add_symbol(2855, " ");
}
GibCursorGibCursorGibCursorGibCursorProd loop(GibCursor end_r_1446,
                                              GibCursor end_r_1447,
                                              GibCursor loc_1445,
                                              GibVector *nums_89_780_952,
                                              GibInt idx_90_781_953,
                                              GibCursor tr_91_782_954,
                                              GibInt n_92_783_955)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1445 + 26 > end_r_1447) {
        gib_grow_region(&loc_1445, &end_r_1447);
    }

    GibBool fltIf_904_956 = n_92_783_955 == 0;

    if (fltIf_904_956) {
        if (loc_1445 + 18 > end_r_1447) {
            gib_grow_region(&loc_1445, &end_r_1447);
        }
        gib_indirection_barrier(loc_1445, end_r_1447, tr_91_782_954, end_r_1446,
                                SearchTree_T);

        GibCursor end_2120 = loc_1445 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1446,
                                                           end_r_1447, loc_1445,
                                                           end_2120};
    } else {
        GibInt fltPrm_905_957 = idx_90_781_953 + 1;
        GibInt fltPrm_906_959 = gib_vector_length(nums_89_780_952);
        GibInt idx1_93_784_960 = fltPrm_905_957 % fltPrm_906_959;
        GibInt *tmp_7;

        tmp_7 = (GibInt *) gib_vector_nth(nums_89_780_952, idx1_93_784_960);

        GibInt j_94_785_963 = *tmp_7;
        GibInt fltPrm_908_964 = j_94_785_963 % 2;
        GibBool fltIf_907_965 = fltPrm_908_964 == 0;

        if (fltIf_907_965) {
            gib_shadowstack_push(rstack, tr_91_782_954, end_r_1446, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1445, end_r_1447, Stk,
                                 SearchTree_T);

            GibChunk region_2892 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1496 = region_2892.start;
            GibCursor end_r_1496 = region_2892.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1445 = frame->ptr;
            end_r_1447 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_91_782_954 = frame->ptr;
            end_r_1446 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_3 =
                                                      treeInsert(end_r_1446, end_r_1496, r_1496, tr_91_782_954, j_94_785_963);
            GibCursor pvrtmp_2893 = tmp_struct_3.field0;
            GibCursor pvrtmp_2894 = tmp_struct_3.field1;
            GibCursor pvrtmp_2895 = tmp_struct_3.field2;
            GibCursor pvrtmp_2896 = tmp_struct_3.field3;
            GibInt fltAppE_910_967 = n_92_783_955 - 1;
            // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_4 =
                                                      return loop(pvrtmp_2894, end_r_1447, loc_1445, nums_89_780_952, idx1_93_784_960, pvrtmp_2895, fltAppE_910_967);
            // GibCursor pvrtmp_2901 = tmp_struct_4.field0;
            // GibCursor pvrtmp_2902 = tmp_struct_4.field1;
            // GibCursor pvrtmp_2903 = tmp_struct_4.field2;
            // GibCursor pvrtmp_2904 = tmp_struct_4.field3;

            // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2893,
            //                                                    pvrtmp_2902,
            //                                                    pvrtmp_2903,
            //                                                    pvrtmp_2904};
        } else {
            GibInt fltAppE_912_968 = j_94_785_963 - 1;

            gib_shadowstack_push(rstack, tr_91_782_954, end_r_1446, Stk,
                                 SearchTree_T);
            gib_shadowstack_push(wstack, loc_1445, end_r_1447, Stk,
                                 SearchTree_T);

            GibChunk region_2911 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1505 = region_2911.start;
            GibCursor end_r_1505 = region_2911.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1445 = frame->ptr;
            end_r_1447 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tr_91_782_954 = frame->ptr;
            end_r_1446 = frame->endptr;

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_5 =
                                                      treeDelete(end_r_1446, end_r_1505, r_1505, tr_91_782_954, fltAppE_912_968);
            GibCursor pvrtmp_2912 = tmp_struct_5.field0;
            GibCursor pvrtmp_2913 = tmp_struct_5.field1;
            GibCursor pvrtmp_2914 = tmp_struct_5.field2;
            GibCursor pvrtmp_2915 = tmp_struct_5.field3;
            GibInt fltAppE_913_970 = n_92_783_955 - 1;
            // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                      return loop(pvrtmp_2913, end_r_1447, loc_1445, nums_89_780_952, idx1_93_784_960, pvrtmp_2914, fltAppE_913_970);
            // GibCursor pvrtmp_2920 = tmp_struct_6.field0;
            // GibCursor pvrtmp_2921 = tmp_struct_6.field1;
            // GibCursor pvrtmp_2922 = tmp_struct_6.field2;
            // GibCursor pvrtmp_2923 = tmp_struct_6.field3;

            // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2912,
            //                                                    pvrtmp_2921,
            //                                                    pvrtmp_2922,
            //                                                    pvrtmp_2923};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeDelete(GibCursor end_r_1450,
                                                    GibCursor end_r_1451,
                                                    GibCursor loc_1449,
                                                    GibCursor tr_95_786_971,
                                                    GibInt n_96_787_972)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1449 + 26 > end_r_1451) {
        gib_grow_region(&loc_1449, &end_r_1451);
    }

    GibPackedTag tmpval_2930 = *(GibPackedTag *) tr_95_786_971;
    GibCursor tmpcur_2931 = tr_95_786_971 + 1;


  switch_3021:
    ;
    switch (tmpval_2930) {

      case 0:
        {
            *(GibPackedTag *) loc_1449 = 0;

            GibCursor writetag_2135 = loc_1449 + 1;
            GibCursor after_tag_2136 = loc_1449 + 1;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1450,
                                                               end_r_1451,
                                                               loc_1449,
                                                               after_tag_2136};
            break;
        }

      case 1:
        {
            GibInt tmpval_2936 = *(GibInt *) tmpcur_2931;
            GibCursor tmpcur_2937 = tmpcur_2931 + sizeof(GibInt);
            GibBool fltIf_914_974 = tmpval_2936 == n_96_787_972;

            if (fltIf_914_974) {
                *(GibPackedTag *) loc_1449 = 0;

                GibCursor writetag_2144 = loc_1449 + 1;
                GibCursor after_tag_2145 = loc_1449 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1450,
                                                                   end_r_1451,
                                                                   loc_1449,
                                                                   after_tag_2145};
            } else {
                *(GibPackedTag *) loc_1449 = 1;

                GibCursor writetag_2151 = loc_1449 + 1;
                GibCursor after_tag_2152 = loc_1449 + 1;

                *(GibInt *) after_tag_2152 = tmpval_2936;

                GibCursor writecur_2156 = after_tag_2152 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1450,
                                                                   end_r_1451,
                                                                   loc_1449,
                                                                   writecur_2156};
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2931;
            GibCursor tmpcur_2946 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2947 = tmpcur_2931 + 8;
            uint16_t tmptag_2948 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_absran_1392 = tmpcur_2946 + tmptag_2948;
            GibInt tmpval_2949 = *(GibInt *) tmpaftercur_2947;
            GibCursor tmpcur_2950 = tmpaftercur_2947 + sizeof(GibInt);
            GibBool fltIf_915_978 = tmpval_2949 == n_96_787_972;

            if (fltIf_915_978) {
                GibCursorGibIntProd tmp_struct_11 =
                                     minTree(end_from_tagged_absran_1392, tmpcur_2946);
                GibCursor pvrtmp_2951 = tmp_struct_11.field0;
                GibInt pvrtmp_2952 = tmp_struct_11.field1;
                GibCursor loc_1528 = loc_1449 + 17;

                *(GibPackedTag *) loc_1449 = 3;

                GibCursor writetag_2170 = loc_1449 + 1;

                // if (loc_1528 + 18 > end_r_1451) {
                //     gib_grow_region(&loc_1528, &end_r_1451);
                // }
                gib_indirection_barrier(loc_1528, end_r_1451, tmpcur_2950,
                                        end_r_1450, SearchTree_T);

                GibCursor end_2165 = loc_1528 + 9;
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_12 =
                                                          treeDelete(end_from_tagged_absran_1392, end_r_1451, end_2165, tmpcur_2946, pvrtmp_2952);
                GibCursor pvrtmp_2955 = tmp_struct_12.field0;
                GibCursor pvrtmp_2956 = tmp_struct_12.field1;
                GibCursor pvrtmp_2957 = tmp_struct_12.field2;
                GibCursor pvrtmp_2958 = tmp_struct_12.field3;
                uint16_t offset_13 = end_r_1451 - loc_1528;
                uintptr_t ran_1395 = GIB_STORE_TAG(loc_1528, offset_13);
                GibCursor after_tag_2171 = loc_1449 + 1;

                *(uintptr_t *) after_tag_2171 = ran_1395;

                GibCursor writecur_2175 = after_tag_2171 + 8;

                *(GibInt *) writecur_2175 = pvrtmp_2952;

                GibCursor writecur_2176 = writecur_2175 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2955,
                                                                   pvrtmp_2956,
                                                                   loc_1449,
                                                                   pvrtmp_2958};
            } else {
                GibBool fltIf_918_982 = tmpval_2949 < n_96_787_972;

                if (fltIf_918_982) {
                    GibCursor loc_1528 = loc_1449 + 17;

                    *(GibPackedTag *) loc_1449 = 3;

                    GibCursor writetag_2188 = loc_1449 + 1;

                    // if (loc_1528 + 18 > end_r_1451) {
                    //     gib_grow_region(&loc_1528, &end_r_1451);
                    // }
                    gib_indirection_barrier(loc_1528, end_r_1451, tmpcur_2950,
                                            end_r_1450, SearchTree_T);

                    GibCursor end_2183 = loc_1528 + 9;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_17 =
                                                              treeDelete(end_from_tagged_absran_1392, end_r_1451, end_2183, tmpcur_2946, n_96_787_972);
                    GibCursor pvrtmp_2969 = tmp_struct_17.field0;
                    GibCursor pvrtmp_2970 = tmp_struct_17.field1;
                    GibCursor pvrtmp_2971 = tmp_struct_17.field2;
                    GibCursor pvrtmp_2972 = tmp_struct_17.field3;
                    uint16_t offset_18 = end_r_1451 - loc_1528;
                    uintptr_t ran_1396 = GIB_STORE_TAG(loc_1528, offset_18);
                    GibCursor after_tag_2189 = loc_1449 + 1;

                    *(uintptr_t *) after_tag_2189 = ran_1396;

                    GibCursor writecur_2193 = after_tag_2189 + 8;

                    *(GibInt *) writecur_2193 = tmpval_2949;

                    GibCursor writecur_2194 = writecur_2193 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2969,
                                                                       pvrtmp_2970,
                                                                       loc_1449,
                                                                       pvrtmp_2972};
                } else {
                    GibCursor loc_1528 = loc_1449 + 17;

                    *(GibPackedTag *) loc_1449 = 3;

                    GibCursor writetag_2206 = loc_1449 + 1;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_22 =
                                                              treeDelete(end_r_1450, end_r_1451, loc_1528, tmpcur_2950, n_96_787_972);
                    GibCursor pvrtmp_2981 = tmp_struct_22.field0;
                    GibCursor pvrtmp_2982 = tmp_struct_22.field1;
                    GibCursor pvrtmp_2983 = tmp_struct_22.field2;
                    GibCursor pvrtmp_2984 = tmp_struct_22.field3;

                    // if (pvrtmp_2984 + 18 > pvrtmp_2982) {
                    //     gib_grow_region(&pvrtmp_2984, &pvrtmp_2982);
                    // }
                    gib_indirection_barrier(pvrtmp_2984, pvrtmp_2982,
                                            tmpcur_2946,
                                            end_from_tagged_absran_1392,
                                            SearchTree_T);

                    GibCursor end_2204 = pvrtmp_2984 + 9;
                    uint16_t offset_23 = end_r_1451 - loc_1528;
                    uintptr_t ran_1397 = GIB_STORE_TAG(loc_1528, offset_23);
                    GibCursor after_tag_2207 = loc_1449 + 1;

                    *(uintptr_t *) after_tag_2207 = ran_1397;

                    GibCursor writecur_2211 = after_tag_2207 + 8;

                    *(GibInt *) writecur_2211 = tmpval_2949;

                    GibCursor writecur_2212 = writecur_2211 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2981,
                                                                       pvrtmp_2982,
                                                                       loc_1449,
                                                                       end_2204};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_2931;
            GibCursor tmpcur_2995 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_2996 = tmpcur_2931 + 8;
            uint16_t tmptag_2997 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_1899 = tmpcur_2995 + tmptag_2997;
            GibCursor jump_1901 = tmpcur_2931 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                      treeDelete(end_from_tagged_indr_1899, end_r_1451, loc_1449, tmpcur_2995, n_96_787_972);
            GibCursor pvrtmp_2998 = tmp_struct_28.field0;
            GibCursor pvrtmp_2999 = tmp_struct_28.field1;
            GibCursor pvrtmp_3000 = tmp_struct_28.field2;
            GibCursor pvrtmp_3001 = tmp_struct_28.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1450,
                                                               pvrtmp_2999,
                                                               pvrtmp_3000,
                                                               pvrtmp_3001};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_31 = *(uintptr_t *) tmpcur_2931;
            GibCursor tmpcur_3008 = GIB_UNTAG(tagged_tmpcur_31);
            GibCursor tmpaftercur_3009 = tmpcur_2931 + 8;
            uint16_t tmptag_3010 = GIB_GET_TAG(tagged_tmpcur_31);
            GibCursor end_from_tagged_indr_1899 = tmpcur_3008 + tmptag_3010;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_30 =
                                                      treeDelete(end_from_tagged_indr_1899, end_r_1451, loc_1449, tmpcur_3008, n_96_787_972);
            GibCursor pvrtmp_3011 = tmp_struct_30.field0;
            GibCursor pvrtmp_3012 = tmp_struct_30.field1;
            GibCursor pvrtmp_3013 = tmp_struct_30.field2;
            GibCursor pvrtmp_3014 = tmp_struct_30.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3011,
                                                               pvrtmp_3012,
                                                               pvrtmp_3013,
                                                               pvrtmp_3014};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2930");
            exit(1);
        }
    }
}
GibCursorGibIntProd minTree(GibCursor end_r_1453, GibCursor tr_102_793_987)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3022 = *(GibPackedTag *) tr_102_793_987;
    GibCursor tmpcur_3023 = tr_102_793_987 + 1;


  switch_3043:
    ;
    switch (tmpval_3022) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1453, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_3024 = *(GibInt *) tmpcur_3023;
            GibCursor tmpcur_3025 = tmpcur_3023 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1453, tmpval_3024};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_3023;
            GibCursor tmpcur_3026 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_3027 = tmpcur_3023 + 8;
            uint16_t tmptag_3028 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_absran_1401 = tmpcur_3026 + tmptag_3028;
            GibInt tmpval_3029 = *(GibInt *) tmpaftercur_3027;
            GibCursor tmpcur_3030 = tmpaftercur_3027 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_35 =
                                 caseFn_773(end_r_1453, tmpcur_3030, tmpval_3029);
            GibCursor pvrtmp_3031 = tmp_struct_35.field0;
            GibInt pvrtmp_3032 = tmp_struct_35.field1;

            return (GibCursorGibIntProd) {pvrtmp_3031, pvrtmp_3032};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) tmpcur_3023;
            GibCursor tmpcur_3033 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_3034 = tmpcur_3023 + 8;
            uint16_t tmptag_3035 = GIB_GET_TAG(tagged_tmpcur_38);
            GibCursor end_from_tagged_indr_1904 = tmpcur_3033 + tmptag_3035;
            GibCursor jump_1906 = tmpcur_3023 + 8;
            GibCursorGibIntProd tmp_struct_37 =
                                 minTree(end_from_tagged_indr_1904, tmpcur_3033);
            GibCursor pvrtmp_3036 = tmp_struct_37.field0;
            GibInt pvrtmp_3037 = tmp_struct_37.field1;

            return (GibCursorGibIntProd) {end_r_1453, pvrtmp_3037};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_3023;
            GibCursor tmpcur_3038 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_3039 = tmpcur_3023 + 8;
            uint16_t tmptag_3040 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_1904 = tmpcur_3038 + tmptag_3040;
            GibCursorGibIntProd tmp_struct_39 =
                                 minTree(end_from_tagged_indr_1904, tmpcur_3038);
            GibCursor pvrtmp_3041 = tmp_struct_39.field0;
            GibInt pvrtmp_3042 = tmp_struct_39.field1;

            return (GibCursorGibIntProd) {pvrtmp_3041, pvrtmp_3042};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3022");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd treeInsert(GibCursor end_r_1456,
                                                    GibCursor end_r_1457,
                                                    GibCursor loc_1455,
                                                    GibCursor tr_111_798_992,
                                                    GibInt n_112_799_993)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1455 + 26 > end_r_1457) {
        gib_grow_region(&loc_1455, &end_r_1457);
    }

    GibPackedTag tmpval_3044 = *(GibPackedTag *) tr_111_798_992;
    GibCursor tmpcur_3045 = tr_111_798_992 + 1;


  switch_3139:
    ;
    switch (tmpval_3044) {

      case 0:
        {
            *(GibPackedTag *) loc_1455 = 1;

            GibCursor writetag_2245 = loc_1455 + 1;
            GibCursor after_tag_2246 = loc_1455 + 1;

            *(GibInt *) after_tag_2246 = n_112_799_993;

            GibCursor writecur_2250 = after_tag_2246 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1456,
                                                               end_r_1457,
                                                               loc_1455,
                                                               writecur_2250};
            break;
        }

      case 1:
        {
            GibInt tmpval_3050 = *(GibInt *) tmpcur_3045;
            GibCursor tmpcur_3051 = tmpcur_3045 + sizeof(GibInt);
            GibBool fltIf_923_995 = n_112_799_993 == tmpval_3050;

            if (fltIf_923_995) {
                *(GibPackedTag *) loc_1455 = 1;

                GibCursor writetag_2255 = loc_1455 + 1;
                GibCursor after_tag_2256 = loc_1455 + 1;

                *(GibInt *) after_tag_2256 = tmpval_3050;

                GibCursor writecur_2260 = after_tag_2256 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1456,
                                                                   end_r_1457,
                                                                   loc_1455,
                                                                   writecur_2260};
            } else {
                GibBool fltIf_924_996 = n_112_799_993 < tmpval_3050;

                if (fltIf_924_996) {
                    GibCursor loc_1597 = loc_1455 + 17;

                    *(GibPackedTag *) loc_1455 = 3;

                    GibCursor writetag_2278 = loc_1455 + 1;

                    *(GibPackedTag *) loc_1597 = 1;

                    GibCursor writetag_2263 = loc_1597 + 1;
                    GibCursor after_tag_2264 = loc_1597 + 1;

                    *(GibInt *) after_tag_2264 = n_112_799_993;

                    GibCursor writecur_2268 = after_tag_2264 + sizeof(GibInt);

                    *(GibPackedTag *) writecur_2268 = 0;

                    GibCursor writetag_2271 = writecur_2268 + 1;
                    GibCursor after_tag_2272 = writecur_2268 + 1;
                    uint16_t offset_41 = end_r_1457 - loc_1597;
                    uintptr_t ran_1404 = GIB_STORE_TAG(loc_1597, offset_41);
                    GibCursor after_tag_2279 = loc_1455 + 1;

                    *(uintptr_t *) after_tag_2279 = ran_1404;

                    GibCursor writecur_2283 = after_tag_2279 + 8;

                    *(GibInt *) writecur_2283 = tmpval_3050;

                    GibCursor writecur_2284 = writecur_2283 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1456,
                                                                       end_r_1457,
                                                                       loc_1455,
                                                                       after_tag_2272};
                } else {
                    GibCursor loc_1597 = loc_1455 + 17;

                    *(GibPackedTag *) loc_1455 = 3;

                    GibCursor writetag_2305 = loc_1455 + 1;

                    *(GibPackedTag *) loc_1597 = 0;

                    GibCursor writetag_2290 = loc_1597 + 1;
                    GibCursor after_tag_2291 = loc_1597 + 1;

                    *(GibPackedTag *) after_tag_2291 = 1;

                    GibCursor writetag_2297 = after_tag_2291 + 1;
                    GibCursor after_tag_2298 = after_tag_2291 + 1;

                    *(GibInt *) after_tag_2298 = n_112_799_993;

                    GibCursor writecur_2302 = after_tag_2298 + sizeof(GibInt);
                    uint16_t offset_42 = end_r_1457 - loc_1597;
                    uintptr_t ran_1405 = GIB_STORE_TAG(loc_1597, offset_42);
                    GibCursor after_tag_2306 = loc_1455 + 1;

                    *(uintptr_t *) after_tag_2306 = ran_1405;

                    GibCursor writecur_2310 = after_tag_2306 + 8;

                    *(GibInt *) writecur_2310 = tmpval_3050;

                    GibCursor writecur_2311 = writecur_2310 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1456,
                                                                       end_r_1457,
                                                                       loc_1455,
                                                                       writecur_2302};
                }
            }
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_60 = *(uintptr_t *) tmpcur_3045;
            GibCursor tmpcur_3072 = GIB_UNTAG(tagged_tmpcur_60);
            GibCursor tmpaftercur_3073 = tmpcur_3045 + 8;
            uint16_t tmptag_3074 = GIB_GET_TAG(tagged_tmpcur_60);
            GibCursor end_from_tagged_absran_1409 = tmpcur_3072 + tmptag_3074;
            GibInt tmpval_3075 = *(GibInt *) tmpaftercur_3073;
            GibCursor tmpcur_3076 = tmpaftercur_3073 + sizeof(GibInt);
            GibBool fltIf_929_1004 = tmpval_3075 == n_112_799_993;

            if (fltIf_929_1004) {
                GibCursor loc_1597 = loc_1455 + 17;

                *(GibPackedTag *) loc_1455 = 3;

                GibCursor writetag_2326 = loc_1455 + 1;

                // if (loc_1597 + 18 > end_r_1457) {
                //     gib_grow_region(&loc_1597, &end_r_1457);
                // }
                gib_indirection_barrier(loc_1597, end_r_1457, tmpcur_3076,
                                        end_r_1456, SearchTree_T);

                GibCursor end_2321 = loc_1597 + 9;

                // if (end_2321 + 18 > end_r_1457) {
                //     gib_grow_region(&end_2321, &end_r_1457);
                // }
                gib_indirection_barrier(end_2321, end_r_1457, tmpcur_3072,
                                        end_from_tagged_absran_1409,
                                        SearchTree_T);

                GibCursor end_2324 = end_2321 + 9;
                uint16_t offset_43 = end_r_1457 - loc_1597;
                uintptr_t ran_1412 = GIB_STORE_TAG(loc_1597, offset_43);
                GibCursor after_tag_2327 = loc_1455 + 1;

                *(uintptr_t *) after_tag_2327 = ran_1412;

                GibCursor writecur_2331 = after_tag_2327 + 8;

                *(GibInt *) writecur_2331 = tmpval_3075;

                GibCursor writecur_2332 = writecur_2331 + sizeof(GibInt);

                return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1456,
                                                                   end_r_1457,
                                                                   loc_1455,
                                                                   end_2324};
            } else {
                GibBool fltIf_932_1007 = n_112_799_993 < tmpval_3075;

                if (fltIf_932_1007) {
                    GibCursor loc_1597 = loc_1455 + 17;

                    *(GibPackedTag *) loc_1455 = 3;

                    GibCursor writetag_2344 = loc_1455 + 1;

                    // if (loc_1597 + 18 > end_r_1457) {
                    //     gib_grow_region(&loc_1597, &end_r_1457);
                    // }
                    gib_indirection_barrier(loc_1597, end_r_1457, tmpcur_3076,
                                            end_r_1456, SearchTree_T);

                    GibCursor end_2339 = loc_1597 + 9;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                              treeInsert(end_from_tagged_absran_1409, end_r_1457, end_2339, tmpcur_3072, n_112_799_993);
                    GibCursor pvrtmp_3087 = tmp_struct_50.field0;
                    GibCursor pvrtmp_3088 = tmp_struct_50.field1;
                    GibCursor pvrtmp_3089 = tmp_struct_50.field2;
                    GibCursor pvrtmp_3090 = tmp_struct_50.field3;
                    uint16_t offset_51 = end_r_1457 - loc_1597;
                    uintptr_t ran_1413 = GIB_STORE_TAG(loc_1597, offset_51);
                    GibCursor after_tag_2345 = loc_1455 + 1;

                    *(uintptr_t *) after_tag_2345 = ran_1413;

                    GibCursor writecur_2349 = after_tag_2345 + 8;

                    *(GibInt *) writecur_2349 = tmpval_3075;

                    GibCursor writecur_2350 = writecur_2349 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3087,
                                                                       pvrtmp_3088,
                                                                       loc_1455,
                                                                       pvrtmp_3090};
                } else {
                    GibCursor loc_1597 = loc_1455 + 17;

                    *(GibPackedTag *) loc_1455 = 3;

                    GibCursor writetag_2362 = loc_1455 + 1;
                    GibCursorGibCursorGibCursorGibCursorProd tmp_struct_55 =
                                                              treeInsert(end_r_1456, end_r_1457, loc_1597, tmpcur_3076, n_112_799_993);
                    GibCursor pvrtmp_3099 = tmp_struct_55.field0;
                    GibCursor pvrtmp_3100 = tmp_struct_55.field1;
                    GibCursor pvrtmp_3101 = tmp_struct_55.field2;
                    GibCursor pvrtmp_3102 = tmp_struct_55.field3;

                    // if (pvrtmp_3102 + 18 > pvrtmp_3100) {
                    //     gib_grow_region(&pvrtmp_3102, &pvrtmp_3100);
                    // }
                    gib_indirection_barrier(pvrtmp_3102, pvrtmp_3100,
                                            tmpcur_3072,
                                            end_from_tagged_absran_1409,
                                            SearchTree_T);

                    GibCursor end_2360 = pvrtmp_3102 + 9;
                    uint16_t offset_56 = end_r_1457 - loc_1597;
                    uintptr_t ran_1414 = GIB_STORE_TAG(loc_1597, offset_56);
                    GibCursor after_tag_2363 = loc_1455 + 1;

                    *(uintptr_t *) after_tag_2363 = ran_1414;

                    GibCursor writecur_2367 = after_tag_2363 + 8;

                    *(GibInt *) writecur_2367 = tmpval_3075;

                    GibCursor writecur_2368 = writecur_2367 + sizeof(GibInt);

                    return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3099,
                                                                       pvrtmp_3100,
                                                                       loc_1455,
                                                                       end_2360};
                }
            }
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_62 = *(uintptr_t *) tmpcur_3045;
            GibCursor tmpcur_3113 = GIB_UNTAG(tagged_tmpcur_62);
            GibCursor tmpaftercur_3114 = tmpcur_3045 + 8;
            uint16_t tmptag_3115 = GIB_GET_TAG(tagged_tmpcur_62);
            GibCursor end_from_tagged_indr_1909 = tmpcur_3113 + tmptag_3115;
            GibCursor jump_1911 = tmpcur_3045 + 8;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_61 =
                                                      treeInsert(end_from_tagged_indr_1909, end_r_1457, loc_1455, tmpcur_3113, n_112_799_993);
            GibCursor pvrtmp_3116 = tmp_struct_61.field0;
            GibCursor pvrtmp_3117 = tmp_struct_61.field1;
            GibCursor pvrtmp_3118 = tmp_struct_61.field2;
            GibCursor pvrtmp_3119 = tmp_struct_61.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1456,
                                                               pvrtmp_3117,
                                                               pvrtmp_3118,
                                                               pvrtmp_3119};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_64 = *(uintptr_t *) tmpcur_3045;
            GibCursor tmpcur_3126 = GIB_UNTAG(tagged_tmpcur_64);
            GibCursor tmpaftercur_3127 = tmpcur_3045 + 8;
            uint16_t tmptag_3128 = GIB_GET_TAG(tagged_tmpcur_64);
            GibCursor end_from_tagged_indr_1909 = tmpcur_3126 + tmptag_3128;
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_63 =
                                                      treeInsert(end_from_tagged_indr_1909, end_r_1457, loc_1455, tmpcur_3126, n_112_799_993);
            GibCursor pvrtmp_3129 = tmp_struct_63.field0;
            GibCursor pvrtmp_3130 = tmp_struct_63.field1;
            GibCursor pvrtmp_3131 = tmp_struct_63.field2;
            GibCursor pvrtmp_3132 = tmp_struct_63.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3129,
                                                               pvrtmp_3130,
                                                               pvrtmp_3131,
                                                               pvrtmp_3132};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3044");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd countnodes(GibCursor end_r_1459,
                                        GibCursor tr_122_809_1012)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3140 = *(GibPackedTag *) tr_122_809_1012;
    GibCursor tmpcur_3141 = tr_122_809_1012 + 1;


  switch_3167:
    ;
    switch (tmpval_3140) {

      case 0:
        {
            GibCursor jump_1844 = tr_122_809_1012 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_1459, jump_1844, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_3142 = *(GibInt *) tmpcur_3141;
            GibCursor tmpcur_3143 = tmpcur_3141 + sizeof(GibInt);
            GibCursor jump_1845 = tmpcur_3141 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_1459, jump_1845, 1};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_70 = *(uintptr_t *) tmpcur_3141;
            GibCursor tmpcur_3144 = GIB_UNTAG(tagged_tmpcur_70);
            GibCursor tmpaftercur_3145 = tmpcur_3141 + 8;
            uint16_t tmptag_3146 = GIB_GET_TAG(tagged_tmpcur_70);
            GibCursor end_from_tagged_absran_1418 = tmpcur_3144 + tmptag_3146;
            GibInt tmpval_3147 = *(GibInt *) tmpaftercur_3145;
            GibCursor tmpcur_3148 = tmpaftercur_3145 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_68 =
                                          countnodes(end_r_1459, tmpcur_3148);
            GibCursor pvrtmp_3149 = tmp_struct_68.field0;
            GibCursor pvrtmp_3150 = tmp_struct_68.field1;
            GibInt pvrtmp_3151 = tmp_struct_68.field2;
            GibInt fltPrm_937_1018 = 1 + pvrtmp_3151;
            GibCursorGibCursorGibIntProd tmp_struct_69 =
                                          countnodes(end_from_tagged_absran_1418, tmpcur_3144);
            GibCursor pvrtmp_3152 = tmp_struct_69.field0;
            GibCursor pvrtmp_3153 = tmp_struct_69.field1;
            GibInt pvrtmp_3154 = tmp_struct_69.field2;
            GibInt tailprim_1850 = fltPrm_937_1018 + pvrtmp_3154;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3152, pvrtmp_3153,
                                                   tailprim_1850};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_72 = *(uintptr_t *) tmpcur_3141;
            GibCursor tmpcur_3155 = GIB_UNTAG(tagged_tmpcur_72);
            GibCursor tmpaftercur_3156 = tmpcur_3141 + 8;
            uint16_t tmptag_3157 = GIB_GET_TAG(tagged_tmpcur_72);
            GibCursor end_from_tagged_indr_1914 = tmpcur_3155 + tmptag_3157;
            GibCursor jump_1916 = tmpcur_3141 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_71 =
                                          countnodes(end_from_tagged_indr_1914, tmpcur_3155);
            GibCursor pvrtmp_3158 = tmp_struct_71.field0;
            GibCursor pvrtmp_3159 = tmp_struct_71.field1;
            GibInt pvrtmp_3160 = tmp_struct_71.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_1459, jump_1916,
                                                   pvrtmp_3160};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_3141;
            GibCursor tmpcur_3161 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_3162 = tmpcur_3141 + 8;
            uint16_t tmptag_3163 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_1914 = tmpcur_3161 + tmptag_3163;
            GibCursorGibCursorGibIntProd tmp_struct_73 =
                                          countnodes(end_from_tagged_indr_1914, tmpcur_3161);
            GibCursor pvrtmp_3164 = tmp_struct_73.field0;
            GibCursor pvrtmp_3165 = tmp_struct_73.field1;
            GibInt pvrtmp_3166 = tmp_struct_73.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_3164, pvrtmp_3165,
                                                   pvrtmp_3166};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3140");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd helper(GibCursor end_r_1461, GibCursor loc_1460,
                                       GibInt s_127_814_1020,
                                       GibInt e_128_815_1021)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1460 + 26 > end_r_1461) {
        gib_grow_region(&loc_1460, &end_r_1461);
    }

    GibBool fltIf_940_1022 = e_128_815_1021 < s_127_814_1020;

    if (fltIf_940_1022) {
        *(GibPackedTag *) loc_1460 = 0;

        GibCursor writetag_2402 = loc_1460 + 1;
        GibCursor after_tag_2403 = loc_1460 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_1461, loc_1460,
                                                  after_tag_2403};
    } else {
        GibBool fltIf_941_1023 = s_127_814_1020 == e_128_815_1021;

        if (fltIf_941_1023) {
            *(GibPackedTag *) loc_1460 = 1;

            GibCursor writetag_2409 = loc_1460 + 1;
            GibCursor after_tag_2410 = loc_1460 + 1;

            *(GibInt *) after_tag_2410 = s_127_814_1020;

            GibCursor writecur_2414 = after_tag_2410 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {end_r_1461, loc_1460,
                                                      writecur_2414};
        } else {
            GibInt fltPrm_943_1024 = e_128_815_1021 - s_127_814_1020;
            GibInt fltPrm_942_1025 = fltPrm_943_1024 / 2;
            GibInt m_129_816_1026 = fltPrm_942_1025 + s_127_814_1020;
            GibInt fltAppE_945_1027 = m_129_816_1026 - 1;
            GibCursor loc_1697 = loc_1460 + 17;

            *(GibPackedTag *) loc_1460 = 3;

            GibCursor writetag_2421 = loc_1460 + 1;
            GibCursorGibCursorGibCursorProd tmp_struct_75 =
                                             helper(end_r_1461, loc_1697, s_127_814_1020, fltAppE_945_1027);
            GibCursor pvrtmp_3176 = tmp_struct_75.field0;
            GibCursor pvrtmp_3177 = tmp_struct_75.field1;
            GibCursor pvrtmp_3178 = tmp_struct_75.field2;
            GibInt fltAppE_947_1029 = m_129_816_1026 + 1;
            GibCursorGibCursorGibCursorProd tmp_struct_76 =
                                             helper(pvrtmp_3176, pvrtmp_3178, fltAppE_947_1029, e_128_815_1021);
            GibCursor pvrtmp_3183 = tmp_struct_76.field0;
            GibCursor pvrtmp_3184 = tmp_struct_76.field1;
            GibCursor pvrtmp_3185 = tmp_struct_76.field2;
            uint16_t offset_77 = end_r_1461 - loc_1697;
            uintptr_t ran_1421 = GIB_STORE_TAG(loc_1697, offset_77);
            GibCursor after_tag_2422 = loc_1460 + 1;

            *(uintptr_t *) after_tag_2422 = ran_1421;

            GibCursor writecur_2426 = after_tag_2422 + 8;

            *(GibInt *) writecur_2426 = m_129_816_1026;

            GibCursor writecur_2427 = writecur_2426 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorProd) {pvrtmp_3183, loc_1460,
                                                      pvrtmp_3185};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_SearchTree(GibCursor end_r_1464,
                                                                   GibCursor end_r_1465,
                                                                   GibCursor loc_1463,
                                                                   GibCursor arg_723_843_1031)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1463 + 26 > end_r_1465) {
        gib_grow_region(&loc_1463, &end_r_1465);
    }

    GibPackedTag tmpval_3194 = *(GibPackedTag *) arg_723_843_1031;
    GibCursor tmpcur_3195 = arg_723_843_1031 + 1;


  switch_3261:
    ;
    switch (tmpval_3194) {

      case 0:
        {
            GibCursor jump_1854 = arg_723_843_1031 + 1;

            *(GibPackedTag *) loc_1463 = 0;

            GibCursor writetag_2434 = loc_1463 + 1;
            GibCursor after_tag_2435 = loc_1463 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1464,
                                                                        end_r_1465,
                                                                        jump_1854,
                                                                        loc_1463,
                                                                        after_tag_2435};
            break;
        }

      case 1:
        {
            GibInt tmpval_3200 = *(GibInt *) tmpcur_3195;
            GibCursor tmpcur_3201 = tmpcur_3195 + sizeof(GibInt);
            GibCursor jump_1856 = tmpcur_3195 + 8;

            *(GibPackedTag *) loc_1463 = 1;

            GibCursor writetag_2443 = loc_1463 + 1;
            GibCursor after_tag_2444 = loc_1463 + 1;

            *(GibInt *) after_tag_2444 = tmpval_3200;

            GibCursor writecur_2448 = after_tag_2444 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1464,
                                                                        end_r_1465,
                                                                        jump_1856,
                                                                        loc_1463,
                                                                        writecur_2448};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_3195;
            GibCursor tmpcur_3206 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_3207 = tmpcur_3195 + 8;
            uint16_t tmptag_3208 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_absran_1423 = tmpcur_3206 + tmptag_3208;
            GibInt tmpval_3209 = *(GibInt *) tmpaftercur_3207;
            GibCursor tmpcur_3210 = tmpaftercur_3207 + sizeof(GibInt);
            GibCursor loc_1725 = loc_1463 + 17;

            *(GibPackedTag *) loc_1463 = 3;

            GibCursor writetag_2460 = loc_1463 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_81 =
                                                               _copy_SearchTree(end_r_1464, end_r_1465, loc_1725, tmpcur_3210);
            GibCursor pvrtmp_3211 = tmp_struct_81.field0;
            GibCursor pvrtmp_3212 = tmp_struct_81.field1;
            GibCursor pvrtmp_3213 = tmp_struct_81.field2;
            GibCursor pvrtmp_3214 = tmp_struct_81.field3;
            GibCursor pvrtmp_3215 = tmp_struct_81.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_82 =
                                                               _copy_SearchTree(end_from_tagged_absran_1423, pvrtmp_3212, pvrtmp_3215, tmpcur_3206);
            GibCursor pvrtmp_3220 = tmp_struct_82.field0;
            GibCursor pvrtmp_3221 = tmp_struct_82.field1;
            GibCursor pvrtmp_3222 = tmp_struct_82.field2;
            GibCursor pvrtmp_3223 = tmp_struct_82.field3;
            GibCursor pvrtmp_3224 = tmp_struct_82.field4;
            uint16_t offset_83 = end_r_1465 - loc_1725;
            uintptr_t ran_1426 = GIB_STORE_TAG(loc_1725, offset_83);
            GibCursor after_tag_2461 = loc_1463 + 1;

            *(uintptr_t *) after_tag_2461 = ran_1426;

            GibCursor writecur_2465 = after_tag_2461 + 8;

            *(GibInt *) writecur_2465 = tmpval_3209;

            GibCursor writecur_2466 = writecur_2465 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3220,
                                                                        pvrtmp_3221,
                                                                        pvrtmp_3222,
                                                                        loc_1463,
                                                                        pvrtmp_3224};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_3195;
            GibCursor tmpcur_3233 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_3234 = tmpcur_3195 + 8;
            uint16_t tmptag_3235 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1920 = tmpcur_3233 + tmptag_3235;
            GibCursor jump_1922 = tmpcur_3195 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_85 =
                                                               _copy_SearchTree(end_from_tagged_indr_1920, end_r_1465, loc_1463, tmpcur_3233);
            GibCursor pvrtmp_3236 = tmp_struct_85.field0;
            GibCursor pvrtmp_3237 = tmp_struct_85.field1;
            GibCursor pvrtmp_3238 = tmp_struct_85.field2;
            GibCursor pvrtmp_3239 = tmp_struct_85.field3;
            GibCursor pvrtmp_3240 = tmp_struct_85.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1464,
                                                                        pvrtmp_3237,
                                                                        jump_1922,
                                                                        pvrtmp_3239,
                                                                        pvrtmp_3240};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3195;
            GibCursor tmpcur_3247 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3248 = tmpcur_3195 + 8;
            uint16_t tmptag_3249 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1920 = tmpcur_3247 + tmptag_3249;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_SearchTree(end_from_tagged_indr_1920, end_r_1465, loc_1463, tmpcur_3247);
            GibCursor pvrtmp_3250 = tmp_struct_87.field0;
            GibCursor pvrtmp_3251 = tmp_struct_87.field1;
            GibCursor pvrtmp_3252 = tmp_struct_87.field2;
            GibCursor pvrtmp_3253 = tmp_struct_87.field3;
            GibCursor pvrtmp_3254 = tmp_struct_87.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3250,
                                                                        pvrtmp_3251,
                                                                        pvrtmp_3252,
                                                                        pvrtmp_3253,
                                                                        pvrtmp_3254};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3194");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_SearchTree(GibCursor end_r_1468,
                                                                                GibCursor end_r_1469,
                                                                                GibCursor loc_1467,
                                                                                GibCursor arg_732_852_1040)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3262 = *(GibPackedTag *) arg_732_852_1040;
    GibCursor tmpcur_3263 = arg_732_852_1040 + 1;


  switch_3329:
    ;
    switch (tmpval_3262) {

      case 0:
        {
            GibCursor jump_1863 = arg_732_852_1040 + 1;

            *(GibPackedTag *) loc_1467 = 0;

            GibCursor writetag_2483 = loc_1467 + 1;
            GibCursor after_tag_2484 = loc_1467 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1468,
                                                                        end_r_1469,
                                                                        jump_1863,
                                                                        loc_1467,
                                                                        after_tag_2484};
            break;
        }

      case 1:
        {
            GibInt tmpval_3268 = *(GibInt *) tmpcur_3263;
            GibCursor tmpcur_3269 = tmpcur_3263 + sizeof(GibInt);
            GibCursor jump_1865 = tmpcur_3263 + 8;

            *(GibPackedTag *) loc_1467 = 1;

            GibCursor writetag_2492 = loc_1467 + 1;
            GibCursor after_tag_2493 = loc_1467 + 1;

            *(GibInt *) after_tag_2493 = tmpval_3268;

            GibCursor writecur_2497 = after_tag_2493 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1468,
                                                                        end_r_1469,
                                                                        jump_1865,
                                                                        loc_1467,
                                                                        writecur_2497};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_94 = *(uintptr_t *) tmpcur_3263;
            GibCursor tmpcur_3274 = GIB_UNTAG(tagged_tmpcur_94);
            GibCursor tmpaftercur_3275 = tmpcur_3263 + 8;
            uint16_t tmptag_3276 = GIB_GET_TAG(tagged_tmpcur_94);
            GibCursor end_from_tagged_absran_1428 = tmpcur_3274 + tmptag_3276;
            GibInt tmpval_3277 = *(GibInt *) tmpaftercur_3275;
            GibCursor tmpcur_3278 = tmpaftercur_3275 + sizeof(GibInt);
            GibCursor loc_1752 = loc_1467 + 9;

            *(GibPackedTag *) loc_1467 = 2;

            GibCursor writetag_2509 = loc_1467 + 1;
            GibCursor after_tag_2510 = loc_1467 + 1;

            *(GibInt *) after_tag_2510 = tmpval_3277;

            GibCursor writecur_2514 = after_tag_2510 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_92 =
                                                               _copy_without_ptrs_SearchTree(end_r_1468, end_r_1469, loc_1752, tmpcur_3278);
            GibCursor pvrtmp_3279 = tmp_struct_92.field0;
            GibCursor pvrtmp_3280 = tmp_struct_92.field1;
            GibCursor pvrtmp_3281 = tmp_struct_92.field2;
            GibCursor pvrtmp_3282 = tmp_struct_92.field3;
            GibCursor pvrtmp_3283 = tmp_struct_92.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_93 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_absran_1428, pvrtmp_3280, pvrtmp_3283, tmpcur_3274);
            GibCursor pvrtmp_3288 = tmp_struct_93.field0;
            GibCursor pvrtmp_3289 = tmp_struct_93.field1;
            GibCursor pvrtmp_3290 = tmp_struct_93.field2;
            GibCursor pvrtmp_3291 = tmp_struct_93.field3;
            GibCursor pvrtmp_3292 = tmp_struct_93.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3288,
                                                                        pvrtmp_3289,
                                                                        pvrtmp_3290,
                                                                        loc_1467,
                                                                        pvrtmp_3292};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_96 = *(uintptr_t *) tmpcur_3263;
            GibCursor tmpcur_3301 = GIB_UNTAG(tagged_tmpcur_96);
            GibCursor tmpaftercur_3302 = tmpcur_3263 + 8;
            uint16_t tmptag_3303 = GIB_GET_TAG(tagged_tmpcur_96);
            GibCursor end_from_tagged_indr_1926 = tmpcur_3301 + tmptag_3303;
            GibCursor jump_1928 = tmpcur_3263 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_95 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1926, end_r_1469, loc_1467, tmpcur_3301);
            GibCursor pvrtmp_3304 = tmp_struct_95.field0;
            GibCursor pvrtmp_3305 = tmp_struct_95.field1;
            GibCursor pvrtmp_3306 = tmp_struct_95.field2;
            GibCursor pvrtmp_3307 = tmp_struct_95.field3;
            GibCursor pvrtmp_3308 = tmp_struct_95.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1468,
                                                                        pvrtmp_3305,
                                                                        jump_1928,
                                                                        pvrtmp_3307,
                                                                        pvrtmp_3308};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_98 = *(uintptr_t *) tmpcur_3263;
            GibCursor tmpcur_3315 = GIB_UNTAG(tagged_tmpcur_98);
            GibCursor tmpaftercur_3316 = tmpcur_3263 + 8;
            uint16_t tmptag_3317 = GIB_GET_TAG(tagged_tmpcur_98);
            GibCursor end_from_tagged_indr_1926 = tmpcur_3315 + tmptag_3317;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_97 =
                                                               _copy_without_ptrs_SearchTree(end_from_tagged_indr_1926, end_r_1469, loc_1467, tmpcur_3315);
            GibCursor pvrtmp_3318 = tmp_struct_97.field0;
            GibCursor pvrtmp_3319 = tmp_struct_97.field1;
            GibCursor pvrtmp_3320 = tmp_struct_97.field2;
            GibCursor pvrtmp_3321 = tmp_struct_97.field3;
            GibCursor pvrtmp_3322 = tmp_struct_97.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3318,
                                                                        pvrtmp_3319,
                                                                        pvrtmp_3320,
                                                                        pvrtmp_3321,
                                                                        pvrtmp_3322};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3262");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_SearchTree(GibCursor end_r_1471,
                                            GibCursor arg_741_861_1049)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3330 = *(GibPackedTag *) arg_741_861_1049;
    GibCursor tmpcur_3331 = arg_741_861_1049 + 1;


  switch_3353:
    ;
    switch (tmpval_3330) {

      case 0:
        {
            GibCursor jump_1872 = arg_741_861_1049 + 1;

            return (GibCursorGibCursorProd) {end_r_1471, jump_1872};
            break;
        }

      case 1:
        {
            GibInt tmpval_3332 = *(GibInt *) tmpcur_3331;
            GibCursor tmpcur_3333 = tmpcur_3331 + sizeof(GibInt);
            GibCursor jump_1874 = tmpcur_3331 + 8;

            return (GibCursorGibCursorProd) {end_r_1471, jump_1874};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_3331;
            GibCursor tmpcur_3334 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_3335 = tmpcur_3331 + 8;
            uint16_t tmptag_3336 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_absran_1431 = tmpcur_3334 + tmptag_3336;
            GibInt tmpval_3337 = *(GibInt *) tmpaftercur_3335;
            GibCursor tmpcur_3338 = tmpaftercur_3335 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_99 =
                                    _traverse_SearchTree(end_r_1471, tmpcur_3338);
            GibCursor pvrtmp_3339 = tmp_struct_99.field0;
            GibCursor pvrtmp_3340 = tmp_struct_99.field1;
            GibCursorGibCursorProd tmp_struct_100 =
                                    _traverse_SearchTree(end_from_tagged_absran_1431, tmpcur_3334);
            GibCursor pvrtmp_3341 = tmp_struct_100.field0;
            GibCursor pvrtmp_3342 = tmp_struct_100.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3341, pvrtmp_3342};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_3331;
            GibCursor tmpcur_3343 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_3344 = tmpcur_3331 + 8;
            uint16_t tmptag_3345 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_1932 = tmpcur_3343 + tmptag_3345;
            GibCursor jump_1934 = tmpcur_3331 + 8;
            GibCursorGibCursorProd tmp_struct_102 =
                                    _traverse_SearchTree(end_from_tagged_indr_1932, tmpcur_3343);
            GibCursor pvrtmp_3346 = tmp_struct_102.field0;
            GibCursor pvrtmp_3347 = tmp_struct_102.field1;

            return (GibCursorGibCursorProd) {end_r_1471, jump_1934};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) tmpcur_3331;
            GibCursor tmpcur_3348 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_3349 = tmpcur_3331 + 8;
            uint16_t tmptag_3350 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_indr_1932 = tmpcur_3348 + tmptag_3350;
            GibCursorGibCursorProd tmp_struct_104 =
                                    _traverse_SearchTree(end_from_tagged_indr_1932, tmpcur_3348);
            GibCursor pvrtmp_3351 = tmp_struct_104.field0;
            GibCursor pvrtmp_3352 = tmp_struct_104.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3351, pvrtmp_3352};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3330");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_SearchTree(GibCursor end_r_1473,
                                         GibCursor arg_750_868_1056)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3354 = *(GibPackedTag *) arg_750_868_1056;
    GibCursor tmpcur_3355 = arg_750_868_1056 + 1;


  switch_3377:
    ;
    switch (tmpval_3354) {

      case 0:
        {
            GibCursor jump_1881 = arg_750_868_1056 + 1;
            unsigned char wildcard_751_869_1057 = gib_print_symbol(2850);
            unsigned char wildcard_752_870_1058 = gib_print_symbol(2849);

            return (GibCursorGibCursorProd) {end_r_1473, jump_1881};
            break;
        }

      case 1:
        {
            GibInt tmpval_3356 = *(GibInt *) tmpcur_3355;
            GibCursor tmpcur_3357 = tmpcur_3355 + sizeof(GibInt);
            GibCursor jump_1883 = tmpcur_3355 + 8;
            unsigned char wildcard_755_872_1060 = gib_print_symbol(2852);
            unsigned char wildcard_758_873_1061 = gib_print_symbol(2855);
            unsigned char y_754_874_1062 = printf("%ld", tmpval_3356);
            unsigned char wildcard_757_875_1063 = gib_print_symbol(2855);
            unsigned char y_754_876_1064 = gib_print_symbol(2855);
            unsigned char wildcard_756_877_1065 = gib_print_symbol(2849);

            return (GibCursorGibCursorProd) {end_r_1473, jump_1883};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_108 = *(uintptr_t *) tmpcur_3355;
            GibCursor tmpcur_3358 = GIB_UNTAG(tagged_tmpcur_108);
            GibCursor tmpaftercur_3359 = tmpcur_3355 + 8;
            uint16_t tmptag_3360 = GIB_GET_TAG(tagged_tmpcur_108);
            GibCursor end_from_tagged_absran_1434 = tmpcur_3358 + tmptag_3360;
            GibInt tmpval_3361 = *(GibInt *) tmpaftercur_3359;
            GibCursor tmpcur_3362 = tmpaftercur_3359 + sizeof(GibInt);
            unsigned char wildcard_765_881_1069 = gib_print_symbol(2851);
            unsigned char wildcard_772_882_1070 = gib_print_symbol(2855);
            unsigned char y_762_883_1071 = printf("%ld", tmpval_3361);
            unsigned char wildcard_771_884_1072 = gib_print_symbol(2855);
            unsigned char y_762_885_1073 = gib_print_symbol(2855);
            unsigned char wildcard_770_886_1074 = gib_print_symbol(2855);
            GibCursorGibCursorProd tmp_struct_106 =
                                    _print_SearchTree(end_r_1473, tmpcur_3362);
            GibCursor pvrtmp_3363 = tmp_struct_106.field0;
            GibCursor pvrtmp_3364 = tmp_struct_106.field1;
            unsigned char wildcard_769_888_1076 = gib_print_symbol(2855);
            unsigned char y_763_889_1077 = gib_print_symbol(2855);
            unsigned char wildcard_768_890_1078 = gib_print_symbol(2855);
            GibCursorGibCursorProd tmp_struct_107 =
                                    _print_SearchTree(end_from_tagged_absran_1434, tmpcur_3358);
            GibCursor pvrtmp_3365 = tmp_struct_107.field0;
            GibCursor pvrtmp_3366 = tmp_struct_107.field1;
            unsigned char wildcard_767_892_1080 = gib_print_symbol(2855);
            unsigned char y_764_893_1081 = gib_print_symbol(2855);
            unsigned char wildcard_766_894_1082 = gib_print_symbol(2849);

            return (GibCursorGibCursorProd) {pvrtmp_3365, pvrtmp_3366};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_3355;
            GibCursor tmpcur_3367 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_3368 = tmpcur_3355 + 8;
            uint16_t tmptag_3369 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_1938 = tmpcur_3367 + tmptag_3369;
            GibCursor jump_1940 = tmpcur_3355 + 8;
            unsigned char wildcard_1943 = gib_print_symbol(2854);
            GibCursorGibCursorProd tmp_struct_109 =
                                    _print_SearchTree(end_from_tagged_indr_1938, tmpcur_3367);
            GibCursor pvrtmp_3370 = tmp_struct_109.field0;
            GibCursor pvrtmp_3371 = tmp_struct_109.field1;

            return (GibCursorGibCursorProd) {end_r_1473, jump_1940};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_3355;
            GibCursor tmpcur_3372 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_3373 = tmpcur_3355 + 8;
            uint16_t tmptag_3374 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_1938 = tmpcur_3372 + tmptag_3374;
            unsigned char wildcard_1943 = gib_print_symbol(2853);
            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_SearchTree(end_from_tagged_indr_1938, tmpcur_3372);
            GibCursor pvrtmp_3375 = tmp_struct_111.field0;
            GibCursor pvrtmp_3376 = tmp_struct_111.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3375, pvrtmp_3376};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3354");
            exit(1);
        }
    }
}
GibCursorGibIntProd caseFn_773(GibCursor end_r_1475,
                               GibCursor l_105_774_895_1083,
                               GibInt n_104_775_896_1084)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3378 = *(GibPackedTag *) l_105_774_895_1083;
    GibCursor tmpcur_3379 = l_105_774_895_1083 + 1;


  switch_3399:
    ;
    switch (tmpval_3378) {

      case 0:
        {
            return (GibCursorGibIntProd) {end_r_1475, n_104_775_896_1084};
            break;
        }

      case 1:
        {
            GibInt tmpval_3380 = *(GibInt *) tmpcur_3379;
            GibCursor tmpcur_3381 = tmpcur_3379 + sizeof(GibInt);

            return (GibCursorGibIntProd) {end_r_1475, tmpval_3380};
            break;
        }

      case 3:
        {
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) tmpcur_3379;
            GibCursor tmpcur_3382 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_3383 = tmpcur_3379 + 8;
            uint16_t tmptag_3384 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_absran_1437 = tmpcur_3382 + tmptag_3384;
            GibInt tmpval_3385 = *(GibInt *) tmpaftercur_3383;
            GibCursor tmpcur_3386 = tmpaftercur_3383 + sizeof(GibInt);
            GibCursorGibIntProd tmp_struct_113 =
                                 minTree(end_r_1475, tmpcur_3386);
            GibCursor pvrtmp_3387 = tmp_struct_113.field0;
            GibInt pvrtmp_3388 = tmp_struct_113.field1;

            return (GibCursorGibIntProd) {pvrtmp_3387, pvrtmp_3388};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_116 = *(uintptr_t *) tmpcur_3379;
            GibCursor tmpcur_3389 = GIB_UNTAG(tagged_tmpcur_116);
            GibCursor tmpaftercur_3390 = tmpcur_3379 + 8;
            uint16_t tmptag_3391 = GIB_GET_TAG(tagged_tmpcur_116);
            GibCursor end_from_tagged_indr_1944 = tmpcur_3389 + tmptag_3391;
            GibCursor jump_1946 = tmpcur_3379 + 8;
            GibCursorGibIntProd tmp_struct_115 =
                                 caseFn_773(end_from_tagged_indr_1944, tmpcur_3389, n_104_775_896_1084);
            GibCursor pvrtmp_3392 = tmp_struct_115.field0;
            GibInt pvrtmp_3393 = tmp_struct_115.field1;

            return (GibCursorGibIntProd) {end_r_1475, pvrtmp_3393};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_118 = *(uintptr_t *) tmpcur_3379;
            GibCursor tmpcur_3394 = GIB_UNTAG(tagged_tmpcur_118);
            GibCursor tmpaftercur_3395 = tmpcur_3379 + 8;
            uint16_t tmptag_3396 = GIB_GET_TAG(tagged_tmpcur_118);
            GibCursor end_from_tagged_indr_1944 = tmpcur_3394 + tmptag_3396;
            GibCursorGibIntProd tmp_struct_117 =
                                 caseFn_773(end_from_tagged_indr_1944, tmpcur_3394, n_104_775_896_1084);
            GibCursor pvrtmp_3397 = tmp_struct_117.field0;
            GibInt pvrtmp_3398 = tmp_struct_117.field1;

            return (GibCursorGibIntProd) {pvrtmp_3397, pvrtmp_3398};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3378");
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
    GibVector *pts_85_776_948 =
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
        gib_vector_inplace_update(pts_85_776_948, i_132, &arr_elem_127);
        i_132++;
    }

    GibInt n_86_777_949 = gib_get_size_param();
    GibChunk region_2856 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1487 = region_2856.start;
    GibCursor end_r_1487 = region_2856.end;
    GibCursorGibCursorGibCursorProd tmp_struct_119 =
                                     helper(end_r_1487, r_1487, 0, 3);
    GibCursor pvrtmp_2857 = tmp_struct_119.field0;
    GibCursor pvrtmp_2858 = tmp_struct_119.field1;
    GibCursor pvrtmp_2859 = tmp_struct_119.field2;

    gib_shadowstack_push(rstack, pvrtmp_2858, pvrtmp_2857, Stk, SearchTree_T);

    GibChunk region_2864 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1486 = region_2864.start;
    GibCursor end_r_1486 = region_2864.end;

    frame = gib_shadowstack_pop(rstack);
    pvrtmp_2858 = frame->ptr;
    pvrtmp_2857 = frame->endptr;

    GibCursor pvrtmp_2875;
    GibCursor pvrtmp_2876;
    GibCursor pvrtmp_2877;
    GibVector *times_124 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2875;
    struct timespec end_pvrtmp_2875;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(2);

    for (long long iters_pvrtmp_2875 = 0; iters_pvrtmp_2875 <
         gib_get_iters_param(); iters_pvrtmp_2875++) {
        if (iters_pvrtmp_2875 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 2, region_2864.end, region_2856.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2875);

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                  loop(pvrtmp_2857, end_r_1486, r_1486, pts_85_776_948, 0, pvrtmp_2858, n_86_777_949);
        GibCursor pvrtmp_2865 = tmp_struct_120.field0;
        GibCursor pvrtmp_2866 = tmp_struct_120.field1;
        GibCursor pvrtmp_2867 = tmp_struct_120.field2;
        GibCursor pvrtmp_2868 = tmp_struct_120.field3;

        pvrtmp_2875 = pvrtmp_2866;
        pvrtmp_2876 = pvrtmp_2867;
        pvrtmp_2877 = pvrtmp_2868;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2875);
        if (iters_pvrtmp_2875 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_121 = gib_difftimespecs(&begin_pvrtmp_2875,
                                                &end_pvrtmp_2875);

        printf("itertime: %lf\n", itertime_121);
        gib_vector_inplace_update(times_124, iters_pvrtmp_2875, &itertime_121);
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
                                  countnodes(end_r_1486, pvrtmp_2876);
    GibCursor pvrtmp_2885 = tmp_struct_126.field0;
    GibCursor pvrtmp_2886 = tmp_struct_126.field1;
    GibInt pvrtmp_2887 = tmp_struct_126.field2;

    printf("%ld", pvrtmp_2887);
    printf("\n");
    return 0;

    int exit_135 = gib_exit();

    return exit_135;
}
