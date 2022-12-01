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
typedef struct GibCursorGibCursorGibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
            GibCursor field3;
            GibCursor field4;
        } GibCursorGibCursorGibCursorGibCursorGibCursorProd;
typedef struct GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd_struct {
            GibCursor field0;
            GibCursor field1;
            GibCursor field2;
            GibCursor field3;
            GibCursor field4;
            GibCursor field5;
        } GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd;
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
reverse(GibCursor end_r_274, GibCursor end_r_275, GibCursor end_r_276,
        GibCursor loc_273, GibCursor xs_22_82_122, GibCursor acc_23_83_123);
GibCursorGibCursorGibIntProd sumList(GibCursor end_r_278,
                                     GibCursor xs_26_86_127);
GibCursorGibCursorGibCursorProd buildList(GibCursor end_r_280,
                                          GibCursor loc_279,
                                          GibInt n_29_89_131);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList(GibCursor end_r_283, GibCursor end_r_284, GibCursor loc_282,
            GibCursor arg_54_90_135);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList(GibCursor end_r_287, GibCursor end_r_288,
                         GibCursor loc_286, GibCursor arg_59_95_140);
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_290,
                                       GibCursor arg_64_100_145);
GibCursorGibCursorProd _print_PList(GibCursor end_r_292,
                                    GibCursor arg_69_104_149);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            PList_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[2];

    field_tys[0] = PList_T;
    error = gib_info_table_insert_packed_dcon(PList_T, 0, 8, 0, 1, 1, field_tys,
                                              1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_T, 1);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(808, ")");
    gib_add_symbol(809, "(Nil ");
    gib_add_symbol(810, "(Cons ");
    gib_add_symbol(811, " ->r ");
    gib_add_symbol(812, " ->i ");
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_274,
                                                                   GibCursor end_r_275,
                                                                   GibCursor end_r_276,
                                                                   GibCursor loc_273,
                                                                   GibCursor xs_22_82_122,
                                                                   GibCursor acc_23_83_123)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_273 + 18 > end_r_276) {
        gib_grow_region(&loc_273, &end_r_276);
    }

    GibPackedTag tmpval_850 = *(GibPackedTag *) xs_22_82_122;
    GibCursor tmpcur_851 = xs_22_82_122 + 1;


  switch_905:
    ;
    switch (tmpval_850) {

      case 1:
        {
            GibCursor jump_390 = xs_22_82_122 + 1;

            if (loc_273 + 18 > end_r_276) {
                gib_grow_region(&loc_273, &end_r_276);
            }
            gib_indirection_barrier(loc_273, end_r_276, acc_23_83_123,
                                    end_r_275, PList_T);

            GibCursor end_515 = loc_273 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_274,
                                                                                 end_r_275,
                                                                                 end_r_276,
                                                                                 jump_390,
                                                                                 loc_273,
                                                                                 end_515};
            break;
        }

      case 0:
        {
            GibInt tmpval_856 = *(GibInt *) tmpcur_851;
            GibCursor tmpcur_857 = tmpcur_851 + sizeof(GibInt);

            gib_shadowstack_push(rstack, acc_23_83_123, end_r_275, Stk,
                                 PList_T);
            gib_shadowstack_push(rstack, tmpcur_857, end_r_274, Stk, PList_T);
            gib_shadowstack_push(wstack, loc_273, end_r_276, Stk, PList_T);

            GibChunk region_858 = gib_alloc_region(27);
            GibCursor r_328 = region_858.start;
            GibCursor end_r_328 = region_858.end;

            frame = gib_shadowstack_pop(wstack);
            loc_273 = frame->ptr;
            end_r_276 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_857 = frame->ptr;
            end_r_274 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            acc_23_83_123 = frame->ptr;
            end_r_275 = frame->endptr;

            GibCursor loc_317 = r_328 + 9;

            *(GibPackedTag *) r_328 = 0;

            GibCursor writetag_522 = r_328 + 1;
            GibCursor after_tag_523 = r_328 + 1;

            *(GibInt *) after_tag_523 = tmpval_856;

            GibCursor writecur_527 = after_tag_523 + sizeof(GibInt);

            if (loc_317 + 18 > end_r_328) {
                gib_grow_region(&loc_317, &end_r_328);
            }
            gib_indirection_barrier(loc_317, end_r_328, acc_23_83_123,
                                    end_r_275, PList_T);

            GibCursor end_520 = loc_317 + 9;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_3 =
             reverse(end_r_274, end_r_328, end_r_276, loc_273, tmpcur_857, r_328);
            GibCursor pvrtmp_863 = tmp_struct_3.field0;
            GibCursor pvrtmp_864 = tmp_struct_3.field1;
            GibCursor pvrtmp_865 = tmp_struct_3.field2;
            GibCursor pvrtmp_866 = tmp_struct_3.field3;
            GibCursor pvrtmp_867 = tmp_struct_3.field4;
            GibCursor pvrtmp_868 = tmp_struct_3.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_863,
                                                                                 end_r_275,
                                                                                 pvrtmp_865,
                                                                                 pvrtmp_866,
                                                                                 pvrtmp_867,
                                                                                 pvrtmp_868};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_851;
            GibCursor tmpcur_875 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_876 = tmpcur_851 + 8;
            uint16_t tmptag_877 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_indr_426 = tmpcur_875 + tmptag_877;
            GibCursor jump_428 = tmpcur_851 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_7 =
             reverse(end_from_tagged_indr_426, end_r_275, end_r_276, loc_273, tmpcur_875, acc_23_83_123);
            GibCursor pvrtmp_878 = tmp_struct_7.field0;
            GibCursor pvrtmp_879 = tmp_struct_7.field1;
            GibCursor pvrtmp_880 = tmp_struct_7.field2;
            GibCursor pvrtmp_881 = tmp_struct_7.field3;
            GibCursor pvrtmp_882 = tmp_struct_7.field4;
            GibCursor pvrtmp_883 = tmp_struct_7.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_274,
                                                                                 pvrtmp_879,
                                                                                 pvrtmp_880,
                                                                                 jump_428,
                                                                                 pvrtmp_882,
                                                                                 pvrtmp_883};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) tmpcur_851;
            GibCursor tmpcur_890 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_891 = tmpcur_851 + 8;
            uint16_t tmptag_892 = GIB_GET_TAG(tagged_tmpcur_10);
            GibCursor end_from_tagged_indr_426 = tmpcur_890 + tmptag_892;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_9 =
             reverse(end_from_tagged_indr_426, end_r_275, end_r_276, loc_273, tmpcur_890, acc_23_83_123);
            GibCursor pvrtmp_893 = tmp_struct_9.field0;
            GibCursor pvrtmp_894 = tmp_struct_9.field1;
            GibCursor pvrtmp_895 = tmp_struct_9.field2;
            GibCursor pvrtmp_896 = tmp_struct_9.field3;
            GibCursor pvrtmp_897 = tmp_struct_9.field4;
            GibCursor pvrtmp_898 = tmp_struct_9.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_893,
                                                                                 pvrtmp_894,
                                                                                 pvrtmp_895,
                                                                                 pvrtmp_896,
                                                                                 pvrtmp_897,
                                                                                 pvrtmp_898};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_850");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd sumList(GibCursor end_r_278,
                                     GibCursor xs_26_86_127)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_906 = *(GibPackedTag *) xs_26_86_127;
    GibCursor tmpcur_907 = xs_26_86_127 + 1;


  switch_925:
    ;
    switch (tmpval_906) {

      case 1:
        {
            GibCursor jump_395 = xs_26_86_127 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_278, jump_395, 0};
            break;
        }

      case 0:
        {
            GibInt tmpval_908 = *(GibInt *) tmpcur_907;
            GibCursor tmpcur_909 = tmpcur_907 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_14 =
                                          sumList(end_r_278, tmpcur_909);
            GibCursor pvrtmp_910 = tmp_struct_14.field0;
            GibCursor pvrtmp_911 = tmp_struct_14.field1;
            GibInt pvrtmp_912 = tmp_struct_14.field2;
            GibInt tailprim_398 = tmpval_908 + pvrtmp_912;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_910, pvrtmp_911,
                                                   tailprim_398};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) tmpcur_907;
            GibCursor tmpcur_913 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_914 = tmpcur_907 + 8;
            uint16_t tmptag_915 = GIB_GET_TAG(tagged_tmpcur_16);
            GibCursor end_from_tagged_indr_432 = tmpcur_913 + tmptag_915;
            GibCursor jump_434 = tmpcur_907 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_15 =
                                          sumList(end_from_tagged_indr_432, tmpcur_913);
            GibCursor pvrtmp_916 = tmp_struct_15.field0;
            GibCursor pvrtmp_917 = tmp_struct_15.field1;
            GibInt pvrtmp_918 = tmp_struct_15.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_278, jump_434,
                                                   pvrtmp_918};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_18 = *(uintptr_t *) tmpcur_907;
            GibCursor tmpcur_919 = GIB_UNTAG(tagged_tmpcur_18);
            GibCursor tmpaftercur_920 = tmpcur_907 + 8;
            uint16_t tmptag_921 = GIB_GET_TAG(tagged_tmpcur_18);
            GibCursor end_from_tagged_indr_432 = tmpcur_919 + tmptag_921;
            GibCursorGibCursorGibIntProd tmp_struct_17 =
                                          sumList(end_from_tagged_indr_432, tmpcur_919);
            GibCursor pvrtmp_922 = tmp_struct_17.field0;
            GibCursor pvrtmp_923 = tmp_struct_17.field1;
            GibInt pvrtmp_924 = tmp_struct_17.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_922, pvrtmp_923,
                                                   pvrtmp_924};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_906");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildList(GibCursor end_r_280,
                                          GibCursor loc_279, GibInt n_29_89_131)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_279 + 18 > end_r_280) {
        gib_grow_region(&loc_279, &end_r_280);
    }

    GibBool fltIf_115_132 = n_29_89_131 == 0;

    if (fltIf_115_132) {
        *(GibPackedTag *) loc_279 = 1;

        GibCursor writetag_560 = loc_279 + 1;
        GibCursor after_tag_561 = loc_279 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_280, loc_279,
                                                  after_tag_561};
    } else {
        GibInt fltAppE_117_133 = n_29_89_131 - 1;
        GibCursor loc_338 = loc_279 + 9;

        *(GibPackedTag *) loc_279 = 0;

        GibCursor writetag_569 = loc_279 + 1;
        GibCursor after_tag_570 = loc_279 + 1;

        *(GibInt *) after_tag_570 = n_29_89_131;

        GibCursor writecur_574 = after_tag_570 + sizeof(GibInt);

        gib_shadowstack_push(rstack, loc_279, end_r_280, Stk, PList_T);

        GibCursorGibCursorGibCursorProd tmp_struct_19 =
                                         buildList(end_r_280, loc_338, fltAppE_117_133);
        GibCursor pvrtmp_930 = tmp_struct_19.field0;
        GibCursor pvrtmp_931 = tmp_struct_19.field1;
        GibCursor pvrtmp_932 = tmp_struct_19.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_279 = frame->ptr;
        end_r_280 = frame->endptr;
        return (GibCursorGibCursorGibCursorProd) {pvrtmp_930, loc_279,
                                                  pvrtmp_932};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList(GibCursor end_r_283,
                                                              GibCursor end_r_284,
                                                              GibCursor loc_282,
                                                              GibCursor arg_54_90_135)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_282 + 18 > end_r_284) {
        gib_grow_region(&loc_282, &end_r_284);
    }

    GibPackedTag tmpval_941 = *(GibPackedTag *) arg_54_90_135;
    GibCursor tmpcur_942 = arg_54_90_135 + 1;


  switch_990:
    ;
    switch (tmpval_941) {

      case 0:
        {
            GibInt tmpval_943 = *(GibInt *) tmpcur_942;
            GibCursor tmpcur_944 = tmpcur_942 + sizeof(GibInt);
            GibCursor loc_350 = loc_282 + 9;

            *(GibPackedTag *) loc_282 = 0;

            GibCursor writetag_583 = loc_282 + 1;
            GibCursor after_tag_584 = loc_282 + 1;

            *(GibInt *) after_tag_584 = tmpval_943;

            GibCursor writecur_588 = after_tag_584 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_282, end_r_284, Stk, PList_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_23 =
                                                               _copy_PList(end_r_283, end_r_284, loc_350, tmpcur_944);
            GibCursor pvrtmp_945 = tmp_struct_23.field0;
            GibCursor pvrtmp_946 = tmp_struct_23.field1;
            GibCursor pvrtmp_947 = tmp_struct_23.field2;
            GibCursor pvrtmp_948 = tmp_struct_23.field3;
            GibCursor pvrtmp_949 = tmp_struct_23.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_282 = frame->ptr;
            end_r_284 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_945,
                                                                        pvrtmp_946,
                                                                        pvrtmp_947,
                                                                        loc_282,
                                                                        pvrtmp_949};
            break;
        }

      case 1:
        {
            GibCursor jump_404 = arg_54_90_135 + 1;

            *(GibPackedTag *) loc_282 = 1;

            GibCursor writetag_593 = loc_282 + 1;
            GibCursor after_tag_594 = loc_282 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_283,
                                                                        end_r_284,
                                                                        jump_404,
                                                                        loc_282,
                                                                        after_tag_594};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_942;
            GibCursor tmpcur_962 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_963 = tmpcur_942 + 8;
            uint16_t tmptag_964 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_indr_438 = tmpcur_962 + tmptag_964;
            GibCursor jump_440 = tmpcur_942 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                               _copy_PList(end_from_tagged_indr_438, end_r_284, loc_282, tmpcur_962);
            GibCursor pvrtmp_965 = tmp_struct_24.field0;
            GibCursor pvrtmp_966 = tmp_struct_24.field1;
            GibCursor pvrtmp_967 = tmp_struct_24.field2;
            GibCursor pvrtmp_968 = tmp_struct_24.field3;
            GibCursor pvrtmp_969 = tmp_struct_24.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_283,
                                                                        pvrtmp_966,
                                                                        jump_440,
                                                                        pvrtmp_968,
                                                                        pvrtmp_969};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_942;
            GibCursor tmpcur_976 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_977 = tmpcur_942 + 8;
            uint16_t tmptag_978 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_438 = tmpcur_976 + tmptag_978;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_26 =
                                                               _copy_PList(end_from_tagged_indr_438, end_r_284, loc_282, tmpcur_976);
            GibCursor pvrtmp_979 = tmp_struct_26.field0;
            GibCursor pvrtmp_980 = tmp_struct_26.field1;
            GibCursor pvrtmp_981 = tmp_struct_26.field2;
            GibCursor pvrtmp_982 = tmp_struct_26.field3;
            GibCursor pvrtmp_983 = tmp_struct_26.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_979,
                                                                        pvrtmp_980,
                                                                        pvrtmp_981,
                                                                        pvrtmp_982,
                                                                        pvrtmp_983};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_941");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList(GibCursor end_r_287,
                                                                           GibCursor end_r_288,
                                                                           GibCursor loc_286,
                                                                           GibCursor arg_59_95_140)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_991 = *(GibPackedTag *) arg_59_95_140;
    GibCursor tmpcur_992 = arg_59_95_140 + 1;


  switch_1040:
    ;
    switch (tmpval_991) {

      case 0:
        {
            GibInt tmpval_993 = *(GibInt *) tmpcur_992;
            GibCursor tmpcur_994 = tmpcur_992 + sizeof(GibInt);
            GibCursor loc_363 = loc_286 + 9;

            *(GibPackedTag *) loc_286 = 0;

            GibCursor writetag_615 = loc_286 + 1;
            GibCursor after_tag_616 = loc_286 + 1;

            *(GibInt *) after_tag_616 = tmpval_993;

            GibCursor writecur_620 = after_tag_616 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_286, end_r_288, Stk, PList_T);

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_31 =
                                                               _copy_without_ptrs_PList(end_r_287, end_r_288, loc_363, tmpcur_994);
            GibCursor pvrtmp_995 = tmp_struct_31.field0;
            GibCursor pvrtmp_996 = tmp_struct_31.field1;
            GibCursor pvrtmp_997 = tmp_struct_31.field2;
            GibCursor pvrtmp_998 = tmp_struct_31.field3;
            GibCursor pvrtmp_999 = tmp_struct_31.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_286 = frame->ptr;
            end_r_288 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_995,
                                                                        pvrtmp_996,
                                                                        pvrtmp_997,
                                                                        loc_286,
                                                                        pvrtmp_999};
            break;
        }

      case 1:
        {
            GibCursor jump_409 = arg_59_95_140 + 1;

            *(GibPackedTag *) loc_286 = 1;

            GibCursor writetag_625 = loc_286 + 1;
            GibCursor after_tag_626 = loc_286 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_287,
                                                                        end_r_288,
                                                                        jump_409,
                                                                        loc_286,
                                                                        after_tag_626};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) tmpcur_992;
            GibCursor tmpcur_1012 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_1013 = tmpcur_992 + 8;
            uint16_t tmptag_1014 = GIB_GET_TAG(tagged_tmpcur_33);
            GibCursor end_from_tagged_indr_444 = tmpcur_1012 + tmptag_1014;
            GibCursor jump_446 = tmpcur_992 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_32 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_444, end_r_288, loc_286, tmpcur_1012);
            GibCursor pvrtmp_1015 = tmp_struct_32.field0;
            GibCursor pvrtmp_1016 = tmp_struct_32.field1;
            GibCursor pvrtmp_1017 = tmp_struct_32.field2;
            GibCursor pvrtmp_1018 = tmp_struct_32.field3;
            GibCursor pvrtmp_1019 = tmp_struct_32.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_287,
                                                                        pvrtmp_1016,
                                                                        jump_446,
                                                                        pvrtmp_1018,
                                                                        pvrtmp_1019};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_992;
            GibCursor tmpcur_1026 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_1027 = tmpcur_992 + 8;
            uint16_t tmptag_1028 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_indr_444 = tmpcur_1026 + tmptag_1028;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_34 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_444, end_r_288, loc_286, tmpcur_1026);
            GibCursor pvrtmp_1029 = tmp_struct_34.field0;
            GibCursor pvrtmp_1030 = tmp_struct_34.field1;
            GibCursor pvrtmp_1031 = tmp_struct_34.field2;
            GibCursor pvrtmp_1032 = tmp_struct_34.field3;
            GibCursor pvrtmp_1033 = tmp_struct_34.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1029,
                                                                        pvrtmp_1030,
                                                                        pvrtmp_1031,
                                                                        pvrtmp_1032,
                                                                        pvrtmp_1033};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_991");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_290,
                                       GibCursor arg_64_100_145)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1041 = *(GibPackedTag *) arg_64_100_145;
    GibCursor tmpcur_1042 = arg_64_100_145 + 1;


  switch_1057:
    ;
    switch (tmpval_1041) {

      case 0:
        {
            GibInt tmpval_1043 = *(GibInt *) tmpcur_1042;
            GibCursor tmpcur_1044 = tmpcur_1042 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_36 =
                                    _traverse_PList(end_r_290, tmpcur_1044);
            GibCursor pvrtmp_1045 = tmp_struct_36.field0;
            GibCursor pvrtmp_1046 = tmp_struct_36.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1045, pvrtmp_1046};
            break;
        }

      case 1:
        {
            GibCursor jump_414 = arg_64_100_145 + 1;

            return (GibCursorGibCursorProd) {end_r_290, jump_414};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) tmpcur_1042;
            GibCursor tmpcur_1047 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_1048 = tmpcur_1042 + 8;
            uint16_t tmptag_1049 = GIB_GET_TAG(tagged_tmpcur_38);
            GibCursor end_from_tagged_indr_450 = tmpcur_1047 + tmptag_1049;
            GibCursor jump_452 = tmpcur_1042 + 8;
            GibCursorGibCursorProd tmp_struct_37 =
                                    _traverse_PList(end_from_tagged_indr_450, tmpcur_1047);
            GibCursor pvrtmp_1050 = tmp_struct_37.field0;
            GibCursor pvrtmp_1051 = tmp_struct_37.field1;

            return (GibCursorGibCursorProd) {end_r_290, jump_452};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_1042;
            GibCursor tmpcur_1052 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_1053 = tmpcur_1042 + 8;
            uint16_t tmptag_1054 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_450 = tmpcur_1052 + tmptag_1054;
            GibCursorGibCursorProd tmp_struct_39 =
                                    _traverse_PList(end_from_tagged_indr_450, tmpcur_1052);
            GibCursor pvrtmp_1055 = tmp_struct_39.field0;
            GibCursor pvrtmp_1056 = tmp_struct_39.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1055, pvrtmp_1056};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1041");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList(GibCursor end_r_292,
                                    GibCursor arg_69_104_149)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1058 = *(GibPackedTag *) arg_69_104_149;
    GibCursor tmpcur_1059 = arg_69_104_149 + 1;


  switch_1074:
    ;
    switch (tmpval_1058) {

      case 0:
        {
            GibInt tmpval_1060 = *(GibInt *) tmpcur_1059;
            GibCursor tmpcur_1061 = tmpcur_1059 + sizeof(GibInt);
            unsigned char wildcard_74_107_152 = gib_print_symbol(810);
            unsigned char y_72_108_153 = printf("%ld", tmpval_1060);
            GibCursorGibCursorProd tmp_struct_41 =
                                    _print_PList(end_r_292, tmpcur_1061);
            GibCursor pvrtmp_1062 = tmp_struct_41.field0;
            GibCursor pvrtmp_1063 = tmp_struct_41.field1;
            unsigned char wildcard_75_110_155 = gib_print_symbol(808);

            return (GibCursorGibCursorProd) {pvrtmp_1062, pvrtmp_1063};
            break;
        }

      case 1:
        {
            GibCursor jump_419 = arg_69_104_149 + 1;
            unsigned char wildcard_76_111_156 = gib_print_symbol(809);
            unsigned char wildcard_77_112_157 = gib_print_symbol(808);

            return (GibCursorGibCursorProd) {end_r_292, jump_419};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_1059;
            GibCursor tmpcur_1064 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_1065 = tmpcur_1059 + 8;
            uint16_t tmptag_1066 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_indr_456 = tmpcur_1064 + tmptag_1066;
            GibCursor jump_458 = tmpcur_1059 + 8;
            unsigned char wildcard_461 = gib_print_symbol(812);
            GibCursorGibCursorProd tmp_struct_42 =
                                    _print_PList(end_from_tagged_indr_456, tmpcur_1064);
            GibCursor pvrtmp_1067 = tmp_struct_42.field0;
            GibCursor pvrtmp_1068 = tmp_struct_42.field1;

            return (GibCursorGibCursorProd) {end_r_292, jump_458};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_45 = *(uintptr_t *) tmpcur_1059;
            GibCursor tmpcur_1069 = GIB_UNTAG(tagged_tmpcur_45);
            GibCursor tmpaftercur_1070 = tmpcur_1059 + 8;
            uint16_t tmptag_1071 = GIB_GET_TAG(tagged_tmpcur_45);
            GibCursor end_from_tagged_indr_456 = tmpcur_1069 + tmptag_1071;
            unsigned char wildcard_461 = gib_print_symbol(811);
            GibCursorGibCursorProd tmp_struct_44 =
                                    _print_PList(end_from_tagged_indr_456, tmpcur_1069);
            GibCursor pvrtmp_1072 = tmp_struct_44.field0;
            GibCursor pvrtmp_1073 = tmp_struct_44.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1072, pvrtmp_1073};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1058");
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
    GibChunk region_813 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_310 = region_813.start;
    GibCursor end_r_310 = region_813.end;
    GibChunk region_814 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_309 = region_814.start;
    GibCursor end_r_309 = region_814.end;
    GibChunk region_815 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_308 = region_815.start;
    GibCursor end_r_308 = region_815.end;
    GibInt n_18_78_118 = gib_get_size_param();
    GibCursorGibCursorGibCursorProd tmp_struct_46 =
                                     buildList(end_r_310, r_310, n_18_78_118);
    GibCursor pvrtmp_816 = tmp_struct_46.field0;
    GibCursor pvrtmp_817 = tmp_struct_46.field1;
    GibCursor pvrtmp_818 = tmp_struct_46.field2;

    gib_shadowstack_push(rstack, r_310, pvrtmp_816, Stk, PList_T);
    frame = gib_shadowstack_pop(rstack);
    r_310 = frame->ptr;
    pvrtmp_816 = frame->endptr;
    *(GibPackedTag *) r_309 = 1;

    GibCursor writetag_670 = r_309 + 1;
    GibCursor after_tag_671 = r_309 + 1;

    gib_shadowstack_push(rstack, r_309, end_r_309, Stk, PList_T);
    gib_shadowstack_push(rstack, r_310, pvrtmp_816, Stk, PList_T);
    frame = gib_shadowstack_pop(rstack);
    r_310 = frame->ptr;
    pvrtmp_816 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    r_309 = frame->ptr;
    end_r_309 = frame->endptr;

    GibCursor pvrtmp_837;
    GibCursor pvrtmp_838;
    GibCursor pvrtmp_839;
    GibVector *times_51 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_837;
    struct timespec end_pvrtmp_837;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(3);

    for (long long iters_pvrtmp_837 = 0; iters_pvrtmp_837 <
         gib_get_iters_param(); iters_pvrtmp_837++) {
        if (iters_pvrtmp_837 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 3, region_813.end, region_814.end, region_815.end);
            gib_list_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_837);

        GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47
                                                                   =
                                                                    reverse(pvrtmp_816, end_r_309, end_r_308, r_308, pvrtmp_817, r_309);
        GibCursor pvrtmp_825 = tmp_struct_47.field0;
        GibCursor pvrtmp_826 = tmp_struct_47.field1;
        GibCursor pvrtmp_827 = tmp_struct_47.field2;
        GibCursor pvrtmp_828 = tmp_struct_47.field3;
        GibCursor pvrtmp_829 = tmp_struct_47.field4;
        GibCursor pvrtmp_830 = tmp_struct_47.field5;

        pvrtmp_837 = pvrtmp_827;
        pvrtmp_838 = pvrtmp_829;
        pvrtmp_839 = pvrtmp_830;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_837);
        if (iters_pvrtmp_837 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
        }

        double itertime_48 = gib_difftimespecs(&begin_pvrtmp_837,
                                               &end_pvrtmp_837);

        printf("itertime: %lf\n", itertime_48);
        gib_vector_inplace_update(times_51, iters_pvrtmp_837, &itertime_48);
    }
    gib_vector_inplace_sort(times_51, gib_compare_doubles);

    double *tmp_52 = (double *) gib_vector_nth(times_51, gib_get_iters_param() /
                                               2);
    double selftimed_50 = *tmp_52;
    double batchtime_49 = gib_sum_timing_array(times_51);

    gib_print_timing_array(times_51);
    gib_vector_free(times_51);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_49);
    printf("SELFTIMED: %e\n", selftimed_50);

    GibCursorGibCursorGibIntProd tmp_struct_53 =
                                  sumList(end_r_308, pvrtmp_838);
    GibCursor pvrtmp_847 = tmp_struct_53.field0;
    GibCursor pvrtmp_848 = tmp_struct_53.field1;
    GibInt pvrtmp_849 = tmp_struct_53.field2;

    printf("%ld", pvrtmp_849);
    printf("\n");
    return 0;
}
