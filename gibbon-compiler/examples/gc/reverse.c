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
reverse(GibCursor end_r_281, GibCursor end_r_282, GibCursor end_r_283,
        GibCursor loc_280, GibCursor xs_21_85_129, GibCursor acc_22_86_130);
GibCursorGibCursorGibIntProd sumList(GibCursor end_r_285,
                                     GibCursor xs_25_89_134);
GibCursorGibCursorGibCursorProd buildList(GibCursor end_r_287,
                                          GibCursor loc_286,
                                          GibInt n_28_92_138);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList(GibCursor end_r_290, GibCursor end_r_291, GibCursor loc_289,
            GibCursor arg_57_93_142);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList(GibCursor end_r_294, GibCursor end_r_295,
                         GibCursor loc_293, GibCursor arg_62_98_147);
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_297,
                                       GibCursor arg_67_103_152);
GibCursorGibCursorProd _print_PList(GibCursor end_r_299,
                                    GibCursor arg_72_107_156);
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
    gib_add_symbol(809, ")");
    gib_add_symbol(810, "(Nil ");
    gib_add_symbol(811, "(Cons ");
    gib_add_symbol(812, " ->r ");
    gib_add_symbol(813, " ->i ");
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_281,
                                                                   GibCursor end_r_282,
                                                                   GibCursor end_r_283,
                                                                   GibCursor loc_280,
                                                                   GibCursor xs_21_85_129,
                                                                   GibCursor acc_22_86_130)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_280 + 18 > end_r_283) {
        gib_grow_region(&loc_280, &end_r_283);
    }

    GibPackedTag tmpval_842 = *(GibPackedTag *) xs_21_85_129;
    GibCursor tmpcur_843 = xs_21_85_129 + 1;


  switch_897:
    ;
    switch (tmpval_842) {

      case 1:
        {
            GibCursor jump_397 = xs_21_85_129 + 1;

            if (loc_280 + 18 > end_r_283) {
                gib_grow_region(&loc_280, &end_r_283);
            }
            gib_indirection_barrier(loc_280, end_r_283, acc_22_86_130,
                                    end_r_282, PList_T);

            GibCursor end_525 = loc_280 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_281,
                                                                                 end_r_282,
                                                                                 end_r_283,
                                                                                 jump_397,
                                                                                 loc_280,
                                                                                 end_525};
            break;
        }

      case 0:
        {
            GibInt tmpval_848 = *(GibInt *) tmpcur_843;
            GibCursor tmpcur_849 = tmpcur_843 + sizeof(GibInt);

            gib_shadowstack_push(rstack, acc_22_86_130, end_r_282, Stk,
                                 PList_T);
            gib_shadowstack_push(rstack, tmpcur_849, end_r_281, Stk, PList_T);
            gib_shadowstack_push(wstack, loc_280, end_r_283, Stk, PList_T);

            GibChunk region_850 = gib_alloc_region(64);
            GibCursor r_335 = region_850.start;
            GibCursor end_r_335 = region_850.end;

            frame = gib_shadowstack_pop(wstack);
            loc_280 = frame->ptr;
            end_r_283 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_849 = frame->ptr;
            end_r_281 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            acc_22_86_130 = frame->ptr;
            end_r_282 = frame->endptr;

            GibCursor loc_324 = r_335 + 9;

            *(GibPackedTag *) r_335 = 0;

            GibCursor writetag_532 = r_335 + 1;
            GibCursor after_tag_533 = r_335 + 1;

            *(GibInt *) after_tag_533 = tmpval_848;

            GibCursor writecur_537 = after_tag_533 + sizeof(GibInt);

            if (loc_324 + 18 > end_r_335) {
                gib_grow_region(&loc_324, &end_r_335);
            }
            gib_indirection_barrier(loc_324, end_r_335, acc_22_86_130,
                                    end_r_282, PList_T);

            GibCursor end_530 = loc_324 + 9;
            GibBool chk_543 = tmpcur_849 < end_r_281;

            #ifdef _GIBBON_DEBUG
            assert(chk_543);
            #endif

            GibBool chk_542 = r_335 < end_r_335;

            #ifdef _GIBBON_DEBUG
            assert(chk_542);
            #endif

            GibBool chk_541 = loc_280 < end_r_283;

            #ifdef _GIBBON_DEBUG
            assert(chk_541);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_3 =
             reverse(end_r_281, end_r_335, end_r_283, loc_280, tmpcur_849, r_335);
            GibCursor pvrtmp_855 = tmp_struct_3.field0;
            GibCursor pvrtmp_856 = tmp_struct_3.field1;
            GibCursor pvrtmp_857 = tmp_struct_3.field2;
            GibCursor pvrtmp_858 = tmp_struct_3.field3;
            GibCursor pvrtmp_859 = tmp_struct_3.field4;
            GibCursor pvrtmp_860 = tmp_struct_3.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_855,
                                                                                 end_r_282,
                                                                                 pvrtmp_857,
                                                                                 pvrtmp_858,
                                                                                 pvrtmp_859,
                                                                                 pvrtmp_860};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_843;
            GibCursor tmpcur_867 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_868 = tmpcur_843 + 8;
            uint16_t tmptag_869 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_indr_433 = tmpcur_867 + tmptag_869;
            GibCursor jump_435 = tmpcur_843 + 8;
            GibBool chk_549 = tmpcur_867 < end_from_tagged_indr_433;

            #ifdef _GIBBON_DEBUG
            assert(chk_549);
            #endif

            GibBool chk_548 = acc_22_86_130 < end_r_282;

            #ifdef _GIBBON_DEBUG
            assert(chk_548);
            #endif

            GibBool chk_547 = loc_280 < end_r_283;

            #ifdef _GIBBON_DEBUG
            assert(chk_547);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_7 =
             reverse(end_from_tagged_indr_433, end_r_282, end_r_283, loc_280, tmpcur_867, acc_22_86_130);
            GibCursor pvrtmp_870 = tmp_struct_7.field0;
            GibCursor pvrtmp_871 = tmp_struct_7.field1;
            GibCursor pvrtmp_872 = tmp_struct_7.field2;
            GibCursor pvrtmp_873 = tmp_struct_7.field3;
            GibCursor pvrtmp_874 = tmp_struct_7.field4;
            GibCursor pvrtmp_875 = tmp_struct_7.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_281,
                                                                                 pvrtmp_871,
                                                                                 pvrtmp_872,
                                                                                 jump_435,
                                                                                 pvrtmp_874,
                                                                                 pvrtmp_875};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) tmpcur_843;
            GibCursor tmpcur_882 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_883 = tmpcur_843 + 8;
            uint16_t tmptag_884 = GIB_GET_TAG(tagged_tmpcur_10);
            GibCursor end_from_tagged_indr_433 = tmpcur_882 + tmptag_884;
            GibBool chk_555 = tmpcur_882 < end_from_tagged_indr_433;

            #ifdef _GIBBON_DEBUG
            assert(chk_555);
            #endif

            GibBool chk_554 = acc_22_86_130 < end_r_282;

            #ifdef _GIBBON_DEBUG
            assert(chk_554);
            #endif

            GibBool chk_553 = loc_280 < end_r_283;

            #ifdef _GIBBON_DEBUG
            assert(chk_553);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_9 =
             reverse(end_from_tagged_indr_433, end_r_282, end_r_283, loc_280, tmpcur_882, acc_22_86_130);
            GibCursor pvrtmp_885 = tmp_struct_9.field0;
            GibCursor pvrtmp_886 = tmp_struct_9.field1;
            GibCursor pvrtmp_887 = tmp_struct_9.field2;
            GibCursor pvrtmp_888 = tmp_struct_9.field3;
            GibCursor pvrtmp_889 = tmp_struct_9.field4;
            GibCursor pvrtmp_890 = tmp_struct_9.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_885,
                                                                                 pvrtmp_886,
                                                                                 pvrtmp_887,
                                                                                 pvrtmp_888,
                                                                                 pvrtmp_889,
                                                                                 pvrtmp_890};
            break;
        }

      default:
        {
            printf("Unknown tag in tmpval_842(%p), %d\n", xs_21_85_129, tmpval_842);
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd sumList(GibCursor end_r_285,
                                     GibCursor xs_25_89_134)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_898 = *(GibPackedTag *) xs_25_89_134;
    GibCursor tmpcur_899 = xs_25_89_134 + 1;


  switch_917:
    ;
    switch (tmpval_898) {

      case 1:
        {
            GibCursor jump_402 = xs_25_89_134 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_285, jump_402, 0};
            break;
        }

      case 0:
        {
            GibInt tmpval_900 = *(GibInt *) tmpcur_899;
            GibCursor tmpcur_901 = tmpcur_899 + sizeof(GibInt);
            GibBool chk_560 = tmpcur_901 < end_r_285;

            #ifdef _GIBBON_DEBUG
            assert(chk_560);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_14 =
                                          sumList(end_r_285, tmpcur_901);
            GibCursor pvrtmp_902 = tmp_struct_14.field0;
            GibCursor pvrtmp_903 = tmp_struct_14.field1;
            GibInt pvrtmp_904 = tmp_struct_14.field2;
            GibInt tailprim_405 = tmpval_900 + pvrtmp_904;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_902, pvrtmp_903,
                                                   tailprim_405};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) tmpcur_899;
            GibCursor tmpcur_905 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_906 = tmpcur_899 + 8;
            uint16_t tmptag_907 = GIB_GET_TAG(tagged_tmpcur_16);
            GibCursor end_from_tagged_indr_439 = tmpcur_905 + tmptag_907;
            GibCursor jump_441 = tmpcur_899 + 8;
            GibBool chk_564 = tmpcur_905 < end_from_tagged_indr_439;

            #ifdef _GIBBON_DEBUG
            assert(chk_564);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_15 =
                                          sumList(end_from_tagged_indr_439, tmpcur_905);
            GibCursor pvrtmp_908 = tmp_struct_15.field0;
            GibCursor pvrtmp_909 = tmp_struct_15.field1;
            GibInt pvrtmp_910 = tmp_struct_15.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_285, jump_441,
                                                   pvrtmp_910};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_18 = *(uintptr_t *) tmpcur_899;
            GibCursor tmpcur_911 = GIB_UNTAG(tagged_tmpcur_18);
            GibCursor tmpaftercur_912 = tmpcur_899 + 8;
            uint16_t tmptag_913 = GIB_GET_TAG(tagged_tmpcur_18);
            GibCursor end_from_tagged_indr_439 = tmpcur_911 + tmptag_913;
            GibBool chk_568 = tmpcur_911 < end_from_tagged_indr_439;

            #ifdef _GIBBON_DEBUG
            assert(chk_568);
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_17 =
                                          sumList(end_from_tagged_indr_439, tmpcur_911);
            GibCursor pvrtmp_914 = tmp_struct_17.field0;
            GibCursor pvrtmp_915 = tmp_struct_17.field1;
            GibInt pvrtmp_916 = tmp_struct_17.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_914, pvrtmp_915,
                                                   pvrtmp_916};
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_898(%p) %d", xs_25_89_134, tmpval_898);
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildList(GibCursor end_r_287,
                                          GibCursor loc_286, GibInt n_28_92_138)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_286 + 18 > end_r_287) {
        gib_grow_region(&loc_286, &end_r_287);
    }

    GibBool fltIf_120_139 = n_28_92_138 == 0;

    if (fltIf_120_139) {
        *(GibPackedTag *) loc_286 = 1;

        GibCursor writetag_570 = loc_286 + 1;
        GibCursor after_tag_571 = loc_286 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_287, loc_286,
                                                  after_tag_571};
    } else {
        GibInt fltAppE_122_140 = n_28_92_138 - 1;
        GibCursor loc_345 = loc_286 + 9;

        *(GibPackedTag *) loc_286 = 0;

        GibCursor writetag_579 = loc_286 + 1;
        GibCursor after_tag_580 = loc_286 + 1;

        *(GibInt *) after_tag_580 = n_28_92_138;

        GibCursor writecur_584 = after_tag_580 + sizeof(GibInt);

        gib_shadowstack_push(rstack, loc_286, end_r_287, Stk, PList_T);

        GibBool chk_577 = loc_345 < end_r_287;

        #ifdef _GIBBON_DEBUG
        assert(chk_577);
        #endif

        GibCursorGibCursorGibCursorProd tmp_struct_19 =
                                         buildList(end_r_287, loc_345, fltAppE_122_140);
        GibCursor pvrtmp_922 = tmp_struct_19.field0;
        GibCursor pvrtmp_923 = tmp_struct_19.field1;
        GibCursor pvrtmp_924 = tmp_struct_19.field2;

        frame = gib_shadowstack_pop(rstack);
        loc_286 = frame->ptr;
        end_r_287 = frame->endptr;
        return (GibCursorGibCursorGibCursorProd) {pvrtmp_922, loc_286,
                                                  pvrtmp_924};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList(GibCursor end_r_290,
                                                              GibCursor end_r_291,
                                                              GibCursor loc_289,
                                                              GibCursor arg_57_93_142)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_289 + 18 > end_r_291) {
        gib_grow_region(&loc_289, &end_r_291);
    }

    GibPackedTag tmpval_933 = *(GibPackedTag *) arg_57_93_142;
    GibCursor tmpcur_934 = arg_57_93_142 + 1;


  switch_982:
    ;
    switch (tmpval_933) {

      case 0:
        {
            GibInt tmpval_935 = *(GibInt *) tmpcur_934;
            GibCursor tmpcur_936 = tmpcur_934 + sizeof(GibInt);
            GibCursor loc_357 = loc_289 + 9;

            *(GibPackedTag *) loc_289 = 0;

            GibCursor writetag_593 = loc_289 + 1;
            GibCursor after_tag_594 = loc_289 + 1;

            *(GibInt *) after_tag_594 = tmpval_935;

            GibCursor writecur_598 = after_tag_594 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_289, end_r_291, Stk, PList_T);

            GibBool chk_591 = tmpcur_936 < end_r_290;

            #ifdef _GIBBON_DEBUG
            assert(chk_591);
            #endif

            GibBool chk_590 = loc_357 < end_r_291;

            #ifdef _GIBBON_DEBUG
            assert(chk_590);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_23 =
                                                               _copy_PList(end_r_290, end_r_291, loc_357, tmpcur_936);
            GibCursor pvrtmp_937 = tmp_struct_23.field0;
            GibCursor pvrtmp_938 = tmp_struct_23.field1;
            GibCursor pvrtmp_939 = tmp_struct_23.field2;
            GibCursor pvrtmp_940 = tmp_struct_23.field3;
            GibCursor pvrtmp_941 = tmp_struct_23.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_289 = frame->ptr;
            end_r_291 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_937,
                                                                        pvrtmp_938,
                                                                        pvrtmp_939,
                                                                        loc_289,
                                                                        pvrtmp_941};
            break;
        }

      case 1:
        {
            GibCursor jump_411 = arg_57_93_142 + 1;

            *(GibPackedTag *) loc_289 = 1;

            GibCursor writetag_603 = loc_289 + 1;
            GibCursor after_tag_604 = loc_289 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_290,
                                                                        end_r_291,
                                                                        jump_411,
                                                                        loc_289,
                                                                        after_tag_604};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_934;
            GibCursor tmpcur_954 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_955 = tmpcur_934 + 8;
            uint16_t tmptag_956 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_indr_445 = tmpcur_954 + tmptag_956;
            GibCursor jump_447 = tmpcur_934 + 8;
            GibBool chk_613 = tmpcur_954 < end_from_tagged_indr_445;

            #ifdef _GIBBON_DEBUG
            assert(chk_613);
            #endif

            GibBool chk_612 = loc_289 < end_r_291;

            #ifdef _GIBBON_DEBUG
            assert(chk_612);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                               _copy_PList(end_from_tagged_indr_445, end_r_291, loc_289, tmpcur_954);
            GibCursor pvrtmp_957 = tmp_struct_24.field0;
            GibCursor pvrtmp_958 = tmp_struct_24.field1;
            GibCursor pvrtmp_959 = tmp_struct_24.field2;
            GibCursor pvrtmp_960 = tmp_struct_24.field3;
            GibCursor pvrtmp_961 = tmp_struct_24.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_290,
                                                                        pvrtmp_958,
                                                                        jump_447,
                                                                        pvrtmp_960,
                                                                        pvrtmp_961};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_934;
            GibCursor tmpcur_968 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_969 = tmpcur_934 + 8;
            uint16_t tmptag_970 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_445 = tmpcur_968 + tmptag_970;
            GibBool chk_618 = tmpcur_968 < end_from_tagged_indr_445;

            #ifdef _GIBBON_DEBUG
            assert(chk_618);
            #endif

            GibBool chk_617 = loc_289 < end_r_291;

            #ifdef _GIBBON_DEBUG
            assert(chk_617);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_26 =
                                                               _copy_PList(end_from_tagged_indr_445, end_r_291, loc_289, tmpcur_968);
            GibCursor pvrtmp_971 = tmp_struct_26.field0;
            GibCursor pvrtmp_972 = tmp_struct_26.field1;
            GibCursor pvrtmp_973 = tmp_struct_26.field2;
            GibCursor pvrtmp_974 = tmp_struct_26.field3;
            GibCursor pvrtmp_975 = tmp_struct_26.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_971,
                                                                        pvrtmp_972,
                                                                        pvrtmp_973,
                                                                        pvrtmp_974,
                                                                        pvrtmp_975};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_933");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList(GibCursor end_r_294,
                                                                           GibCursor end_r_295,
                                                                           GibCursor loc_293,
                                                                           GibCursor arg_62_98_147)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_983 = *(GibPackedTag *) arg_62_98_147;
    GibCursor tmpcur_984 = arg_62_98_147 + 1;


  switch_1032:
    ;
    switch (tmpval_983) {

      case 0:
        {
            GibInt tmpval_985 = *(GibInt *) tmpcur_984;
            GibCursor tmpcur_986 = tmpcur_984 + sizeof(GibInt);
            GibCursor loc_370 = loc_293 + 9;

            *(GibPackedTag *) loc_293 = 0;

            GibCursor writetag_625 = loc_293 + 1;
            GibCursor after_tag_626 = loc_293 + 1;

            *(GibInt *) after_tag_626 = tmpval_985;

            GibCursor writecur_630 = after_tag_626 + sizeof(GibInt);

            gib_shadowstack_push(rstack, loc_293, end_r_295, Stk, PList_T);

            GibBool chk_623 = tmpcur_986 < end_r_294;

            #ifdef _GIBBON_DEBUG
            assert(chk_623);
            #endif

            GibBool chk_622 = loc_370 < end_r_295;

            #ifdef _GIBBON_DEBUG
            assert(chk_622);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_31 =
                                                               _copy_without_ptrs_PList(end_r_294, end_r_295, loc_370, tmpcur_986);
            GibCursor pvrtmp_987 = tmp_struct_31.field0;
            GibCursor pvrtmp_988 = tmp_struct_31.field1;
            GibCursor pvrtmp_989 = tmp_struct_31.field2;
            GibCursor pvrtmp_990 = tmp_struct_31.field3;
            GibCursor pvrtmp_991 = tmp_struct_31.field4;

            frame = gib_shadowstack_pop(rstack);
            loc_293 = frame->ptr;
            end_r_295 = frame->endptr;
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_987,
                                                                        pvrtmp_988,
                                                                        pvrtmp_989,
                                                                        loc_293,
                                                                        pvrtmp_991};
            break;
        }

      case 1:
        {
            GibCursor jump_416 = arg_62_98_147 + 1;

            *(GibPackedTag *) loc_293 = 1;

            GibCursor writetag_635 = loc_293 + 1;
            GibCursor after_tag_636 = loc_293 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_294,
                                                                        end_r_295,
                                                                        jump_416,
                                                                        loc_293,
                                                                        after_tag_636};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) tmpcur_984;
            GibCursor tmpcur_1004 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_1005 = tmpcur_984 + 8;
            uint16_t tmptag_1006 = GIB_GET_TAG(tagged_tmpcur_33);
            GibCursor end_from_tagged_indr_451 = tmpcur_1004 + tmptag_1006;
            GibCursor jump_453 = tmpcur_984 + 8;
            GibBool chk_645 = tmpcur_1004 < end_from_tagged_indr_451;

            #ifdef _GIBBON_DEBUG
            assert(chk_645);
            #endif

            GibBool chk_644 = loc_293 < end_r_295;

            #ifdef _GIBBON_DEBUG
            assert(chk_644);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_32 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_451, end_r_295, loc_293, tmpcur_1004);
            GibCursor pvrtmp_1007 = tmp_struct_32.field0;
            GibCursor pvrtmp_1008 = tmp_struct_32.field1;
            GibCursor pvrtmp_1009 = tmp_struct_32.field2;
            GibCursor pvrtmp_1010 = tmp_struct_32.field3;
            GibCursor pvrtmp_1011 = tmp_struct_32.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_294,
                                                                        pvrtmp_1008,
                                                                        jump_453,
                                                                        pvrtmp_1010,
                                                                        pvrtmp_1011};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_984;
            GibCursor tmpcur_1018 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_1019 = tmpcur_984 + 8;
            uint16_t tmptag_1020 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_indr_451 = tmpcur_1018 + tmptag_1020;
            GibBool chk_650 = tmpcur_1018 < end_from_tagged_indr_451;

            #ifdef _GIBBON_DEBUG
            assert(chk_650);
            #endif

            GibBool chk_649 = loc_293 < end_r_295;

            #ifdef _GIBBON_DEBUG
            assert(chk_649);
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_34 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_451, end_r_295, loc_293, tmpcur_1018);
            GibCursor pvrtmp_1021 = tmp_struct_34.field0;
            GibCursor pvrtmp_1022 = tmp_struct_34.field1;
            GibCursor pvrtmp_1023 = tmp_struct_34.field2;
            GibCursor pvrtmp_1024 = tmp_struct_34.field3;
            GibCursor pvrtmp_1025 = tmp_struct_34.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1021,
                                                                        pvrtmp_1022,
                                                                        pvrtmp_1023,
                                                                        pvrtmp_1024,
                                                                        pvrtmp_1025};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_983");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_297,
                                       GibCursor arg_67_103_152)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1033 = *(GibPackedTag *) arg_67_103_152;
    GibCursor tmpcur_1034 = arg_67_103_152 + 1;


  switch_1049:
    ;
    switch (tmpval_1033) {

      case 0:
        {
            GibInt tmpval_1035 = *(GibInt *) tmpcur_1034;
            GibCursor tmpcur_1036 = tmpcur_1034 + sizeof(GibInt);
            GibBool chk_654 = tmpcur_1036 < end_r_297;

            #ifdef _GIBBON_DEBUG
            assert(chk_654);
            #endif

            GibCursorGibCursorProd tmp_struct_36 =
                                    _traverse_PList(end_r_297, tmpcur_1036);
            GibCursor pvrtmp_1037 = tmp_struct_36.field0;
            GibCursor pvrtmp_1038 = tmp_struct_36.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1037, pvrtmp_1038};
            break;
        }

      case 1:
        {
            GibCursor jump_421 = arg_67_103_152 + 1;

            return (GibCursorGibCursorProd) {end_r_297, jump_421};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) tmpcur_1034;
            GibCursor tmpcur_1039 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_1040 = tmpcur_1034 + 8;
            uint16_t tmptag_1041 = GIB_GET_TAG(tagged_tmpcur_38);
            GibCursor end_from_tagged_indr_457 = tmpcur_1039 + tmptag_1041;
            GibCursor jump_459 = tmpcur_1034 + 8;
            GibBool chk_659 = tmpcur_1039 < end_from_tagged_indr_457;

            #ifdef _GIBBON_DEBUG
            assert(chk_659);
            #endif

            GibCursorGibCursorProd tmp_struct_37 =
                                    _traverse_PList(end_from_tagged_indr_457, tmpcur_1039);
            GibCursor pvrtmp_1042 = tmp_struct_37.field0;
            GibCursor pvrtmp_1043 = tmp_struct_37.field1;

            return (GibCursorGibCursorProd) {end_r_297, jump_459};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_1034;
            GibCursor tmpcur_1044 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_1045 = tmpcur_1034 + 8;
            uint16_t tmptag_1046 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_457 = tmpcur_1044 + tmptag_1046;
            GibBool chk_663 = tmpcur_1044 < end_from_tagged_indr_457;

            #ifdef _GIBBON_DEBUG
            assert(chk_663);
            #endif

            GibCursorGibCursorProd tmp_struct_39 =
                                    _traverse_PList(end_from_tagged_indr_457, tmpcur_1044);
            GibCursor pvrtmp_1047 = tmp_struct_39.field0;
            GibCursor pvrtmp_1048 = tmp_struct_39.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1047, pvrtmp_1048};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1033");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList(GibCursor end_r_299,
                                    GibCursor arg_72_107_156)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1050 = *(GibPackedTag *) arg_72_107_156;
    GibCursor tmpcur_1051 = arg_72_107_156 + 1;


  switch_1066:
    ;
    switch (tmpval_1050) {

      case 0:
        {
            GibInt tmpval_1052 = *(GibInt *) tmpcur_1051;
            GibCursor tmpcur_1053 = tmpcur_1051 + sizeof(GibInt);
            unsigned char wildcard_77_110_159 = gib_print_symbol(811);
            unsigned char y_75_111_160 = printf("%ld", tmpval_1052);
            GibBool chk_667 = tmpcur_1053 < end_r_299;

            #ifdef _GIBBON_DEBUG
            // assert(chk_667);
            #endif

            GibCursorGibCursorProd tmp_struct_41 =
                                    _print_PList(end_r_299, tmpcur_1053);
            GibCursor pvrtmp_1054 = tmp_struct_41.field0;
            GibCursor pvrtmp_1055 = tmp_struct_41.field1;
            unsigned char wildcard_78_113_162 = gib_print_symbol(809);

            return (GibCursorGibCursorProd) {pvrtmp_1054, pvrtmp_1055};
            break;
        }

      case 1:
        {
            GibCursor jump_426 = arg_72_107_156 + 1;
            unsigned char wildcard_79_114_163 = gib_print_symbol(810);
            unsigned char wildcard_80_115_164 = gib_print_symbol(809);

            return (GibCursorGibCursorProd) {end_r_299, jump_426};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_1051;
            GibCursor tmpcur_1056 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_1057 = tmpcur_1051 + 8;
            uint16_t tmptag_1058 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_indr_463 = tmpcur_1056 + tmptag_1058;
            GibCursor jump_465 = tmpcur_1051 + 8;
            unsigned char wildcard_468 = gib_print_symbol(813);
            GibBool chk_672 = tmpcur_1056 < end_from_tagged_indr_463;

            #ifdef _GIBBON_DEBUG
            // assert(chk_672);
            #endif

            GibCursorGibCursorProd tmp_struct_42 =
                                    _print_PList(end_from_tagged_indr_463, tmpcur_1056);
            GibCursor pvrtmp_1059 = tmp_struct_42.field0;
            GibCursor pvrtmp_1060 = tmp_struct_42.field1;

            return (GibCursorGibCursorProd) {end_r_299, jump_465};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_45 = *(uintptr_t *) tmpcur_1051;
            GibCursor tmpcur_1061 = GIB_UNTAG(tagged_tmpcur_45);
            GibCursor tmpaftercur_1062 = tmpcur_1051 + 8;
            uint16_t tmptag_1063 = GIB_GET_TAG(tagged_tmpcur_45);
            GibCursor end_from_tagged_indr_463 = tmpcur_1061 + tmptag_1063;
            unsigned char wildcard_468 = gib_print_symbol(812);
            GibBool chk_676 = tmpcur_1061 < end_from_tagged_indr_463;

            #ifdef _GIBBON_DEBUG
            // assert(chk_676);
            #endif

            GibCursorGibCursorProd tmp_struct_44 =
                                    _print_PList(end_from_tagged_indr_463, tmpcur_1061);
            GibCursor pvrtmp_1064 = tmp_struct_44.field0;
            GibCursor pvrtmp_1065 = tmp_struct_44.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1064, pvrtmp_1065};
            break;
        }

      default:
        {
            printf("Unknown tag in: tmpval_1050 %d", tmpval_1050);
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
    GibInt n_17_81_123 = gib_get_size_param();
    GibChunk region_814 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_317 = region_814.start;
    GibCursor end_r_317 = region_814.end;
    GibBool chk_678 = r_317 < end_r_317;

    #ifdef _GIBBON_DEBUG
    assert(chk_678);
    #endif

    GibCursorGibCursorGibCursorProd tmp_struct_46 =
                                     buildList(end_r_317, r_317, n_17_81_123);
    GibCursor pvrtmp_815 = tmp_struct_46.field0;
    GibCursor pvrtmp_816 = tmp_struct_46.field1;
    GibCursor pvrtmp_817 = tmp_struct_46.field2;

    gib_shadowstack_push(rstack, r_317, pvrtmp_815, Stk, PList_T);

    GibChunk region_822 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_316 = region_822.start;
    GibCursor end_r_316 = region_822.end;

    frame = gib_shadowstack_pop(rstack);
    r_317 = frame->ptr;
    pvrtmp_815 = frame->endptr;
    *(GibPackedTag *) r_316 = 1;

    GibCursor writetag_680 = r_316 + 1;
    GibCursor after_tag_681 = r_316 + 1;

    gib_shadowstack_push(rstack, r_317, pvrtmp_815, Stk, PList_T);
    gib_shadowstack_push(rstack, r_316, end_r_316, Stk, PList_T);

    GibChunk region_825 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_315 = region_825.start;
    GibCursor end_r_315 = region_825.end;

    frame = gib_shadowstack_pop(rstack);
    r_316 = frame->ptr;
    end_r_316 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    r_317 = frame->ptr;
    pvrtmp_815 = frame->endptr;
    gib_shadowstack_push(rstack, r_317, pvrtmp_815, Stk, PList_T);

    GibBool chk_689 = r_317 < pvrtmp_815;

    #ifdef _GIBBON_DEBUG
    assert(chk_689);
    #endif

    GibBool chk_688 = r_316 < end_r_316;

    #ifdef _GIBBON_DEBUG
    assert(chk_688);
    #endif

    GibBool chk_687 = r_315 < end_r_315;

    #ifdef _GIBBON_DEBUG
    assert(chk_687);
    #endif

    GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                                reverse(pvrtmp_815, end_r_316, end_r_315, r_315, pvrtmp_816, r_316);
    GibCursor pvrtmp_826 = tmp_struct_47.field0;
    GibCursor pvrtmp_827 = tmp_struct_47.field1;
    GibCursor pvrtmp_828 = tmp_struct_47.field2;
    GibCursor pvrtmp_829 = tmp_struct_47.field3;
    GibCursor pvrtmp_830 = tmp_struct_47.field4;
    GibCursor pvrtmp_831 = tmp_struct_47.field5;

    frame = gib_shadowstack_pop(rstack);
    r_317 = frame->ptr;
    pvrtmp_815 = frame->endptr;
    gib_shadowstack_push(rstack, r_315, pvrtmp_828, Stk, PList_T);
    pvrtmp_816 = r_317;

    GibBool chk_691 = r_317 < pvrtmp_815;

    #ifdef _GIBBON_DEBUG
    assert(chk_691);
    #endif

    GibCursorGibCursorGibIntProd tmp_struct_48 =
                                  sumList(pvrtmp_815, pvrtmp_816);
    GibCursor pvrtmp_836 = tmp_struct_48.field0;
    GibCursor pvrtmp_837 = tmp_struct_48.field1;
    GibInt pvrtmp_838 = tmp_struct_48.field2;

    frame = gib_shadowstack_pop(rstack);
    r_315 = frame->ptr;
    pvrtmp_828 = frame->endptr;

    GibBool chk_693 = r_315 < pvrtmp_828;

    #ifdef _GIBBON_DEBUG
    assert(chk_693);
    #endif

    GibCursorGibCursorGibIntProd tmp_struct_49 =
                                  sumList(pvrtmp_828, pvrtmp_830);
    GibCursor pvrtmp_839 = tmp_struct_49.field0;
    GibCursor pvrtmp_840 = tmp_struct_49.field1;
    GibInt pvrtmp_841 = tmp_struct_49.field2;
    GibBool tailprim_431 = pvrtmp_838 == pvrtmp_841;

    if (tailprim_431) {
        printf("#t");
        printf("\n");
        return 0;
    } else {
        printf("#f");
        printf("\n");
        return 0;
    }
}
