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
GibCursorGibCursorGibIntProd sumPList(GibCursor end_r_287,
                                      GibCursor xs_27_94_137);
GibCursorGibCursorGibCursorProd buildList(GibCursor end_r_289,
                                          GibCursor loc_288,
                                          GibInt n_30_97_141);
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
reverse(GibCursor end_r_293, GibCursor end_r_294, GibCursor end_r_295,
        GibCursor loc_292, GibCursor xs_31_98_145, GibCursor acc_32_99_146);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList(GibCursor end_r_298, GibCursor end_r_299, GibCursor loc_297,
            GibCursor arg_66_105_150);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList(GibCursor end_r_302, GibCursor end_r_303,
                         GibCursor loc_301, GibCursor arg_71_110_155);
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_305,
                                       GibCursor arg_76_115_160);
GibCursorGibCursorProd _print_PList(GibCursor end_r_307,
                                    GibCursor arg_81_119_164);
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
    gib_add_symbol(854, ")");
    gib_add_symbol(855, "(Nil ");
    gib_add_symbol(856, "(Cons ");
    gib_add_symbol(857, " ->r ");
    gib_add_symbol(858, " ->i ");
}
GibCursorGibCursorGibIntProd sumPList(GibCursor end_r_287,
                                      GibCursor xs_27_94_137)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_896 = *(GibPackedTag *) xs_27_94_137;
    GibCursor tmpcur_897 = xs_27_94_137 + 1;


  switch_915:
    ;
    switch (tmpval_896) {

      case 1:
        {
            GibCursor jump_406 = xs_27_94_137 + 1;

            return (GibCursorGibCursorGibIntProd) {end_r_287, jump_406, 0};
            break;
        }

      case 0:
        {
            GibInt tmpval_898 = *(GibInt *) tmpcur_897;
            GibCursor tmpcur_899 = tmpcur_897 + sizeof(GibInt);
            GibCursorGibCursorGibIntProd tmp_struct_0 =
                                          sumPList(end_r_287, tmpcur_899);
            GibCursor pvrtmp_900 = tmp_struct_0.field0;
            GibCursor pvrtmp_901 = tmp_struct_0.field1;
            GibInt pvrtmp_902 = tmp_struct_0.field2;
            GibInt tailprim_409 = tmpval_898 + pvrtmp_902;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_900, pvrtmp_901,
                                                   tailprim_409};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_2 = *(uintptr_t *) tmpcur_897;
            GibCursor tmpcur_903 = GIB_UNTAG(tagged_tmpcur_2);
            GibCursor tmpaftercur_904 = tmpcur_897 + 8;
            uint16_t tmptag_905 = GIB_GET_TAG(tagged_tmpcur_2);
            GibCursor end_from_tagged_indr_441 = tmpcur_903 + tmptag_905;
            GibCursor jump_443 = tmpcur_897 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_1 =
                                          sumPList(end_from_tagged_indr_441, tmpcur_903);
            GibCursor pvrtmp_906 = tmp_struct_1.field0;
            GibCursor pvrtmp_907 = tmp_struct_1.field1;
            GibInt pvrtmp_908 = tmp_struct_1.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_287, jump_443,
                                                   pvrtmp_908};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_4 = *(uintptr_t *) tmpcur_897;
            GibCursor tmpcur_909 = GIB_UNTAG(tagged_tmpcur_4);
            GibCursor tmpaftercur_910 = tmpcur_897 + 8;
            uint16_t tmptag_911 = GIB_GET_TAG(tagged_tmpcur_4);
            GibCursor end_from_tagged_indr_441 = tmpcur_909 + tmptag_911;
            GibCursorGibCursorGibIntProd tmp_struct_3 =
                                          sumPList(end_from_tagged_indr_441, tmpcur_909);
            GibCursor pvrtmp_912 = tmp_struct_3.field0;
            GibCursor pvrtmp_913 = tmp_struct_3.field1;
            GibInt pvrtmp_914 = tmp_struct_3.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_912, pvrtmp_913,
                                                   pvrtmp_914};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_896");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd buildList(GibCursor end_r_289,
                                          GibCursor loc_288, GibInt n_30_97_141)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_288 + 18 > end_r_289) {
        gib_grow_region(&loc_288, &end_r_289);
    }

    GibBool fltIf_129_142 = n_30_97_141 == 0;

    if (fltIf_129_142) {
        *(GibPackedTag *) loc_288 = 1;

        GibCursor writetag_572 = loc_288 + 1;
        GibCursor after_tag_573 = loc_288 + 1;

        return (GibCursorGibCursorGibCursorProd) {end_r_289, loc_288,
                                                  after_tag_573};
    } else {
        GibInt fltAppE_131_143 = n_30_97_141 - 1;
        GibCursor loc_335 = loc_288 + 9;

        *(GibPackedTag *) loc_288 = 0;

        GibCursor writetag_581 = loc_288 + 1;
        GibCursor after_tag_582 = loc_288 + 1;

        *(GibInt *) after_tag_582 = n_30_97_141;

        GibCursor writecur_586 = after_tag_582 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd tmp_struct_5 =
                                         buildList(end_r_289, loc_335, fltAppE_131_143);
        GibCursor pvrtmp_920 = tmp_struct_5.field0;
        GibCursor pvrtmp_921 = tmp_struct_5.field1;
        GibCursor pvrtmp_922 = tmp_struct_5.field2;

        return (GibCursorGibCursorGibCursorProd) {pvrtmp_920, loc_288,
                                                  pvrtmp_922};
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd reverse(GibCursor end_r_293,
                                                                   GibCursor end_r_294,
                                                                   GibCursor end_r_295,
                                                                   GibCursor loc_292,
                                                                   GibCursor xs_31_98_145,
                                                                   GibCursor acc_32_99_146)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (UNLIKELY((loc_292 + 18) > end_r_295)) {
        gib_grow_region(&loc_292, &end_r_295);
    }

    GibPackedTag tmpval_931 = *(GibPackedTag *) xs_31_98_145;
    GibCursor tmpcur_932 = xs_31_98_145 + 1;


  switch_986:
    ;
    switch (tmpval_931) {

      case 0:
        {
            GibInt tmpval_937 = *(GibInt *) tmpcur_932;
            GibCursor tmpcur_938 = tmpcur_932 + sizeof(GibInt);

            gib_shadowstack_push(rstack, acc_32_99_146, end_r_294, Stk, PList_T);
            gib_shadowstack_push(rstack, tmpcur_938, end_r_293, Stk, PList_T);
            gib_shadowstack_push(wstack, loc_292, end_r_295, Stk, PList_T);

            GibChunk region_939 =
                     gib_alloc_region(32);
            GibCursor r_356 = region_939.start;
            GibCursor end_r_356 = region_939.end;

            frame = gib_shadowstack_pop(wstack);
            loc_292 = frame->ptr;
            end_r_295 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            tmpcur_938 = frame->ptr;
            end_r_293 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            acc_32_99_146 = frame->ptr;
            end_r_294 = frame->endptr;

            GibCursor loc_345 = r_356 + 9;

            *(GibPackedTag *) r_356 = 0;

            GibCursor writetag_599 = r_356 + 1;
            GibCursor after_tag_600 = r_356 + 1;

            *(GibInt *) after_tag_600 = tmpval_937;

            GibCursor writecur_604 = after_tag_600 + sizeof(GibInt);

            if (loc_345 + 18 > end_r_356) {
                gib_grow_region(&loc_345, &end_r_356);
            }
            gib_indirection_barrier(loc_345, end_r_356, acc_32_99_146,
                                    end_r_294, PList_T);

            GibCursor end_597 = loc_345 + 9;
            // GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            // tmp_struct_12 =
              reverse(end_r_293, end_r_356, end_r_295, loc_292, tmpcur_938, r_356);
            // GibCursor pvrtmp_944 = tmp_struct_12.field0;
            // GibCursor pvrtmp_945 = tmp_struct_12.field1;
            // GibCursor pvrtmp_946 = tmp_struct_12.field2;
            // GibCursor pvrtmp_947 = tmp_struct_12.field3;
            // GibCursor pvrtmp_948 = tmp_struct_12.field4;
            // GibCursor pvrtmp_949 = tmp_struct_12.field5;

            // // gib_free_region(end_r_356);
            // return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_944,
            //                                                                      end_r_294,
            //                                                                      pvrtmp_946,
            //                                                                      pvrtmp_947,
            //                                                                      pvrtmp_948,
            //                                                                      pvrtmp_949};
            break;
        }

      case 1:
        {
            GibCursor jump_412 = xs_31_98_145 + 1;

            if (loc_292 + 18 > end_r_295) {
                gib_grow_region(&loc_292, &end_r_295);
            }
            gib_indirection_barrier(loc_292, end_r_295, acc_32_99_146,
                                    end_r_294, PList_T);

            GibCursor end_592 = loc_292 + 9;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_293,
                                                                                 end_r_294,
                                                                                 end_r_295,
                                                                                 jump_412,
                                                                                 loc_292,
                                                                                 end_592};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_932;
            GibCursor tmpcur_956 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_957 = tmpcur_932 + 8;
            uint16_t tmptag_958 = GIB_GET_TAG(tagged_tmpcur_17);
            GibCursor end_from_tagged_indr_447 = tmpcur_956 + tmptag_958;
            GibCursor jump_449 = tmpcur_932 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_16 =
             reverse(end_from_tagged_indr_447, end_r_294, end_r_295, loc_292, tmpcur_956, acc_32_99_146);
            GibCursor pvrtmp_959 = tmp_struct_16.field0;
            GibCursor pvrtmp_960 = tmp_struct_16.field1;
            GibCursor pvrtmp_961 = tmp_struct_16.field2;
            GibCursor pvrtmp_962 = tmp_struct_16.field3;
            GibCursor pvrtmp_963 = tmp_struct_16.field4;
            GibCursor pvrtmp_964 = tmp_struct_16.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_293,
                                                                                 pvrtmp_960,
                                                                                 pvrtmp_961,
                                                                                 jump_449,
                                                                                 pvrtmp_963,
                                                                                 pvrtmp_964};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_19 = *(uintptr_t *) tmpcur_932;
            GibCursor tmpcur_971 = GIB_UNTAG(tagged_tmpcur_19);
            GibCursor tmpaftercur_972 = tmpcur_932 + 8;
            uint16_t tmptag_973 = GIB_GET_TAG(tagged_tmpcur_19);
            GibCursor end_from_tagged_indr_447 = tmpcur_971 + tmptag_973;
            GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd
            tmp_struct_18 =
             reverse(end_from_tagged_indr_447, end_r_294, end_r_295, loc_292, tmpcur_971, acc_32_99_146);
            GibCursor pvrtmp_974 = tmp_struct_18.field0;
            GibCursor pvrtmp_975 = tmp_struct_18.field1;
            GibCursor pvrtmp_976 = tmp_struct_18.field2;
            GibCursor pvrtmp_977 = tmp_struct_18.field3;
            GibCursor pvrtmp_978 = tmp_struct_18.field4;
            GibCursor pvrtmp_979 = tmp_struct_18.field5;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_974,
                                                                                 pvrtmp_975,
                                                                                 pvrtmp_976,
                                                                                 pvrtmp_977,
                                                                                 pvrtmp_978,
                                                                                 pvrtmp_979};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_931");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList(GibCursor end_r_298,
                                                              GibCursor end_r_299,
                                                              GibCursor loc_297,
                                                              GibCursor arg_66_105_150)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_297 + 18 > end_r_299) {
        gib_grow_region(&loc_297, &end_r_299);
    }

    GibPackedTag tmpval_987 = *(GibPackedTag *) arg_66_105_150;
    GibCursor tmpcur_988 = arg_66_105_150 + 1;


  switch_1036:
    ;
    switch (tmpval_987) {

      case 0:
        {
            GibInt tmpval_989 = *(GibInt *) tmpcur_988;
            GibCursor tmpcur_990 = tmpcur_988 + sizeof(GibInt);
            GibCursor loc_365 = loc_297 + 9;

            *(GibPackedTag *) loc_297 = 0;

            GibCursor writetag_629 = loc_297 + 1;
            GibCursor after_tag_630 = loc_297 + 1;

            *(GibInt *) after_tag_630 = tmpval_989;

            GibCursor writecur_634 = after_tag_630 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_23 =
                                                               _copy_PList(end_r_298, end_r_299, loc_365, tmpcur_990);
            GibCursor pvrtmp_991 = tmp_struct_23.field0;
            GibCursor pvrtmp_992 = tmp_struct_23.field1;
            GibCursor pvrtmp_993 = tmp_struct_23.field2;
            GibCursor pvrtmp_994 = tmp_struct_23.field3;
            GibCursor pvrtmp_995 = tmp_struct_23.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_991,
                                                                        pvrtmp_992,
                                                                        pvrtmp_993,
                                                                        loc_297,
                                                                        pvrtmp_995};
            break;
        }

      case 1:
        {
            GibCursor jump_419 = arg_66_105_150 + 1;

            *(GibPackedTag *) loc_297 = 1;

            GibCursor writetag_639 = loc_297 + 1;
            GibCursor after_tag_640 = loc_297 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_298,
                                                                        end_r_299,
                                                                        jump_419,
                                                                        loc_297,
                                                                        after_tag_640};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_988;
            GibCursor tmpcur_1008 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_1009 = tmpcur_988 + 8;
            uint16_t tmptag_1010 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_indr_453 = tmpcur_1008 + tmptag_1010;
            GibCursor jump_455 = tmpcur_988 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                               _copy_PList(end_from_tagged_indr_453, end_r_299, loc_297, tmpcur_1008);
            GibCursor pvrtmp_1011 = tmp_struct_24.field0;
            GibCursor pvrtmp_1012 = tmp_struct_24.field1;
            GibCursor pvrtmp_1013 = tmp_struct_24.field2;
            GibCursor pvrtmp_1014 = tmp_struct_24.field3;
            GibCursor pvrtmp_1015 = tmp_struct_24.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_298,
                                                                        pvrtmp_1012,
                                                                        jump_455,
                                                                        pvrtmp_1014,
                                                                        pvrtmp_1015};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_988;
            GibCursor tmpcur_1022 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_1023 = tmpcur_988 + 8;
            uint16_t tmptag_1024 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_453 = tmpcur_1022 + tmptag_1024;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_26 =
                                                               _copy_PList(end_from_tagged_indr_453, end_r_299, loc_297, tmpcur_1022);
            GibCursor pvrtmp_1025 = tmp_struct_26.field0;
            GibCursor pvrtmp_1026 = tmp_struct_26.field1;
            GibCursor pvrtmp_1027 = tmp_struct_26.field2;
            GibCursor pvrtmp_1028 = tmp_struct_26.field3;
            GibCursor pvrtmp_1029 = tmp_struct_26.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1025,
                                                                        pvrtmp_1026,
                                                                        pvrtmp_1027,
                                                                        pvrtmp_1028,
                                                                        pvrtmp_1029};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_987");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList(GibCursor end_r_302,
                                                                           GibCursor end_r_303,
                                                                           GibCursor loc_301,
                                                                           GibCursor arg_71_110_155)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1037 = *(GibPackedTag *) arg_71_110_155;
    GibCursor tmpcur_1038 = arg_71_110_155 + 1;


  switch_1086:
    ;
    switch (tmpval_1037) {

      case 0:
        {
            GibInt tmpval_1039 = *(GibInt *) tmpcur_1038;
            GibCursor tmpcur_1040 = tmpcur_1038 + sizeof(GibInt);
            GibCursor loc_378 = loc_301 + 9;

            *(GibPackedTag *) loc_301 = 0;

            GibCursor writetag_661 = loc_301 + 1;
            GibCursor after_tag_662 = loc_301 + 1;

            *(GibInt *) after_tag_662 = tmpval_1039;

            GibCursor writecur_666 = after_tag_662 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_31 =
                                                               _copy_without_ptrs_PList(end_r_302, end_r_303, loc_378, tmpcur_1040);
            GibCursor pvrtmp_1041 = tmp_struct_31.field0;
            GibCursor pvrtmp_1042 = tmp_struct_31.field1;
            GibCursor pvrtmp_1043 = tmp_struct_31.field2;
            GibCursor pvrtmp_1044 = tmp_struct_31.field3;
            GibCursor pvrtmp_1045 = tmp_struct_31.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1041,
                                                                        pvrtmp_1042,
                                                                        pvrtmp_1043,
                                                                        loc_301,
                                                                        pvrtmp_1045};
            break;
        }

      case 1:
        {
            GibCursor jump_424 = arg_71_110_155 + 1;

            *(GibPackedTag *) loc_301 = 1;

            GibCursor writetag_671 = loc_301 + 1;
            GibCursor after_tag_672 = loc_301 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_302,
                                                                        end_r_303,
                                                                        jump_424,
                                                                        loc_301,
                                                                        after_tag_672};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_33 = *(uintptr_t *) tmpcur_1038;
            GibCursor tmpcur_1058 = GIB_UNTAG(tagged_tmpcur_33);
            GibCursor tmpaftercur_1059 = tmpcur_1038 + 8;
            uint16_t tmptag_1060 = GIB_GET_TAG(tagged_tmpcur_33);
            GibCursor end_from_tagged_indr_459 = tmpcur_1058 + tmptag_1060;
            GibCursor jump_461 = tmpcur_1038 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_32 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_459, end_r_303, loc_301, tmpcur_1058);
            GibCursor pvrtmp_1061 = tmp_struct_32.field0;
            GibCursor pvrtmp_1062 = tmp_struct_32.field1;
            GibCursor pvrtmp_1063 = tmp_struct_32.field2;
            GibCursor pvrtmp_1064 = tmp_struct_32.field3;
            GibCursor pvrtmp_1065 = tmp_struct_32.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_302,
                                                                        pvrtmp_1062,
                                                                        jump_461,
                                                                        pvrtmp_1064,
                                                                        pvrtmp_1065};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_1038;
            GibCursor tmpcur_1072 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_1073 = tmpcur_1038 + 8;
            uint16_t tmptag_1074 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_indr_459 = tmpcur_1072 + tmptag_1074;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_34 =
                                                               _copy_without_ptrs_PList(end_from_tagged_indr_459, end_r_303, loc_301, tmpcur_1072);
            GibCursor pvrtmp_1075 = tmp_struct_34.field0;
            GibCursor pvrtmp_1076 = tmp_struct_34.field1;
            GibCursor pvrtmp_1077 = tmp_struct_34.field2;
            GibCursor pvrtmp_1078 = tmp_struct_34.field3;
            GibCursor pvrtmp_1079 = tmp_struct_34.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_1075,
                                                                        pvrtmp_1076,
                                                                        pvrtmp_1077,
                                                                        pvrtmp_1078,
                                                                        pvrtmp_1079};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1037");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList(GibCursor end_r_305,
                                       GibCursor arg_76_115_160)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1087 = *(GibPackedTag *) arg_76_115_160;
    GibCursor tmpcur_1088 = arg_76_115_160 + 1;


  switch_1103:
    ;
    switch (tmpval_1087) {

      case 0:
        {
            GibInt tmpval_1089 = *(GibInt *) tmpcur_1088;
            GibCursor tmpcur_1090 = tmpcur_1088 + sizeof(GibInt);
            GibCursorGibCursorProd tmp_struct_36 =
                                    _traverse_PList(end_r_305, tmpcur_1090);
            GibCursor pvrtmp_1091 = tmp_struct_36.field0;
            GibCursor pvrtmp_1092 = tmp_struct_36.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1091, pvrtmp_1092};
            break;
        }

      case 1:
        {
            GibCursor jump_429 = arg_76_115_160 + 1;

            return (GibCursorGibCursorProd) {end_r_305, jump_429};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_38 = *(uintptr_t *) tmpcur_1088;
            GibCursor tmpcur_1093 = GIB_UNTAG(tagged_tmpcur_38);
            GibCursor tmpaftercur_1094 = tmpcur_1088 + 8;
            uint16_t tmptag_1095 = GIB_GET_TAG(tagged_tmpcur_38);
            GibCursor end_from_tagged_indr_465 = tmpcur_1093 + tmptag_1095;
            GibCursor jump_467 = tmpcur_1088 + 8;
            GibCursorGibCursorProd tmp_struct_37 =
                                    _traverse_PList(end_from_tagged_indr_465, tmpcur_1093);
            GibCursor pvrtmp_1096 = tmp_struct_37.field0;
            GibCursor pvrtmp_1097 = tmp_struct_37.field1;

            return (GibCursorGibCursorProd) {end_r_305, jump_467};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_1088;
            GibCursor tmpcur_1098 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_1099 = tmpcur_1088 + 8;
            uint16_t tmptag_1100 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_465 = tmpcur_1098 + tmptag_1100;
            GibCursorGibCursorProd tmp_struct_39 =
                                    _traverse_PList(end_from_tagged_indr_465, tmpcur_1098);
            GibCursor pvrtmp_1101 = tmp_struct_39.field0;
            GibCursor pvrtmp_1102 = tmp_struct_39.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1101, pvrtmp_1102};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1087");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList(GibCursor end_r_307,
                                    GibCursor arg_81_119_164)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_1104 = *(GibPackedTag *) arg_81_119_164;
    GibCursor tmpcur_1105 = arg_81_119_164 + 1;


  switch_1120:
    ;
    switch (tmpval_1104) {

      case 0:
        {
            GibInt tmpval_1106 = *(GibInt *) tmpcur_1105;
            GibCursor tmpcur_1107 = tmpcur_1105 + sizeof(GibInt);
            unsigned char wildcard_86_122_167 = gib_print_symbol(856);
            unsigned char y_84_123_168 = printf("%ld", tmpval_1106);
            GibCursorGibCursorProd tmp_struct_41 =
                                    _print_PList(end_r_307, tmpcur_1107);
            GibCursor pvrtmp_1108 = tmp_struct_41.field0;
            GibCursor pvrtmp_1109 = tmp_struct_41.field1;
            unsigned char wildcard_87_125_170 = gib_print_symbol(854);

            return (GibCursorGibCursorProd) {pvrtmp_1108, pvrtmp_1109};
            break;
        }

      case 1:
        {
            GibCursor jump_434 = arg_81_119_164 + 1;
            unsigned char wildcard_88_126_171 = gib_print_symbol(855);
            unsigned char wildcard_89_127_172 = gib_print_symbol(854);

            return (GibCursorGibCursorProd) {end_r_307, jump_434};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_1105;
            GibCursor tmpcur_1110 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_1111 = tmpcur_1105 + 8;
            uint16_t tmptag_1112 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_indr_471 = tmpcur_1110 + tmptag_1112;
            GibCursor jump_473 = tmpcur_1105 + 8;
            unsigned char wildcard_476 = gib_print_symbol(858);
            GibCursorGibCursorProd tmp_struct_42 =
                                    _print_PList(end_from_tagged_indr_471, tmpcur_1110);
            GibCursor pvrtmp_1113 = tmp_struct_42.field0;
            GibCursor pvrtmp_1114 = tmp_struct_42.field1;

            return (GibCursorGibCursorProd) {end_r_307, jump_473};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_45 = *(uintptr_t *) tmpcur_1105;
            GibCursor tmpcur_1115 = GIB_UNTAG(tagged_tmpcur_45);
            GibCursor tmpaftercur_1116 = tmpcur_1105 + 8;
            uint16_t tmptag_1117 = GIB_GET_TAG(tagged_tmpcur_45);
            GibCursor end_from_tagged_indr_471 = tmpcur_1115 + tmptag_1117;
            unsigned char wildcard_476 = gib_print_symbol(857);
            GibCursorGibCursorProd tmp_struct_44 =
                                    _print_PList(end_from_tagged_indr_471, tmpcur_1115);
            GibCursor pvrtmp_1118 = tmp_struct_44.field0;
            GibCursor pvrtmp_1119 = tmp_struct_44.field1;

            return (GibCursorGibCursorProd) {pvrtmp_1118, pvrtmp_1119};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1104");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_54 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibInt n_23_90_133 = gib_get_size_param();
    GibChunk region_859 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_325 = region_859.start;
    GibCursor end_r_325 = region_859.end;
    GibCursorGibCursorGibCursorProd tmp_struct_46 =
                                     buildList(end_r_325, r_325, n_23_90_133);
    GibCursor pvrtmp_860 = tmp_struct_46.field0;
    GibCursor pvrtmp_861 = tmp_struct_46.field1;
    GibCursor pvrtmp_862 = tmp_struct_46.field2;

    gib_shadowstack_push(rstack, r_325, pvrtmp_860, Stk, PList_T);

    GibChunk region_867 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_324 = region_867.start;
    GibCursor end_r_324 = region_867.end;

    frame = gib_shadowstack_pop(rstack);
    r_325 = frame->ptr;
    pvrtmp_860 = frame->endptr;
    *(GibPackedTag *) r_324 = 1;

    GibCursor writetag_716 = r_324 + 1;
    GibCursor after_tag_717 = r_324 + 1;

    gib_shadowstack_push(rstack, r_324, end_r_324, Stk, PList_T);
    gib_shadowstack_push(rstack, r_325, pvrtmp_860, Stk, PList_T);

    GibChunk region_870 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_323 = region_870.start;
    GibCursor end_r_323 = region_870.end;

    frame = gib_shadowstack_pop(rstack);
    r_325 = frame->ptr;
    pvrtmp_860 = frame->endptr;
    frame = gib_shadowstack_pop(rstack);
    r_324 = frame->ptr;
    end_r_324 = frame->endptr;

    GibCursor pvrtmp_883;
    GibCursor pvrtmp_884;
    GibCursor pvrtmp_885;
    GibVector *times_51 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_883;
    struct timespec end_pvrtmp_883;
    GibGcStateSnapshot *snapshot = gib_gc_init_state(3);
    for (long long iters_pvrtmp_883 = 0; iters_pvrtmp_883 <
         gib_get_iters_param(); iters_pvrtmp_883++) {
        if (iters_pvrtmp_883 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 3, region_859.end, region_867.end, region_870.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_883);

        GibCursorGibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47
                                                                   =
                                                                    reverse(pvrtmp_860, end_r_324, end_r_323, r_323, pvrtmp_861, r_324);
        GibCursor pvrtmp_871 = tmp_struct_47.field0;
        GibCursor pvrtmp_872 = tmp_struct_47.field1;
        GibCursor pvrtmp_873 = tmp_struct_47.field2;
        GibCursor pvrtmp_874 = tmp_struct_47.field3;
        GibCursor pvrtmp_875 = tmp_struct_47.field4;
        GibCursor pvrtmp_876 = tmp_struct_47.field5;

        pvrtmp_883 = pvrtmp_873;
        pvrtmp_884 = pvrtmp_875;
        pvrtmp_885 = pvrtmp_876;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_883);
        if (iters_pvrtmp_883 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_48 = gib_difftimespecs(&begin_pvrtmp_883,
                                               &end_pvrtmp_883);

        printf("itertime: %lf\n", itertime_48);
        gib_vector_inplace_update(times_51, iters_pvrtmp_883, &itertime_48);
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
                                  sumPList(end_r_323, pvrtmp_884);
    GibCursor pvrtmp_893 = tmp_struct_53.field0;
    GibCursor pvrtmp_894 = tmp_struct_53.field1;
    GibInt pvrtmp_895 = tmp_struct_53.field2;

    printf("%ld", pvrtmp_895);
    printf("\n");
    // gib_free_region(end_r_323);
    // gib_free_region(end_r_324);
    // gib_free_region(end_r_325);
    // return 0;

    int exit_55 = gib_exit();

    return exit_55;
}
