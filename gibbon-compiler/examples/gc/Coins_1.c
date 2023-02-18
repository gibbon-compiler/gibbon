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
typedef struct GibCursorGibIntGibIntProd_struct {
            GibCursor field0;
            GibInt field1;
            GibInt field2;
        } GibCursorGibIntGibIntProd;
typedef struct GibCursorGibBoolProd_struct {
            GibCursor field0;
            GibBool field1;
        } GibCursorGibBoolProd;
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
GibCursorGibCursorProd check_coins(GibCursor end_r_1152, GibInt amt_65_480_692,
                                   GibCursor tr_66_481_693);
GibCursorGibCursorGibCursorGibCursorProd payA_seq(GibCursor end_r_1155,
                                                  GibCursor end_r_1156,
                                                  GibCursor loc_1154,
                                                  GibInt amt_72_487_702,
                                                  GibCursor coins_73_488_703);
GibCursorGibCursorGibCursorGibCursorProd getCoins1(GibCursor end_r_1159,
                                                   GibCursor end_r_1160,
                                                   GibCursor loc_1158,
                                                   GibInt c_90_505_715,
                                                   GibInt q_91_506_716,
                                                   GibCursor coins_rst_92_507_717);
GibCursorGibCursorGibIntProd lenA(GibCursor end_r_1162,
                                  GibCursor ls_93_508_722);
unsigned char print_check(GibBool b_110_513_729);
static inline
GibCursorGibIntGibIntProd head_plist_282(GibCursor end_r_1164,
                                         GibCursor ls_106_533_732);
static inline
GibCursorGibCursorGibCursorGibCursorProd tail_plist_283(GibCursor end_r_1167,
                                                        GibCursor end_r_1168,
                                                        GibCursor loc_1166,
                                                        GibCursor ls_102_537_736);
static inline
GibCursorGibBoolProd is_empty_plist_281(GibCursor end_r_1170,
                                        GibCursor ls_98_541_740);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_AList(GibCursor end_r_1173, GibCursor end_r_1174, GibCursor loc_1172,
            GibCursor arg_387_545_744);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_AList(GibCursor end_r_1177, GibCursor end_r_1178,
                         GibCursor loc_1176, GibCursor arg_396_554_753);
GibCursorGibCursorProd _traverse_AList(GibCursor end_r_1180,
                                       GibCursor arg_405_563_762);
GibCursorGibCursorProd _print_AList(GibCursor end_r_1182,
                                    GibCursor arg_414_570_769);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList_v_280(GibCursor end_r_1185, GibCursor end_r_1186,
                  GibCursor loc_1184, GibCursor arg_429_589_788);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList_v_280(GibCursor end_r_1189, GibCursor end_r_1190,
                               GibCursor loc_1188, GibCursor arg_436_596_795);
GibCursorGibCursorProd _traverse_PList_v_280(GibCursor end_r_1192,
                                             GibCursor arg_443_603_802);
GibCursorGibCursorProd _print_PList_v_280(GibCursor end_r_1194,
                                          GibCursor arg_450_608_807);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Maybe_v_284(GibCursor end_r_1197, GibCursor end_r_1198,
                  GibCursor loc_1196, GibCursor arg_461_622_821);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Maybe_v_284(GibCursor end_r_1201, GibCursor end_r_1202,
                               GibCursor loc_1200, GibCursor arg_464_625_824);
GibCursorGibCursorProd _traverse_Maybe_v_284(GibCursor end_r_1204,
                                             GibCursor arg_467_628_827);
GibCursorGibCursorProd _print_Maybe_v_284(GibCursor end_r_1206,
                                          GibCursor arg_470_630_829);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            AList_T,
            Maybe_v_284_T,
            PList_v_280_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(10);

    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }

    GibDatatype field_tys[3];

    error = gib_info_table_insert_packed_dcon(AList_T, 0, 8, 0, 1, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, AList_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(AList_T, 1, 8, 0, 1, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, AList_T, 1);
        exit(1);
    }
    field_tys[0] = AList_T;
    field_tys[1] = AList_T;
    error = gib_info_table_insert_packed_dcon(AList_T, 2, 0, 0, 0, 2, field_tys,
                                              2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, AList_T, 2);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Maybe_v_284_T, 0, 8, 0, 1, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_284_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Maybe_v_284_T, 1, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_284_T, 1);
        exit(1);
    }
    field_tys[0] = PList_v_280_T;
    error = gib_info_table_insert_packed_dcon(PList_v_280_T, 1, 16, 0, 2, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_280_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_v_280_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_280_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(2648, "OK\n");
    gib_add_symbol(2649, "Err\n");
    gib_add_symbol(2650, ")");
    gib_add_symbol(2651, "(Nothing_v_284 ");
    gib_add_symbol(2652, "(Nil_v_280 ");
    gib_add_symbol(2653, "(Just_v_284 ");
    gib_add_symbol(2654, "(Cons_v_280 ");
    gib_add_symbol(2655, "(Append ");
    gib_add_symbol(2656, "(ASing ");
    gib_add_symbol(2657, "(ANil ");
    gib_add_symbol(2658, " ->r ");
    gib_add_symbol(2659, " ->i ");
    gib_add_symbol(2660, " ");
    gib_add_symbol(2661, "\n");
}
GibCursorGibCursorProd check_coins(GibCursor end_r_1152, GibInt amt_65_480_692,
                                   GibCursor tr_66_481_693)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibBool chk_1871 = tr_66_481_693 < end_r_1152;

    #ifdef _GIBBON_DEBUG
    #endif

    GibCursorGibCursorGibIntProd tmp_struct_0 =
                                  lenA(end_r_1152, tr_66_481_693);
    GibCursor pvrtmp_2700 = tmp_struct_0.field0;
    GibCursor pvrtmp_2701 = tmp_struct_0.field1;
    GibInt pvrtmp_2702 = tmp_struct_0.field2;
    GibBool fltIf_656_695 = amt_65_480_692 == 777;

    if (fltIf_656_695) {
        GibBool fltAppE_657_696 = pvrtmp_2702 == 140899;
        unsigned char tailapp_1474 =  print_check(fltAppE_657_696);

        return (GibCursorGibCursorProd) {pvrtmp_2700, pvrtmp_2701};
    } else {
        GibBool fltIf_658_697 = amt_65_480_692 == 999;

        if (fltIf_658_697) {
            GibBool fltAppE_659_698 = pvrtmp_2702 == 329565;
            unsigned char tailapp_1475 =  print_check(fltAppE_659_698);

            return (GibCursorGibCursorProd) {pvrtmp_2700, pvrtmp_2701};
        } else {
            unsigned char wildcard__45_68_483_699 = printf("%ld", pvrtmp_2702);
            unsigned char wildcard__43_69_484_700 = gib_print_symbol(2661);
            unsigned char tailapp_1476 =  print_check(true);

            return (GibCursorGibCursorProd) {pvrtmp_2700, pvrtmp_2701};
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd payA_seq(GibCursor end_r_1155,
                                                  GibCursor end_r_1156,
                                                  GibCursor loc_1154,
                                                  GibInt amt_72_487_702,
                                                  GibCursor coins_73_488_703)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1154 + 18 > end_r_1156) {
        gib_grow_region(&loc_1154, &end_r_1156);
    }

    GibBool fltIf_661_704 = amt_72_487_702 == 0;

    if (fltIf_661_704) {
        *(GibPackedTag *) loc_1154 = 1;

        GibCursor writetag_1873 = loc_1154 + 1;
        GibCursor after_tag_1874 = loc_1154 + 1;

        *(GibInt *) after_tag_1874 = 1;

        GibCursor writecur_1878 = after_tag_1874 + sizeof(GibInt);

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1155,
                                                           end_r_1156, loc_1154,
                                                           writecur_1878};
    } else {
        GibBool chk_1881 = coins_73_488_703 < end_r_1155;

        #ifdef _GIBBON_DEBUG
        #endif

        GibCursorGibBoolProd tmp_struct_1 =
                              is_empty_plist_281(end_r_1155, coins_73_488_703);
        GibCursor pvrtmp_2707 = tmp_struct_1.field0;
        GibBool pvrtmp_2708 = tmp_struct_1.field1;

        if (pvrtmp_2708) {
            *(GibPackedTag *) loc_1154 = 0;

            GibCursor writetag_1883 = loc_1154 + 1;
            GibCursor after_tag_1884 = loc_1154 + 1;

            *(GibInt *) after_tag_1884 = 0;

            GibCursor writecur_1888 = after_tag_1884 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2707,
                                                               end_r_1156,
                                                               loc_1154,
                                                               writecur_1888};
        } else {
            GibBool chk_1891 = coins_73_488_703 < end_r_1155;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibIntGibIntProd tmp_struct_2 =
                                       head_plist_282(end_r_1155, coins_73_488_703);
            GibCursor pvrtmp_2713 = tmp_struct_2.field0;
            GibInt pvrtmp_2714 = tmp_struct_2.field1;
            GibInt pvrtmp_2715 = tmp_struct_2.field2;

            gib_shadowstack_push(rstack, coins_73_488_703, end_r_1155, Stk,
                                 PList_v_280_T);
            gib_shadowstack_push(wstack, loc_1154, end_r_1156, Stk, AList_T);

            GibChunk region_2718 =
                     gib_alloc_region(64);
            GibCursor r_1281 = region_2718.start;
            GibCursor end_r_1281 = region_2718.end;

            frame = gib_shadowstack_pop(wstack);
            loc_1154 = frame->ptr;
            end_r_1156 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            coins_73_488_703 = frame->ptr;
            end_r_1155 = frame->endptr;

            GibBool chk_1894 = coins_73_488_703 < end_r_1155;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_1893 = r_1281 < end_r_1281;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_3 =
                                                      tail_plist_283(end_r_1155, end_r_1281, r_1281, coins_73_488_703);
            GibCursor pvrtmp_2719 = tmp_struct_3.field0;
            GibCursor pvrtmp_2720 = tmp_struct_3.field1;
            GibCursor pvrtmp_2721 = tmp_struct_3.field2;
            GibCursor pvrtmp_2722 = tmp_struct_3.field3;
            GibBool fltIf_663_710 = pvrtmp_2714 > amt_72_487_702;

            if (fltIf_663_710) {
                GibBool chk_1897 = r_1281 < pvrtmp_2720;

                #ifdef _GIBBON_DEBUG
                #endif

                GibBool chk_1896 = loc_1154 < end_r_1156;

                #ifdef _GIBBON_DEBUG
                #endif

                // GibCursorGibCursorGibCursorGibCursorProd tmp_struct_4 =
                                                          return payA_seq(pvrtmp_2720, end_r_1156, loc_1154, amt_72_487_702, pvrtmp_2721);
                // GibCursor pvrtmp_2727 = tmp_struct_4.field0;
                // GibCursor pvrtmp_2728 = tmp_struct_4.field1;
                // GibCursor pvrtmp_2729 = tmp_struct_4.field2;
                // GibCursor pvrtmp_2730 = tmp_struct_4.field3;

                // return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2719,
                //                                                    pvrtmp_2728,
                //                                                    pvrtmp_2729,
                //                                                    pvrtmp_2730};
            } else {
                gib_shadowstack_push(rstack, pvrtmp_2721, pvrtmp_2720, Stk,
                                     PList_v_280_T);
                gib_shadowstack_push(wstack, loc_1154, end_r_1156, Stk,
                                     AList_T);

                GibChunk region_2737 =
                         gib_alloc_region(64);
                GibCursor r_1280 = region_2737.start;
                GibCursor end_r_1280 = region_2737.end;

                frame = gib_shadowstack_pop(wstack);
                loc_1154 = frame->ptr;
                end_r_1156 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                pvrtmp_2721 = frame->ptr;
                pvrtmp_2720 = frame->endptr;

                GibBool chk_1900 = r_1281 < pvrtmp_2720;

                #ifdef _GIBBON_DEBUG
                #endif

                GibBool chk_1899 = r_1280 < end_r_1280;

                #ifdef _GIBBON_DEBUG
                #endif

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_5 =
                                                          getCoins1(pvrtmp_2720, end_r_1280, r_1280, pvrtmp_2714, pvrtmp_2715, pvrtmp_2721);
                GibCursor pvrtmp_2738 = tmp_struct_5.field0;
                GibCursor pvrtmp_2739 = tmp_struct_5.field1;
                GibCursor pvrtmp_2740 = tmp_struct_5.field2;
                GibCursor pvrtmp_2741 = tmp_struct_5.field3;
                GibInt fltAppE_664_712 = amt_72_487_702 - pvrtmp_2714;
                GibCursor loc_1276 = loc_1154 + 1;

                *(GibPackedTag *) loc_1154 = 2;

                GibCursor writetag_1908 = loc_1154 + 1;

                gib_shadowstack_push(rstack, loc_1154, end_r_1156, Stk,
                                     AList_T);
                gib_shadowstack_push(rstack, pvrtmp_2721, pvrtmp_2720, Stk,
                                     PList_v_280_T);

                GibBool chk_1903 = r_1280 < pvrtmp_2739;

                #ifdef _GIBBON_DEBUG
                #endif

                GibBool chk_1902 = loc_1276 < end_r_1156;

                #ifdef _GIBBON_DEBUG
                #endif

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                          payA_seq(pvrtmp_2739, end_r_1156, loc_1276, fltAppE_664_712, pvrtmp_2740);
                GibCursor pvrtmp_2746 = tmp_struct_6.field0;
                GibCursor pvrtmp_2747 = tmp_struct_6.field1;
                GibCursor pvrtmp_2748 = tmp_struct_6.field2;
                GibCursor pvrtmp_2749 = tmp_struct_6.field3;

                frame = gib_shadowstack_pop(rstack);
                pvrtmp_2721 = frame->ptr;
                pvrtmp_2720 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                loc_1154 = frame->ptr;
                end_r_1156 = frame->endptr;
                gib_shadowstack_push(rstack, loc_1154, pvrtmp_2747, Stk,
                                     AList_T);

                GibBool chk_1906 = r_1281 < pvrtmp_2720;

                #ifdef _GIBBON_DEBUG
                #endif

                GibBool chk_1905 = pvrtmp_2749 < pvrtmp_2747;

                #ifdef _GIBBON_DEBUG
                #endif

                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_7 =
                                                          payA_seq(pvrtmp_2720, pvrtmp_2747, pvrtmp_2749, amt_72_487_702, pvrtmp_2721);
                GibCursor pvrtmp_2754 = tmp_struct_7.field0;
                GibCursor pvrtmp_2755 = tmp_struct_7.field1;
                GibCursor pvrtmp_2756 = tmp_struct_7.field2;
                GibCursor pvrtmp_2757 = tmp_struct_7.field3;

                frame = gib_shadowstack_pop(rstack);
                loc_1154 = frame->ptr;
                pvrtmp_2747 = frame->endptr;

                GibCursor after_tag_1909 = loc_1154 + 1;

                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2719,
                                                                   pvrtmp_2755,
                                                                   loc_1154,
                                                                   pvrtmp_2757};
            }
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd getCoins1(GibCursor end_r_1159,
                                                   GibCursor end_r_1160,
                                                   GibCursor loc_1158,
                                                   GibInt c_90_505_715,
                                                   GibInt q_91_506_716,
                                                   GibCursor coins_rst_92_507_717)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    // if (loc_1158 + 26 > end_r_1160) {
    //     gib_grow_region(&loc_1158, &end_r_1160);
    // }

    GibBool fltIf_665_718 = q_91_506_716 == 1;

    if (fltIf_665_718) {
        // if (loc_1158 + 18 > end_r_1160) {
        //     gib_grow_region(&loc_1158, &end_r_1160);
        // }
        gib_indirection_barrier(loc_1158, end_r_1160, coins_rst_92_507_717,
                                end_r_1159, PList_v_280_T);

        GibCursor end_1919 = loc_1158 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1159,
                                                           end_r_1160, loc_1158,
                                                           end_1919};
    } else {
        GibInt fltPkd_667_720 = q_91_506_716 - 1;
        GibCursor loc_1291 = loc_1158 + 17;

        *(GibPackedTag *) loc_1158 = 1;

        GibCursor writetag_1924 = loc_1158 + 1;
        GibCursor after_tag_1925 = loc_1158 + 1;

        *(GibInt *) after_tag_1925 = c_90_505_715;

        GibCursor writecur_1929 = after_tag_1925 + sizeof(GibInt);

        *(GibInt *) writecur_1929 = fltPkd_667_720;

        GibCursor writecur_1930 = writecur_1929 + sizeof(GibInt);

        if (loc_1291 + 18 > end_r_1160) {
            gib_grow_region(&loc_1291, &end_r_1160);
        }
        gib_indirection_barrier(loc_1291, end_r_1160, coins_rst_92_507_717,
                                end_r_1159, PList_v_280_T);

        GibCursor end_1922 = loc_1291 + 9;

        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1159,
                                                           end_r_1160, loc_1158,
                                                           end_1922};
    }
}
GibCursorGibCursorGibIntProd lenA(GibCursor end_r_1162, GibCursor ls_93_508_722)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2776 = *(GibPackedTag *) ls_93_508_722;
    GibCursor tmpcur_2777 = ls_93_508_722 + 1;


  switch_2800:
    ;
    switch (tmpval_2776) {

      case 0:
        {
            GibInt tmpval_2778 = *(GibInt *) tmpcur_2777;
            GibCursor tmpcur_2779 = tmpcur_2777 + sizeof(GibInt);
            GibCursor jump_1484 = tmpcur_2777 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_1162, jump_1484, 0};
            break;
        }

      case 1:
        {
            GibInt tmpval_2780 = *(GibInt *) tmpcur_2777;
            GibCursor tmpcur_2781 = tmpcur_2777 + sizeof(GibInt);
            GibCursor jump_1485 = tmpcur_2777 + 8;

            return (GibCursorGibCursorGibIntProd) {end_r_1162, jump_1485, 1};
            break;
        }

      case 2:
        {
            GibBool chk_1939 = tmpcur_2777 < end_r_1162;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_20 =
                                          lenA(end_r_1162, tmpcur_2777);
            GibCursor pvrtmp_2782 = tmp_struct_20.field0;
            GibCursor pvrtmp_2783 = tmp_struct_20.field1;
            GibInt pvrtmp_2784 = tmp_struct_20.field2;
            GibBool chk_1941 = pvrtmp_2783 < pvrtmp_2782;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_21 =
                                          lenA(pvrtmp_2782, pvrtmp_2783);
            GibCursor pvrtmp_2785 = tmp_struct_21.field0;
            GibCursor pvrtmp_2786 = tmp_struct_21.field1;
            GibInt pvrtmp_2787 = tmp_struct_21.field2;
            GibInt tailprim_1488 = pvrtmp_2784 + pvrtmp_2787;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2785, pvrtmp_2786,
                                                   tailprim_1488};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_23 = *(uintptr_t *) tmpcur_2777;
            GibCursor tmpcur_2788 = GIB_UNTAG(tagged_tmpcur_23);
            GibCursor tmpaftercur_2789 = tmpcur_2777 + 8;
            uint16_t tmptag_2790 = GIB_GET_TAG(tagged_tmpcur_23);
            GibCursor end_from_tagged_indr_1575 = tmpcur_2788 + tmptag_2790;
            GibCursor jump_1577 = tmpcur_2777 + 8;
            GibBool chk_1945 = tmpcur_2788 < end_from_tagged_indr_1575;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_22 =
                                          lenA(end_from_tagged_indr_1575, tmpcur_2788);
            GibCursor pvrtmp_2791 = tmp_struct_22.field0;
            GibCursor pvrtmp_2792 = tmp_struct_22.field1;
            GibInt pvrtmp_2793 = tmp_struct_22.field2;

            return (GibCursorGibCursorGibIntProd) {end_r_1162, jump_1577,
                                                   pvrtmp_2793};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_25 = *(uintptr_t *) tmpcur_2777;
            GibCursor tmpcur_2794 = GIB_UNTAG(tagged_tmpcur_25);
            GibCursor tmpaftercur_2795 = tmpcur_2777 + 8;
            uint16_t tmptag_2796 = GIB_GET_TAG(tagged_tmpcur_25);
            GibCursor end_from_tagged_indr_1575 = tmpcur_2794 + tmptag_2796;
            GibBool chk_1949 = tmpcur_2794 < end_from_tagged_indr_1575;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibIntProd tmp_struct_24 =
                                          lenA(end_from_tagged_indr_1575, tmpcur_2794);
            GibCursor pvrtmp_2797 = tmp_struct_24.field0;
            GibCursor pvrtmp_2798 = tmp_struct_24.field1;
            GibInt pvrtmp_2799 = tmp_struct_24.field2;

            return (GibCursorGibCursorGibIntProd) {pvrtmp_2797, pvrtmp_2798,
                                                   pvrtmp_2799};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2776");
            exit(1);
        }
    }
}
unsigned char print_check(GibBool b_110_513_729)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (b_110_513_729) {
        unsigned char wildcard__14_111_514_730 = gib_print_symbol(2648);

        return 0;
    } else {
        unsigned char wildcard__16_112_515_731 = gib_print_symbol(2649);

        return 0;
    }
}
static inline
GibCursorGibIntGibIntProd head_plist_282(GibCursor end_r_1164,
                                         GibCursor ls_106_533_732)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2801 = *(GibPackedTag *) ls_106_533_732;
    GibCursor tmpcur_2802 = ls_106_533_732 + 1;


  switch_2825:
    ;
    switch (tmpval_2801) {

      case 1:
        {
            GibInt tmpval_2803 = *(GibInt *) tmpcur_2802;
            GibCursor tmpcur_2804 = tmpcur_2802 + sizeof(GibInt);
            GibInt tmpval_2805 = *(GibInt *) tmpcur_2804;
            GibCursor tmpcur_2806 = tmpcur_2804 + sizeof(GibInt);

            return (GibCursorGibIntGibIntProd) {end_r_1164, tmpval_2803,
                                                tmpval_2805};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2802;
            GibCursor tmpcur_2809 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2810 = tmpcur_2802 + 8;
            uint16_t tmptag_2811 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_1581 = tmpcur_2809 + tmptag_2811;
            GibCursor jump_1583 = tmpcur_2802 + 8;
            GibBool chk_1956 = tmpcur_2809 < end_from_tagged_indr_1581;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibIntGibIntProd tmp_struct_26 =
                                       head_plist_282(end_from_tagged_indr_1581, tmpcur_2809);
            GibCursor pvrtmp_2812 = tmp_struct_26.field0;
            GibInt pvrtmp_2813 = tmp_struct_26.field1;
            GibInt pvrtmp_2814 = tmp_struct_26.field2;

            return (GibCursorGibIntGibIntProd) {end_r_1164, pvrtmp_2813,
                                                pvrtmp_2814};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_2802;
            GibCursor tmpcur_2817 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_2818 = tmpcur_2802 + 8;
            uint16_t tmptag_2819 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_1581 = tmpcur_2817 + tmptag_2819;
            GibBool chk_1960 = tmpcur_2817 < end_from_tagged_indr_1581;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibIntGibIntProd tmp_struct_28 =
                                       head_plist_282(end_from_tagged_indr_1581, tmpcur_2817);
            GibCursor pvrtmp_2820 = tmp_struct_28.field0;
            GibInt pvrtmp_2821 = tmp_struct_28.field1;
            GibInt pvrtmp_2822 = tmp_struct_28.field2;

            return (GibCursorGibIntGibIntProd) {pvrtmp_2820, pvrtmp_2821,
                                                pvrtmp_2822};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2801");
            exit(1);
        }
    }
}
static inline
GibCursorGibCursorGibCursorGibCursorProd tail_plist_283(GibCursor end_r_1167,
                                                        GibCursor end_r_1168,
                                                        GibCursor loc_1166,
                                                        GibCursor ls_102_537_736)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    // if (loc_1166 + 26 > end_r_1168) {
    //     gib_grow_region(&loc_1166, &end_r_1168);
    // }

    GibPackedTag tmpval_2826 = *(GibPackedTag *) ls_102_537_736;
    GibCursor tmpcur_2827 = ls_102_537_736 + 1;


  switch_2862:
    ;
    switch (tmpval_2826) {

      case 1:
        {
            GibInt tmpval_2828 = *(GibInt *) tmpcur_2827;
            GibCursor tmpcur_2829 = tmpcur_2827 + sizeof(GibInt);
            GibInt tmpval_2830 = *(GibInt *) tmpcur_2829;
            GibCursor tmpcur_2831 = tmpcur_2829 + sizeof(GibInt);

            // if (loc_1166 + 18 > end_r_1168) {
            //     gib_grow_region(&loc_1166, &end_r_1168);
            // }
            gib_indirection_barrier(loc_1166, end_r_1168, tmpcur_2831,
                                    end_r_1167, PList_v_280_T);

            GibCursor end_1966 = loc_1166 + 9;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1167,
                                                               end_r_1168,
                                                               loc_1166,
                                                               end_1966};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) tmpcur_2827;
            GibCursor tmpcur_2836 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_2837 = tmpcur_2827 + 8;
            uint16_t tmptag_2838 = GIB_GET_TAG(tagged_tmpcur_34);
            GibCursor end_from_tagged_indr_1586 = tmpcur_2836 + tmptag_2838;
            GibCursor jump_1588 = tmpcur_2827 + 8;
            GibBool chk_1971 = tmpcur_2836 < end_from_tagged_indr_1586;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_1970 = loc_1166 < end_r_1168;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_33 =
                                                      tail_plist_283(end_from_tagged_indr_1586, end_r_1168, loc_1166, tmpcur_2836);
            GibCursor pvrtmp_2839 = tmp_struct_33.field0;
            GibCursor pvrtmp_2840 = tmp_struct_33.field1;
            GibCursor pvrtmp_2841 = tmp_struct_33.field2;
            GibCursor pvrtmp_2842 = tmp_struct_33.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1167,
                                                               pvrtmp_2840,
                                                               pvrtmp_2841,
                                                               pvrtmp_2842};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_2827;
            GibCursor tmpcur_2849 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_2850 = tmpcur_2827 + 8;
            uint16_t tmptag_2851 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_indr_1586 = tmpcur_2849 + tmptag_2851;
            GibBool chk_1976 = tmpcur_2849 < end_from_tagged_indr_1586;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_1975 = loc_1166 < end_r_1168;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_35 =
                                                      tail_plist_283(end_from_tagged_indr_1586, end_r_1168, loc_1166, tmpcur_2849);
            GibCursor pvrtmp_2852 = tmp_struct_35.field0;
            GibCursor pvrtmp_2853 = tmp_struct_35.field1;
            GibCursor pvrtmp_2854 = tmp_struct_35.field2;
            GibCursor pvrtmp_2855 = tmp_struct_35.field3;

            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2852,
                                                               pvrtmp_2853,
                                                               pvrtmp_2854,
                                                               pvrtmp_2855};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2826");
            exit(1);
        }
    }
}
static inline
GibCursorGibBoolProd is_empty_plist_281(GibCursor end_r_1170,
                                        GibCursor ls_98_541_740)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2863 = *(GibPackedTag *) ls_98_541_740;
    GibCursor tmpcur_2864 = ls_98_541_740 + 1;


  switch_2879:
    ;
    switch (tmpval_2863) {

      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_1170, true};
            break;
        }

      case 1:
        {
            GibInt tmpval_2865 = *(GibInt *) tmpcur_2864;
            GibCursor tmpcur_2866 = tmpcur_2864 + sizeof(GibInt);
            GibInt tmpval_2867 = *(GibInt *) tmpcur_2866;
            GibCursor tmpcur_2868 = tmpcur_2866 + sizeof(GibInt);

            return (GibCursorGibBoolProd) {end_r_1170, false};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) tmpcur_2864;
            GibCursor tmpcur_2869 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_2870 = tmpcur_2864 + 8;
            uint16_t tmptag_2871 = GIB_GET_TAG(tagged_tmpcur_41);
            GibCursor end_from_tagged_indr_1591 = tmpcur_2869 + tmptag_2871;
            GibCursor jump_1593 = tmpcur_2864 + 8;
            GibBool chk_1984 = tmpcur_2869 < end_from_tagged_indr_1591;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibBoolProd tmp_struct_40 =
                                  is_empty_plist_281(end_from_tagged_indr_1591, tmpcur_2869);
            GibCursor pvrtmp_2872 = tmp_struct_40.field0;
            GibBool pvrtmp_2873 = tmp_struct_40.field1;

            return (GibCursorGibBoolProd) {end_r_1170, pvrtmp_2873};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_43 = *(uintptr_t *) tmpcur_2864;
            GibCursor tmpcur_2874 = GIB_UNTAG(tagged_tmpcur_43);
            GibCursor tmpaftercur_2875 = tmpcur_2864 + 8;
            uint16_t tmptag_2876 = GIB_GET_TAG(tagged_tmpcur_43);
            GibCursor end_from_tagged_indr_1591 = tmpcur_2874 + tmptag_2876;
            GibBool chk_1988 = tmpcur_2874 < end_from_tagged_indr_1591;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibBoolProd tmp_struct_42 =
                                  is_empty_plist_281(end_from_tagged_indr_1591, tmpcur_2874);
            GibCursor pvrtmp_2877 = tmp_struct_42.field0;
            GibBool pvrtmp_2878 = tmp_struct_42.field1;

            return (GibCursorGibBoolProd) {pvrtmp_2877, pvrtmp_2878};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2863");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_AList(GibCursor end_r_1173,
                                                              GibCursor end_r_1174,
                                                              GibCursor loc_1172,
                                                              GibCursor arg_387_545_744)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1172 + 18 > end_r_1174) {
        gib_grow_region(&loc_1172, &end_r_1174);
    }

    GibPackedTag tmpval_2880 = *(GibPackedTag *) arg_387_545_744;
    GibCursor tmpcur_2881 = arg_387_545_744 + 1;


  switch_2944:
    ;
    switch (tmpval_2880) {

      case 0:
        {
            GibInt tmpval_2882 = *(GibInt *) tmpcur_2881;
            GibCursor tmpcur_2883 = tmpcur_2881 + sizeof(GibInt);
            GibCursor jump_1501 = tmpcur_2881 + 8;

            *(GibPackedTag *) loc_1172 = 0;

            GibCursor writetag_1992 = loc_1172 + 1;
            GibCursor after_tag_1993 = loc_1172 + 1;

            *(GibInt *) after_tag_1993 = tmpval_2882;

            GibCursor writecur_1997 = after_tag_1993 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1173,
                                                                        end_r_1174,
                                                                        jump_1501,
                                                                        loc_1172,
                                                                        writecur_1997};
            break;
        }

      case 1:
        {
            GibInt tmpval_2888 = *(GibInt *) tmpcur_2881;
            GibCursor tmpcur_2889 = tmpcur_2881 + sizeof(GibInt);
            GibCursor jump_1503 = tmpcur_2881 + 8;

            *(GibPackedTag *) loc_1172 = 1;

            GibCursor writetag_2002 = loc_1172 + 1;
            GibCursor after_tag_2003 = loc_1172 + 1;

            *(GibInt *) after_tag_2003 = tmpval_2888;

            GibCursor writecur_2007 = after_tag_2003 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1173,
                                                                        end_r_1174,
                                                                        jump_1503,
                                                                        loc_1172,
                                                                        writecur_2007};
            break;
        }

      case 2:
        {
            GibCursor loc_1340 = loc_1172 + 1;

            *(GibPackedTag *) loc_1172 = 2;

            GibCursor writetag_2017 = loc_1172 + 1;
            GibBool chk_2012 = tmpcur_2881 < end_r_1173;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2011 = loc_1340 < end_r_1174;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_44 =
                                                               _copy_AList(end_r_1173, end_r_1174, loc_1340, tmpcur_2881);
            GibCursor pvrtmp_2894 = tmp_struct_44.field0;
            GibCursor pvrtmp_2895 = tmp_struct_44.field1;
            GibCursor pvrtmp_2896 = tmp_struct_44.field2;
            GibCursor pvrtmp_2897 = tmp_struct_44.field3;
            GibCursor pvrtmp_2898 = tmp_struct_44.field4;
            GibBool chk_2015 = pvrtmp_2896 < pvrtmp_2894;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2014 = pvrtmp_2898 < pvrtmp_2895;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_45 =
                                                               _copy_AList(pvrtmp_2894, pvrtmp_2895, pvrtmp_2898, pvrtmp_2896);
            GibCursor pvrtmp_2903 = tmp_struct_45.field0;
            GibCursor pvrtmp_2904 = tmp_struct_45.field1;
            GibCursor pvrtmp_2905 = tmp_struct_45.field2;
            GibCursor pvrtmp_2906 = tmp_struct_45.field3;
            GibCursor pvrtmp_2907 = tmp_struct_45.field4;
            GibCursor after_tag_2018 = loc_1172 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2903,
                                                                        pvrtmp_2904,
                                                                        pvrtmp_2905,
                                                                        loc_1172,
                                                                        pvrtmp_2907};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_47 = *(uintptr_t *) tmpcur_2881;
            GibCursor tmpcur_2916 = GIB_UNTAG(tagged_tmpcur_47);
            GibCursor tmpaftercur_2917 = tmpcur_2881 + 8;
            uint16_t tmptag_2918 = GIB_GET_TAG(tagged_tmpcur_47);
            GibCursor end_from_tagged_indr_1596 = tmpcur_2916 + tmptag_2918;
            GibCursor jump_1598 = tmpcur_2881 + 8;
            GibBool chk_2030 = tmpcur_2916 < end_from_tagged_indr_1596;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2029 = loc_1172 < end_r_1174;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                               _copy_AList(end_from_tagged_indr_1596, end_r_1174, loc_1172, tmpcur_2916);
            GibCursor pvrtmp_2919 = tmp_struct_46.field0;
            GibCursor pvrtmp_2920 = tmp_struct_46.field1;
            GibCursor pvrtmp_2921 = tmp_struct_46.field2;
            GibCursor pvrtmp_2922 = tmp_struct_46.field3;
            GibCursor pvrtmp_2923 = tmp_struct_46.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1173,
                                                                        pvrtmp_2920,
                                                                        jump_1598,
                                                                        pvrtmp_2922,
                                                                        pvrtmp_2923};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) tmpcur_2881;
            GibCursor tmpcur_2930 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_2931 = tmpcur_2881 + 8;
            uint16_t tmptag_2932 = GIB_GET_TAG(tagged_tmpcur_49);
            GibCursor end_from_tagged_indr_1596 = tmpcur_2930 + tmptag_2932;
            GibBool chk_2035 = tmpcur_2930 < end_from_tagged_indr_1596;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2034 = loc_1172 < end_r_1174;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_48 =
                                                               _copy_AList(end_from_tagged_indr_1596, end_r_1174, loc_1172, tmpcur_2930);
            GibCursor pvrtmp_2933 = tmp_struct_48.field0;
            GibCursor pvrtmp_2934 = tmp_struct_48.field1;
            GibCursor pvrtmp_2935 = tmp_struct_48.field2;
            GibCursor pvrtmp_2936 = tmp_struct_48.field3;
            GibCursor pvrtmp_2937 = tmp_struct_48.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2933,
                                                                        pvrtmp_2934,
                                                                        pvrtmp_2935,
                                                                        pvrtmp_2936,
                                                                        pvrtmp_2937};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2880");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_AList(GibCursor end_r_1177,
                                                                           GibCursor end_r_1178,
                                                                           GibCursor loc_1176,
                                                                           GibCursor arg_396_554_753)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2945 = *(GibPackedTag *) arg_396_554_753;
    GibCursor tmpcur_2946 = arg_396_554_753 + 1;


  switch_3009:
    ;
    switch (tmpval_2945) {

      case 0:
        {
            GibInt tmpval_2947 = *(GibInt *) tmpcur_2946;
            GibCursor tmpcur_2948 = tmpcur_2946 + sizeof(GibInt);
            GibCursor jump_1508 = tmpcur_2946 + 8;

            *(GibPackedTag *) loc_1176 = 0;

            GibCursor writetag_2039 = loc_1176 + 1;
            GibCursor after_tag_2040 = loc_1176 + 1;

            *(GibInt *) after_tag_2040 = tmpval_2947;

            GibCursor writecur_2044 = after_tag_2040 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1177,
                                                                        end_r_1178,
                                                                        jump_1508,
                                                                        loc_1176,
                                                                        writecur_2044};
            break;
        }

      case 1:
        {
            GibInt tmpval_2953 = *(GibInt *) tmpcur_2946;
            GibCursor tmpcur_2954 = tmpcur_2946 + sizeof(GibInt);
            GibCursor jump_1510 = tmpcur_2946 + 8;

            *(GibPackedTag *) loc_1176 = 1;

            GibCursor writetag_2049 = loc_1176 + 1;
            GibCursor after_tag_2050 = loc_1176 + 1;

            *(GibInt *) after_tag_2050 = tmpval_2953;

            GibCursor writecur_2054 = after_tag_2050 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1177,
                                                                        end_r_1178,
                                                                        jump_1510,
                                                                        loc_1176,
                                                                        writecur_2054};
            break;
        }

      case 2:
        {
            GibCursor loc_1362 = loc_1176 + 1;

            *(GibPackedTag *) loc_1176 = 2;

            GibCursor writetag_2064 = loc_1176 + 1;
            GibBool chk_2059 = tmpcur_2946 < end_r_1177;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2058 = loc_1362 < end_r_1178;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_53 =
                                                               _copy_without_ptrs_AList(end_r_1177, end_r_1178, loc_1362, tmpcur_2946);
            GibCursor pvrtmp_2959 = tmp_struct_53.field0;
            GibCursor pvrtmp_2960 = tmp_struct_53.field1;
            GibCursor pvrtmp_2961 = tmp_struct_53.field2;
            GibCursor pvrtmp_2962 = tmp_struct_53.field3;
            GibCursor pvrtmp_2963 = tmp_struct_53.field4;
            GibBool chk_2062 = pvrtmp_2961 < pvrtmp_2959;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2061 = pvrtmp_2963 < pvrtmp_2960;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_54 =
                                                               _copy_without_ptrs_AList(pvrtmp_2959, pvrtmp_2960, pvrtmp_2963, pvrtmp_2961);
            GibCursor pvrtmp_2968 = tmp_struct_54.field0;
            GibCursor pvrtmp_2969 = tmp_struct_54.field1;
            GibCursor pvrtmp_2970 = tmp_struct_54.field2;
            GibCursor pvrtmp_2971 = tmp_struct_54.field3;
            GibCursor pvrtmp_2972 = tmp_struct_54.field4;
            GibCursor after_tag_2065 = loc_1176 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2968,
                                                                        pvrtmp_2969,
                                                                        pvrtmp_2970,
                                                                        loc_1176,
                                                                        pvrtmp_2972};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_56 = *(uintptr_t *) tmpcur_2946;
            GibCursor tmpcur_2981 = GIB_UNTAG(tagged_tmpcur_56);
            GibCursor tmpaftercur_2982 = tmpcur_2946 + 8;
            uint16_t tmptag_2983 = GIB_GET_TAG(tagged_tmpcur_56);
            GibCursor end_from_tagged_indr_1602 = tmpcur_2981 + tmptag_2983;
            GibCursor jump_1604 = tmpcur_2946 + 8;
            GibBool chk_2077 = tmpcur_2981 < end_from_tagged_indr_1602;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2076 = loc_1176 < end_r_1178;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_55 =
                                                               _copy_without_ptrs_AList(end_from_tagged_indr_1602, end_r_1178, loc_1176, tmpcur_2981);
            GibCursor pvrtmp_2984 = tmp_struct_55.field0;
            GibCursor pvrtmp_2985 = tmp_struct_55.field1;
            GibCursor pvrtmp_2986 = tmp_struct_55.field2;
            GibCursor pvrtmp_2987 = tmp_struct_55.field3;
            GibCursor pvrtmp_2988 = tmp_struct_55.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1177,
                                                                        pvrtmp_2985,
                                                                        jump_1604,
                                                                        pvrtmp_2987,
                                                                        pvrtmp_2988};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) tmpcur_2946;
            GibCursor tmpcur_2995 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_2996 = tmpcur_2946 + 8;
            uint16_t tmptag_2997 = GIB_GET_TAG(tagged_tmpcur_58);
            GibCursor end_from_tagged_indr_1602 = tmpcur_2995 + tmptag_2997;
            GibBool chk_2082 = tmpcur_2995 < end_from_tagged_indr_1602;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2081 = loc_1176 < end_r_1178;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_57 =
                                                               _copy_without_ptrs_AList(end_from_tagged_indr_1602, end_r_1178, loc_1176, tmpcur_2995);
            GibCursor pvrtmp_2998 = tmp_struct_57.field0;
            GibCursor pvrtmp_2999 = tmp_struct_57.field1;
            GibCursor pvrtmp_3000 = tmp_struct_57.field2;
            GibCursor pvrtmp_3001 = tmp_struct_57.field3;
            GibCursor pvrtmp_3002 = tmp_struct_57.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2998,
                                                                        pvrtmp_2999,
                                                                        pvrtmp_3000,
                                                                        pvrtmp_3001,
                                                                        pvrtmp_3002};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2945");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_AList(GibCursor end_r_1180,
                                       GibCursor arg_405_563_762)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3010 = *(GibPackedTag *) arg_405_563_762;
    GibCursor tmpcur_3011 = arg_405_563_762 + 1;


  switch_3030:
    ;
    switch (tmpval_3010) {

      case 0:
        {
            GibInt tmpval_3012 = *(GibInt *) tmpcur_3011;
            GibCursor tmpcur_3013 = tmpcur_3011 + sizeof(GibInt);
            GibCursor jump_1515 = tmpcur_3011 + 8;

            return (GibCursorGibCursorProd) {end_r_1180, jump_1515};
            break;
        }

      case 1:
        {
            GibInt tmpval_3014 = *(GibInt *) tmpcur_3011;
            GibCursor tmpcur_3015 = tmpcur_3011 + sizeof(GibInt);
            GibCursor jump_1517 = tmpcur_3011 + 8;

            return (GibCursorGibCursorProd) {end_r_1180, jump_1517};
            break;
        }

      case 2:
        {
            GibBool chk_2089 = tmpcur_3011 < end_r_1180;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_59 =
                                    _traverse_AList(end_r_1180, tmpcur_3011);
            GibCursor pvrtmp_3016 = tmp_struct_59.field0;
            GibCursor pvrtmp_3017 = tmp_struct_59.field1;
            GibBool chk_2091 = pvrtmp_3017 < pvrtmp_3016;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_60 =
                                    _traverse_AList(pvrtmp_3016, pvrtmp_3017);
            GibCursor pvrtmp_3018 = tmp_struct_60.field0;
            GibCursor pvrtmp_3019 = tmp_struct_60.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3018, pvrtmp_3019};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_62 = *(uintptr_t *) tmpcur_3011;
            GibCursor tmpcur_3020 = GIB_UNTAG(tagged_tmpcur_62);
            GibCursor tmpaftercur_3021 = tmpcur_3011 + 8;
            uint16_t tmptag_3022 = GIB_GET_TAG(tagged_tmpcur_62);
            GibCursor end_from_tagged_indr_1608 = tmpcur_3020 + tmptag_3022;
            GibCursor jump_1610 = tmpcur_3011 + 8;
            GibBool chk_2095 = tmpcur_3020 < end_from_tagged_indr_1608;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_61 =
                                    _traverse_AList(end_from_tagged_indr_1608, tmpcur_3020);
            GibCursor pvrtmp_3023 = tmp_struct_61.field0;
            GibCursor pvrtmp_3024 = tmp_struct_61.field1;

            return (GibCursorGibCursorProd) {end_r_1180, jump_1610};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_64 = *(uintptr_t *) tmpcur_3011;
            GibCursor tmpcur_3025 = GIB_UNTAG(tagged_tmpcur_64);
            GibCursor tmpaftercur_3026 = tmpcur_3011 + 8;
            uint16_t tmptag_3027 = GIB_GET_TAG(tagged_tmpcur_64);
            GibCursor end_from_tagged_indr_1608 = tmpcur_3025 + tmptag_3027;
            GibBool chk_2099 = tmpcur_3025 < end_from_tagged_indr_1608;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_63 =
                                    _traverse_AList(end_from_tagged_indr_1608, tmpcur_3025);
            GibCursor pvrtmp_3028 = tmp_struct_63.field0;
            GibCursor pvrtmp_3029 = tmp_struct_63.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3028, pvrtmp_3029};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3010");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_AList(GibCursor end_r_1182,
                                    GibCursor arg_414_570_769)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3031 = *(GibPackedTag *) arg_414_570_769;
    GibCursor tmpcur_3032 = arg_414_570_769 + 1;


  switch_3051:
    ;
    switch (tmpval_3031) {

      case 0:
        {
            GibInt tmpval_3033 = *(GibInt *) tmpcur_3032;
            GibCursor tmpcur_3034 = tmpcur_3032 + sizeof(GibInt);
            GibCursor jump_1522 = tmpcur_3032 + 8;
            unsigned char wildcard_417_572_771 = gib_print_symbol(2657);
            unsigned char y_416_573_772 = printf("%ld", tmpval_3033);
            unsigned char y_416_574_773 = gib_print_symbol(2660);
            unsigned char wildcard_418_575_774 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {end_r_1182, jump_1522};
            break;
        }

      case 1:
        {
            GibInt tmpval_3035 = *(GibInt *) tmpcur_3032;
            GibCursor tmpcur_3036 = tmpcur_3032 + sizeof(GibInt);
            GibCursor jump_1524 = tmpcur_3032 + 8;
            unsigned char wildcard_421_577_776 = gib_print_symbol(2656);
            unsigned char y_420_578_777 = printf("%ld", tmpval_3035);
            unsigned char y_420_579_778 = gib_print_symbol(2660);
            unsigned char wildcard_422_580_779 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {end_r_1182, jump_1524};
            break;
        }

      case 2:
        {
            unsigned char wildcard_427_583_782 = gib_print_symbol(2655);
            GibBool chk_2106 = tmpcur_3032 < end_r_1182;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_65 =
                                    _print_AList(end_r_1182, tmpcur_3032);
            GibCursor pvrtmp_3037 = tmp_struct_65.field0;
            GibCursor pvrtmp_3038 = tmp_struct_65.field1;
            unsigned char y_425_585_784 = gib_print_symbol(2660);
            GibBool chk_2108 = pvrtmp_3038 < pvrtmp_3037;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_66 =
                                    _print_AList(pvrtmp_3037, pvrtmp_3038);
            GibCursor pvrtmp_3039 = tmp_struct_66.field0;
            GibCursor pvrtmp_3040 = tmp_struct_66.field1;
            unsigned char y_426_587_786 = gib_print_symbol(2660);
            unsigned char wildcard_428_588_787 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {pvrtmp_3039, pvrtmp_3040};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_68 = *(uintptr_t *) tmpcur_3032;
            GibCursor tmpcur_3041 = GIB_UNTAG(tagged_tmpcur_68);
            GibCursor tmpaftercur_3042 = tmpcur_3032 + 8;
            uint16_t tmptag_3043 = GIB_GET_TAG(tagged_tmpcur_68);
            GibCursor end_from_tagged_indr_1614 = tmpcur_3041 + tmptag_3043;
            GibCursor jump_1616 = tmpcur_3032 + 8;
            unsigned char wildcard_1619 = gib_print_symbol(2659);
            GibBool chk_2112 = tmpcur_3041 < end_from_tagged_indr_1614;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_67 =
                                    _print_AList(end_from_tagged_indr_1614, tmpcur_3041);
            GibCursor pvrtmp_3044 = tmp_struct_67.field0;
            GibCursor pvrtmp_3045 = tmp_struct_67.field1;

            return (GibCursorGibCursorProd) {end_r_1182, jump_1616};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_70 = *(uintptr_t *) tmpcur_3032;
            GibCursor tmpcur_3046 = GIB_UNTAG(tagged_tmpcur_70);
            GibCursor tmpaftercur_3047 = tmpcur_3032 + 8;
            uint16_t tmptag_3048 = GIB_GET_TAG(tagged_tmpcur_70);
            GibCursor end_from_tagged_indr_1614 = tmpcur_3046 + tmptag_3048;
            unsigned char wildcard_1619 = gib_print_symbol(2658);
            GibBool chk_2116 = tmpcur_3046 < end_from_tagged_indr_1614;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_69 =
                                    _print_AList(end_from_tagged_indr_1614, tmpcur_3046);
            GibCursor pvrtmp_3049 = tmp_struct_69.field0;
            GibCursor pvrtmp_3050 = tmp_struct_69.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3049, pvrtmp_3050};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3031");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList_v_280(GibCursor end_r_1185,
                                                                    GibCursor end_r_1186,
                                                                    GibCursor loc_1184,
                                                                    GibCursor arg_429_589_788)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1184 + 26 > end_r_1186) {
        gib_grow_region(&loc_1184, &end_r_1186);
    }

    GibPackedTag tmpval_3052 = *(GibPackedTag *) arg_429_589_788;
    GibCursor tmpcur_3053 = arg_429_589_788 + 1;


  switch_3103:
    ;
    switch (tmpval_3052) {

      case 0:
        {
            GibCursor jump_1529 = arg_429_589_788 + 1;

            *(GibPackedTag *) loc_1184 = 0;

            GibCursor writetag_2119 = loc_1184 + 1;
            GibCursor after_tag_2120 = loc_1184 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1185,
                                                                        end_r_1186,
                                                                        jump_1529,
                                                                        loc_1184,
                                                                        after_tag_2120};
            break;
        }

      case 1:
        {
            GibInt tmpval_3058 = *(GibInt *) tmpcur_3053;
            GibCursor tmpcur_3059 = tmpcur_3053 + sizeof(GibInt);
            GibInt tmpval_3060 = *(GibInt *) tmpcur_3059;
            GibCursor tmpcur_3061 = tmpcur_3059 + sizeof(GibInt);
            GibCursor loc_1397 = loc_1184 + 17;

            *(GibPackedTag *) loc_1184 = 1;

            GibCursor writetag_2132 = loc_1184 + 1;
            GibCursor after_tag_2133 = loc_1184 + 1;

            *(GibInt *) after_tag_2133 = tmpval_3058;

            GibCursor writecur_2137 = after_tag_2133 + sizeof(GibInt);

            *(GibInt *) writecur_2137 = tmpval_3060;

            GibCursor writecur_2138 = writecur_2137 + sizeof(GibInt);
            GibBool chk_2130 = tmpcur_3061 < end_r_1185;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2129 = loc_1397 < end_r_1186;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_71 =
                                                               _copy_PList_v_280(end_r_1185, end_r_1186, loc_1397, tmpcur_3061);
            GibCursor pvrtmp_3062 = tmp_struct_71.field0;
            GibCursor pvrtmp_3063 = tmp_struct_71.field1;
            GibCursor pvrtmp_3064 = tmp_struct_71.field2;
            GibCursor pvrtmp_3065 = tmp_struct_71.field3;
            GibCursor pvrtmp_3066 = tmp_struct_71.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3062,
                                                                        pvrtmp_3063,
                                                                        pvrtmp_3064,
                                                                        loc_1184,
                                                                        pvrtmp_3066};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_73 = *(uintptr_t *) tmpcur_3053;
            GibCursor tmpcur_3075 = GIB_UNTAG(tagged_tmpcur_73);
            GibCursor tmpaftercur_3076 = tmpcur_3053 + 8;
            uint16_t tmptag_3077 = GIB_GET_TAG(tagged_tmpcur_73);
            GibCursor end_from_tagged_indr_1620 = tmpcur_3075 + tmptag_3077;
            GibCursor jump_1622 = tmpcur_3053 + 8;
            GibBool chk_2145 = tmpcur_3075 < end_from_tagged_indr_1620;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2144 = loc_1184 < end_r_1186;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_72 =
                                                               _copy_PList_v_280(end_from_tagged_indr_1620, end_r_1186, loc_1184, tmpcur_3075);
            GibCursor pvrtmp_3078 = tmp_struct_72.field0;
            GibCursor pvrtmp_3079 = tmp_struct_72.field1;
            GibCursor pvrtmp_3080 = tmp_struct_72.field2;
            GibCursor pvrtmp_3081 = tmp_struct_72.field3;
            GibCursor pvrtmp_3082 = tmp_struct_72.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1185,
                                                                        pvrtmp_3079,
                                                                        jump_1622,
                                                                        pvrtmp_3081,
                                                                        pvrtmp_3082};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_75 = *(uintptr_t *) tmpcur_3053;
            GibCursor tmpcur_3089 = GIB_UNTAG(tagged_tmpcur_75);
            GibCursor tmpaftercur_3090 = tmpcur_3053 + 8;
            uint16_t tmptag_3091 = GIB_GET_TAG(tagged_tmpcur_75);
            GibCursor end_from_tagged_indr_1620 = tmpcur_3089 + tmptag_3091;
            GibBool chk_2150 = tmpcur_3089 < end_from_tagged_indr_1620;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2149 = loc_1184 < end_r_1186;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_74 =
                                                               _copy_PList_v_280(end_from_tagged_indr_1620, end_r_1186, loc_1184, tmpcur_3089);
            GibCursor pvrtmp_3092 = tmp_struct_74.field0;
            GibCursor pvrtmp_3093 = tmp_struct_74.field1;
            GibCursor pvrtmp_3094 = tmp_struct_74.field2;
            GibCursor pvrtmp_3095 = tmp_struct_74.field3;
            GibCursor pvrtmp_3096 = tmp_struct_74.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3092,
                                                                        pvrtmp_3093,
                                                                        pvrtmp_3094,
                                                                        pvrtmp_3095,
                                                                        pvrtmp_3096};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3052");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList_v_280(GibCursor end_r_1189,
                                                                                 GibCursor end_r_1190,
                                                                                 GibCursor loc_1188,
                                                                                 GibCursor arg_436_596_795)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3104 = *(GibPackedTag *) arg_436_596_795;
    GibCursor tmpcur_3105 = arg_436_596_795 + 1;


  switch_3155:
    ;
    switch (tmpval_3104) {

      case 0:
        {
            GibCursor jump_1535 = arg_436_596_795 + 1;

            *(GibPackedTag *) loc_1188 = 0;

            GibCursor writetag_2153 = loc_1188 + 1;
            GibCursor after_tag_2154 = loc_1188 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1189,
                                                                        end_r_1190,
                                                                        jump_1535,
                                                                        loc_1188,
                                                                        after_tag_2154};
            break;
        }

      case 1:
        {
            GibInt tmpval_3110 = *(GibInt *) tmpcur_3105;
            GibCursor tmpcur_3111 = tmpcur_3105 + sizeof(GibInt);
            GibInt tmpval_3112 = *(GibInt *) tmpcur_3111;
            GibCursor tmpcur_3113 = tmpcur_3111 + sizeof(GibInt);
            GibCursor loc_1414 = loc_1188 + 17;

            *(GibPackedTag *) loc_1188 = 1;

            GibCursor writetag_2166 = loc_1188 + 1;
            GibCursor after_tag_2167 = loc_1188 + 1;

            *(GibInt *) after_tag_2167 = tmpval_3110;

            GibCursor writecur_2171 = after_tag_2167 + sizeof(GibInt);

            *(GibInt *) writecur_2171 = tmpval_3112;

            GibCursor writecur_2172 = writecur_2171 + sizeof(GibInt);
            GibBool chk_2164 = tmpcur_3113 < end_r_1189;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2163 = loc_1414 < end_r_1190;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_79 =
                                                               _copy_without_ptrs_PList_v_280(end_r_1189, end_r_1190, loc_1414, tmpcur_3113);
            GibCursor pvrtmp_3114 = tmp_struct_79.field0;
            GibCursor pvrtmp_3115 = tmp_struct_79.field1;
            GibCursor pvrtmp_3116 = tmp_struct_79.field2;
            GibCursor pvrtmp_3117 = tmp_struct_79.field3;
            GibCursor pvrtmp_3118 = tmp_struct_79.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3114,
                                                                        pvrtmp_3115,
                                                                        pvrtmp_3116,
                                                                        loc_1188,
                                                                        pvrtmp_3118};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_81 = *(uintptr_t *) tmpcur_3105;
            GibCursor tmpcur_3127 = GIB_UNTAG(tagged_tmpcur_81);
            GibCursor tmpaftercur_3128 = tmpcur_3105 + 8;
            uint16_t tmptag_3129 = GIB_GET_TAG(tagged_tmpcur_81);
            GibCursor end_from_tagged_indr_1626 = tmpcur_3127 + tmptag_3129;
            GibCursor jump_1628 = tmpcur_3105 + 8;
            GibBool chk_2179 = tmpcur_3127 < end_from_tagged_indr_1626;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2178 = loc_1188 < end_r_1190;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_80 =
                                                               _copy_without_ptrs_PList_v_280(end_from_tagged_indr_1626, end_r_1190, loc_1188, tmpcur_3127);
            GibCursor pvrtmp_3130 = tmp_struct_80.field0;
            GibCursor pvrtmp_3131 = tmp_struct_80.field1;
            GibCursor pvrtmp_3132 = tmp_struct_80.field2;
            GibCursor pvrtmp_3133 = tmp_struct_80.field3;
            GibCursor pvrtmp_3134 = tmp_struct_80.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1189,
                                                                        pvrtmp_3131,
                                                                        jump_1628,
                                                                        pvrtmp_3133,
                                                                        pvrtmp_3134};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_83 = *(uintptr_t *) tmpcur_3105;
            GibCursor tmpcur_3141 = GIB_UNTAG(tagged_tmpcur_83);
            GibCursor tmpaftercur_3142 = tmpcur_3105 + 8;
            uint16_t tmptag_3143 = GIB_GET_TAG(tagged_tmpcur_83);
            GibCursor end_from_tagged_indr_1626 = tmpcur_3141 + tmptag_3143;
            GibBool chk_2184 = tmpcur_3141 < end_from_tagged_indr_1626;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2183 = loc_1188 < end_r_1190;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_82 =
                                                               _copy_without_ptrs_PList_v_280(end_from_tagged_indr_1626, end_r_1190, loc_1188, tmpcur_3141);
            GibCursor pvrtmp_3144 = tmp_struct_82.field0;
            GibCursor pvrtmp_3145 = tmp_struct_82.field1;
            GibCursor pvrtmp_3146 = tmp_struct_82.field2;
            GibCursor pvrtmp_3147 = tmp_struct_82.field3;
            GibCursor pvrtmp_3148 = tmp_struct_82.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3144,
                                                                        pvrtmp_3145,
                                                                        pvrtmp_3146,
                                                                        pvrtmp_3147,
                                                                        pvrtmp_3148};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3104");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList_v_280(GibCursor end_r_1192,
                                             GibCursor arg_443_603_802)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3156 = *(GibPackedTag *) arg_443_603_802;
    GibCursor tmpcur_3157 = arg_443_603_802 + 1;


  switch_3174:
    ;
    switch (tmpval_3156) {

      case 0:
        {
            GibCursor jump_1541 = arg_443_603_802 + 1;

            return (GibCursorGibCursorProd) {end_r_1192, jump_1541};
            break;
        }

      case 1:
        {
            GibInt tmpval_3158 = *(GibInt *) tmpcur_3157;
            GibCursor tmpcur_3159 = tmpcur_3157 + sizeof(GibInt);
            GibInt tmpval_3160 = *(GibInt *) tmpcur_3159;
            GibCursor tmpcur_3161 = tmpcur_3159 + sizeof(GibInt);
            GibBool chk_2190 = tmpcur_3161 < end_r_1192;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_84 =
                                    _traverse_PList_v_280(end_r_1192, tmpcur_3161);
            GibCursor pvrtmp_3162 = tmp_struct_84.field0;
            GibCursor pvrtmp_3163 = tmp_struct_84.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3162, pvrtmp_3163};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_3157;
            GibCursor tmpcur_3164 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_3165 = tmpcur_3157 + 8;
            uint16_t tmptag_3166 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1632 = tmpcur_3164 + tmptag_3166;
            GibCursor jump_1634 = tmpcur_3157 + 8;
            GibBool chk_2194 = tmpcur_3164 < end_from_tagged_indr_1632;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_85 =
                                    _traverse_PList_v_280(end_from_tagged_indr_1632, tmpcur_3164);
            GibCursor pvrtmp_3167 = tmp_struct_85.field0;
            GibCursor pvrtmp_3168 = tmp_struct_85.field1;

            return (GibCursorGibCursorProd) {end_r_1192, jump_1634};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3157;
            GibCursor tmpcur_3169 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3170 = tmpcur_3157 + 8;
            uint16_t tmptag_3171 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1632 = tmpcur_3169 + tmptag_3171;
            GibBool chk_2198 = tmpcur_3169 < end_from_tagged_indr_1632;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_87 =
                                    _traverse_PList_v_280(end_from_tagged_indr_1632, tmpcur_3169);
            GibCursor pvrtmp_3172 = tmp_struct_87.field0;
            GibCursor pvrtmp_3173 = tmp_struct_87.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3172, pvrtmp_3173};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3156");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList_v_280(GibCursor end_r_1194,
                                          GibCursor arg_450_608_807)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3175 = *(GibPackedTag *) arg_450_608_807;
    GibCursor tmpcur_3176 = arg_450_608_807 + 1;


  switch_3193:
    ;
    switch (tmpval_3175) {

      case 0:
        {
            GibCursor jump_1547 = arg_450_608_807 + 1;
            unsigned char wildcard_451_609_808 = gib_print_symbol(2652);
            unsigned char wildcard_452_610_809 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {end_r_1194, jump_1547};
            break;
        }

      case 1:
        {
            GibInt tmpval_3177 = *(GibInt *) tmpcur_3176;
            GibCursor tmpcur_3178 = tmpcur_3176 + sizeof(GibInt);
            GibInt tmpval_3179 = *(GibInt *) tmpcur_3178;
            GibCursor tmpcur_3180 = tmpcur_3178 + sizeof(GibInt);
            unsigned char wildcard_459_614_813 = gib_print_symbol(2654);
            unsigned char y_456_615_814 = printf("%ld", tmpval_3177);
            unsigned char y_456_616_815 = gib_print_symbol(2660);
            unsigned char y_457_617_816 = printf("%ld", tmpval_3179);
            unsigned char y_457_618_817 = gib_print_symbol(2660);
            GibBool chk_2204 = tmpcur_3180 < end_r_1194;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_89 =
                                    _print_PList_v_280(end_r_1194, tmpcur_3180);
            GibCursor pvrtmp_3181 = tmp_struct_89.field0;
            GibCursor pvrtmp_3182 = tmp_struct_89.field1;
            unsigned char y_458_620_819 = gib_print_symbol(2660);
            unsigned char wildcard_460_621_820 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {pvrtmp_3181, pvrtmp_3182};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_91 = *(uintptr_t *) tmpcur_3176;
            GibCursor tmpcur_3183 = GIB_UNTAG(tagged_tmpcur_91);
            GibCursor tmpaftercur_3184 = tmpcur_3176 + 8;
            uint16_t tmptag_3185 = GIB_GET_TAG(tagged_tmpcur_91);
            GibCursor end_from_tagged_indr_1638 = tmpcur_3183 + tmptag_3185;
            GibCursor jump_1640 = tmpcur_3176 + 8;
            unsigned char wildcard_1643 = gib_print_symbol(2659);
            GibBool chk_2208 = tmpcur_3183 < end_from_tagged_indr_1638;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_90 =
                                    _print_PList_v_280(end_from_tagged_indr_1638, tmpcur_3183);
            GibCursor pvrtmp_3186 = tmp_struct_90.field0;
            GibCursor pvrtmp_3187 = tmp_struct_90.field1;

            return (GibCursorGibCursorProd) {end_r_1194, jump_1640};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_93 = *(uintptr_t *) tmpcur_3176;
            GibCursor tmpcur_3188 = GIB_UNTAG(tagged_tmpcur_93);
            GibCursor tmpaftercur_3189 = tmpcur_3176 + 8;
            uint16_t tmptag_3190 = GIB_GET_TAG(tagged_tmpcur_93);
            GibCursor end_from_tagged_indr_1638 = tmpcur_3188 + tmptag_3190;
            unsigned char wildcard_1643 = gib_print_symbol(2658);
            GibBool chk_2212 = tmpcur_3188 < end_from_tagged_indr_1638;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_92 =
                                    _print_PList_v_280(end_from_tagged_indr_1638, tmpcur_3188);
            GibCursor pvrtmp_3191 = tmp_struct_92.field0;
            GibCursor pvrtmp_3192 = tmp_struct_92.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3191, pvrtmp_3192};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3175");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Maybe_v_284(GibCursor end_r_1197,
                                                                    GibCursor end_r_1198,
                                                                    GibCursor loc_1196,
                                                                    GibCursor arg_461_622_821)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;

    if (loc_1196 + 18 > end_r_1198) {
        gib_grow_region(&loc_1196, &end_r_1198);
    }

    GibPackedTag tmpval_3194 = *(GibPackedTag *) arg_461_622_821;
    GibCursor tmpcur_3195 = arg_461_622_821 + 1;


  switch_3234:
    ;
    switch (tmpval_3194) {

      case 0:
        {
            GibInt tmpval_3196 = *(GibInt *) tmpcur_3195;
            GibCursor tmpcur_3197 = tmpcur_3195 + sizeof(GibInt);
            GibCursor jump_1553 = tmpcur_3195 + 8;

            *(GibPackedTag *) loc_1196 = 0;

            GibCursor writetag_2216 = loc_1196 + 1;
            GibCursor after_tag_2217 = loc_1196 + 1;

            *(GibInt *) after_tag_2217 = tmpval_3196;

            GibCursor writecur_2221 = after_tag_2217 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1197,
                                                                        end_r_1198,
                                                                        jump_1553,
                                                                        loc_1196,
                                                                        writecur_2221};
            break;
        }

      case 1:
        {
            GibCursor jump_1555 = arg_461_622_821 + 1;

            *(GibPackedTag *) loc_1196 = 1;

            GibCursor writetag_2225 = loc_1196 + 1;
            GibCursor after_tag_2226 = loc_1196 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1197,
                                                                        end_r_1198,
                                                                        jump_1555,
                                                                        loc_1196,
                                                                        after_tag_2226};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_95 = *(uintptr_t *) tmpcur_3195;
            GibCursor tmpcur_3206 = GIB_UNTAG(tagged_tmpcur_95);
            GibCursor tmpaftercur_3207 = tmpcur_3195 + 8;
            uint16_t tmptag_3208 = GIB_GET_TAG(tagged_tmpcur_95);
            GibCursor end_from_tagged_indr_1644 = tmpcur_3206 + tmptag_3208;
            GibCursor jump_1646 = tmpcur_3195 + 8;
            GibBool chk_2235 = tmpcur_3206 < end_from_tagged_indr_1644;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2234 = loc_1196 < end_r_1198;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_94 =
                                                               _copy_Maybe_v_284(end_from_tagged_indr_1644, end_r_1198, loc_1196, tmpcur_3206);
            GibCursor pvrtmp_3209 = tmp_struct_94.field0;
            GibCursor pvrtmp_3210 = tmp_struct_94.field1;
            GibCursor pvrtmp_3211 = tmp_struct_94.field2;
            GibCursor pvrtmp_3212 = tmp_struct_94.field3;
            GibCursor pvrtmp_3213 = tmp_struct_94.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1197,
                                                                        pvrtmp_3210,
                                                                        jump_1646,
                                                                        pvrtmp_3212,
                                                                        pvrtmp_3213};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_97 = *(uintptr_t *) tmpcur_3195;
            GibCursor tmpcur_3220 = GIB_UNTAG(tagged_tmpcur_97);
            GibCursor tmpaftercur_3221 = tmpcur_3195 + 8;
            uint16_t tmptag_3222 = GIB_GET_TAG(tagged_tmpcur_97);
            GibCursor end_from_tagged_indr_1644 = tmpcur_3220 + tmptag_3222;
            GibBool chk_2240 = tmpcur_3220 < end_from_tagged_indr_1644;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2239 = loc_1196 < end_r_1198;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_96 =
                                                               _copy_Maybe_v_284(end_from_tagged_indr_1644, end_r_1198, loc_1196, tmpcur_3220);
            GibCursor pvrtmp_3223 = tmp_struct_96.field0;
            GibCursor pvrtmp_3224 = tmp_struct_96.field1;
            GibCursor pvrtmp_3225 = tmp_struct_96.field2;
            GibCursor pvrtmp_3226 = tmp_struct_96.field3;
            GibCursor pvrtmp_3227 = tmp_struct_96.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3223,
                                                                        pvrtmp_3224,
                                                                        pvrtmp_3225,
                                                                        pvrtmp_3226,
                                                                        pvrtmp_3227};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3194");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Maybe_v_284(GibCursor end_r_1201,
                                                                                 GibCursor end_r_1202,
                                                                                 GibCursor loc_1200,
                                                                                 GibCursor arg_464_625_824)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3235 = *(GibPackedTag *) arg_464_625_824;
    GibCursor tmpcur_3236 = arg_464_625_824 + 1;


  switch_3275:
    ;
    switch (tmpval_3235) {

      case 0:
        {
            GibInt tmpval_3237 = *(GibInt *) tmpcur_3236;
            GibCursor tmpcur_3238 = tmpcur_3236 + sizeof(GibInt);
            GibCursor jump_1557 = tmpcur_3236 + 8;

            *(GibPackedTag *) loc_1200 = 0;

            GibCursor writetag_2244 = loc_1200 + 1;
            GibCursor after_tag_2245 = loc_1200 + 1;

            *(GibInt *) after_tag_2245 = tmpval_3237;

            GibCursor writecur_2249 = after_tag_2245 + sizeof(GibInt);

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1201,
                                                                        end_r_1202,
                                                                        jump_1557,
                                                                        loc_1200,
                                                                        writecur_2249};
            break;
        }

      case 1:
        {
            GibCursor jump_1559 = arg_464_625_824 + 1;

            *(GibPackedTag *) loc_1200 = 1;

            GibCursor writetag_2253 = loc_1200 + 1;
            GibCursor after_tag_2254 = loc_1200 + 1;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1201,
                                                                        end_r_1202,
                                                                        jump_1559,
                                                                        loc_1200,
                                                                        after_tag_2254};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_102 = *(uintptr_t *) tmpcur_3236;
            GibCursor tmpcur_3247 = GIB_UNTAG(tagged_tmpcur_102);
            GibCursor tmpaftercur_3248 = tmpcur_3236 + 8;
            uint16_t tmptag_3249 = GIB_GET_TAG(tagged_tmpcur_102);
            GibCursor end_from_tagged_indr_1650 = tmpcur_3247 + tmptag_3249;
            GibCursor jump_1652 = tmpcur_3236 + 8;
            GibBool chk_2263 = tmpcur_3247 < end_from_tagged_indr_1650;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2262 = loc_1200 < end_r_1202;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_101 =
                                                               _copy_without_ptrs_Maybe_v_284(end_from_tagged_indr_1650, end_r_1202, loc_1200, tmpcur_3247);
            GibCursor pvrtmp_3250 = tmp_struct_101.field0;
            GibCursor pvrtmp_3251 = tmp_struct_101.field1;
            GibCursor pvrtmp_3252 = tmp_struct_101.field2;
            GibCursor pvrtmp_3253 = tmp_struct_101.field3;
            GibCursor pvrtmp_3254 = tmp_struct_101.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1201,
                                                                        pvrtmp_3251,
                                                                        jump_1652,
                                                                        pvrtmp_3253,
                                                                        pvrtmp_3254};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_104 = *(uintptr_t *) tmpcur_3236;
            GibCursor tmpcur_3261 = GIB_UNTAG(tagged_tmpcur_104);
            GibCursor tmpaftercur_3262 = tmpcur_3236 + 8;
            uint16_t tmptag_3263 = GIB_GET_TAG(tagged_tmpcur_104);
            GibCursor end_from_tagged_indr_1650 = tmpcur_3261 + tmptag_3263;
            GibBool chk_2268 = tmpcur_3261 < end_from_tagged_indr_1650;

            #ifdef _GIBBON_DEBUG
            #endif

            GibBool chk_2267 = loc_1200 < end_r_1202;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_103 =
                                                               _copy_without_ptrs_Maybe_v_284(end_from_tagged_indr_1650, end_r_1202, loc_1200, tmpcur_3261);
            GibCursor pvrtmp_3264 = tmp_struct_103.field0;
            GibCursor pvrtmp_3265 = tmp_struct_103.field1;
            GibCursor pvrtmp_3266 = tmp_struct_103.field2;
            GibCursor pvrtmp_3267 = tmp_struct_103.field3;
            GibCursor pvrtmp_3268 = tmp_struct_103.field4;

            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3264,
                                                                        pvrtmp_3265,
                                                                        pvrtmp_3266,
                                                                        pvrtmp_3267,
                                                                        pvrtmp_3268};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3235");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Maybe_v_284(GibCursor end_r_1204,
                                             GibCursor arg_467_628_827)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3276 = *(GibPackedTag *) arg_467_628_827;
    GibCursor tmpcur_3277 = arg_467_628_827 + 1;


  switch_3290:
    ;
    switch (tmpval_3276) {

      case 0:
        {
            GibInt tmpval_3278 = *(GibInt *) tmpcur_3277;
            GibCursor tmpcur_3279 = tmpcur_3277 + sizeof(GibInt);
            GibCursor jump_1561 = tmpcur_3277 + 8;

            return (GibCursorGibCursorProd) {end_r_1204, jump_1561};
            break;
        }

      case 1:
        {
            GibCursor jump_1563 = arg_467_628_827 + 1;

            return (GibCursorGibCursorProd) {end_r_1204, jump_1563};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_106 = *(uintptr_t *) tmpcur_3277;
            GibCursor tmpcur_3280 = GIB_UNTAG(tagged_tmpcur_106);
            GibCursor tmpaftercur_3281 = tmpcur_3277 + 8;
            uint16_t tmptag_3282 = GIB_GET_TAG(tagged_tmpcur_106);
            GibCursor end_from_tagged_indr_1656 = tmpcur_3280 + tmptag_3282;
            GibCursor jump_1658 = tmpcur_3277 + 8;
            GibBool chk_2275 = tmpcur_3280 < end_from_tagged_indr_1656;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_105 =
                                    _traverse_Maybe_v_284(end_from_tagged_indr_1656, tmpcur_3280);
            GibCursor pvrtmp_3283 = tmp_struct_105.field0;
            GibCursor pvrtmp_3284 = tmp_struct_105.field1;

            return (GibCursorGibCursorProd) {end_r_1204, jump_1658};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_108 = *(uintptr_t *) tmpcur_3277;
            GibCursor tmpcur_3285 = GIB_UNTAG(tagged_tmpcur_108);
            GibCursor tmpaftercur_3286 = tmpcur_3277 + 8;
            uint16_t tmptag_3287 = GIB_GET_TAG(tagged_tmpcur_108);
            GibCursor end_from_tagged_indr_1656 = tmpcur_3285 + tmptag_3287;
            GibBool chk_2279 = tmpcur_3285 < end_from_tagged_indr_1656;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_107 =
                                    _traverse_Maybe_v_284(end_from_tagged_indr_1656, tmpcur_3285);
            GibCursor pvrtmp_3288 = tmp_struct_107.field0;
            GibCursor pvrtmp_3289 = tmp_struct_107.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3288, pvrtmp_3289};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3276");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Maybe_v_284(GibCursor end_r_1206,
                                          GibCursor arg_470_630_829)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3291 = *(GibPackedTag *) arg_470_630_829;
    GibCursor tmpcur_3292 = arg_470_630_829 + 1;


  switch_3305:
    ;
    switch (tmpval_3291) {

      case 0:
        {
            GibInt tmpval_3293 = *(GibInt *) tmpcur_3292;
            GibCursor tmpcur_3294 = tmpcur_3292 + sizeof(GibInt);
            GibCursor jump_1565 = tmpcur_3292 + 8;
            unsigned char wildcard_473_632_831 = gib_print_symbol(2653);
            unsigned char y_472_633_832 = printf("%ld", tmpval_3293);
            unsigned char y_472_634_833 = gib_print_symbol(2660);
            unsigned char wildcard_474_635_834 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {end_r_1206, jump_1565};
            break;
        }

      case 1:
        {
            GibCursor jump_1567 = arg_470_630_829 + 1;
            unsigned char wildcard_475_636_835 = gib_print_symbol(2651);
            unsigned char wildcard_476_637_836 = gib_print_symbol(2650);

            return (GibCursorGibCursorProd) {end_r_1206, jump_1567};
            break;
        }

      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) tmpcur_3292;
            GibCursor tmpcur_3295 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_3296 = tmpcur_3292 + 8;
            uint16_t tmptag_3297 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_indr_1662 = tmpcur_3295 + tmptag_3297;
            GibCursor jump_1664 = tmpcur_3292 + 8;
            unsigned char wildcard_1667 = gib_print_symbol(2659);
            GibBool chk_2286 = tmpcur_3295 < end_from_tagged_indr_1662;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_109 =
                                    _print_Maybe_v_284(end_from_tagged_indr_1662, tmpcur_3295);
            GibCursor pvrtmp_3298 = tmp_struct_109.field0;
            GibCursor pvrtmp_3299 = tmp_struct_109.field1;

            return (GibCursorGibCursorProd) {end_r_1206, jump_1664};
            break;
        }

      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) tmpcur_3292;
            GibCursor tmpcur_3300 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_3301 = tmpcur_3292 + 8;
            uint16_t tmptag_3302 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_indr_1662 = tmpcur_3300 + tmptag_3302;
            unsigned char wildcard_1667 = gib_print_symbol(2658);
            GibBool chk_2290 = tmpcur_3300 < end_from_tagged_indr_1662;

            #ifdef _GIBBON_DEBUG
            #endif

            GibCursorGibCursorProd tmp_struct_111 =
                                    _print_Maybe_v_284(end_from_tagged_indr_1662, tmpcur_3300);
            GibCursor pvrtmp_3303 = tmp_struct_111.field0;
            GibCursor pvrtmp_3304 = tmp_struct_111.field1;

            return (GibCursorGibCursorProd) {pvrtmp_3303, pvrtmp_3304};
            break;
        }

      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3291");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_120 = gib_init(argc, argv);

    info_table_initialize();
    symbol_table_initialize();

    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_2662 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1249 = region_2662.start;
    GibCursor end_r_1249 = region_2662.end;
    GibCursor loc_1237 = r_1249 + 17;
    GibCursor loc_1232 = r_1249 + 34;
    GibCursor loc_1227 = r_1249 + 51;
    GibCursor loc_1222 = r_1249 + 68;
    GibCursor loc_1217 = r_1249 + 85;
    GibCursor loc_1212 = r_1249 + 102;

    *(GibPackedTag *) r_1249 = 1;

    GibCursor writetag_2349 = r_1249 + 1;
    GibCursor after_tag_2350 = r_1249 + 1;

    *(GibInt *) after_tag_2350 = 1;

    GibCursor writecur_2354 = after_tag_2350 + sizeof(GibInt);

    *(GibInt *) writecur_2354 = 177;

    GibCursor writecur_2355 = writecur_2354 + sizeof(GibInt);

    *(GibPackedTag *) loc_1212 = 0;

    GibCursor writetag_2292 = loc_1212 + 1;
    GibCursor after_tag_2293 = loc_1212 + 1;

    *(GibPackedTag *) loc_1217 = 1;

    GibCursor writetag_2299 = loc_1217 + 1;
    GibCursor after_tag_2300 = loc_1217 + 1;

    *(GibInt *) after_tag_2300 = 250;

    GibCursor writecur_2304 = after_tag_2300 + sizeof(GibInt);

    *(GibInt *) writecur_2304 = 55;

    GibCursor writecur_2305 = writecur_2304 + sizeof(GibInt);

    *(GibPackedTag *) loc_1222 = 1;

    GibCursor writetag_2309 = loc_1222 + 1;
    GibCursor after_tag_2310 = loc_1222 + 1;

    *(GibInt *) after_tag_2310 = 100;

    GibCursor writecur_2314 = after_tag_2310 + sizeof(GibInt);

    *(GibInt *) writecur_2314 = 88;

    GibCursor writecur_2315 = writecur_2314 + sizeof(GibInt);

    *(GibPackedTag *) loc_1227 = 1;

    GibCursor writetag_2319 = loc_1227 + 1;
    GibCursor after_tag_2320 = loc_1227 + 1;

    *(GibInt *) after_tag_2320 = 25;

    GibCursor writecur_2324 = after_tag_2320 + sizeof(GibInt);

    *(GibInt *) writecur_2324 = 88;

    GibCursor writecur_2325 = writecur_2324 + sizeof(GibInt);

    *(GibPackedTag *) loc_1232 = 1;

    GibCursor writetag_2329 = loc_1232 + 1;
    GibCursor after_tag_2330 = loc_1232 + 1;

    *(GibInt *) after_tag_2330 = 10;

    GibCursor writecur_2334 = after_tag_2330 + sizeof(GibInt);

    *(GibInt *) writecur_2334 = 99;

    GibCursor writecur_2335 = writecur_2334 + sizeof(GibInt);

    *(GibPackedTag *) loc_1237 = 1;

    GibCursor writetag_2339 = loc_1237 + 1;
    GibCursor after_tag_2340 = loc_1237 + 1;

    *(GibInt *) after_tag_2340 = 5;

    GibCursor writecur_2344 = after_tag_2340 + sizeof(GibInt);

    *(GibInt *) writecur_2344 = 122;

    GibCursor writecur_2345 = writecur_2344 + sizeof(GibInt);
    GibInt amt_61_478_690 = gib_get_size_param();

    gib_shadowstack_push(rstack, r_1249, end_r_1249, Stk, PList_v_280_T);

    GibChunk region_2677 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1248 = region_2677.start;
    GibCursor end_r_1248 = region_2677.end;

    frame = gib_shadowstack_pop(rstack);
    r_1249 = frame->ptr;
    end_r_1249 = frame->endptr;

    GibCursor pvrtmp_2688;
    GibCursor pvrtmp_2689;
    GibCursor pvrtmp_2690;
    GibVector *times_117 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2688;
    struct timespec end_pvrtmp_2688;

    GibGcStateSnapshot *snapshot = gib_gc_init_state(2);

    for (long long iters_pvrtmp_2688 = 0; iters_pvrtmp_2688 <
         gib_get_iters_param(); iters_pvrtmp_2688++) {
        if (iters_pvrtmp_2688 != gib_get_iters_param() - 1) {
            gib_gc_save_state(snapshot, 2, region_2677.end, region_2662.end);
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2688);

        GibBool chk_2360 = r_1249 < end_r_1249;

        #ifdef _GIBBON_DEBUG
        #endif

        GibBool chk_2359 = r_1248 < end_r_1248;

        #ifdef _GIBBON_DEBUG
        #endif

        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_113 =
                                                  payA_seq(end_r_1249, end_r_1248, r_1248, amt_61_478_690, r_1249);
        GibCursor pvrtmp_2678 = tmp_struct_113.field0;
        GibCursor pvrtmp_2679 = tmp_struct_113.field1;
        GibCursor pvrtmp_2680 = tmp_struct_113.field2;
        GibCursor pvrtmp_2681 = tmp_struct_113.field3;

        pvrtmp_2688 = pvrtmp_2679;
        pvrtmp_2689 = pvrtmp_2680;
        pvrtmp_2690 = pvrtmp_2681;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2688);
        if (iters_pvrtmp_2688 != gib_get_iters_param() - 1) {
            gib_gc_restore_state(snapshot);
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }

        double itertime_114 = gib_difftimespecs(&begin_pvrtmp_2688,
                                                &end_pvrtmp_2688);

        printf("itertime: %lf\n", itertime_114);
        gib_vector_inplace_update(times_117, iters_pvrtmp_2688, &itertime_114);
    }
    gib_vector_inplace_sort(times_117, gib_compare_doubles);

    double *tmp_118 = (double *) gib_vector_nth(times_117,
                                                gib_get_iters_param() / 2);
    double selftimed_116 = *tmp_118;
    double batchtime_115 = gib_sum_timing_array(times_117);

    gib_print_timing_array(times_117);
    gib_vector_free(times_117);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_115);
    printf("SELFTIMED: %e\n", selftimed_116);

    GibBool chk_2363 = r_1248 < end_r_1248;

    #ifdef _GIBBON_DEBUG
    #endif

    GibCursorGibCursorProd tmp_struct_119 =
                            check_coins(end_r_1248, amt_61_478_690, pvrtmp_2689);
    GibCursor pvrtmp_2698 = tmp_struct_119.field0;
    GibCursor pvrtmp_2699 = tmp_struct_119.field1;

    printf("'#()");
    printf("\n");
    // return 0;

    int exit_121 = gib_exit();

    return exit_121;
}
