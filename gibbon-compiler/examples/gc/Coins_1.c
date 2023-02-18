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
GibCursorGibCursorGibCursorGibCursorProd payA_seq(GibCursor end_r_1104,
                                                  GibCursor end_r_1105,
                                                  GibCursor loc_1103,
                                                  GibInt amt_72_483_681,
                                                  GibCursor coins_73_484_682);
GibCursorGibCursorGibCursorGibCursorProd getCoins1(GibCursor end_r_1108,
                                                   GibCursor end_r_1109,
                                                   GibCursor loc_1107,
                                                   GibInt c_90_501_694,
                                                   GibInt q_91_502_695,
                                                   GibCursor coins_rst_92_503_696);
GibCursorGibIntGibIntProd head_plist_281(GibCursor end_r_1111,
                                         GibCursor ls_106_529_701);
GibCursorGibCursorGibCursorGibCursorProd tail_plist_282(GibCursor end_r_1114,
                                                        GibCursor end_r_1115,
                                                        GibCursor loc_1113,
                                                        GibCursor ls_102_533_705);
GibCursorGibBoolProd is_empty_plist_280(GibCursor end_r_1117,
                                        GibCursor ls_98_537_709);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_AList(GibCursor end_r_1120, GibCursor end_r_1121, GibCursor loc_1119,
            GibCursor arg_383_541_713);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_AList(GibCursor end_r_1124, GibCursor end_r_1125,
                         GibCursor loc_1123, GibCursor arg_392_550_722);
GibCursorGibCursorProd _traverse_AList(GibCursor end_r_1127,
                                       GibCursor arg_401_559_731);
GibCursorGibCursorProd _print_AList(GibCursor end_r_1129,
                                    GibCursor arg_410_566_738);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_PList_v_279(GibCursor end_r_1132, GibCursor end_r_1133,
                  GibCursor loc_1131, GibCursor arg_425_585_757);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_PList_v_279(GibCursor end_r_1136, GibCursor end_r_1137,
                               GibCursor loc_1135, GibCursor arg_432_592_764);
GibCursorGibCursorProd _traverse_PList_v_279(GibCursor end_r_1139,
                                             GibCursor arg_439_599_771);
GibCursorGibCursorProd _print_PList_v_279(GibCursor end_r_1141,
                                          GibCursor arg_446_604_776);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_Maybe_v_283(GibCursor end_r_1144, GibCursor end_r_1145,
                  GibCursor loc_1143, GibCursor arg_457_618_790);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_Maybe_v_283(GibCursor end_r_1148, GibCursor end_r_1149,
                               GibCursor loc_1147, GibCursor arg_460_621_793);
GibCursorGibCursorProd _traverse_Maybe_v_283(GibCursor end_r_1151,
                                             GibCursor arg_463_624_796);
GibCursorGibCursorProd _print_Maybe_v_283(GibCursor end_r_1153,
                                          GibCursor arg_466_626_798);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            AList_T,
            Maybe_v_283_T,
            PList_v_279_T,
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
    error = gib_info_table_insert_packed_dcon(Maybe_v_283_T, 0, 8, 0, 1, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_283_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(Maybe_v_283_T, 1, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, Maybe_v_283_T, 1);
        exit(1);
    }
    field_tys[0] = PList_v_279_T;
    error = gib_info_table_insert_packed_dcon(PList_v_279_T, 1, 16, 0, 2, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_279_T, 1);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(PList_v_279_T, 0, 0, 0, 0, 0,
                                              field_tys, 0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, PList_v_279_T, 0);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(2527, ")");
    gib_add_symbol(2528, "(Nothing_v_283 ");
    gib_add_symbol(2529, "(Nil_v_279 ");
    gib_add_symbol(2530, "(Just_v_283 ");
    gib_add_symbol(2531, "(Cons_v_279 ");
    gib_add_symbol(2532, "(Append ");
    gib_add_symbol(2533, "(ASing ");
    gib_add_symbol(2534, "(ANil ");
    gib_add_symbol(2535, " ->r ");
    gib_add_symbol(2536, " ->i ");
    gib_add_symbol(2537, " ");
}
GibCursorGibCursorGibCursorGibCursorProd payA_seq(GibCursor end_r_1104,
                                                  GibCursor end_r_1105,
                                                  GibCursor loc_1103,
                                                  GibInt amt_72_483_681,
                                                  GibCursor coins_73_484_682)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_1103 + 18 > end_r_1105) {
        gib_grow_region(&loc_1103, &end_r_1105);
    }
    
    GibBool fltIf_652_683 = amt_72_483_681 == 0;
    
    if (fltIf_652_683) {
        *(GibPackedTag *) loc_1103 = 1;
        
        GibCursor writetag_1771 = loc_1103 + 1;
        GibCursor after_tag_1772 = loc_1103 + 1;
        
        *(GibInt *) after_tag_1772 = 1;
        
        GibCursor writecur_1776 = after_tag_1772 + sizeof(GibInt);
        
        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1104,
                                                           end_r_1105, loc_1103,
                                                           writecur_1776};
    } else {
        GibBool chk_1779 = coins_73_484_682 < end_r_1104;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursorGibBoolProd tmp_struct_0 =
                              is_empty_plist_280(end_r_1104, coins_73_484_682);
        GibCursor pvrtmp_2578 = tmp_struct_0.field0;
        GibBool pvrtmp_2579 = tmp_struct_0.field1;
        
        if (pvrtmp_2579) {
            *(GibPackedTag *) loc_1103 = 0;
            
            GibCursor writetag_1781 = loc_1103 + 1;
            GibCursor after_tag_1782 = loc_1103 + 1;
            
            *(GibInt *) after_tag_1782 = 0;
            
            GibCursor writecur_1786 = after_tag_1782 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2578,
                                                               end_r_1105,
                                                               loc_1103,
                                                               writecur_1786};
        } else {
            GibBool chk_1789 = coins_73_484_682 < end_r_1104;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibIntGibIntProd tmp_struct_1 =
                                       head_plist_281(end_r_1104, coins_73_484_682);
            GibCursor pvrtmp_2584 = tmp_struct_1.field0;
            GibInt pvrtmp_2585 = tmp_struct_1.field1;
            GibInt pvrtmp_2586 = tmp_struct_1.field2;
            
            gib_shadowstack_push(rstack, coins_73_484_682, end_r_1104, Stk,
                                 PList_v_279_T);
            gib_shadowstack_push(wstack, loc_1103, end_r_1105, Stk, AList_T);
            
            GibChunk region_2589 =
                     gib_alloc_region(gib_get_inf_init_chunk_size());
            GibCursor r_1224 = region_2589.start;
            GibCursor end_r_1224 = region_2589.end;
            
            frame = gib_shadowstack_pop(wstack);
            loc_1103 = frame->ptr;
            end_r_1105 = frame->endptr;
            frame = gib_shadowstack_pop(rstack);
            coins_73_484_682 = frame->ptr;
            end_r_1104 = frame->endptr;
            
            GibBool chk_1792 = coins_73_484_682 < end_r_1104;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1791 = r_1224 < end_r_1224;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_2 =
                                                      tail_plist_282(end_r_1104, end_r_1224, r_1224, coins_73_484_682);
            GibCursor pvrtmp_2590 = tmp_struct_2.field0;
            GibCursor pvrtmp_2591 = tmp_struct_2.field1;
            GibCursor pvrtmp_2592 = tmp_struct_2.field2;
            GibCursor pvrtmp_2593 = tmp_struct_2.field3;
            GibBool fltIf_654_689 = pvrtmp_2585 > amt_72_483_681;
            
            if (fltIf_654_689) {
                GibBool chk_1795 = r_1224 < pvrtmp_2591;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibBool chk_1794 = loc_1103 < end_r_1105;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_3 =
                                                          payA_seq(pvrtmp_2591, end_r_1105, loc_1103, amt_72_483_681, pvrtmp_2592);
                GibCursor pvrtmp_2598 = tmp_struct_3.field0;
                GibCursor pvrtmp_2599 = tmp_struct_3.field1;
                GibCursor pvrtmp_2600 = tmp_struct_3.field2;
                GibCursor pvrtmp_2601 = tmp_struct_3.field3;
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2590,
                                                                   pvrtmp_2599,
                                                                   pvrtmp_2600,
                                                                   pvrtmp_2601};
            } else {
                gib_shadowstack_push(rstack, pvrtmp_2592, pvrtmp_2591, Stk,
                                     PList_v_279_T);
                gib_shadowstack_push(wstack, loc_1103, end_r_1105, Stk,
                                     AList_T);
                
                GibChunk region_2608 =
                         gib_alloc_region(gib_get_inf_init_chunk_size());
                GibCursor r_1223 = region_2608.start;
                GibCursor end_r_1223 = region_2608.end;
                
                frame = gib_shadowstack_pop(wstack);
                loc_1103 = frame->ptr;
                end_r_1105 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                pvrtmp_2592 = frame->ptr;
                pvrtmp_2591 = frame->endptr;
                
                GibBool chk_1798 = r_1224 < pvrtmp_2591;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibBool chk_1797 = r_1223 < end_r_1223;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_4 =
                                                          getCoins1(pvrtmp_2591, end_r_1223, r_1223, pvrtmp_2585, pvrtmp_2586, pvrtmp_2592);
                GibCursor pvrtmp_2609 = tmp_struct_4.field0;
                GibCursor pvrtmp_2610 = tmp_struct_4.field1;
                GibCursor pvrtmp_2611 = tmp_struct_4.field2;
                GibCursor pvrtmp_2612 = tmp_struct_4.field3;
                GibInt fltAppE_655_691 = amt_72_483_681 - pvrtmp_2585;
                GibCursor loc_1219 = loc_1103 + 1;
                
                *(GibPackedTag *) loc_1103 = 2;
                
                GibCursor writetag_1806 = loc_1103 + 1;
                
                gib_shadowstack_push(rstack, loc_1103, end_r_1105, Stk,
                                     AList_T);
                gib_shadowstack_push(rstack, pvrtmp_2592, pvrtmp_2591, Stk,
                                     PList_v_279_T);
                
                GibBool chk_1801 = r_1223 < pvrtmp_2610;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibBool chk_1800 = loc_1219 < end_r_1105;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_5 =
                                                          payA_seq(pvrtmp_2610, end_r_1105, loc_1219, fltAppE_655_691, pvrtmp_2611);
                GibCursor pvrtmp_2617 = tmp_struct_5.field0;
                GibCursor pvrtmp_2618 = tmp_struct_5.field1;
                GibCursor pvrtmp_2619 = tmp_struct_5.field2;
                GibCursor pvrtmp_2620 = tmp_struct_5.field3;
                
                frame = gib_shadowstack_pop(rstack);
                pvrtmp_2592 = frame->ptr;
                pvrtmp_2591 = frame->endptr;
                frame = gib_shadowstack_pop(rstack);
                loc_1103 = frame->ptr;
                end_r_1105 = frame->endptr;
                gib_shadowstack_push(rstack, loc_1103, pvrtmp_2618, Stk,
                                     AList_T);
                
                GibBool chk_1804 = r_1224 < pvrtmp_2591;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibBool chk_1803 = pvrtmp_2620 < pvrtmp_2618;
                
                #ifdef _GIBBON_DEBUG
                #endif
                
                GibCursorGibCursorGibCursorGibCursorProd tmp_struct_6 =
                                                          payA_seq(pvrtmp_2591, pvrtmp_2618, pvrtmp_2620, amt_72_483_681, pvrtmp_2592);
                GibCursor pvrtmp_2625 = tmp_struct_6.field0;
                GibCursor pvrtmp_2626 = tmp_struct_6.field1;
                GibCursor pvrtmp_2627 = tmp_struct_6.field2;
                GibCursor pvrtmp_2628 = tmp_struct_6.field3;
                
                frame = gib_shadowstack_pop(rstack);
                loc_1103 = frame->ptr;
                pvrtmp_2618 = frame->endptr;
                
                GibCursor after_tag_1807 = loc_1103 + 1;
                
                return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2590,
                                                                   pvrtmp_2626,
                                                                   loc_1103,
                                                                   pvrtmp_2628};
            }
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd getCoins1(GibCursor end_r_1108,
                                                   GibCursor end_r_1109,
                                                   GibCursor loc_1107,
                                                   GibInt c_90_501_694,
                                                   GibInt q_91_502_695,
                                                   GibCursor coins_rst_92_503_696)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_1107 + 26 > end_r_1109) {
        gib_grow_region(&loc_1107, &end_r_1109);
    }
    
    GibBool fltIf_656_697 = q_91_502_695 == 1;
    
    if (fltIf_656_697) {
        if (loc_1107 + 18 > end_r_1109) {
            gib_grow_region(&loc_1107, &end_r_1109);
        }
        gib_indirection_barrier(loc_1107, end_r_1109, coins_rst_92_503_696,
                                end_r_1108, PList_v_279_T);
        
        GibCursor end_1817 = loc_1107 + 9;
        
        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1108,
                                                           end_r_1109, loc_1107,
                                                           end_1817};
    } else {
        GibInt fltPkd_658_699 = q_91_502_695 - 1;
        GibCursor loc_1234 = loc_1107 + 17;
        
        *(GibPackedTag *) loc_1107 = 1;
        
        GibCursor writetag_1822 = loc_1107 + 1;
        GibCursor after_tag_1823 = loc_1107 + 1;
        
        *(GibInt *) after_tag_1823 = c_90_501_694;
        
        GibCursor writecur_1827 = after_tag_1823 + sizeof(GibInt);
        
        *(GibInt *) writecur_1827 = fltPkd_658_699;
        
        GibCursor writecur_1828 = writecur_1827 + sizeof(GibInt);
        
        if (loc_1234 + 18 > end_r_1109) {
            gib_grow_region(&loc_1234, &end_r_1109);
        }
        gib_indirection_barrier(loc_1234, end_r_1109, coins_rst_92_503_696,
                                end_r_1108, PList_v_279_T);
        
        GibCursor end_1820 = loc_1234 + 9;
        
        return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1108,
                                                           end_r_1109, loc_1107,
                                                           end_1820};
    }
}
GibCursorGibIntGibIntProd head_plist_281(GibCursor end_r_1111,
                                         GibCursor ls_106_529_701)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2647 = *(GibPackedTag *) ls_106_529_701;
    GibCursor tmpcur_2648 = ls_106_529_701 + 1;
    
    
  switch_2671:
    ;
    switch (tmpval_2647) {
        
      case 1:
        {
            GibInt tmpval_2649 = *(GibInt *) tmpcur_2648;
            GibCursor tmpcur_2650 = tmpcur_2648 + sizeof(GibInt);
            GibInt tmpval_2651 = *(GibInt *) tmpcur_2650;
            GibCursor tmpcur_2652 = tmpcur_2650 + sizeof(GibInt);
            
            return (GibCursorGibIntGibIntProd) {end_r_1111, tmpval_2649,
                                                tmpval_2651};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) tmpcur_2648;
            GibCursor tmpcur_2655 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_2656 = tmpcur_2648 + 8;
            uint16_t tmptag_2657 = GIB_GET_TAG(tagged_tmpcur_20);
            GibCursor end_from_tagged_indr_1494 = tmpcur_2655 + tmptag_2657;
            GibCursor jump_1496 = tmpcur_2648 + 8;
            GibBool chk_1837 = tmpcur_2655 < end_from_tagged_indr_1494;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibIntGibIntProd tmp_struct_19 =
                                       head_plist_281(end_from_tagged_indr_1494, tmpcur_2655);
            GibCursor pvrtmp_2658 = tmp_struct_19.field0;
            GibInt pvrtmp_2659 = tmp_struct_19.field1;
            GibInt pvrtmp_2660 = tmp_struct_19.field2;
            
            return (GibCursorGibIntGibIntProd) {end_r_1111, pvrtmp_2659,
                                                pvrtmp_2660};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_22 = *(uintptr_t *) tmpcur_2648;
            GibCursor tmpcur_2663 = GIB_UNTAG(tagged_tmpcur_22);
            GibCursor tmpaftercur_2664 = tmpcur_2648 + 8;
            uint16_t tmptag_2665 = GIB_GET_TAG(tagged_tmpcur_22);
            GibCursor end_from_tagged_indr_1494 = tmpcur_2663 + tmptag_2665;
            GibBool chk_1841 = tmpcur_2663 < end_from_tagged_indr_1494;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibIntGibIntProd tmp_struct_21 =
                                       head_plist_281(end_from_tagged_indr_1494, tmpcur_2663);
            GibCursor pvrtmp_2666 = tmp_struct_21.field0;
            GibInt pvrtmp_2667 = tmp_struct_21.field1;
            GibInt pvrtmp_2668 = tmp_struct_21.field2;
            
            return (GibCursorGibIntGibIntProd) {pvrtmp_2666, pvrtmp_2667,
                                                pvrtmp_2668};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2647");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorProd tail_plist_282(GibCursor end_r_1114,
                                                        GibCursor end_r_1115,
                                                        GibCursor loc_1113,
                                                        GibCursor ls_102_533_705)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_1113 + 26 > end_r_1115) {
        gib_grow_region(&loc_1113, &end_r_1115);
    }
    
    GibPackedTag tmpval_2672 = *(GibPackedTag *) ls_102_533_705;
    GibCursor tmpcur_2673 = ls_102_533_705 + 1;
    
    
  switch_2708:
    ;
    switch (tmpval_2672) {
        
      case 1:
        {
            GibInt tmpval_2674 = *(GibInt *) tmpcur_2673;
            GibCursor tmpcur_2675 = tmpcur_2673 + sizeof(GibInt);
            GibInt tmpval_2676 = *(GibInt *) tmpcur_2675;
            GibCursor tmpcur_2677 = tmpcur_2675 + sizeof(GibInt);
            
            if (loc_1113 + 18 > end_r_1115) {
                gib_grow_region(&loc_1113, &end_r_1115);
            }
            gib_indirection_barrier(loc_1113, end_r_1115, tmpcur_2677,
                                    end_r_1114, PList_v_279_T);
            
            GibCursor end_1847 = loc_1113 + 9;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1114,
                                                               end_r_1115,
                                                               loc_1113,
                                                               end_1847};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_27 = *(uintptr_t *) tmpcur_2673;
            GibCursor tmpcur_2682 = GIB_UNTAG(tagged_tmpcur_27);
            GibCursor tmpaftercur_2683 = tmpcur_2673 + 8;
            uint16_t tmptag_2684 = GIB_GET_TAG(tagged_tmpcur_27);
            GibCursor end_from_tagged_indr_1499 = tmpcur_2682 + tmptag_2684;
            GibCursor jump_1501 = tmpcur_2673 + 8;
            GibBool chk_1852 = tmpcur_2682 < end_from_tagged_indr_1499;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1851 = loc_1113 < end_r_1115;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_26 =
                                                      tail_plist_282(end_from_tagged_indr_1499, end_r_1115, loc_1113, tmpcur_2682);
            GibCursor pvrtmp_2685 = tmp_struct_26.field0;
            GibCursor pvrtmp_2686 = tmp_struct_26.field1;
            GibCursor pvrtmp_2687 = tmp_struct_26.field2;
            GibCursor pvrtmp_2688 = tmp_struct_26.field3;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {end_r_1114,
                                                               pvrtmp_2686,
                                                               pvrtmp_2687,
                                                               pvrtmp_2688};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_2673;
            GibCursor tmpcur_2695 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_2696 = tmpcur_2673 + 8;
            uint16_t tmptag_2697 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_1499 = tmpcur_2695 + tmptag_2697;
            GibBool chk_1857 = tmpcur_2695 < end_from_tagged_indr_1499;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1856 = loc_1113 < end_r_1115;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorProd tmp_struct_28 =
                                                      tail_plist_282(end_from_tagged_indr_1499, end_r_1115, loc_1113, tmpcur_2695);
            GibCursor pvrtmp_2698 = tmp_struct_28.field0;
            GibCursor pvrtmp_2699 = tmp_struct_28.field1;
            GibCursor pvrtmp_2700 = tmp_struct_28.field2;
            GibCursor pvrtmp_2701 = tmp_struct_28.field3;
            
            return (GibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2698,
                                                               pvrtmp_2699,
                                                               pvrtmp_2700,
                                                               pvrtmp_2701};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2672");
            exit(1);
        }
    }
}
GibCursorGibBoolProd is_empty_plist_280(GibCursor end_r_1117,
                                        GibCursor ls_98_537_709)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2709 = *(GibPackedTag *) ls_98_537_709;
    GibCursor tmpcur_2710 = ls_98_537_709 + 1;
    
    
  switch_2725:
    ;
    switch (tmpval_2709) {
        
      case 0:
        {
            return (GibCursorGibBoolProd) {end_r_1117, true};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2711 = *(GibInt *) tmpcur_2710;
            GibCursor tmpcur_2712 = tmpcur_2710 + sizeof(GibInt);
            GibInt tmpval_2713 = *(GibInt *) tmpcur_2712;
            GibCursor tmpcur_2714 = tmpcur_2712 + sizeof(GibInt);
            
            return (GibCursorGibBoolProd) {end_r_1117, false};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) tmpcur_2710;
            GibCursor tmpcur_2715 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_2716 = tmpcur_2710 + 8;
            uint16_t tmptag_2717 = GIB_GET_TAG(tagged_tmpcur_34);
            GibCursor end_from_tagged_indr_1504 = tmpcur_2715 + tmptag_2717;
            GibCursor jump_1506 = tmpcur_2710 + 8;
            GibBool chk_1865 = tmpcur_2715 < end_from_tagged_indr_1504;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibBoolProd tmp_struct_33 =
                                  is_empty_plist_280(end_from_tagged_indr_1504, tmpcur_2715);
            GibCursor pvrtmp_2718 = tmp_struct_33.field0;
            GibBool pvrtmp_2719 = tmp_struct_33.field1;
            
            return (GibCursorGibBoolProd) {end_r_1117, pvrtmp_2719};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_2710;
            GibCursor tmpcur_2720 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_2721 = tmpcur_2710 + 8;
            uint16_t tmptag_2722 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_indr_1504 = tmpcur_2720 + tmptag_2722;
            GibBool chk_1869 = tmpcur_2720 < end_from_tagged_indr_1504;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibBoolProd tmp_struct_35 =
                                  is_empty_plist_280(end_from_tagged_indr_1504, tmpcur_2720);
            GibCursor pvrtmp_2723 = tmp_struct_35.field0;
            GibBool pvrtmp_2724 = tmp_struct_35.field1;
            
            return (GibCursorGibBoolProd) {pvrtmp_2723, pvrtmp_2724};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2709");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_AList(GibCursor end_r_1120,
                                                              GibCursor end_r_1121,
                                                              GibCursor loc_1119,
                                                              GibCursor arg_383_541_713)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_1119 + 18 > end_r_1121) {
        gib_grow_region(&loc_1119, &end_r_1121);
    }
    
    GibPackedTag tmpval_2726 = *(GibPackedTag *) arg_383_541_713;
    GibCursor tmpcur_2727 = arg_383_541_713 + 1;
    
    
  switch_2790:
    ;
    switch (tmpval_2726) {
        
      case 0:
        {
            GibInt tmpval_2728 = *(GibInt *) tmpcur_2727;
            GibCursor tmpcur_2729 = tmpcur_2727 + sizeof(GibInt);
            GibCursor jump_1421 = tmpcur_2727 + 8;
            
            *(GibPackedTag *) loc_1119 = 0;
            
            GibCursor writetag_1873 = loc_1119 + 1;
            GibCursor after_tag_1874 = loc_1119 + 1;
            
            *(GibInt *) after_tag_1874 = tmpval_2728;
            
            GibCursor writecur_1878 = after_tag_1874 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1120,
                                                                        end_r_1121,
                                                                        jump_1421,
                                                                        loc_1119,
                                                                        writecur_1878};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2734 = *(GibInt *) tmpcur_2727;
            GibCursor tmpcur_2735 = tmpcur_2727 + sizeof(GibInt);
            GibCursor jump_1423 = tmpcur_2727 + 8;
            
            *(GibPackedTag *) loc_1119 = 1;
            
            GibCursor writetag_1883 = loc_1119 + 1;
            GibCursor after_tag_1884 = loc_1119 + 1;
            
            *(GibInt *) after_tag_1884 = tmpval_2734;
            
            GibCursor writecur_1888 = after_tag_1884 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1120,
                                                                        end_r_1121,
                                                                        jump_1423,
                                                                        loc_1119,
                                                                        writecur_1888};
            break;
        }
        
      case 2:
        {
            GibCursor loc_1273 = loc_1119 + 1;
            
            *(GibPackedTag *) loc_1119 = 2;
            
            GibCursor writetag_1898 = loc_1119 + 1;
            GibBool chk_1893 = tmpcur_2727 < end_r_1120;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1892 = loc_1273 < end_r_1121;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_37 =
                                                               _copy_AList(end_r_1120, end_r_1121, loc_1273, tmpcur_2727);
            GibCursor pvrtmp_2740 = tmp_struct_37.field0;
            GibCursor pvrtmp_2741 = tmp_struct_37.field1;
            GibCursor pvrtmp_2742 = tmp_struct_37.field2;
            GibCursor pvrtmp_2743 = tmp_struct_37.field3;
            GibCursor pvrtmp_2744 = tmp_struct_37.field4;
            GibBool chk_1896 = pvrtmp_2742 < pvrtmp_2740;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1895 = pvrtmp_2744 < pvrtmp_2741;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_38 =
                                                               _copy_AList(pvrtmp_2740, pvrtmp_2741, pvrtmp_2744, pvrtmp_2742);
            GibCursor pvrtmp_2749 = tmp_struct_38.field0;
            GibCursor pvrtmp_2750 = tmp_struct_38.field1;
            GibCursor pvrtmp_2751 = tmp_struct_38.field2;
            GibCursor pvrtmp_2752 = tmp_struct_38.field3;
            GibCursor pvrtmp_2753 = tmp_struct_38.field4;
            GibCursor after_tag_1899 = loc_1119 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2749,
                                                                        pvrtmp_2750,
                                                                        pvrtmp_2751,
                                                                        loc_1119,
                                                                        pvrtmp_2753};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_40 = *(uintptr_t *) tmpcur_2727;
            GibCursor tmpcur_2762 = GIB_UNTAG(tagged_tmpcur_40);
            GibCursor tmpaftercur_2763 = tmpcur_2727 + 8;
            uint16_t tmptag_2764 = GIB_GET_TAG(tagged_tmpcur_40);
            GibCursor end_from_tagged_indr_1509 = tmpcur_2762 + tmptag_2764;
            GibCursor jump_1511 = tmpcur_2727 + 8;
            GibBool chk_1911 = tmpcur_2762 < end_from_tagged_indr_1509;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1910 = loc_1119 < end_r_1121;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_39 =
                                                               _copy_AList(end_from_tagged_indr_1509, end_r_1121, loc_1119, tmpcur_2762);
            GibCursor pvrtmp_2765 = tmp_struct_39.field0;
            GibCursor pvrtmp_2766 = tmp_struct_39.field1;
            GibCursor pvrtmp_2767 = tmp_struct_39.field2;
            GibCursor pvrtmp_2768 = tmp_struct_39.field3;
            GibCursor pvrtmp_2769 = tmp_struct_39.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1120,
                                                                        pvrtmp_2766,
                                                                        jump_1511,
                                                                        pvrtmp_2768,
                                                                        pvrtmp_2769};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_2727;
            GibCursor tmpcur_2776 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_2777 = tmpcur_2727 + 8;
            uint16_t tmptag_2778 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_indr_1509 = tmpcur_2776 + tmptag_2778;
            GibBool chk_1916 = tmpcur_2776 < end_from_tagged_indr_1509;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1915 = loc_1119 < end_r_1121;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_41 =
                                                               _copy_AList(end_from_tagged_indr_1509, end_r_1121, loc_1119, tmpcur_2776);
            GibCursor pvrtmp_2779 = tmp_struct_41.field0;
            GibCursor pvrtmp_2780 = tmp_struct_41.field1;
            GibCursor pvrtmp_2781 = tmp_struct_41.field2;
            GibCursor pvrtmp_2782 = tmp_struct_41.field3;
            GibCursor pvrtmp_2783 = tmp_struct_41.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2779,
                                                                        pvrtmp_2780,
                                                                        pvrtmp_2781,
                                                                        pvrtmp_2782,
                                                                        pvrtmp_2783};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2726");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_AList(GibCursor end_r_1124,
                                                                           GibCursor end_r_1125,
                                                                           GibCursor loc_1123,
                                                                           GibCursor arg_392_550_722)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2791 = *(GibPackedTag *) arg_392_550_722;
    GibCursor tmpcur_2792 = arg_392_550_722 + 1;
    
    
  switch_2855:
    ;
    switch (tmpval_2791) {
        
      case 0:
        {
            GibInt tmpval_2793 = *(GibInt *) tmpcur_2792;
            GibCursor tmpcur_2794 = tmpcur_2792 + sizeof(GibInt);
            GibCursor jump_1428 = tmpcur_2792 + 8;
            
            *(GibPackedTag *) loc_1123 = 0;
            
            GibCursor writetag_1920 = loc_1123 + 1;
            GibCursor after_tag_1921 = loc_1123 + 1;
            
            *(GibInt *) after_tag_1921 = tmpval_2793;
            
            GibCursor writecur_1925 = after_tag_1921 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1124,
                                                                        end_r_1125,
                                                                        jump_1428,
                                                                        loc_1123,
                                                                        writecur_1925};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2799 = *(GibInt *) tmpcur_2792;
            GibCursor tmpcur_2800 = tmpcur_2792 + sizeof(GibInt);
            GibCursor jump_1430 = tmpcur_2792 + 8;
            
            *(GibPackedTag *) loc_1123 = 1;
            
            GibCursor writetag_1930 = loc_1123 + 1;
            GibCursor after_tag_1931 = loc_1123 + 1;
            
            *(GibInt *) after_tag_1931 = tmpval_2799;
            
            GibCursor writecur_1935 = after_tag_1931 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1124,
                                                                        end_r_1125,
                                                                        jump_1430,
                                                                        loc_1123,
                                                                        writecur_1935};
            break;
        }
        
      case 2:
        {
            GibCursor loc_1295 = loc_1123 + 1;
            
            *(GibPackedTag *) loc_1123 = 2;
            
            GibCursor writetag_1945 = loc_1123 + 1;
            GibBool chk_1940 = tmpcur_2792 < end_r_1124;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1939 = loc_1295 < end_r_1125;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_46 =
                                                               _copy_without_ptrs_AList(end_r_1124, end_r_1125, loc_1295, tmpcur_2792);
            GibCursor pvrtmp_2805 = tmp_struct_46.field0;
            GibCursor pvrtmp_2806 = tmp_struct_46.field1;
            GibCursor pvrtmp_2807 = tmp_struct_46.field2;
            GibCursor pvrtmp_2808 = tmp_struct_46.field3;
            GibCursor pvrtmp_2809 = tmp_struct_46.field4;
            GibBool chk_1943 = pvrtmp_2807 < pvrtmp_2805;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1942 = pvrtmp_2809 < pvrtmp_2806;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_47 =
                                                               _copy_without_ptrs_AList(pvrtmp_2805, pvrtmp_2806, pvrtmp_2809, pvrtmp_2807);
            GibCursor pvrtmp_2814 = tmp_struct_47.field0;
            GibCursor pvrtmp_2815 = tmp_struct_47.field1;
            GibCursor pvrtmp_2816 = tmp_struct_47.field2;
            GibCursor pvrtmp_2817 = tmp_struct_47.field3;
            GibCursor pvrtmp_2818 = tmp_struct_47.field4;
            GibCursor after_tag_1946 = loc_1123 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2814,
                                                                        pvrtmp_2815,
                                                                        pvrtmp_2816,
                                                                        loc_1123,
                                                                        pvrtmp_2818};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) tmpcur_2792;
            GibCursor tmpcur_2827 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_2828 = tmpcur_2792 + 8;
            uint16_t tmptag_2829 = GIB_GET_TAG(tagged_tmpcur_49);
            GibCursor end_from_tagged_indr_1515 = tmpcur_2827 + tmptag_2829;
            GibCursor jump_1517 = tmpcur_2792 + 8;
            GibBool chk_1958 = tmpcur_2827 < end_from_tagged_indr_1515;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1957 = loc_1123 < end_r_1125;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_48 =
                                                               _copy_without_ptrs_AList(end_from_tagged_indr_1515, end_r_1125, loc_1123, tmpcur_2827);
            GibCursor pvrtmp_2830 = tmp_struct_48.field0;
            GibCursor pvrtmp_2831 = tmp_struct_48.field1;
            GibCursor pvrtmp_2832 = tmp_struct_48.field2;
            GibCursor pvrtmp_2833 = tmp_struct_48.field3;
            GibCursor pvrtmp_2834 = tmp_struct_48.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1124,
                                                                        pvrtmp_2831,
                                                                        jump_1517,
                                                                        pvrtmp_2833,
                                                                        pvrtmp_2834};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_51 = *(uintptr_t *) tmpcur_2792;
            GibCursor tmpcur_2841 = GIB_UNTAG(tagged_tmpcur_51);
            GibCursor tmpaftercur_2842 = tmpcur_2792 + 8;
            uint16_t tmptag_2843 = GIB_GET_TAG(tagged_tmpcur_51);
            GibCursor end_from_tagged_indr_1515 = tmpcur_2841 + tmptag_2843;
            GibBool chk_1963 = tmpcur_2841 < end_from_tagged_indr_1515;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_1962 = loc_1123 < end_r_1125;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_50 =
                                                               _copy_without_ptrs_AList(end_from_tagged_indr_1515, end_r_1125, loc_1123, tmpcur_2841);
            GibCursor pvrtmp_2844 = tmp_struct_50.field0;
            GibCursor pvrtmp_2845 = tmp_struct_50.field1;
            GibCursor pvrtmp_2846 = tmp_struct_50.field2;
            GibCursor pvrtmp_2847 = tmp_struct_50.field3;
            GibCursor pvrtmp_2848 = tmp_struct_50.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2844,
                                                                        pvrtmp_2845,
                                                                        pvrtmp_2846,
                                                                        pvrtmp_2847,
                                                                        pvrtmp_2848};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2791");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_AList(GibCursor end_r_1127,
                                       GibCursor arg_401_559_731)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2856 = *(GibPackedTag *) arg_401_559_731;
    GibCursor tmpcur_2857 = arg_401_559_731 + 1;
    
    
  switch_2876:
    ;
    switch (tmpval_2856) {
        
      case 0:
        {
            GibInt tmpval_2858 = *(GibInt *) tmpcur_2857;
            GibCursor tmpcur_2859 = tmpcur_2857 + sizeof(GibInt);
            GibCursor jump_1435 = tmpcur_2857 + 8;
            
            return (GibCursorGibCursorProd) {end_r_1127, jump_1435};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2860 = *(GibInt *) tmpcur_2857;
            GibCursor tmpcur_2861 = tmpcur_2857 + sizeof(GibInt);
            GibCursor jump_1437 = tmpcur_2857 + 8;
            
            return (GibCursorGibCursorProd) {end_r_1127, jump_1437};
            break;
        }
        
      case 2:
        {
            GibBool chk_1970 = tmpcur_2857 < end_r_1127;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_52 =
                                    _traverse_AList(end_r_1127, tmpcur_2857);
            GibCursor pvrtmp_2862 = tmp_struct_52.field0;
            GibCursor pvrtmp_2863 = tmp_struct_52.field1;
            GibBool chk_1972 = pvrtmp_2863 < pvrtmp_2862;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_53 =
                                    _traverse_AList(pvrtmp_2862, pvrtmp_2863);
            GibCursor pvrtmp_2864 = tmp_struct_53.field0;
            GibCursor pvrtmp_2865 = tmp_struct_53.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_2864, pvrtmp_2865};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_55 = *(uintptr_t *) tmpcur_2857;
            GibCursor tmpcur_2866 = GIB_UNTAG(tagged_tmpcur_55);
            GibCursor tmpaftercur_2867 = tmpcur_2857 + 8;
            uint16_t tmptag_2868 = GIB_GET_TAG(tagged_tmpcur_55);
            GibCursor end_from_tagged_indr_1521 = tmpcur_2866 + tmptag_2868;
            GibCursor jump_1523 = tmpcur_2857 + 8;
            GibBool chk_1976 = tmpcur_2866 < end_from_tagged_indr_1521;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_54 =
                                    _traverse_AList(end_from_tagged_indr_1521, tmpcur_2866);
            GibCursor pvrtmp_2869 = tmp_struct_54.field0;
            GibCursor pvrtmp_2870 = tmp_struct_54.field1;
            
            return (GibCursorGibCursorProd) {end_r_1127, jump_1523};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_57 = *(uintptr_t *) tmpcur_2857;
            GibCursor tmpcur_2871 = GIB_UNTAG(tagged_tmpcur_57);
            GibCursor tmpaftercur_2872 = tmpcur_2857 + 8;
            uint16_t tmptag_2873 = GIB_GET_TAG(tagged_tmpcur_57);
            GibCursor end_from_tagged_indr_1521 = tmpcur_2871 + tmptag_2873;
            GibBool chk_1980 = tmpcur_2871 < end_from_tagged_indr_1521;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_56 =
                                    _traverse_AList(end_from_tagged_indr_1521, tmpcur_2871);
            GibCursor pvrtmp_2874 = tmp_struct_56.field0;
            GibCursor pvrtmp_2875 = tmp_struct_56.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_2874, pvrtmp_2875};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2856");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_AList(GibCursor end_r_1129,
                                    GibCursor arg_410_566_738)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2877 = *(GibPackedTag *) arg_410_566_738;
    GibCursor tmpcur_2878 = arg_410_566_738 + 1;
    
    
  switch_2897:
    ;
    switch (tmpval_2877) {
        
      case 0:
        {
            GibInt tmpval_2879 = *(GibInt *) tmpcur_2878;
            GibCursor tmpcur_2880 = tmpcur_2878 + sizeof(GibInt);
            GibCursor jump_1442 = tmpcur_2878 + 8;
            unsigned char wildcard_413_568_740 = gib_print_symbol(2534);
            unsigned char y_412_569_741 = printf("%ld", tmpval_2879);
            unsigned char y_412_570_742 = gib_print_symbol(2537);
            unsigned char wildcard_414_571_743 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {end_r_1129, jump_1442};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2881 = *(GibInt *) tmpcur_2878;
            GibCursor tmpcur_2882 = tmpcur_2878 + sizeof(GibInt);
            GibCursor jump_1444 = tmpcur_2878 + 8;
            unsigned char wildcard_417_573_745 = gib_print_symbol(2533);
            unsigned char y_416_574_746 = printf("%ld", tmpval_2881);
            unsigned char y_416_575_747 = gib_print_symbol(2537);
            unsigned char wildcard_418_576_748 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {end_r_1129, jump_1444};
            break;
        }
        
      case 2:
        {
            unsigned char wildcard_423_579_751 = gib_print_symbol(2532);
            GibBool chk_1987 = tmpcur_2878 < end_r_1129;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_58 =
                                    _print_AList(end_r_1129, tmpcur_2878);
            GibCursor pvrtmp_2883 = tmp_struct_58.field0;
            GibCursor pvrtmp_2884 = tmp_struct_58.field1;
            unsigned char y_421_581_753 = gib_print_symbol(2537);
            GibBool chk_1989 = pvrtmp_2884 < pvrtmp_2883;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_59 =
                                    _print_AList(pvrtmp_2883, pvrtmp_2884);
            GibCursor pvrtmp_2885 = tmp_struct_59.field0;
            GibCursor pvrtmp_2886 = tmp_struct_59.field1;
            unsigned char y_422_583_755 = gib_print_symbol(2537);
            unsigned char wildcard_424_584_756 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {pvrtmp_2885, pvrtmp_2886};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_61 = *(uintptr_t *) tmpcur_2878;
            GibCursor tmpcur_2887 = GIB_UNTAG(tagged_tmpcur_61);
            GibCursor tmpaftercur_2888 = tmpcur_2878 + 8;
            uint16_t tmptag_2889 = GIB_GET_TAG(tagged_tmpcur_61);
            GibCursor end_from_tagged_indr_1527 = tmpcur_2887 + tmptag_2889;
            GibCursor jump_1529 = tmpcur_2878 + 8;
            unsigned char wildcard_1532 = gib_print_symbol(2536);
            GibBool chk_1993 = tmpcur_2887 < end_from_tagged_indr_1527;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_60 =
                                    _print_AList(end_from_tagged_indr_1527, tmpcur_2887);
            GibCursor pvrtmp_2890 = tmp_struct_60.field0;
            GibCursor pvrtmp_2891 = tmp_struct_60.field1;
            
            return (GibCursorGibCursorProd) {end_r_1129, jump_1529};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_63 = *(uintptr_t *) tmpcur_2878;
            GibCursor tmpcur_2892 = GIB_UNTAG(tagged_tmpcur_63);
            GibCursor tmpaftercur_2893 = tmpcur_2878 + 8;
            uint16_t tmptag_2894 = GIB_GET_TAG(tagged_tmpcur_63);
            GibCursor end_from_tagged_indr_1527 = tmpcur_2892 + tmptag_2894;
            unsigned char wildcard_1532 = gib_print_symbol(2535);
            GibBool chk_1997 = tmpcur_2892 < end_from_tagged_indr_1527;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_62 =
                                    _print_AList(end_from_tagged_indr_1527, tmpcur_2892);
            GibCursor pvrtmp_2895 = tmp_struct_62.field0;
            GibCursor pvrtmp_2896 = tmp_struct_62.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_2895, pvrtmp_2896};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2877");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_PList_v_279(GibCursor end_r_1132,
                                                                    GibCursor end_r_1133,
                                                                    GibCursor loc_1131,
                                                                    GibCursor arg_425_585_757)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_1131 + 26 > end_r_1133) {
        gib_grow_region(&loc_1131, &end_r_1133);
    }
    
    GibPackedTag tmpval_2898 = *(GibPackedTag *) arg_425_585_757;
    GibCursor tmpcur_2899 = arg_425_585_757 + 1;
    
    
  switch_2949:
    ;
    switch (tmpval_2898) {
        
      case 0:
        {
            GibCursor jump_1449 = arg_425_585_757 + 1;
            
            *(GibPackedTag *) loc_1131 = 0;
            
            GibCursor writetag_2000 = loc_1131 + 1;
            GibCursor after_tag_2001 = loc_1131 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1132,
                                                                        end_r_1133,
                                                                        jump_1449,
                                                                        loc_1131,
                                                                        after_tag_2001};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2904 = *(GibInt *) tmpcur_2899;
            GibCursor tmpcur_2905 = tmpcur_2899 + sizeof(GibInt);
            GibInt tmpval_2906 = *(GibInt *) tmpcur_2905;
            GibCursor tmpcur_2907 = tmpcur_2905 + sizeof(GibInt);
            GibCursor loc_1330 = loc_1131 + 17;
            
            *(GibPackedTag *) loc_1131 = 1;
            
            GibCursor writetag_2013 = loc_1131 + 1;
            GibCursor after_tag_2014 = loc_1131 + 1;
            
            *(GibInt *) after_tag_2014 = tmpval_2904;
            
            GibCursor writecur_2018 = after_tag_2014 + sizeof(GibInt);
            
            *(GibInt *) writecur_2018 = tmpval_2906;
            
            GibCursor writecur_2019 = writecur_2018 + sizeof(GibInt);
            GibBool chk_2011 = tmpcur_2907 < end_r_1132;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2010 = loc_1330 < end_r_1133;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_64 =
                                                               _copy_PList_v_279(end_r_1132, end_r_1133, loc_1330, tmpcur_2907);
            GibCursor pvrtmp_2908 = tmp_struct_64.field0;
            GibCursor pvrtmp_2909 = tmp_struct_64.field1;
            GibCursor pvrtmp_2910 = tmp_struct_64.field2;
            GibCursor pvrtmp_2911 = tmp_struct_64.field3;
            GibCursor pvrtmp_2912 = tmp_struct_64.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2908,
                                                                        pvrtmp_2909,
                                                                        pvrtmp_2910,
                                                                        loc_1131,
                                                                        pvrtmp_2912};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_66 = *(uintptr_t *) tmpcur_2899;
            GibCursor tmpcur_2921 = GIB_UNTAG(tagged_tmpcur_66);
            GibCursor tmpaftercur_2922 = tmpcur_2899 + 8;
            uint16_t tmptag_2923 = GIB_GET_TAG(tagged_tmpcur_66);
            GibCursor end_from_tagged_indr_1533 = tmpcur_2921 + tmptag_2923;
            GibCursor jump_1535 = tmpcur_2899 + 8;
            GibBool chk_2026 = tmpcur_2921 < end_from_tagged_indr_1533;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2025 = loc_1131 < end_r_1133;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_65 =
                                                               _copy_PList_v_279(end_from_tagged_indr_1533, end_r_1133, loc_1131, tmpcur_2921);
            GibCursor pvrtmp_2924 = tmp_struct_65.field0;
            GibCursor pvrtmp_2925 = tmp_struct_65.field1;
            GibCursor pvrtmp_2926 = tmp_struct_65.field2;
            GibCursor pvrtmp_2927 = tmp_struct_65.field3;
            GibCursor pvrtmp_2928 = tmp_struct_65.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1132,
                                                                        pvrtmp_2925,
                                                                        jump_1535,
                                                                        pvrtmp_2927,
                                                                        pvrtmp_2928};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_68 = *(uintptr_t *) tmpcur_2899;
            GibCursor tmpcur_2935 = GIB_UNTAG(tagged_tmpcur_68);
            GibCursor tmpaftercur_2936 = tmpcur_2899 + 8;
            uint16_t tmptag_2937 = GIB_GET_TAG(tagged_tmpcur_68);
            GibCursor end_from_tagged_indr_1533 = tmpcur_2935 + tmptag_2937;
            GibBool chk_2031 = tmpcur_2935 < end_from_tagged_indr_1533;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2030 = loc_1131 < end_r_1133;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                               _copy_PList_v_279(end_from_tagged_indr_1533, end_r_1133, loc_1131, tmpcur_2935);
            GibCursor pvrtmp_2938 = tmp_struct_67.field0;
            GibCursor pvrtmp_2939 = tmp_struct_67.field1;
            GibCursor pvrtmp_2940 = tmp_struct_67.field2;
            GibCursor pvrtmp_2941 = tmp_struct_67.field3;
            GibCursor pvrtmp_2942 = tmp_struct_67.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2938,
                                                                        pvrtmp_2939,
                                                                        pvrtmp_2940,
                                                                        pvrtmp_2941,
                                                                        pvrtmp_2942};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2898");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_PList_v_279(GibCursor end_r_1136,
                                                                                 GibCursor end_r_1137,
                                                                                 GibCursor loc_1135,
                                                                                 GibCursor arg_432_592_764)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_2950 = *(GibPackedTag *) arg_432_592_764;
    GibCursor tmpcur_2951 = arg_432_592_764 + 1;
    
    
  switch_3001:
    ;
    switch (tmpval_2950) {
        
      case 0:
        {
            GibCursor jump_1455 = arg_432_592_764 + 1;
            
            *(GibPackedTag *) loc_1135 = 0;
            
            GibCursor writetag_2034 = loc_1135 + 1;
            GibCursor after_tag_2035 = loc_1135 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1136,
                                                                        end_r_1137,
                                                                        jump_1455,
                                                                        loc_1135,
                                                                        after_tag_2035};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_2956 = *(GibInt *) tmpcur_2951;
            GibCursor tmpcur_2957 = tmpcur_2951 + sizeof(GibInt);
            GibInt tmpval_2958 = *(GibInt *) tmpcur_2957;
            GibCursor tmpcur_2959 = tmpcur_2957 + sizeof(GibInt);
            GibCursor loc_1347 = loc_1135 + 17;
            
            *(GibPackedTag *) loc_1135 = 1;
            
            GibCursor writetag_2047 = loc_1135 + 1;
            GibCursor after_tag_2048 = loc_1135 + 1;
            
            *(GibInt *) after_tag_2048 = tmpval_2956;
            
            GibCursor writecur_2052 = after_tag_2048 + sizeof(GibInt);
            
            *(GibInt *) writecur_2052 = tmpval_2958;
            
            GibCursor writecur_2053 = writecur_2052 + sizeof(GibInt);
            GibBool chk_2045 = tmpcur_2959 < end_r_1136;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2044 = loc_1347 < end_r_1137;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_72 =
                                                               _copy_without_ptrs_PList_v_279(end_r_1136, end_r_1137, loc_1347, tmpcur_2959);
            GibCursor pvrtmp_2960 = tmp_struct_72.field0;
            GibCursor pvrtmp_2961 = tmp_struct_72.field1;
            GibCursor pvrtmp_2962 = tmp_struct_72.field2;
            GibCursor pvrtmp_2963 = tmp_struct_72.field3;
            GibCursor pvrtmp_2964 = tmp_struct_72.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2960,
                                                                        pvrtmp_2961,
                                                                        pvrtmp_2962,
                                                                        loc_1135,
                                                                        pvrtmp_2964};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_74 = *(uintptr_t *) tmpcur_2951;
            GibCursor tmpcur_2973 = GIB_UNTAG(tagged_tmpcur_74);
            GibCursor tmpaftercur_2974 = tmpcur_2951 + 8;
            uint16_t tmptag_2975 = GIB_GET_TAG(tagged_tmpcur_74);
            GibCursor end_from_tagged_indr_1539 = tmpcur_2973 + tmptag_2975;
            GibCursor jump_1541 = tmpcur_2951 + 8;
            GibBool chk_2060 = tmpcur_2973 < end_from_tagged_indr_1539;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2059 = loc_1135 < end_r_1137;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_73 =
                                                               _copy_without_ptrs_PList_v_279(end_from_tagged_indr_1539, end_r_1137, loc_1135, tmpcur_2973);
            GibCursor pvrtmp_2976 = tmp_struct_73.field0;
            GibCursor pvrtmp_2977 = tmp_struct_73.field1;
            GibCursor pvrtmp_2978 = tmp_struct_73.field2;
            GibCursor pvrtmp_2979 = tmp_struct_73.field3;
            GibCursor pvrtmp_2980 = tmp_struct_73.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1136,
                                                                        pvrtmp_2977,
                                                                        jump_1541,
                                                                        pvrtmp_2979,
                                                                        pvrtmp_2980};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_76 = *(uintptr_t *) tmpcur_2951;
            GibCursor tmpcur_2987 = GIB_UNTAG(tagged_tmpcur_76);
            GibCursor tmpaftercur_2988 = tmpcur_2951 + 8;
            uint16_t tmptag_2989 = GIB_GET_TAG(tagged_tmpcur_76);
            GibCursor end_from_tagged_indr_1539 = tmpcur_2987 + tmptag_2989;
            GibBool chk_2065 = tmpcur_2987 < end_from_tagged_indr_1539;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2064 = loc_1135 < end_r_1137;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_75 =
                                                               _copy_without_ptrs_PList_v_279(end_from_tagged_indr_1539, end_r_1137, loc_1135, tmpcur_2987);
            GibCursor pvrtmp_2990 = tmp_struct_75.field0;
            GibCursor pvrtmp_2991 = tmp_struct_75.field1;
            GibCursor pvrtmp_2992 = tmp_struct_75.field2;
            GibCursor pvrtmp_2993 = tmp_struct_75.field3;
            GibCursor pvrtmp_2994 = tmp_struct_75.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_2990,
                                                                        pvrtmp_2991,
                                                                        pvrtmp_2992,
                                                                        pvrtmp_2993,
                                                                        pvrtmp_2994};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_2950");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_PList_v_279(GibCursor end_r_1139,
                                             GibCursor arg_439_599_771)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3002 = *(GibPackedTag *) arg_439_599_771;
    GibCursor tmpcur_3003 = arg_439_599_771 + 1;
    
    
  switch_3020:
    ;
    switch (tmpval_3002) {
        
      case 0:
        {
            GibCursor jump_1461 = arg_439_599_771 + 1;
            
            return (GibCursorGibCursorProd) {end_r_1139, jump_1461};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_3004 = *(GibInt *) tmpcur_3003;
            GibCursor tmpcur_3005 = tmpcur_3003 + sizeof(GibInt);
            GibInt tmpval_3006 = *(GibInt *) tmpcur_3005;
            GibCursor tmpcur_3007 = tmpcur_3005 + sizeof(GibInt);
            GibBool chk_2071 = tmpcur_3007 < end_r_1139;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_77 =
                                    _traverse_PList_v_279(end_r_1139, tmpcur_3007);
            GibCursor pvrtmp_3008 = tmp_struct_77.field0;
            GibCursor pvrtmp_3009 = tmp_struct_77.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_3008, pvrtmp_3009};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_79 = *(uintptr_t *) tmpcur_3003;
            GibCursor tmpcur_3010 = GIB_UNTAG(tagged_tmpcur_79);
            GibCursor tmpaftercur_3011 = tmpcur_3003 + 8;
            uint16_t tmptag_3012 = GIB_GET_TAG(tagged_tmpcur_79);
            GibCursor end_from_tagged_indr_1545 = tmpcur_3010 + tmptag_3012;
            GibCursor jump_1547 = tmpcur_3003 + 8;
            GibBool chk_2075 = tmpcur_3010 < end_from_tagged_indr_1545;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_78 =
                                    _traverse_PList_v_279(end_from_tagged_indr_1545, tmpcur_3010);
            GibCursor pvrtmp_3013 = tmp_struct_78.field0;
            GibCursor pvrtmp_3014 = tmp_struct_78.field1;
            
            return (GibCursorGibCursorProd) {end_r_1139, jump_1547};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_81 = *(uintptr_t *) tmpcur_3003;
            GibCursor tmpcur_3015 = GIB_UNTAG(tagged_tmpcur_81);
            GibCursor tmpaftercur_3016 = tmpcur_3003 + 8;
            uint16_t tmptag_3017 = GIB_GET_TAG(tagged_tmpcur_81);
            GibCursor end_from_tagged_indr_1545 = tmpcur_3015 + tmptag_3017;
            GibBool chk_2079 = tmpcur_3015 < end_from_tagged_indr_1545;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_80 =
                                    _traverse_PList_v_279(end_from_tagged_indr_1545, tmpcur_3015);
            GibCursor pvrtmp_3018 = tmp_struct_80.field0;
            GibCursor pvrtmp_3019 = tmp_struct_80.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_3018, pvrtmp_3019};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3002");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_PList_v_279(GibCursor end_r_1141,
                                          GibCursor arg_446_604_776)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3021 = *(GibPackedTag *) arg_446_604_776;
    GibCursor tmpcur_3022 = arg_446_604_776 + 1;
    
    
  switch_3039:
    ;
    switch (tmpval_3021) {
        
      case 0:
        {
            GibCursor jump_1467 = arg_446_604_776 + 1;
            unsigned char wildcard_447_605_777 = gib_print_symbol(2529);
            unsigned char wildcard_448_606_778 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {end_r_1141, jump_1467};
            break;
        }
        
      case 1:
        {
            GibInt tmpval_3023 = *(GibInt *) tmpcur_3022;
            GibCursor tmpcur_3024 = tmpcur_3022 + sizeof(GibInt);
            GibInt tmpval_3025 = *(GibInt *) tmpcur_3024;
            GibCursor tmpcur_3026 = tmpcur_3024 + sizeof(GibInt);
            unsigned char wildcard_455_610_782 = gib_print_symbol(2531);
            unsigned char y_452_611_783 = printf("%ld", tmpval_3023);
            unsigned char y_452_612_784 = gib_print_symbol(2537);
            unsigned char y_453_613_785 = printf("%ld", tmpval_3025);
            unsigned char y_453_614_786 = gib_print_symbol(2537);
            GibBool chk_2085 = tmpcur_3026 < end_r_1141;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_82 =
                                    _print_PList_v_279(end_r_1141, tmpcur_3026);
            GibCursor pvrtmp_3027 = tmp_struct_82.field0;
            GibCursor pvrtmp_3028 = tmp_struct_82.field1;
            unsigned char y_454_616_788 = gib_print_symbol(2537);
            unsigned char wildcard_456_617_789 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {pvrtmp_3027, pvrtmp_3028};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_84 = *(uintptr_t *) tmpcur_3022;
            GibCursor tmpcur_3029 = GIB_UNTAG(tagged_tmpcur_84);
            GibCursor tmpaftercur_3030 = tmpcur_3022 + 8;
            uint16_t tmptag_3031 = GIB_GET_TAG(tagged_tmpcur_84);
            GibCursor end_from_tagged_indr_1551 = tmpcur_3029 + tmptag_3031;
            GibCursor jump_1553 = tmpcur_3022 + 8;
            unsigned char wildcard_1556 = gib_print_symbol(2536);
            GibBool chk_2089 = tmpcur_3029 < end_from_tagged_indr_1551;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_83 =
                                    _print_PList_v_279(end_from_tagged_indr_1551, tmpcur_3029);
            GibCursor pvrtmp_3032 = tmp_struct_83.field0;
            GibCursor pvrtmp_3033 = tmp_struct_83.field1;
            
            return (GibCursorGibCursorProd) {end_r_1141, jump_1553};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_86 = *(uintptr_t *) tmpcur_3022;
            GibCursor tmpcur_3034 = GIB_UNTAG(tagged_tmpcur_86);
            GibCursor tmpaftercur_3035 = tmpcur_3022 + 8;
            uint16_t tmptag_3036 = GIB_GET_TAG(tagged_tmpcur_86);
            GibCursor end_from_tagged_indr_1551 = tmpcur_3034 + tmptag_3036;
            unsigned char wildcard_1556 = gib_print_symbol(2535);
            GibBool chk_2093 = tmpcur_3034 < end_from_tagged_indr_1551;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_85 =
                                    _print_PList_v_279(end_from_tagged_indr_1551, tmpcur_3034);
            GibCursor pvrtmp_3037 = tmp_struct_85.field0;
            GibCursor pvrtmp_3038 = tmp_struct_85.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_3037, pvrtmp_3038};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3021");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_Maybe_v_283(GibCursor end_r_1144,
                                                                    GibCursor end_r_1145,
                                                                    GibCursor loc_1143,
                                                                    GibCursor arg_457_618_790)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    
    if (loc_1143 + 18 > end_r_1145) {
        gib_grow_region(&loc_1143, &end_r_1145);
    }
    
    GibPackedTag tmpval_3040 = *(GibPackedTag *) arg_457_618_790;
    GibCursor tmpcur_3041 = arg_457_618_790 + 1;
    
    
  switch_3080:
    ;
    switch (tmpval_3040) {
        
      case 0:
        {
            GibInt tmpval_3042 = *(GibInt *) tmpcur_3041;
            GibCursor tmpcur_3043 = tmpcur_3041 + sizeof(GibInt);
            GibCursor jump_1473 = tmpcur_3041 + 8;
            
            *(GibPackedTag *) loc_1143 = 0;
            
            GibCursor writetag_2097 = loc_1143 + 1;
            GibCursor after_tag_2098 = loc_1143 + 1;
            
            *(GibInt *) after_tag_2098 = tmpval_3042;
            
            GibCursor writecur_2102 = after_tag_2098 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1144,
                                                                        end_r_1145,
                                                                        jump_1473,
                                                                        loc_1143,
                                                                        writecur_2102};
            break;
        }
        
      case 1:
        {
            GibCursor jump_1475 = arg_457_618_790 + 1;
            
            *(GibPackedTag *) loc_1143 = 1;
            
            GibCursor writetag_2106 = loc_1143 + 1;
            GibCursor after_tag_2107 = loc_1143 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1144,
                                                                        end_r_1145,
                                                                        jump_1475,
                                                                        loc_1143,
                                                                        after_tag_2107};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3041;
            GibCursor tmpcur_3052 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3053 = tmpcur_3041 + 8;
            uint16_t tmptag_3054 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_1557 = tmpcur_3052 + tmptag_3054;
            GibCursor jump_1559 = tmpcur_3041 + 8;
            GibBool chk_2116 = tmpcur_3052 < end_from_tagged_indr_1557;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2115 = loc_1143 < end_r_1145;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_87 =
                                                               _copy_Maybe_v_283(end_from_tagged_indr_1557, end_r_1145, loc_1143, tmpcur_3052);
            GibCursor pvrtmp_3055 = tmp_struct_87.field0;
            GibCursor pvrtmp_3056 = tmp_struct_87.field1;
            GibCursor pvrtmp_3057 = tmp_struct_87.field2;
            GibCursor pvrtmp_3058 = tmp_struct_87.field3;
            GibCursor pvrtmp_3059 = tmp_struct_87.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1144,
                                                                        pvrtmp_3056,
                                                                        jump_1559,
                                                                        pvrtmp_3058,
                                                                        pvrtmp_3059};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_90 = *(uintptr_t *) tmpcur_3041;
            GibCursor tmpcur_3066 = GIB_UNTAG(tagged_tmpcur_90);
            GibCursor tmpaftercur_3067 = tmpcur_3041 + 8;
            uint16_t tmptag_3068 = GIB_GET_TAG(tagged_tmpcur_90);
            GibCursor end_from_tagged_indr_1557 = tmpcur_3066 + tmptag_3068;
            GibBool chk_2121 = tmpcur_3066 < end_from_tagged_indr_1557;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2120 = loc_1143 < end_r_1145;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_89 =
                                                               _copy_Maybe_v_283(end_from_tagged_indr_1557, end_r_1145, loc_1143, tmpcur_3066);
            GibCursor pvrtmp_3069 = tmp_struct_89.field0;
            GibCursor pvrtmp_3070 = tmp_struct_89.field1;
            GibCursor pvrtmp_3071 = tmp_struct_89.field2;
            GibCursor pvrtmp_3072 = tmp_struct_89.field3;
            GibCursor pvrtmp_3073 = tmp_struct_89.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3069,
                                                                        pvrtmp_3070,
                                                                        pvrtmp_3071,
                                                                        pvrtmp_3072,
                                                                        pvrtmp_3073};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3040");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_Maybe_v_283(GibCursor end_r_1148,
                                                                                 GibCursor end_r_1149,
                                                                                 GibCursor loc_1147,
                                                                                 GibCursor arg_460_621_793)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3081 = *(GibPackedTag *) arg_460_621_793;
    GibCursor tmpcur_3082 = arg_460_621_793 + 1;
    
    
  switch_3121:
    ;
    switch (tmpval_3081) {
        
      case 0:
        {
            GibInt tmpval_3083 = *(GibInt *) tmpcur_3082;
            GibCursor tmpcur_3084 = tmpcur_3082 + sizeof(GibInt);
            GibCursor jump_1477 = tmpcur_3082 + 8;
            
            *(GibPackedTag *) loc_1147 = 0;
            
            GibCursor writetag_2125 = loc_1147 + 1;
            GibCursor after_tag_2126 = loc_1147 + 1;
            
            *(GibInt *) after_tag_2126 = tmpval_3083;
            
            GibCursor writecur_2130 = after_tag_2126 + sizeof(GibInt);
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1148,
                                                                        end_r_1149,
                                                                        jump_1477,
                                                                        loc_1147,
                                                                        writecur_2130};
            break;
        }
        
      case 1:
        {
            GibCursor jump_1479 = arg_460_621_793 + 1;
            
            *(GibPackedTag *) loc_1147 = 1;
            
            GibCursor writetag_2134 = loc_1147 + 1;
            GibCursor after_tag_2135 = loc_1147 + 1;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1148,
                                                                        end_r_1149,
                                                                        jump_1479,
                                                                        loc_1147,
                                                                        after_tag_2135};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_95 = *(uintptr_t *) tmpcur_3082;
            GibCursor tmpcur_3093 = GIB_UNTAG(tagged_tmpcur_95);
            GibCursor tmpaftercur_3094 = tmpcur_3082 + 8;
            uint16_t tmptag_3095 = GIB_GET_TAG(tagged_tmpcur_95);
            GibCursor end_from_tagged_indr_1563 = tmpcur_3093 + tmptag_3095;
            GibCursor jump_1565 = tmpcur_3082 + 8;
            GibBool chk_2144 = tmpcur_3093 < end_from_tagged_indr_1563;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2143 = loc_1147 < end_r_1149;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_94 =
                                                               _copy_without_ptrs_Maybe_v_283(end_from_tagged_indr_1563, end_r_1149, loc_1147, tmpcur_3093);
            GibCursor pvrtmp_3096 = tmp_struct_94.field0;
            GibCursor pvrtmp_3097 = tmp_struct_94.field1;
            GibCursor pvrtmp_3098 = tmp_struct_94.field2;
            GibCursor pvrtmp_3099 = tmp_struct_94.field3;
            GibCursor pvrtmp_3100 = tmp_struct_94.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {end_r_1148,
                                                                        pvrtmp_3097,
                                                                        jump_1565,
                                                                        pvrtmp_3099,
                                                                        pvrtmp_3100};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_97 = *(uintptr_t *) tmpcur_3082;
            GibCursor tmpcur_3107 = GIB_UNTAG(tagged_tmpcur_97);
            GibCursor tmpaftercur_3108 = tmpcur_3082 + 8;
            uint16_t tmptag_3109 = GIB_GET_TAG(tagged_tmpcur_97);
            GibCursor end_from_tagged_indr_1563 = tmpcur_3107 + tmptag_3109;
            GibBool chk_2149 = tmpcur_3107 < end_from_tagged_indr_1563;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibBool chk_2148 = loc_1147 < end_r_1149;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_96 =
                                                               _copy_without_ptrs_Maybe_v_283(end_from_tagged_indr_1563, end_r_1149, loc_1147, tmpcur_3107);
            GibCursor pvrtmp_3110 = tmp_struct_96.field0;
            GibCursor pvrtmp_3111 = tmp_struct_96.field1;
            GibCursor pvrtmp_3112 = tmp_struct_96.field2;
            GibCursor pvrtmp_3113 = tmp_struct_96.field3;
            GibCursor pvrtmp_3114 = tmp_struct_96.field4;
            
            return (GibCursorGibCursorGibCursorGibCursorGibCursorProd) {pvrtmp_3110,
                                                                        pvrtmp_3111,
                                                                        pvrtmp_3112,
                                                                        pvrtmp_3113,
                                                                        pvrtmp_3114};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3081");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_Maybe_v_283(GibCursor end_r_1151,
                                             GibCursor arg_463_624_796)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3122 = *(GibPackedTag *) arg_463_624_796;
    GibCursor tmpcur_3123 = arg_463_624_796 + 1;
    
    
  switch_3136:
    ;
    switch (tmpval_3122) {
        
      case 0:
        {
            GibInt tmpval_3124 = *(GibInt *) tmpcur_3123;
            GibCursor tmpcur_3125 = tmpcur_3123 + sizeof(GibInt);
            GibCursor jump_1481 = tmpcur_3123 + 8;
            
            return (GibCursorGibCursorProd) {end_r_1151, jump_1481};
            break;
        }
        
      case 1:
        {
            GibCursor jump_1483 = arg_463_624_796 + 1;
            
            return (GibCursorGibCursorProd) {end_r_1151, jump_1483};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_99 = *(uintptr_t *) tmpcur_3123;
            GibCursor tmpcur_3126 = GIB_UNTAG(tagged_tmpcur_99);
            GibCursor tmpaftercur_3127 = tmpcur_3123 + 8;
            uint16_t tmptag_3128 = GIB_GET_TAG(tagged_tmpcur_99);
            GibCursor end_from_tagged_indr_1569 = tmpcur_3126 + tmptag_3128;
            GibCursor jump_1571 = tmpcur_3123 + 8;
            GibBool chk_2156 = tmpcur_3126 < end_from_tagged_indr_1569;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_98 =
                                    _traverse_Maybe_v_283(end_from_tagged_indr_1569, tmpcur_3126);
            GibCursor pvrtmp_3129 = tmp_struct_98.field0;
            GibCursor pvrtmp_3130 = tmp_struct_98.field1;
            
            return (GibCursorGibCursorProd) {end_r_1151, jump_1571};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) tmpcur_3123;
            GibCursor tmpcur_3131 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_3132 = tmpcur_3123 + 8;
            uint16_t tmptag_3133 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_indr_1569 = tmpcur_3131 + tmptag_3133;
            GibBool chk_2160 = tmpcur_3131 < end_from_tagged_indr_1569;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_100 =
                                    _traverse_Maybe_v_283(end_from_tagged_indr_1569, tmpcur_3131);
            GibCursor pvrtmp_3134 = tmp_struct_100.field0;
            GibCursor pvrtmp_3135 = tmp_struct_100.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_3134, pvrtmp_3135};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3122");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_Maybe_v_283(GibCursor end_r_1153,
                                          GibCursor arg_466_626_798)
{
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibPackedTag tmpval_3137 = *(GibPackedTag *) arg_466_626_798;
    GibCursor tmpcur_3138 = arg_466_626_798 + 1;
    
    
  switch_3151:
    ;
    switch (tmpval_3137) {
        
      case 0:
        {
            GibInt tmpval_3139 = *(GibInt *) tmpcur_3138;
            GibCursor tmpcur_3140 = tmpcur_3138 + sizeof(GibInt);
            GibCursor jump_1485 = tmpcur_3138 + 8;
            unsigned char wildcard_469_628_800 = gib_print_symbol(2530);
            unsigned char y_468_629_801 = printf("%ld", tmpval_3139);
            unsigned char y_468_630_802 = gib_print_symbol(2537);
            unsigned char wildcard_470_631_803 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {end_r_1153, jump_1485};
            break;
        }
        
      case 1:
        {
            GibCursor jump_1487 = arg_466_626_798 + 1;
            unsigned char wildcard_471_632_804 = gib_print_symbol(2528);
            unsigned char wildcard_472_633_805 = gib_print_symbol(2527);
            
            return (GibCursorGibCursorProd) {end_r_1153, jump_1487};
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) tmpcur_3138;
            GibCursor tmpcur_3141 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_3142 = tmpcur_3138 + 8;
            uint16_t tmptag_3143 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_indr_1575 = tmpcur_3141 + tmptag_3143;
            GibCursor jump_1577 = tmpcur_3138 + 8;
            unsigned char wildcard_1580 = gib_print_symbol(2536);
            GibBool chk_2167 = tmpcur_3141 < end_from_tagged_indr_1575;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_102 =
                                    _print_Maybe_v_283(end_from_tagged_indr_1575, tmpcur_3141);
            GibCursor pvrtmp_3144 = tmp_struct_102.field0;
            GibCursor pvrtmp_3145 = tmp_struct_102.field1;
            
            return (GibCursorGibCursorProd) {end_r_1153, jump_1577};
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) tmpcur_3138;
            GibCursor tmpcur_3146 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_3147 = tmpcur_3138 + 8;
            uint16_t tmptag_3148 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_indr_1575 = tmpcur_3146 + tmptag_3148;
            unsigned char wildcard_1580 = gib_print_symbol(2535);
            GibBool chk_2171 = tmpcur_3146 < end_from_tagged_indr_1575;
            
            #ifdef _GIBBON_DEBUG
            #endif
            
            GibCursorGibCursorProd tmp_struct_104 =
                                    _print_Maybe_v_283(end_from_tagged_indr_1575, tmpcur_3146);
            GibCursor pvrtmp_3149 = tmp_struct_104.field0;
            GibCursor pvrtmp_3150 = tmp_struct_104.field1;
            
            return (GibCursorGibCursorProd) {pvrtmp_3149, pvrtmp_3150};
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3137");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_112 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibShadowstack *rstack = DEFAULT_READ_SHADOWSTACK;
    GibShadowstack *wstack = DEFAULT_WRITE_SHADOWSTACK;
    GibShadowstackFrame *frame;
    GibChunk region_2538 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1194 = region_2538.start;
    GibCursor end_r_1194 = region_2538.end;
    GibCursor loc_1184 = r_1194 + 17;
    GibCursor loc_1179 = r_1194 + 34;
    GibCursor loc_1174 = r_1194 + 51;
    GibCursor loc_1169 = r_1194 + 68;
    GibCursor loc_1164 = r_1194 + 85;
    GibCursor loc_1159 = r_1194 + 102;
    
    *(GibPackedTag *) r_1194 = 1;
    
    GibCursor writetag_2230 = r_1194 + 1;
    GibCursor after_tag_2231 = r_1194 + 1;
    
    *(GibInt *) after_tag_2231 = 1;
    
    GibCursor writecur_2235 = after_tag_2231 + sizeof(GibInt);
    
    *(GibInt *) writecur_2235 = 177;
    
    GibCursor writecur_2236 = writecur_2235 + sizeof(GibInt);
    
    *(GibPackedTag *) loc_1159 = 0;
    
    GibCursor writetag_2173 = loc_1159 + 1;
    GibCursor after_tag_2174 = loc_1159 + 1;
    
    *(GibPackedTag *) loc_1164 = 1;
    
    GibCursor writetag_2180 = loc_1164 + 1;
    GibCursor after_tag_2181 = loc_1164 + 1;
    
    *(GibInt *) after_tag_2181 = 250;
    
    GibCursor writecur_2185 = after_tag_2181 + sizeof(GibInt);
    
    *(GibInt *) writecur_2185 = 55;
    
    GibCursor writecur_2186 = writecur_2185 + sizeof(GibInt);
    
    *(GibPackedTag *) loc_1169 = 1;
    
    GibCursor writetag_2190 = loc_1169 + 1;
    GibCursor after_tag_2191 = loc_1169 + 1;
    
    *(GibInt *) after_tag_2191 = 100;
    
    GibCursor writecur_2195 = after_tag_2191 + sizeof(GibInt);
    
    *(GibInt *) writecur_2195 = 88;
    
    GibCursor writecur_2196 = writecur_2195 + sizeof(GibInt);
    
    *(GibPackedTag *) loc_1174 = 1;
    
    GibCursor writetag_2200 = loc_1174 + 1;
    GibCursor after_tag_2201 = loc_1174 + 1;
    
    *(GibInt *) after_tag_2201 = 25;
    
    GibCursor writecur_2205 = after_tag_2201 + sizeof(GibInt);
    
    *(GibInt *) writecur_2205 = 88;
    
    GibCursor writecur_2206 = writecur_2205 + sizeof(GibInt);
    
    *(GibPackedTag *) loc_1179 = 1;
    
    GibCursor writetag_2210 = loc_1179 + 1;
    GibCursor after_tag_2211 = loc_1179 + 1;
    
    *(GibInt *) after_tag_2211 = 10;
    
    GibCursor writecur_2215 = after_tag_2211 + sizeof(GibInt);
    
    *(GibInt *) writecur_2215 = 99;
    
    GibCursor writecur_2216 = writecur_2215 + sizeof(GibInt);
    
    *(GibPackedTag *) loc_1184 = 1;
    
    GibCursor writetag_2220 = loc_1184 + 1;
    GibCursor after_tag_2221 = loc_1184 + 1;
    
    *(GibInt *) after_tag_2221 = 5;
    
    GibCursor writecur_2225 = after_tag_2221 + sizeof(GibInt);
    
    *(GibInt *) writecur_2225 = 122;
    
    GibCursor writecur_2226 = writecur_2225 + sizeof(GibInt);
    GibInt amt_61_474_679 = gib_get_size_param();
    
    gib_shadowstack_push(rstack, r_1194, end_r_1194, Stk, PList_v_279_T);
    
    GibChunk region_2553 = gib_alloc_region(gib_get_inf_init_chunk_size());
    GibCursor r_1193 = region_2553.start;
    GibCursor end_r_1193 = region_2553.end;
    
    frame = gib_shadowstack_pop(rstack);
    r_1194 = frame->ptr;
    end_r_1194 = frame->endptr;
    
    GibCursor pvrtmp_2564;
    GibCursor pvrtmp_2565;
    GibCursor pvrtmp_2566;
    GibVector *times_110 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_pvrtmp_2564;
    struct timespec end_pvrtmp_2564;
    
    for (long long iters_pvrtmp_2564 = 0; iters_pvrtmp_2564 <
         gib_get_iters_param(); iters_pvrtmp_2564++) {
        if (iters_pvrtmp_2564 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_2564);
        
        GibBool chk_2241 = r_1194 < end_r_1194;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibBool chk_2240 = r_1193 < end_r_1193;
        
        #ifdef _GIBBON_DEBUG
        #endif
        
        GibCursorGibCursorGibCursorGibCursorProd tmp_struct_106 =
                                                  payA_seq(end_r_1194, end_r_1193, r_1193, amt_61_474_679, r_1194);
        GibCursor pvrtmp_2554 = tmp_struct_106.field0;
        GibCursor pvrtmp_2555 = tmp_struct_106.field1;
        GibCursor pvrtmp_2556 = tmp_struct_106.field2;
        GibCursor pvrtmp_2557 = tmp_struct_106.field3;
        
        pvrtmp_2564 = pvrtmp_2555;
        pvrtmp_2565 = pvrtmp_2556;
        pvrtmp_2566 = pvrtmp_2557;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_2564);
        if (iters_pvrtmp_2564 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_107 = gib_difftimespecs(&begin_pvrtmp_2564,
                                                &end_pvrtmp_2564);
        
        printf("itertime: %lf\n", itertime_107);
        gib_vector_inplace_update(times_110, iters_pvrtmp_2564, &itertime_107);
    }
    gib_vector_inplace_sort(times_110, gib_compare_doubles);
    
    double *tmp_111 = (double *) gib_vector_nth(times_110,
                                                gib_get_iters_param() / 2);
    double selftimed_109 = *tmp_111;
    double batchtime_108 = gib_sum_timing_array(times_110);
    
    gib_print_timing_array(times_110);
    gib_vector_free(times_110);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_108);
    printf("SELFTIMED: %e\n", selftimed_109);
    printf("'#()");
    printf("\n");
    return 0;
    
    int exit_113 = gib_exit();
    
    return exit_113;
}