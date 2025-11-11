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
typedef struct GibCursorPtr7Prod_struct {
            GibCursor field0[7];
        } GibCursorPtr7Prod;
typedef struct GibCursorPtr7GibCursorPtr7Prod_struct {
            GibCursor field0[7];
            GibCursor field1[7];
        } GibCursorPtr7GibCursorPtr7Prod;
typedef struct GibCursorPtr7GibCursorPtr7GibIntProd_struct {
            GibCursor field0[7];
            GibCursor field1[7];
            GibInt field2;
        } GibCursorPtr7GibCursorPtr7GibIntProd;
typedef struct GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod_struct {
            GibCursor field0[7];
            GibCursor field1[7];
            GibCursor field2[7];
        } GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod;
typedef struct GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod_struct {
            GibCursor field0[7];
            GibCursor field1[7];
            GibCursor field2[7];
            GibCursor field3[7];
            GibCursor field4[7];
        } GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod;
GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
_copy_without_ptrs_ListB(GibCursor cursor_ptr_2498[7],
                         GibCursor cursor_ptr_2497[7],
                         GibCursor cursor_ptr_2499[7],
                         GibCursor arg_191_249_424[7]);
GibCursorGibCursorProd _traverse_ListA(GibCursor end_r_1229,
                                       GibCursor arg_98_264_439);
GibCursorGibCursorProd _print_List(GibCursor end_r_1232,
                                   GibCursor arg_153_268_443);
GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
mkListB(GibCursor cursor_ptr_2686[7], GibCursor cursor_ptr_2687[7],
        GibInt len_34_291_466);
GibCursorGibCursorProd _traverse_List(GibCursor end_r_1249,
                                      GibCursor arg_140_293_470);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_ListA(GibCursor end_r_1253, GibCursor end_r_1255,
                         GibCursor loc_1251, GibCursor arg_93_302_479);
void reduceB(GibCursor cursor_ptr_2775[7],
                       GibCursor lst_36_307_484[7],
                       GibInt *Res);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_ListA(GibCursor end_r_1273, GibCursor end_r_1275, GibCursor loc_1271,
            GibCursor arg_88_315_493);
GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
_copy_ListB(GibCursor cursor_ptr_2925[7], GibCursor cursor_ptr_2924[7],
            GibCursor cursor_ptr_2926[7], GibCursor arg_176_330_498[7]);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_List(GibCursor end_r_1307, GibCursor end_r_1309, GibCursor loc_1305,
           GibCursor arg_114_345_513);
GibCursorPtr7GibCursorPtr7Prod _traverse_ListB(GibCursor cursor_ptr_3126[7],
                                               GibCursor arg_206_358_526[7]);
GibCursorGibCursorProd _print_ListA(GibCursor end_r_1326,
                                    GibCursor arg_103_369_535);
GibCursorPtr7GibCursorPtr7Prod _print_ListB(GibCursor cursor_ptr_3256[7],
                                            GibCursor arg_221_380_546[7]);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_List(GibCursor end_r_1344, GibCursor end_r_1346,
                        GibCursor loc_1342, GibCursor arg_127_406_572);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            List_T,
            ListA_T,
            ListB_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(10);
    
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    
    GibDatatype field_tys[7];
    
    field_tys[0] = ListA_T;
    field_tys[1] = List_T;
    error = gib_info_table_insert_packed_dcon(List_T, 0, 32, 0, 4, 2, field_tys,
                                              2);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(List_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, List_T, 1);
        exit(1);
    }
    field_tys[0] = ListA_T;
    error = gib_info_table_insert_packed_dcon(ListA_T, 0, 8, 0, 1, 1, field_tys,
                                              1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, ListA_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(ListA_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, ListA_T, 1);
        exit(1);
    }
    field_tys[0] = ListB_T;
    error = gib_info_table_insert_packed_dcon(ListB_T, 0, 48, 0, 6, 1,
                                              field_tys, 1);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, ListB_T, 0);
        exit(1);
    }
    error = gib_info_table_insert_packed_dcon(ListB_T, 1, 0, 0, 0, 0, field_tys,
                                              0);
    if (error < 0) {
        fprintf(stderr,
                "Couldn't insert into info table, errorno=%d, tycon=%d, dcon=%d",
                error, ListB_T, 1);
        exit(1);
    }
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(3638, ")");
    gib_add_symbol(3639, "(NilB");
    gib_add_symbol(3640, "(NilA");
    gib_add_symbol(3641, "(Nil");
    gib_add_symbol(3642, "(ConsB");
    gib_add_symbol(3643, "(ConsA");
    gib_add_symbol(3644, "(Cons");
    gib_add_symbol(3645, " ->r ");
    gib_add_symbol(3646, " ->i ");
    gib_add_symbol(3647, " ");
}
GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod _copy_without_ptrs_ListB(GibCursor cursor_ptr_2498[7],
                                                                                               GibCursor cursor_ptr_2497[7],
                                                                                               GibCursor cursor_ptr_2499[7],
                                                                                               GibCursor arg_191_249_424[7])
{
    GibCursor end_r_1213 = cursor_ptr_2498[0];
    GibCursor end_r_1214 = cursor_ptr_2498[1];
    GibCursor end_r_1215 = cursor_ptr_2498[2];
    GibCursor end_r_1216 = cursor_ptr_2498[3];
    GibCursor end_r_1217 = cursor_ptr_2498[4];
    GibCursor end_r_1218 = cursor_ptr_2498[5];
    GibCursor end_r_1219 = cursor_ptr_2498[6];
    GibCursor end_r_1220 = cursor_ptr_2497[0];
    GibCursor end_r_1221 = cursor_ptr_2497[1];
    GibCursor end_r_1222 = cursor_ptr_2497[2];
    GibCursor end_r_1223 = cursor_ptr_2497[3];
    GibCursor end_r_1224 = cursor_ptr_2497[4];
    GibCursor end_r_1225 = cursor_ptr_2497[5];
    GibCursor end_r_1226 = cursor_ptr_2497[6];
    GibCursor dcon_2502 = arg_191_249_424[0];
    GibPackedTag tmpval_3665 = *(GibPackedTag *) dcon_2502;
    GibCursor tmpcur_3666 = dcon_2502 + 1;
    
    
  switch_3760:
    ;
    switch (tmpval_3665) {
        
      case 0:
        {
            GibCursor soa_field_0_2504 = arg_191_249_424[1];
            GibCursor soa_field_1_2505 = arg_191_249_424[2];
            GibCursor soa_field_2_2506 = arg_191_249_424[3];
            GibCursor soa_field_3_2507 = arg_191_249_424[4];
            GibCursor soa_field_4_2508 = arg_191_249_424[5];
            GibCursor soa_field_5_2509 = arg_191_249_424[6];
            GibInt tmpval_3667 = *(GibInt *) soa_field_0_2504;
            GibCursor tmpcur_3668 = soa_field_0_2504 + sizeof(GibInt);
            GibInt tmpval_3669 = *(GibInt *) soa_field_1_2505;
            GibCursor tmpcur_3670 = soa_field_1_2505 + sizeof(GibInt);
            GibInt tmpval_3671 = *(GibInt *) soa_field_2_2506;
            GibCursor tmpcur_3672 = soa_field_2_2506 + sizeof(GibInt);
            GibInt tmpval_3673 = *(GibInt *) soa_field_3_2507;
            GibCursor tmpcur_3674 = soa_field_3_2507 + sizeof(GibInt);
            GibInt tmpval_3675 = *(GibInt *) soa_field_4_2508;
            GibCursor tmpcur_3676 = soa_field_4_2508 + sizeof(GibInt);
            GibInt tmpval_3677 = *(GibInt *) soa_field_5_2509;
            GibCursor tmpcur_3678 = soa_field_5_2509 + sizeof(GibInt);
            GibCursor cursor_ptr_2501[7] = {tmpcur_3666, tmpcur_3668,
                                            tmpcur_3670, tmpcur_3672,
                                            tmpcur_3674, tmpcur_3676,
                                            tmpcur_3678};
            GibCursor loc_1199 = arg_191_249_424[0];
            GibCursor jumpf_dloc_1807 = loc_1199 + 1;
            GibCursor loc_IntTy_1200 = arg_191_249_424[1];
            GibCursor loc_IntTy_1201 = arg_191_249_424[2];
            GibCursor loc_IntTy_1202 = arg_191_249_424[3];
            GibCursor loc_IntTy_1203 = arg_191_249_424[4];
            GibCursor loc_IntTy_1204 = arg_191_249_424[5];
            GibCursor loc_IntTy_1205 = arg_191_249_424[6];
            GibCursor jumpf_floc_loc_1808 = soa_field_0_2504 + 8;
            GibCursor jumpf_floc_loc_1809 = soa_field_1_2505 + 8;
            GibCursor jumpf_floc_loc_1810 = soa_field_2_2506 + 8;
            GibCursor jumpf_floc_loc_1811 = soa_field_3_2507 + 8;
            GibCursor jumpf_floc_loc_1812 = soa_field_4_2508 + 8;
            GibCursor jumpf_floc_loc_1813 = soa_field_5_2509 + 8;
            GibCursor loc_1397 = jumpf_dloc_1807 + 0;
            GibCursor loc_1396 = jumpf_floc_loc_1808 + 0;
            GibCursor cursor_ptr_2518[7] = {jumpf_dloc_1807,
                                            jumpf_floc_loc_1808,
                                            jumpf_floc_loc_1809,
                                            jumpf_floc_loc_1810,
                                            jumpf_floc_loc_1811,
                                            jumpf_floc_loc_1812,
                                            jumpf_floc_loc_1813};
            GibCursor loc_IntTy_1208 = cursor_ptr_2499[2];
            GibCursor new_floc_loc_1427 = loc_IntTy_1208 + 8;
            GibCursor loc_1206 = cursor_ptr_2499[0];
            GibCursor new_dloc_1425 = loc_1206 + 1;
            GibCursor loc_IntTy_1210 = cursor_ptr_2499[4];
            GibCursor new_floc_loc_1429 = loc_IntTy_1210 + 8;
            GibCursor loc_IntTy_1212 = cursor_ptr_2499[6];
            GibCursor new_floc_loc_1431 = loc_IntTy_1212 + 8;
            GibCursor loc_IntTy_1209 = cursor_ptr_2499[3];
            GibCursor new_floc_loc_1428 = loc_IntTy_1209 + 8;
            GibCursor loc_IntTy_1207 = cursor_ptr_2499[1];
            GibCursor new_floc_loc_1426 = loc_IntTy_1207 + 8;
            GibCursor loc_IntTy_1211 = cursor_ptr_2499[5];
            GibCursor new_floc_loc_1430 = loc_IntTy_1211 + 8;
            GibCursor cursor_ptr_2519[7] = {new_dloc_1425, new_floc_loc_1426,
                                            new_floc_loc_1427,
                                            new_floc_loc_1428,
                                            new_floc_loc_1429,
                                            new_floc_loc_1430,
                                            new_floc_loc_1431};
            
            *(GibPackedTag *) loc_1206 = 0;
            
            GibCursor writetag_2529 = loc_1206 + 1;
            GibCursor after_tag_2530 = loc_1206 + 1;
            
            *(GibInt *) loc_IntTy_1207 = tmpval_3667;
            
            GibCursor writecur_2534 = loc_IntTy_1207 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1208 = tmpval_3669;
            
            GibCursor writecur_2536 = loc_IntTy_1208 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1209 = tmpval_3671;
            
            GibCursor writecur_2538 = loc_IntTy_1209 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1210 = tmpval_3673;
            
            GibCursor writecur_2540 = loc_IntTy_1210 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1211 = tmpval_3675;
            
            GibCursor writecur_2542 = loc_IntTy_1211 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1212 = tmpval_3677;
            
            GibCursor writecur_2544 = loc_IntTy_1212 + sizeof(GibInt);
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            tmp_struct_0 =
             _copy_without_ptrs_ListB(cursor_ptr_2498, cursor_ptr_2497, cursor_ptr_2519, cursor_ptr_2501);
            GibCursor pvrtmp_3679[7];
            
            memcpy(pvrtmp_3679, tmp_struct_0.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3680[7];
            
            memcpy(pvrtmp_3680, tmp_struct_0.field1, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3681[7];
            
            memcpy(pvrtmp_3681, tmp_struct_0.field2, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3682[7];
            
            memcpy(pvrtmp_3682, tmp_struct_0.field3, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3683[7];
            
            memcpy(pvrtmp_3683, tmp_struct_0.field4, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_1;
            
            memcpy(return_1.field0, pvrtmp_3679, sizeof(GibCursor [7]));
            memcpy(return_1.field1, pvrtmp_3680, sizeof(GibCursor [7]));
            memcpy(return_1.field2, pvrtmp_3681, sizeof(GibCursor [7]));
            memcpy(return_1.field3, cursor_ptr_2499, sizeof(GibCursor [7]));
            memcpy(return_1.field4, pvrtmp_3683, sizeof(GibCursor [7]));
            return return_1;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_2550 = arg_191_249_424[1];
            GibCursor soa_field_1_2551 = arg_191_249_424[2];
            GibCursor soa_field_2_2552 = arg_191_249_424[3];
            GibCursor soa_field_3_2553 = arg_191_249_424[4];
            GibCursor soa_field_4_2554 = arg_191_249_424[5];
            GibCursor soa_field_5_2555 = arg_191_249_424[6];
            GibCursor loc_1199 = arg_191_249_424[0];
            GibCursor jump_dloc_1822 = loc_1199 + 1;
            GibCursor loc_IntTy_1200 = arg_191_249_424[1];
            GibCursor jump_floc_loc_1823 = loc_IntTy_1200 + 0;
            GibCursor loc_IntTy_1201 = arg_191_249_424[2];
            GibCursor jump_floc_loc_1824 = loc_IntTy_1201 + 0;
            GibCursor loc_IntTy_1202 = arg_191_249_424[3];
            GibCursor jump_floc_loc_1825 = loc_IntTy_1202 + 0;
            GibCursor loc_IntTy_1203 = arg_191_249_424[4];
            GibCursor jump_floc_loc_1826 = loc_IntTy_1203 + 0;
            GibCursor loc_IntTy_1204 = arg_191_249_424[5];
            GibCursor jump_floc_loc_1827 = loc_IntTy_1204 + 0;
            GibCursor loc_IntTy_1205 = arg_191_249_424[6];
            GibCursor jump_floc_loc_1828 = loc_IntTy_1205 + 0;
            GibCursor cursor_ptr_2557[7] = {jump_dloc_1822, jump_floc_loc_1823,
                                            jump_floc_loc_1824,
                                            jump_floc_loc_1825,
                                            jump_floc_loc_1826,
                                            jump_floc_loc_1827,
                                            jump_floc_loc_1828};
            GibCursor loc_IntTy_1208 = cursor_ptr_2499[2];
            GibCursor new_floc_loc_1427 = loc_IntTy_1208 + 8;
            GibCursor loc_1206 = cursor_ptr_2499[0];
            GibCursor new_dloc_1425 = loc_1206 + 1;
            GibCursor loc_IntTy_1210 = cursor_ptr_2499[4];
            GibCursor new_floc_loc_1429 = loc_IntTy_1210 + 8;
            GibCursor loc_IntTy_1212 = cursor_ptr_2499[6];
            GibCursor new_floc_loc_1431 = loc_IntTy_1212 + 8;
            GibCursor loc_IntTy_1209 = cursor_ptr_2499[3];
            GibCursor new_floc_loc_1428 = loc_IntTy_1209 + 8;
            GibCursor loc_IntTy_1207 = cursor_ptr_2499[1];
            GibCursor new_floc_loc_1426 = loc_IntTy_1207 + 8;
            GibCursor loc_IntTy_1211 = cursor_ptr_2499[5];
            GibCursor new_floc_loc_1430 = loc_IntTy_1211 + 8;
            
            *(GibPackedTag *) loc_1206 = 1;
            
            GibCursor writetag_2558 = loc_1206 + 1;
            GibCursor after_tag_2559 = loc_1206 + 1;
            GibCursor aft_soa_loc_2563[7] = {after_tag_2559, loc_IntTy_1207,
                                             loc_IntTy_1208, loc_IntTy_1209,
                                             loc_IntTy_1210, loc_IntTy_1211,
                                             loc_IntTy_1212};
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_2;
            
            memcpy(return_2.field0, cursor_ptr_2498, sizeof(GibCursor [7]));
            memcpy(return_2.field1, cursor_ptr_2497, sizeof(GibCursor [7]));
            memcpy(return_2.field2, cursor_ptr_2557, sizeof(GibCursor [7]));
            memcpy(return_2.field3, cursor_ptr_2499, sizeof(GibCursor [7]));
            memcpy(return_2.field4, aft_soa_loc_2563, sizeof(GibCursor [7]));
            return return_2;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_2567 = arg_191_249_424[1];
            GibCursor soa_field_1_2568 = arg_191_249_424[2];
            GibCursor soa_field_2_2569 = arg_191_249_424[3];
            GibCursor soa_field_3_2570 = arg_191_249_424[4];
            GibCursor soa_field_4_2571 = arg_191_249_424[5];
            GibCursor soa_field_5_2572 = arg_191_249_424[6];
            uintptr_t tagged_tmpcur_11 = *(uintptr_t *) tmpcur_3666;
            GibCursor tmpcur_3696 = GIB_UNTAG(tagged_tmpcur_11);
            GibCursor tmpaftercur_3697 = tmpcur_3666 + 8;
            uint16_t tmptag_3698 = GIB_GET_TAG(tagged_tmpcur_11);
            GibCursor end_from_tagged_dcon_redir_2597 = tmpcur_3696 +
                      tmptag_3698;
            GibCursor field_nxt_2590 = soa_field_0_2567 + 1;
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) field_nxt_2590;
            GibCursor tmpcur_3699 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_3700 = field_nxt_2590 + 8;
            uint16_t tmptag_3701 = GIB_GET_TAG(tagged_tmpcur_10);
            GibCursor end_from_tagged_fld_redir_2598 = tmpcur_3699 +
                      tmptag_3701;
            GibCursor field_nxt_2591 = soa_field_1_2568 + 1;
            uintptr_t tagged_tmpcur_9 = *(uintptr_t *) field_nxt_2591;
            GibCursor tmpcur_3702 = GIB_UNTAG(tagged_tmpcur_9);
            GibCursor tmpaftercur_3703 = field_nxt_2591 + 8;
            uint16_t tmptag_3704 = GIB_GET_TAG(tagged_tmpcur_9);
            GibCursor end_from_tagged_fld_redir_2599 = tmpcur_3702 +
                      tmptag_3704;
            GibCursor field_nxt_2592 = soa_field_2_2569 + 1;
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) field_nxt_2592;
            GibCursor tmpcur_3705 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_3706 = field_nxt_2592 + 8;
            uint16_t tmptag_3707 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_fld_redir_2600 = tmpcur_3705 +
                      tmptag_3707;
            GibCursor field_nxt_2593 = soa_field_3_2570 + 1;
            uintptr_t tagged_tmpcur_7 = *(uintptr_t *) field_nxt_2593;
            GibCursor tmpcur_3708 = GIB_UNTAG(tagged_tmpcur_7);
            GibCursor tmpaftercur_3709 = field_nxt_2593 + 8;
            uint16_t tmptag_3710 = GIB_GET_TAG(tagged_tmpcur_7);
            GibCursor end_from_tagged_fld_redir_2601 = tmpcur_3708 +
                      tmptag_3710;
            GibCursor field_nxt_2594 = soa_field_4_2571 + 1;
            uintptr_t tagged_tmpcur_6 = *(uintptr_t *) field_nxt_2594;
            GibCursor tmpcur_3711 = GIB_UNTAG(tagged_tmpcur_6);
            GibCursor tmpaftercur_3712 = field_nxt_2594 + 8;
            uint16_t tmptag_3713 = GIB_GET_TAG(tagged_tmpcur_6);
            GibCursor end_from_tagged_fld_redir_2602 = tmpcur_3711 +
                      tmptag_3713;
            GibCursor field_nxt_2595 = soa_field_5_2572 + 1;
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) field_nxt_2595;
            GibCursor tmpcur_3714 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_3715 = field_nxt_2595 + 8;
            uint16_t tmptag_3716 = GIB_GET_TAG(tagged_tmpcur_5);
            GibCursor end_from_tagged_fld_redir_2603 = tmpcur_3714 +
                      tmptag_3716;
            GibCursor indr_1995[7] = {tmpcur_3696, tmpcur_3699, tmpcur_3702,
                                      tmpcur_3705, tmpcur_3708, tmpcur_3711,
                                      tmpcur_3714};
            GibCursor loc_1199 = arg_191_249_424[0];
            GibCursor jump_dloc_2003 = loc_1199 + 9;
            GibCursor loc_IntTy_1205 = arg_191_249_424[6];
            GibCursor loc_IntTy_1204 = arg_191_249_424[5];
            GibCursor loc_IntTy_1203 = arg_191_249_424[4];
            GibCursor loc_IntTy_1202 = arg_191_249_424[3];
            GibCursor loc_IntTy_1201 = arg_191_249_424[2];
            GibCursor loc_IntTy_1200 = arg_191_249_424[1];
            GibCursor aft_indir_loc_2019 = loc_IntTy_1200 + 9;
            GibCursor aft_indir_loc_2020 = loc_IntTy_1201 + 9;
            GibCursor aft_indir_loc_2021 = loc_IntTy_1202 + 9;
            GibCursor aft_indir_loc_2022 = loc_IntTy_1203 + 9;
            GibCursor aft_indir_loc_2023 = loc_IntTy_1204 + 9;
            GibCursor aft_indir_loc_2024 = loc_IntTy_1205 + 9;
            GibCursor cursor_ptr_2604[7] = {jump_dloc_2003, aft_indir_loc_2019,
                                            aft_indir_loc_2020,
                                            aft_indir_loc_2021,
                                            aft_indir_loc_2022,
                                            aft_indir_loc_2023,
                                            aft_indir_loc_2024};
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            tmp_struct_3 =
             _copy_without_ptrs_ListB(indr_1995, cursor_ptr_2497, cursor_ptr_2499, indr_1995);
            GibCursor pvrtmp_3717[7];
            
            memcpy(pvrtmp_3717, tmp_struct_3.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3718[7];
            
            memcpy(pvrtmp_3718, tmp_struct_3.field1, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3719[7];
            
            memcpy(pvrtmp_3719, tmp_struct_3.field2, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3720[7];
            
            memcpy(pvrtmp_3720, tmp_struct_3.field3, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3721[7];
            
            memcpy(pvrtmp_3721, tmp_struct_3.field4, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_4;
            
            memcpy(return_4.field0, cursor_ptr_2498, sizeof(GibCursor [7]));
            memcpy(return_4.field1, pvrtmp_3718, sizeof(GibCursor [7]));
            memcpy(return_4.field2, cursor_ptr_2604, sizeof(GibCursor [7]));
            memcpy(return_4.field3, pvrtmp_3720, sizeof(GibCursor [7]));
            memcpy(return_4.field4, pvrtmp_3721, sizeof(GibCursor [7]));
            return return_4;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_2615 = arg_191_249_424[1];
            GibCursor soa_field_1_2616 = arg_191_249_424[2];
            GibCursor soa_field_2_2617 = arg_191_249_424[3];
            GibCursor soa_field_3_2618 = arg_191_249_424[4];
            GibCursor soa_field_4_2619 = arg_191_249_424[5];
            GibCursor soa_field_5_2620 = arg_191_249_424[6];
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) tmpcur_3666;
            GibCursor tmpcur_3728 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_3729 = tmpcur_3666 + 8;
            uint16_t tmptag_3730 = GIB_GET_TAG(tagged_tmpcur_20);
            GibCursor end_from_tagged_dcon_redir_2636 = tmpcur_3728 +
                      tmptag_3730;
            GibCursor field_nxt_2630 = soa_field_0_2615 + 1;
            uintptr_t tagged_tmpcur_19 = *(uintptr_t *) field_nxt_2630;
            GibCursor tmpcur_3731 = GIB_UNTAG(tagged_tmpcur_19);
            GibCursor tmpaftercur_3732 = field_nxt_2630 + 8;
            uint16_t tmptag_3733 = GIB_GET_TAG(tagged_tmpcur_19);
            GibCursor end_from_tagged_fld_redir_2637 = tmpcur_3731 +
                      tmptag_3733;
            GibCursor field_nxt_2631 = soa_field_1_2616 + 1;
            uintptr_t tagged_tmpcur_18 = *(uintptr_t *) field_nxt_2631;
            GibCursor tmpcur_3734 = GIB_UNTAG(tagged_tmpcur_18);
            GibCursor tmpaftercur_3735 = field_nxt_2631 + 8;
            uint16_t tmptag_3736 = GIB_GET_TAG(tagged_tmpcur_18);
            GibCursor end_from_tagged_fld_redir_2638 = tmpcur_3734 +
                      tmptag_3736;
            GibCursor field_nxt_2632 = soa_field_2_2617 + 1;
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) field_nxt_2632;
            GibCursor tmpcur_3737 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_3738 = field_nxt_2632 + 8;
            uint16_t tmptag_3739 = GIB_GET_TAG(tagged_tmpcur_17);
            GibCursor end_from_tagged_fld_redir_2639 = tmpcur_3737 +
                      tmptag_3739;
            GibCursor field_nxt_2633 = soa_field_3_2618 + 1;
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) field_nxt_2633;
            GibCursor tmpcur_3740 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_3741 = field_nxt_2633 + 8;
            uint16_t tmptag_3742 = GIB_GET_TAG(tagged_tmpcur_16);
            GibCursor end_from_tagged_fld_redir_2640 = tmpcur_3740 +
                      tmptag_3742;
            GibCursor field_nxt_2634 = soa_field_4_2619 + 1;
            uintptr_t tagged_tmpcur_15 = *(uintptr_t *) field_nxt_2634;
            GibCursor tmpcur_3743 = GIB_UNTAG(tagged_tmpcur_15);
            GibCursor tmpaftercur_3744 = field_nxt_2634 + 8;
            uint16_t tmptag_3745 = GIB_GET_TAG(tagged_tmpcur_15);
            GibCursor end_from_tagged_fld_redir_2641 = tmpcur_3743 +
                      tmptag_3745;
            GibCursor field_nxt_2635 = soa_field_5_2620 + 1;
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) field_nxt_2635;
            GibCursor tmpcur_3746 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_3747 = field_nxt_2635 + 8;
            uint16_t tmptag_3748 = GIB_GET_TAG(tagged_tmpcur_14);
            GibCursor end_from_tagged_fld_redir_2642 = tmpcur_3746 +
                      tmptag_3748;
            GibCursor indr_1995[7] = {tmpcur_3728, tmpcur_3731, tmpcur_3734,
                                      tmpcur_3737, tmpcur_3740, tmpcur_3743,
                                      tmpcur_3746};
            GibCursor loc_1206 = cursor_ptr_2499[0];
            GibCursor loc_IntTy_1207 = cursor_ptr_2499[1];
            GibCursor loc_IntTy_1208 = cursor_ptr_2499[2];
            GibCursor loc_IntTy_1209 = cursor_ptr_2499[3];
            GibCursor loc_IntTy_1210 = cursor_ptr_2499[4];
            GibCursor loc_IntTy_1211 = cursor_ptr_2499[5];
            GibCursor loc_IntTy_1212 = cursor_ptr_2499[6];
            GibCursor copy_dloc_2025 = loc_1206 + 0;
            GibCursor copy_floc_loc_2031 = loc_IntTy_1212 + 0;
            GibCursor copy_floc_loc_2030 = loc_IntTy_1211 + 0;
            GibCursor copy_floc_loc_2029 = loc_IntTy_1210 + 0;
            GibCursor copy_floc_loc_2028 = loc_IntTy_1209 + 0;
            GibCursor copy_floc_loc_2027 = loc_IntTy_1208 + 0;
            GibCursor copy_floc_loc_2026 = loc_IntTy_1207 + 0;
            GibCursor cursor_ptr_2643[7] = {copy_dloc_2025, copy_floc_loc_2026,
                                            copy_floc_loc_2027,
                                            copy_floc_loc_2028,
                                            copy_floc_loc_2029,
                                            copy_floc_loc_2030,
                                            copy_floc_loc_2031};
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            tmp_struct_12 =
             _copy_without_ptrs_ListB(indr_1995, cursor_ptr_2497, cursor_ptr_2643, indr_1995);
            GibCursor pvrtmp_3749[7];
            
            memcpy(pvrtmp_3749, tmp_struct_12.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3750[7];
            
            memcpy(pvrtmp_3750, tmp_struct_12.field1, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3751[7];
            
            memcpy(pvrtmp_3751, tmp_struct_12.field2, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3752[7];
            
            memcpy(pvrtmp_3752, tmp_struct_12.field3, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_3753[7];
            
            memcpy(pvrtmp_3753, tmp_struct_12.field4, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_13;
            
            memcpy(return_13.field0, pvrtmp_3749, sizeof(GibCursor [7]));
            memcpy(return_13.field1, pvrtmp_3750, sizeof(GibCursor [7]));
            memcpy(return_13.field2, pvrtmp_3751, sizeof(GibCursor [7]));
            memcpy(return_13.field3, pvrtmp_3752, sizeof(GibCursor [7]));
            memcpy(return_13.field4, pvrtmp_3753, sizeof(GibCursor [7]));
            return return_13;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3665");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_ListA(GibCursor end_r_1229,
                                       GibCursor arg_98_264_439)
{
    GibPackedTag tmpval_3761 = *(GibPackedTag *) arg_98_264_439;
    GibCursor tmpcur_3762 = arg_98_264_439 + 1;
    
    
  switch_3777:
    ;
    switch (tmpval_3761) {
        
      case 0:
        {
            GibInt tmpval_3763 = *(GibInt *) tmpcur_3762;
            GibCursor tmpcur_3764 = tmpcur_3762 + sizeof(GibInt);
            GibCursor jump_1830 = tmpcur_3762 + 8;
            GibCursorGibCursorProd tmp_struct_21 =
                                    _traverse_ListA(end_r_1229, tmpcur_3764);
            GibCursor pvrtmp_3765 = tmp_struct_21.field0;
            GibCursor pvrtmp_3766 = tmp_struct_21.field1;
            GibCursorGibCursorProd return_22;
            
            return_22.field0 = pvrtmp_3765;
            return_22.field1 = pvrtmp_3766;
            return return_22;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1833 = arg_98_264_439 + 1;
            GibCursorGibCursorProd return_23;
            
            return_23.field0 = end_r_1229;
            return_23.field1 = jump_loc_1833;
            return return_23;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_26 = *(uintptr_t *) tmpcur_3762;
            GibCursor tmpcur_3767 = GIB_UNTAG(tagged_tmpcur_26);
            GibCursor tmpaftercur_3768 = tmpcur_3762 + 8;
            uint16_t tmptag_3769 = GIB_GET_TAG(tagged_tmpcur_26);
            GibCursor end_from_tagged_indr_2032 = tmpcur_3767 + tmptag_3769;
            GibCursor jump_loc_2034 = tmpcur_3762 + 8;
            GibCursorGibCursorProd tmp_struct_24 =
                                    _traverse_ListA(tmpcur_3767, tmpcur_3767);
            GibCursor pvrtmp_3770 = tmp_struct_24.field0;
            GibCursor pvrtmp_3771 = tmp_struct_24.field1;
            GibCursorGibCursorProd return_25;
            
            return_25.field0 = end_r_1229;
            return_25.field1 = jump_loc_2034;
            return return_25;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_3762;
            GibCursor tmpcur_3772 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_3773 = tmpcur_3762 + 8;
            uint16_t tmptag_3774 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_2032 = tmpcur_3772 + tmptag_3774;
            GibCursorGibCursorProd tmp_struct_27 =
                                    _traverse_ListA(tmpcur_3772, tmpcur_3772);
            GibCursor pvrtmp_3775 = tmp_struct_27.field0;
            GibCursor pvrtmp_3776 = tmp_struct_27.field1;
            GibCursorGibCursorProd return_28;
            
            return_28.field0 = pvrtmp_3775;
            return_28.field1 = pvrtmp_3776;
            return return_28;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3761");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_List(GibCursor end_r_1232,
                                   GibCursor arg_153_268_443)
{
    GibPackedTag tmpval_3778 = *(GibPackedTag *) arg_153_268_443;
    GibCursor tmpcur_3779 = arg_153_268_443 + 1;
    
    
  switch_3802:
    ;
    switch (tmpval_3778) {
        
      case 0:
        {
            GibInt tmpval_3780 = *(GibInt *) tmpcur_3779;
            GibCursor tmpcur_3781 = tmpcur_3779 + sizeof(GibInt);
            GibInt tmpval_3782 = *(GibInt *) tmpcur_3781;
            GibCursor tmpcur_3783 = tmpcur_3781 + sizeof(GibInt);
            GibInt tmpval_3784 = *(GibInt *) tmpcur_3783;
            GibCursor tmpcur_3785 = tmpcur_3783 + sizeof(GibInt);
            GibInt tmpval_3786 = *(GibInt *) tmpcur_3785;
            GibCursor tmpcur_3787 = tmpcur_3785 + sizeof(GibInt);
            GibCursor jump_1838 = tmpcur_3785 + 8;
            GibCursor jump_1837 = tmpcur_3783 + 8;
            GibCursor jump_1836 = tmpcur_3781 + 8;
            GibCursor jump_1835 = tmpcur_3779 + 8;
            unsigned char wildcard_166_275_450 = gib_print_symbol(3644);
            unsigned char wildcard_173_276_451 = gib_print_symbol(3647);
            unsigned char y_160_277_452 = printf("%ld", tmpval_3780);
            unsigned char wildcard_172_278_453 = gib_print_symbol(3647);
            unsigned char y_161_279_454 = printf("%ld", tmpval_3782);
            unsigned char wildcard_171_280_455 = gib_print_symbol(3647);
            unsigned char y_162_281_456 = printf("%ld", tmpval_3784);
            unsigned char wildcard_170_282_457 = gib_print_symbol(3647);
            unsigned char y_163_283_458 = printf("%ld", tmpval_3786);
            unsigned char wildcard_169_284_459 = gib_print_symbol(3647);
            GibCursorGibCursorProd tmp_struct_30 =
                                    _print_ListA(end_r_1232, tmpcur_3787);
            GibCursor pvrtmp_3788 = tmp_struct_30.field0;
            GibCursor pvrtmp_3789 = tmp_struct_30.field1;
            unsigned char wildcard_168_286_461 = gib_print_symbol(3647);
            GibCursorGibCursorProd tmp_struct_31 =
                                    _print_List(pvrtmp_3788, pvrtmp_3789);
            GibCursor pvrtmp_3790 = tmp_struct_31.field0;
            GibCursor pvrtmp_3791 = tmp_struct_31.field1;
            unsigned char wildcard_167_288_463 = gib_print_symbol(3638);
            GibCursorGibCursorProd return_32;
            
            return_32.field0 = pvrtmp_3790;
            return_32.field1 = pvrtmp_3791;
            return return_32;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1842 = arg_153_268_443 + 1;
            unsigned char wildcard_174_289_464 = gib_print_symbol(3641);
            unsigned char wildcard_175_290_465 = gib_print_symbol(3638);
            GibCursorGibCursorProd return_33;
            
            return_33.field0 = end_r_1232;
            return_33.field1 = jump_loc_1842;
            return return_33;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_36 = *(uintptr_t *) tmpcur_3779;
            GibCursor tmpcur_3792 = GIB_UNTAG(tagged_tmpcur_36);
            GibCursor tmpaftercur_3793 = tmpcur_3779 + 8;
            uint16_t tmptag_3794 = GIB_GET_TAG(tagged_tmpcur_36);
            GibCursor end_from_tagged_indr_2038 = tmpcur_3792 + tmptag_3794;
            GibCursor jump_loc_2040 = tmpcur_3779 + 8;
            unsigned char wildcard_2043 = gib_print_symbol(3646);
            GibCursorGibCursorProd tmp_struct_34 =
                                    _print_List(tmpcur_3792, tmpcur_3792);
            GibCursor pvrtmp_3795 = tmp_struct_34.field0;
            GibCursor pvrtmp_3796 = tmp_struct_34.field1;
            GibCursorGibCursorProd return_35;
            
            return_35.field0 = end_r_1232;
            return_35.field1 = jump_loc_2040;
            return return_35;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_39 = *(uintptr_t *) tmpcur_3779;
            GibCursor tmpcur_3797 = GIB_UNTAG(tagged_tmpcur_39);
            GibCursor tmpaftercur_3798 = tmpcur_3779 + 8;
            uint16_t tmptag_3799 = GIB_GET_TAG(tagged_tmpcur_39);
            GibCursor end_from_tagged_indr_2038 = tmpcur_3797 + tmptag_3799;
            unsigned char wildcard_2043 = gib_print_symbol(3645);
            GibCursorGibCursorProd tmp_struct_37 =
                                    _print_List(tmpcur_3797, tmpcur_3797);
            GibCursor pvrtmp_3800 = tmp_struct_37.field0;
            GibCursor pvrtmp_3801 = tmp_struct_37.field1;
            GibCursorGibCursorProd return_38;
            
            return_38.field0 = pvrtmp_3800;
            return_38.field1 = pvrtmp_3801;
            return return_38;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3778");
            exit(1);
        }
    }
}
GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod mkListB(GibCursor cursor_ptr_2686[7],
                                                    GibCursor cursor_ptr_2687[7],
                                                    GibInt len_34_291_466)
{
    GibCursor end_r_1245 = cursor_ptr_2686[5];
    GibCursor end_r_1242 = cursor_ptr_2686[2];
    GibCursor end_r_1246 = cursor_ptr_2686[6];
    GibCursor end_r_1243 = cursor_ptr_2686[3];
    GibCursor end_r_1241 = cursor_ptr_2686[1];
    GibCursor end_r_1240 = cursor_ptr_2686[0];
    GibCursor end_r_1244 = cursor_ptr_2686[4];
    GibCursor loc_IntTy_1235 = cursor_ptr_2687[2];
    GibCursor loc_IntTy_1238 = cursor_ptr_2687[5];
    GibCursor loc_IntTy_1236 = cursor_ptr_2687[3];
    GibCursor loc_IntTy_1234 = cursor_ptr_2687[1];
    GibCursor loc_IntTy_1239 = cursor_ptr_2687[6];
    GibCursor loc_1233 = cursor_ptr_2687[0];
    GibCursor loc_IntTy_1237 = cursor_ptr_2687[4];
    
    if (loc_IntTy_1239 + 17 > end_r_1246 || (loc_IntTy_1238 + 17 > end_r_1245 ||
                                             (loc_IntTy_1237 + 17 >
                                              end_r_1244 || (loc_IntTy_1236 +
                                                             17 > end_r_1243 ||
                                                             (loc_IntTy_1235 +
                                                              17 > end_r_1242 ||
                                                              (loc_IntTy_1234 +
                                                               17 >
                                                               end_r_1241 ||
                                                               loc_1233 + 66 >
                                                               end_r_1240)))))) {
        gib_grow_region(&loc_IntTy_1239, &end_r_1246);
        gib_grow_region(&loc_IntTy_1238, &end_r_1245);
        gib_grow_region(&loc_IntTy_1237, &end_r_1244);
        gib_grow_region(&loc_IntTy_1236, &end_r_1243);
        gib_grow_region(&loc_IntTy_1235, &end_r_1242);
        gib_grow_region(&loc_IntTy_1234, &end_r_1241);
        gib_grow_region(&loc_1233, &end_r_1240);
    }
    
    GibCursor overwrite_reg_2688[7] = {end_r_1240, end_r_1241, end_r_1242,
                                       end_r_1243, end_r_1244, end_r_1245,
                                       end_r_1246};
    GibBool fltIf_419_467 = len_34_291_466 <= 0;
    
    if (fltIf_419_467) {
        GibCursor new_floc_loc_1499 = loc_IntTy_1236 + 8;
        GibCursor new_floc_loc_1500 = loc_IntTy_1237 + 8;
        GibCursor new_dloc_1496 = loc_1233 + 1;
        GibCursor new_floc_loc_1502 = loc_IntTy_1239 + 8;
        GibCursor new_floc_loc_1497 = loc_IntTy_1234 + 8;
        GibCursor new_floc_loc_1498 = loc_IntTy_1235 + 8;
        GibCursor new_floc_loc_1501 = loc_IntTy_1238 + 8;
        
        *(GibPackedTag *) loc_1233 = 1;
        
        GibCursor writetag_2689 = loc_1233 + 1;
        GibCursor after_tag_2690 = loc_1233 + 1;
        GibCursor aft_soa_loc_2694[7] = {after_tag_2690, loc_IntTy_1234,
                                         loc_IntTy_1235, loc_IntTy_1236,
                                         loc_IntTy_1237, loc_IntTy_1238,
                                         loc_IntTy_1239};
        GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod return_40;
        
        memcpy(return_40.field0, overwrite_reg_2688, sizeof(GibCursor [7]));
        memcpy(return_40.field1, cursor_ptr_2687, sizeof(GibCursor [7]));
        memcpy(return_40.field2, aft_soa_loc_2694, sizeof(GibCursor [7]));
        return return_40;
    } else {
        GibInt fltAppE_420_468 = len_34_291_466 - 1;
        GibCursor new_floc_loc_1499 = loc_IntTy_1236 + 8;
        GibCursor new_floc_loc_1500 = loc_IntTy_1237 + 8;
        GibCursor new_dloc_1496 = loc_1233 + 1;
        GibCursor new_floc_loc_1502 = loc_IntTy_1239 + 8;
        GibCursor new_floc_loc_1497 = loc_IntTy_1234 + 8;
        GibCursor new_floc_loc_1498 = loc_IntTy_1235 + 8;
        GibCursor new_floc_loc_1501 = loc_IntTy_1238 + 8;
        GibCursor cursor_ptr_2697[7] = {new_dloc_1496, new_floc_loc_1497,
                                        new_floc_loc_1498, new_floc_loc_1499,
                                        new_floc_loc_1500, new_floc_loc_1501,
                                        new_floc_loc_1502};
        
        *(GibPackedTag *) loc_1233 = 0;
        
        GibCursor writetag_2702 = loc_1233 + 1;
        GibCursor after_tag_2703 = loc_1233 + 1;
        
        *(GibInt *) loc_IntTy_1234 = len_34_291_466;
        
        GibCursor writecur_2707 = loc_IntTy_1234 + sizeof(GibInt);
        
        *(GibInt *) loc_IntTy_1234 = len_34_291_466;
        
        GibCursor writecur_2709 = loc_IntTy_1234 + sizeof(GibInt);
        
        *(GibInt *) loc_IntTy_1234 = len_34_291_466;
        
        GibCursor writecur_2711 = loc_IntTy_1234 + sizeof(GibInt);
        
        *(GibInt *) loc_IntTy_1234 = len_34_291_466;
        
        GibCursor writecur_2713 = loc_IntTy_1234 + sizeof(GibInt);
        
        *(GibInt *) loc_IntTy_1234 = len_34_291_466;
        
        GibCursor writecur_2715 = loc_IntTy_1234 + sizeof(GibInt);
        
        *(GibInt *) loc_IntTy_1234 = len_34_291_466;
        
        GibCursor writecur_2717 = loc_IntTy_1234 + sizeof(GibInt);
        GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod tmp_struct_41 =
                                                     mkListB(overwrite_reg_2688, cursor_ptr_2697, fltAppE_420_468);
        GibCursor pvrtmp_3807[7];
        
        memcpy(pvrtmp_3807, tmp_struct_41.field0, sizeof(GibCursor [7]));
        
        GibCursor pvrtmp_3808[7];
        
        memcpy(pvrtmp_3808, tmp_struct_41.field1, sizeof(GibCursor [7]));
        
        GibCursor pvrtmp_3809[7];
        
        memcpy(pvrtmp_3809, tmp_struct_41.field2, sizeof(GibCursor [7]));
        
        GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod return_42;
        
        memcpy(return_42.field0, pvrtmp_3807, sizeof(GibCursor [7]));
        memcpy(return_42.field1, cursor_ptr_2687, sizeof(GibCursor [7]));
        memcpy(return_42.field2, pvrtmp_3809, sizeof(GibCursor [7]));
        return return_42;
    }
}
GibCursorGibCursorProd _traverse_List(GibCursor end_r_1249,
                                      GibCursor arg_140_293_470)
{
    GibPackedTag tmpval_3818 = *(GibPackedTag *) arg_140_293_470;
    GibCursor tmpcur_3819 = arg_140_293_470 + 1;
    
    
  switch_3842:
    ;
    switch (tmpval_3818) {
        
      case 0:
        {
            GibInt tmpval_3820 = *(GibInt *) tmpcur_3819;
            GibCursor tmpcur_3821 = tmpcur_3819 + sizeof(GibInt);
            GibInt tmpval_3822 = *(GibInt *) tmpcur_3821;
            GibCursor tmpcur_3823 = tmpcur_3821 + sizeof(GibInt);
            GibInt tmpval_3824 = *(GibInt *) tmpcur_3823;
            GibCursor tmpcur_3825 = tmpcur_3823 + sizeof(GibInt);
            GibInt tmpval_3826 = *(GibInt *) tmpcur_3825;
            GibCursor tmpcur_3827 = tmpcur_3825 + sizeof(GibInt);
            GibCursor jump_1849 = tmpcur_3825 + 8;
            GibCursor jump_1848 = tmpcur_3823 + 8;
            GibCursor jump_1847 = tmpcur_3821 + 8;
            GibCursor jump_1846 = tmpcur_3819 + 8;
            GibCursorGibCursorProd tmp_struct_43 =
                                    _traverse_ListA(end_r_1249, tmpcur_3827);
            GibCursor pvrtmp_3828 = tmp_struct_43.field0;
            GibCursor pvrtmp_3829 = tmp_struct_43.field1;
            GibCursorGibCursorProd tmp_struct_44 =
                                    _traverse_List(pvrtmp_3828, pvrtmp_3829);
            GibCursor pvrtmp_3830 = tmp_struct_44.field0;
            GibCursor pvrtmp_3831 = tmp_struct_44.field1;
            GibCursorGibCursorProd return_45;
            
            return_45.field0 = pvrtmp_3830;
            return_45.field1 = pvrtmp_3831;
            return return_45;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1853 = arg_140_293_470 + 1;
            GibCursorGibCursorProd return_46;
            
            return_46.field0 = end_r_1249;
            return_46.field1 = jump_loc_1853;
            return return_46;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_49 = *(uintptr_t *) tmpcur_3819;
            GibCursor tmpcur_3832 = GIB_UNTAG(tagged_tmpcur_49);
            GibCursor tmpaftercur_3833 = tmpcur_3819 + 8;
            uint16_t tmptag_3834 = GIB_GET_TAG(tagged_tmpcur_49);
            GibCursor end_from_tagged_indr_2044 = tmpcur_3832 + tmptag_3834;
            GibCursor jump_loc_2046 = tmpcur_3819 + 8;
            GibCursorGibCursorProd tmp_struct_47 =
                                    _traverse_List(tmpcur_3832, tmpcur_3832);
            GibCursor pvrtmp_3835 = tmp_struct_47.field0;
            GibCursor pvrtmp_3836 = tmp_struct_47.field1;
            GibCursorGibCursorProd return_48;
            
            return_48.field0 = end_r_1249;
            return_48.field1 = jump_loc_2046;
            return return_48;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) tmpcur_3819;
            GibCursor tmpcur_3837 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_3838 = tmpcur_3819 + 8;
            uint16_t tmptag_3839 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_indr_2044 = tmpcur_3837 + tmptag_3839;
            GibCursorGibCursorProd tmp_struct_50 =
                                    _traverse_List(tmpcur_3837, tmpcur_3837);
            GibCursor pvrtmp_3840 = tmp_struct_50.field0;
            GibCursor pvrtmp_3841 = tmp_struct_50.field1;
            GibCursorGibCursorProd return_51;
            
            return_51.field0 = pvrtmp_3840;
            return_51.field1 = pvrtmp_3841;
            return return_51;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3818");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_ListA(GibCursor end_r_1253,
                                                                           GibCursor end_r_1255,
                                                                           GibCursor loc_1251,
                                                                           GibCursor arg_93_302_479)
{
    GibPackedTag tmpval_3843 = *(GibPackedTag *) arg_93_302_479;
    GibCursor tmpcur_3844 = arg_93_302_479 + 1;
    
    
  switch_3892:
    ;
    switch (tmpval_3843) {
        
      case 0:
        {
            GibInt tmpval_3845 = *(GibInt *) tmpcur_3844;
            GibCursor tmpcur_3846 = tmpcur_3844 + sizeof(GibInt);
            GibCursor jump_1855 = tmpcur_3844 + 8;
            GibCursor loc_1541 = loc_1251 + 1;
            GibCursor loc_1542 = loc_1541 + 8;
            
            *(GibPackedTag *) loc_1251 = 0;
            
            GibCursor writetag_2747 = loc_1251 + 1;
            GibCursor after_tag_2748 = loc_1251 + 1;
            
            *(GibInt *) after_tag_2748 = tmpval_3845;
            
            GibCursor writecur_2752 = after_tag_2748 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_53 =
                                                               _copy_without_ptrs_ListA(end_r_1253, end_r_1255, loc_1542, tmpcur_3846);
            GibCursor pvrtmp_3847 = tmp_struct_53.field0;
            GibCursor pvrtmp_3848 = tmp_struct_53.field1;
            GibCursor pvrtmp_3849 = tmp_struct_53.field2;
            GibCursor pvrtmp_3850 = tmp_struct_53.field3;
            GibCursor pvrtmp_3851 = tmp_struct_53.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_54;
            
            return_54.field0 = pvrtmp_3847;
            return_54.field1 = pvrtmp_3848;
            return_54.field2 = pvrtmp_3849;
            return_54.field3 = loc_1251;
            return_54.field4 = pvrtmp_3851;
            return return_54;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1858 = arg_93_302_479 + 1;
            
            *(GibPackedTag *) loc_1251 = 1;
            
            GibCursor writetag_2757 = loc_1251 + 1;
            GibCursor after_tag_2758 = loc_1251 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_55;
            
            return_55.field0 = end_r_1253;
            return_55.field1 = end_r_1255;
            return_55.field2 = jump_loc_1858;
            return_55.field3 = loc_1251;
            return_55.field4 = after_tag_2758;
            return return_55;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_58 = *(uintptr_t *) tmpcur_3844;
            GibCursor tmpcur_3864 = GIB_UNTAG(tagged_tmpcur_58);
            GibCursor tmpaftercur_3865 = tmpcur_3844 + 8;
            uint16_t tmptag_3866 = GIB_GET_TAG(tagged_tmpcur_58);
            GibCursor end_from_tagged_indr_2050 = tmpcur_3864 + tmptag_3866;
            GibCursor jump_loc_2052 = tmpcur_3844 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_56 =
                                                               _copy_without_ptrs_ListA(tmpcur_3864, end_r_1255, loc_1251, tmpcur_3864);
            GibCursor pvrtmp_3867 = tmp_struct_56.field0;
            GibCursor pvrtmp_3868 = tmp_struct_56.field1;
            GibCursor pvrtmp_3869 = tmp_struct_56.field2;
            GibCursor pvrtmp_3870 = tmp_struct_56.field3;
            GibCursor pvrtmp_3871 = tmp_struct_56.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_57;
            
            return_57.field0 = end_r_1253;
            return_57.field1 = pvrtmp_3868;
            return_57.field2 = jump_loc_2052;
            return_57.field3 = pvrtmp_3870;
            return_57.field4 = pvrtmp_3871;
            return return_57;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_61 = *(uintptr_t *) tmpcur_3844;
            GibCursor tmpcur_3878 = GIB_UNTAG(tagged_tmpcur_61);
            GibCursor tmpaftercur_3879 = tmpcur_3844 + 8;
            uint16_t tmptag_3880 = GIB_GET_TAG(tagged_tmpcur_61);
            GibCursor end_from_tagged_indr_2050 = tmpcur_3878 + tmptag_3880;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_59 =
                                                               _copy_without_ptrs_ListA(tmpcur_3878, end_r_1255, loc_1251, tmpcur_3878);
            GibCursor pvrtmp_3881 = tmp_struct_59.field0;
            GibCursor pvrtmp_3882 = tmp_struct_59.field1;
            GibCursor pvrtmp_3883 = tmp_struct_59.field2;
            GibCursor pvrtmp_3884 = tmp_struct_59.field3;
            GibCursor pvrtmp_3885 = tmp_struct_59.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_60;
            
            return_60.field0 = pvrtmp_3881;
            return_60.field1 = pvrtmp_3882;
            return_60.field2 = pvrtmp_3883;
            return_60.field3 = pvrtmp_3884;
            return_60.field4 = pvrtmp_3885;
            return return_60;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3843");
            exit(1);
        }
    }
}
void reduceB(GibCursor cursor_ptr_2775[7],
             GibCursor lst_36_307_484[7],
             GibInt *Res)
{
    // GibCursor *end_r_1263 = &cursor_ptr_2775[0];
    // GibCursor *end_r_1264 = &cursor_ptr_2775[1];
    // GibCursor *end_r_1265 = &cursor_ptr_2775[2];
    // GibCursor *end_r_1266 = &cursor_ptr_2775[3];
    // GibCursor *end_r_1267 = &cursor_ptr_2775[4];
    // GibCursor *end_r_1268 = &cursor_ptr_2775[5];
    // GibCursor *end_r_1269 = &cursor_ptr_2775[6];

    GibCursor *dcon_2778 = &lst_36_307_484[0];
    GibPackedTag tmpval_3893 = *(GibPackedTag *) (*dcon_2778);

    //GibCursor tmpcur_3894 = *dcon_2778 + 1;
    *dcon_2778 += 1;
    
  switch_3958:
    ;
    switch (tmpval_3893) {
        
      case 1:
        {
            // GibCursor *soa_field_0_2780 = &lst_36_307_484[1];
            // GibCursor *soa_field_1_2781 = &lst_36_307_484[2];
            // GibCursor *soa_field_2_2782 = &lst_36_307_484[3];
            // GibCursor *soa_field_3_2783 = &lst_36_307_484[4];
            // GibCursor *soa_field_4_2784 = &lst_36_307_484[5];
            // GibCursor *soa_field_5_2785 = &lst_36_307_484[6];
            GibCursor *loc_1256 = &lst_36_307_484[0];


            //GibCursor jump_dloc_1861 = loc_1256 + 1;
            *loc_1256 += 1;

            // GibCursor *loc_IntTy_1257 = &lst_36_307_484[1];
            //
            // GibCursor *jump_floc_loc_1862 = loc_IntTy_1257;
            // GibCursor *loc_IntTy_1258 = &lst_36_307_484[2];
            // GibCursor *jump_floc_loc_1863 = loc_IntTy_1258;
            // GibCursor *loc_IntTy_1259 = &lst_36_307_484[3];
            // GibCursor *jump_floc_loc_1864 = loc_IntTy_1259;
            // GibCursor *loc_IntTy_1260 = &lst_36_307_484[4];
            // GibCursor *jump_floc_loc_1865 = &loc_IntTy_1260;
            // GibCursor *loc_IntTy_1261 = &lst_36_307_484[5];
            // GibCursor *jump_floc_loc_1866 = &loc_IntTy_1261;
            // GibCursor *loc_IntTy_1262 = &lst_36_307_484[6];
            // GibCursor *jump_floc_loc_1867 = &loc_IntTy_1262;

            // GibCursor cursor_ptr_2787[7] = {jump_dloc_1861, jump_floc_loc_1862,
            //                                 jump_floc_loc_1863,
            //                                 jump_floc_loc_1864,
            //                                 jump_floc_loc_1865,
            //                                 jump_floc_loc_1866,
            //                                 jump_floc_loc_1867};
            //GibCursorPtr7GibCursorPtr7GibIntProd return_62;

            //memcpy(return_62.field0, cursor_ptr_2775, sizeof(GibCursor [7]));
            //memcpy(return_62.field1, lst_36_307_484, sizeof(GibCursor [7]));
            //return_62.field2 = 0;
            //return return_62;
            *Res += 0;
            break;
        }
        
      case 0:
        {
            GibCursor *soa_field_0_2789 = &lst_36_307_484[1];

            // GibCursor *soa_field_1_2790 = &lst_36_307_484[2];
            // GibCursor *soa_field_2_2791 = &lst_36_307_484[3];
            // GibCursor *soa_field_3_2792 = &lst_36_307_484[4];
            // GibCursor *soa_field_4_2793 = &lst_36_307_484[5];
            // GibCursor *soa_field_5_2794 = &lst_36_307_484[6];

            GibInt tmpval_3895 = *(GibInt *) (*soa_field_0_2789);
            //GibCursor tmpcur_3896 = soa_field_0_2789 + sizeof(GibInt);
            *soa_field_0_2789 += sizeof(GibInt);

            // *soa_field_1_2790 += sizeof(GibInt);
            // *soa_field_2_2791 += sizeof(GibInt);
            // *soa_field_3_2792 += sizeof(GibInt);
            // *soa_field_4_2793 += sizeof(GibInt);
            // *soa_field_5_2794 += sizeof(GibInt);

            // GibInt tmpval_3897 = *(GibInt *) soa_field_1_2790;
            // //GibCursor tmpcur_3898 = soa_field_1_2790 + sizeof(GibInt);
            // *soa_field_1_2790 += sizeof(GibInt);
            //
            // GibInt tmpval_3899 = *(GibInt *) soa_field_2_2791;
            // //GibCursor tmpcur_3900 = soa_field_2_2791 + sizeof(GibInt);
            // *soa_field_2_2791 += sizeof(GibInt);
            //
            // GibInt tmpval_3901 = *(GibInt *) soa_field_3_2792;
            // //GibCursor tmpcur_3902 = soa_field_3_2792 + sizeof(GibInt);
            // *soa_field_3_2792 += sizeof(GibInt);
            //
            // GibInt tmpval_3903 = *(GibInt *) soa_field_4_2793;
            // //GibCursor tmpcur_3904 = soa_field_4_2793 + sizeof(GibInt);
            // *soa_field_4_2793 += sizeof(GibInt);
            //
            // GibInt tmpval_3905 = *(GibInt *) soa_field_5_2794;
            // //GibCursor tmpcur_3906 = soa_field_5_2794 + sizeof(GibInt);
            // *soa_field_5_2794 += sizeof(GibInt);


            // GibCursor cursor_ptr_2777[7] = {tmpcur_3894, tmpcur_3896,
            //                                 tmpcur_3898, tmpcur_3900,
            //                                 tmpcur_3902, tmpcur_3904,
            //                                 tmpcur_3906};
            // GibCursor loc_1256 = lst_36_307_484[0];
            // GibCursor jumpf_dloc_1868 = loc_1256 + 1;
            // GibCursor loc_IntTy_1257 = lst_36_307_484[1];
            // GibCursor loc_IntTy_1258 = lst_36_307_484[2];
            // GibCursor loc_IntTy_1259 = lst_36_307_484[3];
            // GibCursor loc_IntTy_1260 = lst_36_307_484[4];
            // GibCursor loc_IntTy_1261 = lst_36_307_484[5];
            // GibCursor loc_IntTy_1262 = lst_36_307_484[6];
            // GibCursor jumpf_floc_loc_1869 = soa_field_0_2789 + 8;
            // GibCursor jumpf_floc_loc_1870 = soa_field_1_2790 + 8;
            // GibCursor jumpf_floc_loc_1871 = soa_field_2_2791 + 8;
            // GibCursor jumpf_floc_loc_1872 = soa_field_3_2792 + 8;
            // GibCursor jumpf_floc_loc_1873 = soa_field_4_2793 + 8;
            // GibCursor jumpf_floc_loc_1874 = soa_field_5_2794 + 8;
            // GibCursor loc_1561 = jumpf_dloc_1868 + 0;
            // GibCursor loc_1560 = jumpf_floc_loc_1869 + 0;
            // GibCursor cursor_ptr_2803[7] = {jumpf_dloc_1868,
            //                                 jumpf_floc_loc_1869,
            //                                 jumpf_floc_loc_1870,
            //                                 jumpf_floc_loc_1871,
            //                                 jumpf_floc_loc_1872,
            //                                 jumpf_floc_loc_1873,
            //                                 jumpf_floc_loc_1874};
            *Res += tmpval_3895;
            reduceB(cursor_ptr_2775, lst_36_307_484, Res);
            //GibCursor pvrtmp_3907[7];
            
            //memcpy(pvrtmp_3907, tmp_struct_63.field0, sizeof(GibCursor [7]));
            
            //GibCursor pvrtmp_3908[7];
            
            //memcpy(pvrtmp_3908, tmp_struct_63.field1, sizeof(GibCursor [7]));
            
//             GibInt pvrtmp_3909 = tmp_struct_63.field2;
//             GibInt tailprim_1882 = tmpval_3895 + pvrtmp_3909;
//             GibCursorPtr7GibCursorPtr7GibIntProd return_64;
//
//             //memcpy(return_64.field0, pvrtmp_3907, sizeof(GibCursor [7]));
//             //memcpy(return_64.field1, pvrtmp_3908, sizeof(GibCursor [7]));
//             return_64.field2 = tailprim_1882;
//             return return_64;
            break;
        }
        
      // case GIB_INDIRECTION_TAG:
      //   {
      //       GibCursor soa_field_0_2811 = lst_36_307_484[1];
      //       GibCursor soa_field_1_2812 = lst_36_307_484[2];
      //       GibCursor soa_field_2_2813 = lst_36_307_484[3];
      //       GibCursor soa_field_3_2814 = lst_36_307_484[4];
      //       GibCursor soa_field_4_2815 = lst_36_307_484[5];
      //       GibCursor soa_field_5_2816 = lst_36_307_484[6];
      //       uintptr_t tagged_tmpcur_73 = *(uintptr_t *) *dcon_2778;
      //       GibCursor tmpcur_3910 = GIB_UNTAG(tagged_tmpcur_73);
      //       GibCursor tmpaftercur_3911 = *dcon_2778 + 8;
      //       uint16_t tmptag_3912 = GIB_GET_TAG(tagged_tmpcur_73);
      //       GibCursor end_from_tagged_dcon_redir_2841 = tmpcur_3910 +
      //                 tmptag_3912;
      //       GibCursor field_nxt_2834 = soa_field_0_2811 + 1;
      //       uintptr_t tagged_tmpcur_72 = *(uintptr_t *) field_nxt_2834;
      //       GibCursor tmpcur_3913 = GIB_UNTAG(tagged_tmpcur_72);
      //       GibCursor tmpaftercur_3914 = field_nxt_2834 + 8;
      //       uint16_t tmptag_3915 = GIB_GET_TAG(tagged_tmpcur_72);
      //       GibCursor end_from_tagged_fld_redir_2842 = tmpcur_3913 +
      //                 tmptag_3915;
      //       GibCursor field_nxt_2835 = soa_field_1_2812 + 1;
      //       uintptr_t tagged_tmpcur_71 = *(uintptr_t *) field_nxt_2835;
      //       GibCursor tmpcur_3916 = GIB_UNTAG(tagged_tmpcur_71);
      //       GibCursor tmpaftercur_3917 = field_nxt_2835 + 8;
      //       uint16_t tmptag_3918 = GIB_GET_TAG(tagged_tmpcur_71);
      //       GibCursor end_from_tagged_fld_redir_2843 = tmpcur_3916 +
      //                 tmptag_3918;
      //       GibCursor field_nxt_2836 = soa_field_2_2813 + 1;
      //       uintptr_t tagged_tmpcur_70 = *(uintptr_t *) field_nxt_2836;
      //       GibCursor tmpcur_3919 = GIB_UNTAG(tagged_tmpcur_70);
      //       GibCursor tmpaftercur_3920 = field_nxt_2836 + 8;
      //       uint16_t tmptag_3921 = GIB_GET_TAG(tagged_tmpcur_70);
      //       GibCursor end_from_tagged_fld_redir_2844 = tmpcur_3919 +
      //                 tmptag_3921;
      //       GibCursor field_nxt_2837 = soa_field_3_2814 + 1;
      //       uintptr_t tagged_tmpcur_69 = *(uintptr_t *) field_nxt_2837;
      //       GibCursor tmpcur_3922 = GIB_UNTAG(tagged_tmpcur_69);
      //       GibCursor tmpaftercur_3923 = field_nxt_2837 + 8;
      //       uint16_t tmptag_3924 = GIB_GET_TAG(tagged_tmpcur_69);
      //       GibCursor end_from_tagged_fld_redir_2845 = tmpcur_3922 +
      //                 tmptag_3924;
      //       GibCursor field_nxt_2838 = soa_field_4_2815 + 1;
      //       uintptr_t tagged_tmpcur_68 = *(uintptr_t *) field_nxt_2838;
      //       GibCursor tmpcur_3925 = GIB_UNTAG(tagged_tmpcur_68);
      //       GibCursor tmpaftercur_3926 = field_nxt_2838 + 8;
      //       uint16_t tmptag_3927 = GIB_GET_TAG(tagged_tmpcur_68);
      //       GibCursor end_from_tagged_fld_redir_2846 = tmpcur_3925 +
      //                 tmptag_3927;
      //       GibCursor field_nxt_2839 = soa_field_5_2816 + 1;
      //       uintptr_t tagged_tmpcur_67 = *(uintptr_t *) field_nxt_2839;
      //       GibCursor tmpcur_3928 = GIB_UNTAG(tagged_tmpcur_67);
      //       GibCursor tmpaftercur_3929 = field_nxt_2839 + 8;
      //       uint16_t tmptag_3930 = GIB_GET_TAG(tagged_tmpcur_67);
      //       GibCursor end_from_tagged_fld_redir_2847 = tmpcur_3928 +
      //                 tmptag_3930;
      //       GibCursor indr_2056[7] = {tmpcur_3910, tmpcur_3913, tmpcur_3916,
      //                                 tmpcur_3919, tmpcur_3922, tmpcur_3925,
      //                                 tmpcur_3928};
      //       GibCursor loc_1256 = lst_36_307_484[0];
      //       GibCursor jump_dloc_2064 = loc_1256 + 9;
      //       GibCursor loc_IntTy_1262 = lst_36_307_484[6];
      //       GibCursor loc_IntTy_1261 = lst_36_307_484[5];
      //       GibCursor loc_IntTy_1260 = lst_36_307_484[4];
      //       GibCursor loc_IntTy_1259 = lst_36_307_484[3];
      //       GibCursor loc_IntTy_1258 = lst_36_307_484[2];
      //       GibCursor loc_IntTy_1257 = lst_36_307_484[1];
      //       GibCursor aft_indir_loc_2080 = loc_IntTy_1257 + 9;
      //       GibCursor aft_indir_loc_2081 = loc_IntTy_1258 + 9;
      //       GibCursor aft_indir_loc_2082 = loc_IntTy_1259 + 9;
      //       GibCursor aft_indir_loc_2083 = loc_IntTy_1260 + 9;
      //       GibCursor aft_indir_loc_2084 = loc_IntTy_1261 + 9;
      //       GibCursor aft_indir_loc_2085 = loc_IntTy_1262 + 9;
      //       GibCursor cursor_ptr_2848[7] = {jump_dloc_2064, aft_indir_loc_2080,
      //                                       aft_indir_loc_2081,
      //                                       aft_indir_loc_2082,
      //                                       aft_indir_loc_2083,
      //                                       aft_indir_loc_2084,
      //                                       aft_indir_loc_2085};
      //       GibCursorPtr7GibCursorPtr7GibIntProd tmp_struct_65 =
      //                                             reduceB(indr_2056, indr_2056);
      //       GibCursor pvrtmp_3931[7];
      //
      //       memcpy(pvrtmp_3931, tmp_struct_65.field0, sizeof(GibCursor [7]));
      //
      //       GibCursor pvrtmp_3932[7];
      //
      //       memcpy(pvrtmp_3932, tmp_struct_65.field1, sizeof(GibCursor [7]));
      //
      //       GibInt pvrtmp_3933 = tmp_struct_65.field2;
      //       GibCursorPtr7GibCursorPtr7GibIntProd return_66;
      //
      //       memcpy(return_66.field0, cursor_ptr_2775, sizeof(GibCursor [7]));
      //       memcpy(return_66.field1, cursor_ptr_2848, sizeof(GibCursor [7]));
      //       return_66.field2 = pvrtmp_3933;
      //       return return_66;
      //       break;
      //   }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor *soa_field_0_2856 = &lst_36_307_484[1];


            uintptr_t tagged_tmpcur_82 = *(uintptr_t *) (*dcon_2778);
            GibCursor tmpcur_3934 = GIB_UNTAG(tagged_tmpcur_82);
            *dcon_2778 = tmpcur_3934;

            // GibCursor tmpaftercur_3935 = *dcon_2778 + 8;
            // uint16_t tmptag_3936 = GIB_GET_TAG(tagged_tmpcur_82);
            // GibCursor end_from_tagged_dcon_redir_2877 = tmpcur_3934 +
            //           tmptag_3936;


            //GibCursor field_nxt_2871 = soa_field_0_2856 + 1;
            *soa_field_0_2856 += 1;
            uintptr_t tagged_tmpcur_81 = *(uintptr_t *) (*soa_field_0_2856);
            GibCursor tmpcur_3937 = GIB_UNTAG(tagged_tmpcur_81);
            *soa_field_0_2856 = tmpcur_3937;


            // GibCursor tmpaftercur_3938 = field_nxt_2871 + 8;
            // uint16_t tmptag_3939 = GIB_GET_TAG(tagged_tmpcur_81);
            // GibCursor end_from_tagged_fld_redir_2878 = tmpcur_3937 +
            //           tmptag_3939;


            // GibCursor field_nxt_2872 = soa_field_1_2857 + 1;
            // uintptr_t tagged_tmpcur_80 = *(uintptr_t *) field_nxt_2872;
            // GibCursor tmpcur_3940 = GIB_UNTAG(tagged_tmpcur_80);
            // GibCursor tmpaftercur_3941 = field_nxt_2872 + 8;
            // uint16_t tmptag_3942 = GIB_GET_TAG(tagged_tmpcur_80);
            // GibCursor end_from_tagged_fld_redir_2879 = tmpcur_3940 +
            //           tmptag_3942;
            // GibCursor field_nxt_2873 = soa_field_2_2858 + 1;
            // uintptr_t tagged_tmpcur_79 = *(uintptr_t *) field_nxt_2873;
            // GibCursor tmpcur_3943 = GIB_UNTAG(tagged_tmpcur_79);
            // GibCursor tmpaftercur_3944 = field_nxt_2873 + 8;
            // uint16_t tmptag_3945 = GIB_GET_TAG(tagged_tmpcur_79);
            // GibCursor end_from_tagged_fld_redir_2880 = tmpcur_3943 +
            //           tmptag_3945;
            // GibCursor field_nxt_2874 = soa_field_3_2859 + 1;
            // uintptr_t tagged_tmpcur_78 = *(uintptr_t *) field_nxt_2874;
            // GibCursor tmpcur_3946 = GIB_UNTAG(tagged_tmpcur_78);
            // GibCursor tmpaftercur_3947 = field_nxt_2874 + 8;
            // uint16_t tmptag_3948 = GIB_GET_TAG(tagged_tmpcur_78);
            // GibCursor end_from_tagged_fld_redir_2881 = tmpcur_3946 +
            //           tmptag_3948;
            // GibCursor field_nxt_2875 = soa_field_4_2860 + 1;
            // uintptr_t tagged_tmpcur_77 = *(uintptr_t *) field_nxt_2875;
            // GibCursor tmpcur_3949 = GIB_UNTAG(tagged_tmpcur_77);
            // GibCursor tmpaftercur_3950 = field_nxt_2875 + 8;
            // uint16_t tmptag_3951 = GIB_GET_TAG(tagged_tmpcur_77);
            // GibCursor end_from_tagged_fld_redir_2882 = tmpcur_3949 +
            //           tmptag_3951;
            // GibCursor field_nxt_2876 = soa_field_5_2861 + 1;
            // uintptr_t tagged_tmpcur_76 = *(uintptr_t *) field_nxt_2876;
            // GibCursor tmpcur_3952 = GIB_UNTAG(tagged_tmpcur_76);
            // GibCursor tmpaftercur_3953 = field_nxt_2876 + 8;
            // uint16_t tmptag_3954 = GIB_GET_TAG(tagged_tmpcur_76);
            // GibCursor end_from_tagged_fld_redir_2883 = tmpcur_3952 +
            //           tmptag_3954;


            // GibCursor indr_2056[7] = {tmpcur_3934, tmpcur_3937, soa_field_1_2857,
            //                           soa_field_2_2858, soa_field_3_2859, soa_field_4_2860,
            //                           soa_field_5_2861};

            reduceB(lst_36_307_484, lst_36_307_484, Res);
            //GibCursor pvrtmp_3955[7];
            
            //memcpy(pvrtmp_3955, tmp_struct_74.field0, sizeof(GibCursor [7]));
            
            //GibCursor pvrtmp_3956[7];
            
            //memcpy(pvrtmp_3956, tmp_struct_74.field1, sizeof(GibCursor [7]));
            
            // GibInt pvrtmp_3957 = tmp_struct_74.field2;
            // GibCursorPtr7GibCursorPtr7GibIntProd return_75;
            
            //memcpy(return_75.field0, pvrtmp_3955, sizeof(GibCursor [7]));
            //memcpy(return_75.field1, pvrtmp_3956, sizeof(GibCursor [7]));
            // return_75.field2 = pvrtmp_3957;
            // return return_75;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3893");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_ListA(GibCursor end_r_1273,
                                                              GibCursor end_r_1275,
                                                              GibCursor loc_1271,
                                                              GibCursor arg_88_315_493)
{
    if (loc_1271 + 18 > end_r_1275) {
        gib_grow_region(&loc_1271, &end_r_1275);
    }
    
    GibPackedTag tmpval_3959 = *(GibPackedTag *) arg_88_315_493;
    GibCursor tmpcur_3960 = arg_88_315_493 + 1;
    
    
  switch_4008:
    ;
    switch (tmpval_3959) {
        
      case 0:
        {
            GibInt tmpval_3961 = *(GibInt *) tmpcur_3960;
            GibCursor tmpcur_3962 = tmpcur_3960 + sizeof(GibInt);
            GibCursor jump_1883 = tmpcur_3960 + 8;
            GibCursor loc_1583 = loc_1271 + 1;
            GibCursor loc_1584 = loc_1583 + 8;
            
            *(GibPackedTag *) loc_1271 = 0;
            
            GibCursor writetag_2896 = loc_1271 + 1;
            GibCursor after_tag_2897 = loc_1271 + 1;
            
            *(GibInt *) after_tag_2897 = tmpval_3961;
            
            GibCursor writecur_2901 = after_tag_2897 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_83 =
                                                               _copy_ListA(end_r_1273, end_r_1275, loc_1584, tmpcur_3962);
            GibCursor pvrtmp_3963 = tmp_struct_83.field0;
            GibCursor pvrtmp_3964 = tmp_struct_83.field1;
            GibCursor pvrtmp_3965 = tmp_struct_83.field2;
            GibCursor pvrtmp_3966 = tmp_struct_83.field3;
            GibCursor pvrtmp_3967 = tmp_struct_83.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_84;
            
            return_84.field0 = pvrtmp_3963;
            return_84.field1 = pvrtmp_3964;
            return_84.field2 = pvrtmp_3965;
            return_84.field3 = loc_1271;
            return_84.field4 = pvrtmp_3967;
            return return_84;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1886 = arg_88_315_493 + 1;
            
            *(GibPackedTag *) loc_1271 = 1;
            
            GibCursor writetag_2906 = loc_1271 + 1;
            GibCursor after_tag_2907 = loc_1271 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_85;
            
            return_85.field0 = end_r_1273;
            return_85.field1 = end_r_1275;
            return_85.field2 = jump_loc_1886;
            return_85.field3 = loc_1271;
            return_85.field4 = after_tag_2907;
            return return_85;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_88 = *(uintptr_t *) tmpcur_3960;
            GibCursor tmpcur_3980 = GIB_UNTAG(tagged_tmpcur_88);
            GibCursor tmpaftercur_3981 = tmpcur_3960 + 8;
            uint16_t tmptag_3982 = GIB_GET_TAG(tagged_tmpcur_88);
            GibCursor end_from_tagged_indr_2086 = tmpcur_3980 + tmptag_3982;
            GibCursor jump_loc_2088 = tmpcur_3960 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_86 =
                                                               _copy_ListA(tmpcur_3980, end_r_1275, loc_1271, tmpcur_3980);
            GibCursor pvrtmp_3983 = tmp_struct_86.field0;
            GibCursor pvrtmp_3984 = tmp_struct_86.field1;
            GibCursor pvrtmp_3985 = tmp_struct_86.field2;
            GibCursor pvrtmp_3986 = tmp_struct_86.field3;
            GibCursor pvrtmp_3987 = tmp_struct_86.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_87;
            
            return_87.field0 = end_r_1273;
            return_87.field1 = pvrtmp_3984;
            return_87.field2 = jump_loc_2088;
            return_87.field3 = pvrtmp_3986;
            return_87.field4 = pvrtmp_3987;
            return return_87;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_91 = *(uintptr_t *) tmpcur_3960;
            GibCursor tmpcur_3994 = GIB_UNTAG(tagged_tmpcur_91);
            GibCursor tmpaftercur_3995 = tmpcur_3960 + 8;
            uint16_t tmptag_3996 = GIB_GET_TAG(tagged_tmpcur_91);
            GibCursor end_from_tagged_indr_2086 = tmpcur_3994 + tmptag_3996;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_89 =
                                                               _copy_ListA(tmpcur_3994, end_r_1275, loc_1271, tmpcur_3994);
            GibCursor pvrtmp_3997 = tmp_struct_89.field0;
            GibCursor pvrtmp_3998 = tmp_struct_89.field1;
            GibCursor pvrtmp_3999 = tmp_struct_89.field2;
            GibCursor pvrtmp_4000 = tmp_struct_89.field3;
            GibCursor pvrtmp_4001 = tmp_struct_89.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_90;
            
            return_90.field0 = pvrtmp_3997;
            return_90.field1 = pvrtmp_3998;
            return_90.field2 = pvrtmp_3999;
            return_90.field3 = pvrtmp_4000;
            return_90.field4 = pvrtmp_4001;
            return return_90;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_3959");
            exit(1);
        }
    }
}
GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod _copy_ListB(GibCursor cursor_ptr_2925[7],
                                                                                  GibCursor cursor_ptr_2924[7],
                                                                                  GibCursor cursor_ptr_2926[7],
                                                                                  GibCursor arg_176_330_498[7])
{
    GibCursor end_r_1298 = cursor_ptr_2924[1];
    GibCursor end_r_1302 = cursor_ptr_2924[5];
    GibCursor end_r_1297 = cursor_ptr_2924[0];
    GibCursor end_r_1301 = cursor_ptr_2924[4];
    GibCursor end_r_1303 = cursor_ptr_2924[6];
    GibCursor end_r_1300 = cursor_ptr_2924[3];
    GibCursor end_r_1299 = cursor_ptr_2924[2];
    GibCursor loc_IntTy_1288 = cursor_ptr_2926[5];
    GibCursor loc_IntTy_1285 = cursor_ptr_2926[2];
    GibCursor loc_IntTy_1289 = cursor_ptr_2926[6];
    GibCursor loc_1283 = cursor_ptr_2926[0];
    GibCursor loc_IntTy_1286 = cursor_ptr_2926[3];
    GibCursor loc_IntTy_1284 = cursor_ptr_2926[1];
    GibCursor loc_IntTy_1287 = cursor_ptr_2926[4];
    
    if (loc_IntTy_1289 + 17 > end_r_1303 || (loc_IntTy_1288 + 17 > end_r_1302 ||
                                             (loc_IntTy_1287 + 17 >
                                              end_r_1301 || (loc_IntTy_1286 +
                                                             17 > end_r_1300 ||
                                                             (loc_IntTy_1285 +
                                                              17 > end_r_1299 ||
                                                              (loc_IntTy_1284 +
                                                               17 >
                                                               end_r_1298 ||
                                                               loc_1283 + 66 >
                                                               end_r_1297)))))) {
        gib_grow_region(&loc_IntTy_1289, &end_r_1303);
        gib_grow_region(&loc_IntTy_1288, &end_r_1302);
        gib_grow_region(&loc_IntTy_1287, &end_r_1301);
        gib_grow_region(&loc_IntTy_1286, &end_r_1300);
        gib_grow_region(&loc_IntTy_1285, &end_r_1299);
        gib_grow_region(&loc_IntTy_1284, &end_r_1298);
        gib_grow_region(&loc_1283, &end_r_1297);
    }
    
    GibCursor end_r_1290 = cursor_ptr_2925[0];
    GibCursor end_r_1291 = cursor_ptr_2925[1];
    GibCursor end_r_1292 = cursor_ptr_2925[2];
    GibCursor end_r_1293 = cursor_ptr_2925[3];
    GibCursor end_r_1294 = cursor_ptr_2925[4];
    GibCursor end_r_1295 = cursor_ptr_2925[5];
    GibCursor end_r_1296 = cursor_ptr_2925[6];
    GibCursor overwrite_reg_2927[7] = {end_r_1297, end_r_1298, end_r_1299,
                                       end_r_1300, end_r_1301, end_r_1302,
                                       end_r_1303};
    GibCursor dcon_2930 = arg_176_330_498[0];
    GibPackedTag tmpval_4009 = *(GibPackedTag *) dcon_2930;
    GibCursor tmpcur_4010 = dcon_2930 + 1;
    
    
  switch_4104:
    ;
    switch (tmpval_4009) {
        
      case 0:
        {
            GibCursor soa_field_0_2932 = arg_176_330_498[1];
            GibCursor soa_field_1_2933 = arg_176_330_498[2];
            GibCursor soa_field_2_2934 = arg_176_330_498[3];
            GibCursor soa_field_3_2935 = arg_176_330_498[4];
            GibCursor soa_field_4_2936 = arg_176_330_498[5];
            GibCursor soa_field_5_2937 = arg_176_330_498[6];
            GibInt tmpval_4011 = *(GibInt *) soa_field_0_2932;
            GibCursor tmpcur_4012 = soa_field_0_2932 + sizeof(GibInt);
            GibInt tmpval_4013 = *(GibInt *) soa_field_1_2933;
            GibCursor tmpcur_4014 = soa_field_1_2933 + sizeof(GibInt);
            GibInt tmpval_4015 = *(GibInt *) soa_field_2_2934;
            GibCursor tmpcur_4016 = soa_field_2_2934 + sizeof(GibInt);
            GibInt tmpval_4017 = *(GibInt *) soa_field_3_2935;
            GibCursor tmpcur_4018 = soa_field_3_2935 + sizeof(GibInt);
            GibInt tmpval_4019 = *(GibInt *) soa_field_4_2936;
            GibCursor tmpcur_4020 = soa_field_4_2936 + sizeof(GibInt);
            GibInt tmpval_4021 = *(GibInt *) soa_field_5_2937;
            GibCursor tmpcur_4022 = soa_field_5_2937 + sizeof(GibInt);
            GibCursor cursor_ptr_2929[7] = {tmpcur_4010, tmpcur_4012,
                                            tmpcur_4014, tmpcur_4016,
                                            tmpcur_4018, tmpcur_4020,
                                            tmpcur_4022};
            GibCursor loc_1276 = arg_176_330_498[0];
            GibCursor jumpf_dloc_1888 = loc_1276 + 1;
            GibCursor loc_IntTy_1277 = arg_176_330_498[1];
            GibCursor loc_IntTy_1278 = arg_176_330_498[2];
            GibCursor loc_IntTy_1279 = arg_176_330_498[3];
            GibCursor loc_IntTy_1280 = arg_176_330_498[4];
            GibCursor loc_IntTy_1281 = arg_176_330_498[5];
            GibCursor loc_IntTy_1282 = arg_176_330_498[6];
            GibCursor jumpf_floc_loc_1889 = soa_field_0_2932 + 8;
            GibCursor jumpf_floc_loc_1890 = soa_field_1_2933 + 8;
            GibCursor jumpf_floc_loc_1891 = soa_field_2_2934 + 8;
            GibCursor jumpf_floc_loc_1892 = soa_field_3_2935 + 8;
            GibCursor jumpf_floc_loc_1893 = soa_field_4_2936 + 8;
            GibCursor jumpf_floc_loc_1894 = soa_field_5_2937 + 8;
            GibCursor loc_1603 = jumpf_dloc_1888 + 0;
            GibCursor loc_1602 = jumpf_floc_loc_1889 + 0;
            GibCursor cursor_ptr_2946[7] = {jumpf_dloc_1888,
                                            jumpf_floc_loc_1889,
                                            jumpf_floc_loc_1890,
                                            jumpf_floc_loc_1891,
                                            jumpf_floc_loc_1892,
                                            jumpf_floc_loc_1893,
                                            jumpf_floc_loc_1894};
            GibCursor new_floc_loc_1632 = loc_IntTy_1284 + 8;
            GibCursor new_floc_loc_1635 = loc_IntTy_1287 + 8;
            GibCursor new_floc_loc_1634 = loc_IntTy_1286 + 8;
            GibCursor new_dloc_1631 = loc_1283 + 1;
            GibCursor new_floc_loc_1637 = loc_IntTy_1289 + 8;
            GibCursor new_floc_loc_1633 = loc_IntTy_1285 + 8;
            GibCursor new_floc_loc_1636 = loc_IntTy_1288 + 8;
            GibCursor cursor_ptr_2947[7] = {new_dloc_1631, new_floc_loc_1632,
                                            new_floc_loc_1633,
                                            new_floc_loc_1634,
                                            new_floc_loc_1635,
                                            new_floc_loc_1636,
                                            new_floc_loc_1637};
            
            *(GibPackedTag *) loc_1283 = 0;
            
            GibCursor writetag_2957 = loc_1283 + 1;
            GibCursor after_tag_2958 = loc_1283 + 1;
            
            *(GibInt *) loc_IntTy_1284 = tmpval_4011;
            
            GibCursor writecur_2962 = loc_IntTy_1284 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1285 = tmpval_4013;
            
            GibCursor writecur_2964 = loc_IntTy_1285 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1286 = tmpval_4015;
            
            GibCursor writecur_2966 = loc_IntTy_1286 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1287 = tmpval_4017;
            
            GibCursor writecur_2968 = loc_IntTy_1287 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1288 = tmpval_4019;
            
            GibCursor writecur_2970 = loc_IntTy_1288 + sizeof(GibInt);
            
            *(GibInt *) loc_IntTy_1289 = tmpval_4021;
            
            GibCursor writecur_2972 = loc_IntTy_1289 + sizeof(GibInt);
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            tmp_struct_95 =
             _copy_ListB(cursor_ptr_2925, overwrite_reg_2927, cursor_ptr_2947, cursor_ptr_2929);
            GibCursor pvrtmp_4023[7];
            
            memcpy(pvrtmp_4023, tmp_struct_95.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4024[7];
            
            memcpy(pvrtmp_4024, tmp_struct_95.field1, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4025[7];
            
            memcpy(pvrtmp_4025, tmp_struct_95.field2, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4026[7];
            
            memcpy(pvrtmp_4026, tmp_struct_95.field3, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4027[7];
            
            memcpy(pvrtmp_4027, tmp_struct_95.field4, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_96;
            
            memcpy(return_96.field0, pvrtmp_4023, sizeof(GibCursor [7]));
            memcpy(return_96.field1, pvrtmp_4024, sizeof(GibCursor [7]));
            memcpy(return_96.field2, pvrtmp_4025, sizeof(GibCursor [7]));
            memcpy(return_96.field3, cursor_ptr_2926, sizeof(GibCursor [7]));
            memcpy(return_96.field4, pvrtmp_4027, sizeof(GibCursor [7]));
            return return_96;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_2978 = arg_176_330_498[1];
            GibCursor soa_field_1_2979 = arg_176_330_498[2];
            GibCursor soa_field_2_2980 = arg_176_330_498[3];
            GibCursor soa_field_3_2981 = arg_176_330_498[4];
            GibCursor soa_field_4_2982 = arg_176_330_498[5];
            GibCursor soa_field_5_2983 = arg_176_330_498[6];
            GibCursor loc_1276 = arg_176_330_498[0];
            GibCursor jump_dloc_1903 = loc_1276 + 1;
            GibCursor loc_IntTy_1277 = arg_176_330_498[1];
            GibCursor jump_floc_loc_1904 = loc_IntTy_1277 + 0;
            GibCursor loc_IntTy_1278 = arg_176_330_498[2];
            GibCursor jump_floc_loc_1905 = loc_IntTy_1278 + 0;
            GibCursor loc_IntTy_1279 = arg_176_330_498[3];
            GibCursor jump_floc_loc_1906 = loc_IntTy_1279 + 0;
            GibCursor loc_IntTy_1280 = arg_176_330_498[4];
            GibCursor jump_floc_loc_1907 = loc_IntTy_1280 + 0;
            GibCursor loc_IntTy_1281 = arg_176_330_498[5];
            GibCursor jump_floc_loc_1908 = loc_IntTy_1281 + 0;
            GibCursor loc_IntTy_1282 = arg_176_330_498[6];
            GibCursor jump_floc_loc_1909 = loc_IntTy_1282 + 0;
            GibCursor cursor_ptr_2985[7] = {jump_dloc_1903, jump_floc_loc_1904,
                                            jump_floc_loc_1905,
                                            jump_floc_loc_1906,
                                            jump_floc_loc_1907,
                                            jump_floc_loc_1908,
                                            jump_floc_loc_1909};
            GibCursor new_floc_loc_1632 = loc_IntTy_1284 + 8;
            GibCursor new_floc_loc_1635 = loc_IntTy_1287 + 8;
            GibCursor new_floc_loc_1634 = loc_IntTy_1286 + 8;
            GibCursor new_dloc_1631 = loc_1283 + 1;
            GibCursor new_floc_loc_1637 = loc_IntTy_1289 + 8;
            GibCursor new_floc_loc_1633 = loc_IntTy_1285 + 8;
            GibCursor new_floc_loc_1636 = loc_IntTy_1288 + 8;
            
            *(GibPackedTag *) loc_1283 = 1;
            
            GibCursor writetag_2986 = loc_1283 + 1;
            GibCursor after_tag_2987 = loc_1283 + 1;
            GibCursor aft_soa_loc_2991[7] = {after_tag_2987, loc_IntTy_1284,
                                             loc_IntTy_1285, loc_IntTy_1286,
                                             loc_IntTy_1287, loc_IntTy_1288,
                                             loc_IntTy_1289};
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_97;
            
            memcpy(return_97.field0, cursor_ptr_2925, sizeof(GibCursor [7]));
            memcpy(return_97.field1, overwrite_reg_2927, sizeof(GibCursor [7]));
            memcpy(return_97.field2, cursor_ptr_2985, sizeof(GibCursor [7]));
            memcpy(return_97.field3, cursor_ptr_2926, sizeof(GibCursor [7]));
            memcpy(return_97.field4, aft_soa_loc_2991, sizeof(GibCursor [7]));
            return return_97;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_2995 = arg_176_330_498[1];
            GibCursor soa_field_1_2996 = arg_176_330_498[2];
            GibCursor soa_field_2_2997 = arg_176_330_498[3];
            GibCursor soa_field_3_2998 = arg_176_330_498[4];
            GibCursor soa_field_4_2999 = arg_176_330_498[5];
            GibCursor soa_field_5_3000 = arg_176_330_498[6];
            uintptr_t tagged_tmpcur_106 = *(uintptr_t *) tmpcur_4010;
            GibCursor tmpcur_4040 = GIB_UNTAG(tagged_tmpcur_106);
            GibCursor tmpaftercur_4041 = tmpcur_4010 + 8;
            uint16_t tmptag_4042 = GIB_GET_TAG(tagged_tmpcur_106);
            GibCursor end_from_tagged_dcon_redir_3025 = tmpcur_4040 +
                      tmptag_4042;
            GibCursor field_nxt_3018 = soa_field_0_2995 + 1;
            uintptr_t tagged_tmpcur_105 = *(uintptr_t *) field_nxt_3018;
            GibCursor tmpcur_4043 = GIB_UNTAG(tagged_tmpcur_105);
            GibCursor tmpaftercur_4044 = field_nxt_3018 + 8;
            uint16_t tmptag_4045 = GIB_GET_TAG(tagged_tmpcur_105);
            GibCursor end_from_tagged_fld_redir_3026 = tmpcur_4043 +
                      tmptag_4045;
            GibCursor field_nxt_3019 = soa_field_1_2996 + 1;
            uintptr_t tagged_tmpcur_104 = *(uintptr_t *) field_nxt_3019;
            GibCursor tmpcur_4046 = GIB_UNTAG(tagged_tmpcur_104);
            GibCursor tmpaftercur_4047 = field_nxt_3019 + 8;
            uint16_t tmptag_4048 = GIB_GET_TAG(tagged_tmpcur_104);
            GibCursor end_from_tagged_fld_redir_3027 = tmpcur_4046 +
                      tmptag_4048;
            GibCursor field_nxt_3020 = soa_field_2_2997 + 1;
            uintptr_t tagged_tmpcur_103 = *(uintptr_t *) field_nxt_3020;
            GibCursor tmpcur_4049 = GIB_UNTAG(tagged_tmpcur_103);
            GibCursor tmpaftercur_4050 = field_nxt_3020 + 8;
            uint16_t tmptag_4051 = GIB_GET_TAG(tagged_tmpcur_103);
            GibCursor end_from_tagged_fld_redir_3028 = tmpcur_4049 +
                      tmptag_4051;
            GibCursor field_nxt_3021 = soa_field_3_2998 + 1;
            uintptr_t tagged_tmpcur_102 = *(uintptr_t *) field_nxt_3021;
            GibCursor tmpcur_4052 = GIB_UNTAG(tagged_tmpcur_102);
            GibCursor tmpaftercur_4053 = field_nxt_3021 + 8;
            uint16_t tmptag_4054 = GIB_GET_TAG(tagged_tmpcur_102);
            GibCursor end_from_tagged_fld_redir_3029 = tmpcur_4052 +
                      tmptag_4054;
            GibCursor field_nxt_3022 = soa_field_4_2999 + 1;
            uintptr_t tagged_tmpcur_101 = *(uintptr_t *) field_nxt_3022;
            GibCursor tmpcur_4055 = GIB_UNTAG(tagged_tmpcur_101);
            GibCursor tmpaftercur_4056 = field_nxt_3022 + 8;
            uint16_t tmptag_4057 = GIB_GET_TAG(tagged_tmpcur_101);
            GibCursor end_from_tagged_fld_redir_3030 = tmpcur_4055 +
                      tmptag_4057;
            GibCursor field_nxt_3023 = soa_field_5_3000 + 1;
            uintptr_t tagged_tmpcur_100 = *(uintptr_t *) field_nxt_3023;
            GibCursor tmpcur_4058 = GIB_UNTAG(tagged_tmpcur_100);
            GibCursor tmpaftercur_4059 = field_nxt_3023 + 8;
            uint16_t tmptag_4060 = GIB_GET_TAG(tagged_tmpcur_100);
            GibCursor end_from_tagged_fld_redir_3031 = tmpcur_4058 +
                      tmptag_4060;
            GibCursor indr_2092[7] = {tmpcur_4040, tmpcur_4043, tmpcur_4046,
                                      tmpcur_4049, tmpcur_4052, tmpcur_4055,
                                      tmpcur_4058};
            GibCursor loc_1276 = arg_176_330_498[0];
            GibCursor jump_dloc_2100 = loc_1276 + 9;
            GibCursor loc_IntTy_1282 = arg_176_330_498[6];
            GibCursor loc_IntTy_1281 = arg_176_330_498[5];
            GibCursor loc_IntTy_1280 = arg_176_330_498[4];
            GibCursor loc_IntTy_1279 = arg_176_330_498[3];
            GibCursor loc_IntTy_1278 = arg_176_330_498[2];
            GibCursor loc_IntTy_1277 = arg_176_330_498[1];
            GibCursor aft_indir_loc_2116 = loc_IntTy_1277 + 9;
            GibCursor aft_indir_loc_2117 = loc_IntTy_1278 + 9;
            GibCursor aft_indir_loc_2118 = loc_IntTy_1279 + 9;
            GibCursor aft_indir_loc_2119 = loc_IntTy_1280 + 9;
            GibCursor aft_indir_loc_2120 = loc_IntTy_1281 + 9;
            GibCursor aft_indir_loc_2121 = loc_IntTy_1282 + 9;
            GibCursor cursor_ptr_3032[7] = {jump_dloc_2100, aft_indir_loc_2116,
                                            aft_indir_loc_2117,
                                            aft_indir_loc_2118,
                                            aft_indir_loc_2119,
                                            aft_indir_loc_2120,
                                            aft_indir_loc_2121};
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            tmp_struct_98 =
             _copy_ListB(indr_2092, overwrite_reg_2927, cursor_ptr_2926, indr_2092);
            GibCursor pvrtmp_4061[7];
            
            memcpy(pvrtmp_4061, tmp_struct_98.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4062[7];
            
            memcpy(pvrtmp_4062, tmp_struct_98.field1, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4063[7];
            
            memcpy(pvrtmp_4063, tmp_struct_98.field2, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4064[7];
            
            memcpy(pvrtmp_4064, tmp_struct_98.field3, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4065[7];
            
            memcpy(pvrtmp_4065, tmp_struct_98.field4, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_99;
            
            memcpy(return_99.field0, cursor_ptr_2925, sizeof(GibCursor [7]));
            memcpy(return_99.field1, pvrtmp_4062, sizeof(GibCursor [7]));
            memcpy(return_99.field2, cursor_ptr_3032, sizeof(GibCursor [7]));
            memcpy(return_99.field3, pvrtmp_4064, sizeof(GibCursor [7]));
            memcpy(return_99.field4, pvrtmp_4065, sizeof(GibCursor [7]));
            return return_99;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_3043 = arg_176_330_498[1];
            GibCursor soa_field_1_3044 = arg_176_330_498[2];
            GibCursor soa_field_2_3045 = arg_176_330_498[3];
            GibCursor soa_field_3_3046 = arg_176_330_498[4];
            GibCursor soa_field_4_3047 = arg_176_330_498[5];
            GibCursor soa_field_5_3048 = arg_176_330_498[6];
            uintptr_t tagged_tmpcur_115 = *(uintptr_t *) tmpcur_4010;
            GibCursor tmpcur_4072 = GIB_UNTAG(tagged_tmpcur_115);
            GibCursor tmpaftercur_4073 = tmpcur_4010 + 8;
            uint16_t tmptag_4074 = GIB_GET_TAG(tagged_tmpcur_115);
            GibCursor end_from_tagged_dcon_redir_3064 = tmpcur_4072 +
                      tmptag_4074;
            GibCursor field_nxt_3058 = soa_field_0_3043 + 1;
            uintptr_t tagged_tmpcur_114 = *(uintptr_t *) field_nxt_3058;
            GibCursor tmpcur_4075 = GIB_UNTAG(tagged_tmpcur_114);
            GibCursor tmpaftercur_4076 = field_nxt_3058 + 8;
            uint16_t tmptag_4077 = GIB_GET_TAG(tagged_tmpcur_114);
            GibCursor end_from_tagged_fld_redir_3065 = tmpcur_4075 +
                      tmptag_4077;
            GibCursor field_nxt_3059 = soa_field_1_3044 + 1;
            uintptr_t tagged_tmpcur_113 = *(uintptr_t *) field_nxt_3059;
            GibCursor tmpcur_4078 = GIB_UNTAG(tagged_tmpcur_113);
            GibCursor tmpaftercur_4079 = field_nxt_3059 + 8;
            uint16_t tmptag_4080 = GIB_GET_TAG(tagged_tmpcur_113);
            GibCursor end_from_tagged_fld_redir_3066 = tmpcur_4078 +
                      tmptag_4080;
            GibCursor field_nxt_3060 = soa_field_2_3045 + 1;
            uintptr_t tagged_tmpcur_112 = *(uintptr_t *) field_nxt_3060;
            GibCursor tmpcur_4081 = GIB_UNTAG(tagged_tmpcur_112);
            GibCursor tmpaftercur_4082 = field_nxt_3060 + 8;
            uint16_t tmptag_4083 = GIB_GET_TAG(tagged_tmpcur_112);
            GibCursor end_from_tagged_fld_redir_3067 = tmpcur_4081 +
                      tmptag_4083;
            GibCursor field_nxt_3061 = soa_field_3_3046 + 1;
            uintptr_t tagged_tmpcur_111 = *(uintptr_t *) field_nxt_3061;
            GibCursor tmpcur_4084 = GIB_UNTAG(tagged_tmpcur_111);
            GibCursor tmpaftercur_4085 = field_nxt_3061 + 8;
            uint16_t tmptag_4086 = GIB_GET_TAG(tagged_tmpcur_111);
            GibCursor end_from_tagged_fld_redir_3068 = tmpcur_4084 +
                      tmptag_4086;
            GibCursor field_nxt_3062 = soa_field_4_3047 + 1;
            uintptr_t tagged_tmpcur_110 = *(uintptr_t *) field_nxt_3062;
            GibCursor tmpcur_4087 = GIB_UNTAG(tagged_tmpcur_110);
            GibCursor tmpaftercur_4088 = field_nxt_3062 + 8;
            uint16_t tmptag_4089 = GIB_GET_TAG(tagged_tmpcur_110);
            GibCursor end_from_tagged_fld_redir_3069 = tmpcur_4087 +
                      tmptag_4089;
            GibCursor field_nxt_3063 = soa_field_5_3048 + 1;
            uintptr_t tagged_tmpcur_109 = *(uintptr_t *) field_nxt_3063;
            GibCursor tmpcur_4090 = GIB_UNTAG(tagged_tmpcur_109);
            GibCursor tmpaftercur_4091 = field_nxt_3063 + 8;
            uint16_t tmptag_4092 = GIB_GET_TAG(tagged_tmpcur_109);
            GibCursor end_from_tagged_fld_redir_3070 = tmpcur_4090 +
                      tmptag_4092;
            GibCursor indr_2092[7] = {tmpcur_4072, tmpcur_4075, tmpcur_4078,
                                      tmpcur_4081, tmpcur_4084, tmpcur_4087,
                                      tmpcur_4090};
            GibCursor copy_dloc_2122 = loc_1283 + 0;
            GibCursor copy_floc_loc_2128 = loc_IntTy_1289 + 0;
            GibCursor copy_floc_loc_2127 = loc_IntTy_1288 + 0;
            GibCursor copy_floc_loc_2126 = loc_IntTy_1287 + 0;
            GibCursor copy_floc_loc_2125 = loc_IntTy_1286 + 0;
            GibCursor copy_floc_loc_2124 = loc_IntTy_1285 + 0;
            GibCursor copy_floc_loc_2123 = loc_IntTy_1284 + 0;
            GibCursor cursor_ptr_3071[7] = {copy_dloc_2122, copy_floc_loc_2123,
                                            copy_floc_loc_2124,
                                            copy_floc_loc_2125,
                                            copy_floc_loc_2126,
                                            copy_floc_loc_2127,
                                            copy_floc_loc_2128};
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            tmp_struct_107 =
             _copy_ListB(indr_2092, overwrite_reg_2927, cursor_ptr_3071, indr_2092);
            GibCursor pvrtmp_4093[7];
            
            memcpy(pvrtmp_4093, tmp_struct_107.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4094[7];
            
            memcpy(pvrtmp_4094, tmp_struct_107.field1, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4095[7];
            
            memcpy(pvrtmp_4095, tmp_struct_107.field2, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4096[7];
            
            memcpy(pvrtmp_4096, tmp_struct_107.field3, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4097[7];
            
            memcpy(pvrtmp_4097, tmp_struct_107.field4, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod
            return_108;
            
            memcpy(return_108.field0, pvrtmp_4093, sizeof(GibCursor [7]));
            memcpy(return_108.field1, pvrtmp_4094, sizeof(GibCursor [7]));
            memcpy(return_108.field2, pvrtmp_4095, sizeof(GibCursor [7]));
            memcpy(return_108.field3, pvrtmp_4096, sizeof(GibCursor [7]));
            memcpy(return_108.field4, pvrtmp_4097, sizeof(GibCursor [7]));
            return return_108;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4009");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_1307,
                                                             GibCursor end_r_1309,
                                                             GibCursor loc_1305,
                                                             GibCursor arg_114_345_513)
{
    if (loc_1305 + 42 > end_r_1309) {
        gib_grow_region(&loc_1305, &end_r_1309);
    }
    
    GibPackedTag tmpval_4105 = *(GibPackedTag *) arg_114_345_513;
    GibCursor tmpcur_4106 = arg_114_345_513 + 1;
    
    
  switch_4169:
    ;
    switch (tmpval_4105) {
        
      case 0:
        {
            GibInt tmpval_4107 = *(GibInt *) tmpcur_4106;
            GibCursor tmpcur_4108 = tmpcur_4106 + sizeof(GibInt);
            GibInt tmpval_4109 = *(GibInt *) tmpcur_4108;
            GibCursor tmpcur_4110 = tmpcur_4108 + sizeof(GibInt);
            GibInt tmpval_4111 = *(GibInt *) tmpcur_4110;
            GibCursor tmpcur_4112 = tmpcur_4110 + sizeof(GibInt);
            GibInt tmpval_4113 = *(GibInt *) tmpcur_4112;
            GibCursor tmpcur_4114 = tmpcur_4112 + sizeof(GibInt);
            GibCursor jump_1914 = tmpcur_4112 + 8;
            GibCursor jump_1913 = tmpcur_4110 + 8;
            GibCursor jump_1912 = tmpcur_4108 + 8;
            GibCursor jump_1911 = tmpcur_4106 + 8;
            GibCursor loc_1678 = loc_1305 + 1;
            GibCursor loc_1679 = loc_1678 + 8;
            GibCursor loc_1680 = loc_1679 + 8;
            GibCursor loc_1681 = loc_1680 + 8;
            GibCursor loc_1682 = loc_1681 + 8;
            
            *(GibPackedTag *) loc_1305 = 0;
            
            GibCursor writetag_3093 = loc_1305 + 1;
            GibCursor after_tag_3094 = loc_1305 + 1;
            
            *(GibInt *) after_tag_3094 = tmpval_4107;
            
            GibCursor writecur_3098 = after_tag_3094 + sizeof(GibInt);
            
            *(GibInt *) writecur_3098 = tmpval_4109;
            
            GibCursor writecur_3099 = writecur_3098 + sizeof(GibInt);
            
            *(GibInt *) writecur_3099 = tmpval_4111;
            
            GibCursor writecur_3100 = writecur_3099 + sizeof(GibInt);
            
            *(GibInt *) writecur_3100 = tmpval_4113;
            
            GibCursor writecur_3101 = writecur_3100 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_116 =
                                                               _copy_ListA(end_r_1307, end_r_1309, loc_1682, tmpcur_4114);
            GibCursor pvrtmp_4115 = tmp_struct_116.field0;
            GibCursor pvrtmp_4116 = tmp_struct_116.field1;
            GibCursor pvrtmp_4117 = tmp_struct_116.field2;
            GibCursor pvrtmp_4118 = tmp_struct_116.field3;
            GibCursor pvrtmp_4119 = tmp_struct_116.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_117 =
                                                               _copy_List(pvrtmp_4115, pvrtmp_4116, pvrtmp_4119, pvrtmp_4117);
            GibCursor pvrtmp_4124 = tmp_struct_117.field0;
            GibCursor pvrtmp_4125 = tmp_struct_117.field1;
            GibCursor pvrtmp_4126 = tmp_struct_117.field2;
            GibCursor pvrtmp_4127 = tmp_struct_117.field3;
            GibCursor pvrtmp_4128 = tmp_struct_117.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_118;
            
            return_118.field0 = pvrtmp_4124;
            return_118.field1 = pvrtmp_4125;
            return_118.field2 = pvrtmp_4126;
            return_118.field3 = loc_1305;
            return_118.field4 = pvrtmp_4128;
            return return_118;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1918 = arg_114_345_513 + 1;
            
            *(GibPackedTag *) loc_1305 = 1;
            
            GibCursor writetag_3108 = loc_1305 + 1;
            GibCursor after_tag_3109 = loc_1305 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_119;
            
            return_119.field0 = end_r_1307;
            return_119.field1 = end_r_1309;
            return_119.field2 = jump_loc_1918;
            return_119.field3 = loc_1305;
            return_119.field4 = after_tag_3109;
            return return_119;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_122 = *(uintptr_t *) tmpcur_4106;
            GibCursor tmpcur_4141 = GIB_UNTAG(tagged_tmpcur_122);
            GibCursor tmpaftercur_4142 = tmpcur_4106 + 8;
            uint16_t tmptag_4143 = GIB_GET_TAG(tagged_tmpcur_122);
            GibCursor end_from_tagged_indr_2129 = tmpcur_4141 + tmptag_4143;
            GibCursor jump_loc_2131 = tmpcur_4106 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_120 =
                                                               _copy_List(tmpcur_4141, end_r_1309, loc_1305, tmpcur_4141);
            GibCursor pvrtmp_4144 = tmp_struct_120.field0;
            GibCursor pvrtmp_4145 = tmp_struct_120.field1;
            GibCursor pvrtmp_4146 = tmp_struct_120.field2;
            GibCursor pvrtmp_4147 = tmp_struct_120.field3;
            GibCursor pvrtmp_4148 = tmp_struct_120.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_121;
            
            return_121.field0 = end_r_1307;
            return_121.field1 = pvrtmp_4145;
            return_121.field2 = jump_loc_2131;
            return_121.field3 = pvrtmp_4147;
            return_121.field4 = pvrtmp_4148;
            return return_121;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_125 = *(uintptr_t *) tmpcur_4106;
            GibCursor tmpcur_4155 = GIB_UNTAG(tagged_tmpcur_125);
            GibCursor tmpaftercur_4156 = tmpcur_4106 + 8;
            uint16_t tmptag_4157 = GIB_GET_TAG(tagged_tmpcur_125);
            GibCursor end_from_tagged_indr_2129 = tmpcur_4155 + tmptag_4157;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_123 =
                                                               _copy_List(tmpcur_4155, end_r_1309, loc_1305, tmpcur_4155);
            GibCursor pvrtmp_4158 = tmp_struct_123.field0;
            GibCursor pvrtmp_4159 = tmp_struct_123.field1;
            GibCursor pvrtmp_4160 = tmp_struct_123.field2;
            GibCursor pvrtmp_4161 = tmp_struct_123.field3;
            GibCursor pvrtmp_4162 = tmp_struct_123.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_124;
            
            return_124.field0 = pvrtmp_4158;
            return_124.field1 = pvrtmp_4159;
            return_124.field2 = pvrtmp_4160;
            return_124.field3 = pvrtmp_4161;
            return_124.field4 = pvrtmp_4162;
            return return_124;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4105");
            exit(1);
        }
    }
}
GibCursorPtr7GibCursorPtr7Prod _traverse_ListB(GibCursor cursor_ptr_3126[7],
                                               GibCursor arg_206_358_526[7])
{
    GibCursor end_r_1317 = cursor_ptr_3126[0];
    GibCursor end_r_1318 = cursor_ptr_3126[1];
    GibCursor end_r_1319 = cursor_ptr_3126[2];
    GibCursor end_r_1320 = cursor_ptr_3126[3];
    GibCursor end_r_1321 = cursor_ptr_3126[4];
    GibCursor end_r_1322 = cursor_ptr_3126[5];
    GibCursor end_r_1323 = cursor_ptr_3126[6];
    GibCursor dcon_3129 = arg_206_358_526[0];
    GibPackedTag tmpval_4170 = *(GibPackedTag *) dcon_3129;
    GibCursor tmpcur_4171 = dcon_3129 + 1;
    
    
  switch_4232:
    ;
    switch (tmpval_4170) {
        
      case 0:
        {
            GibCursor soa_field_0_3131 = arg_206_358_526[1];
            GibCursor soa_field_1_3132 = arg_206_358_526[2];
            GibCursor soa_field_2_3133 = arg_206_358_526[3];
            GibCursor soa_field_3_3134 = arg_206_358_526[4];
            GibCursor soa_field_4_3135 = arg_206_358_526[5];
            GibCursor soa_field_5_3136 = arg_206_358_526[6];
            GibInt tmpval_4172 = *(GibInt *) soa_field_0_3131;
            GibCursor tmpcur_4173 = soa_field_0_3131 + sizeof(GibInt);
            GibInt tmpval_4174 = *(GibInt *) soa_field_1_3132;
            GibCursor tmpcur_4175 = soa_field_1_3132 + sizeof(GibInt);
            GibInt tmpval_4176 = *(GibInt *) soa_field_2_3133;
            GibCursor tmpcur_4177 = soa_field_2_3133 + sizeof(GibInt);
            GibInt tmpval_4178 = *(GibInt *) soa_field_3_3134;
            GibCursor tmpcur_4179 = soa_field_3_3134 + sizeof(GibInt);
            GibInt tmpval_4180 = *(GibInt *) soa_field_4_3135;
            GibCursor tmpcur_4181 = soa_field_4_3135 + sizeof(GibInt);
            GibInt tmpval_4182 = *(GibInt *) soa_field_5_3136;
            GibCursor tmpcur_4183 = soa_field_5_3136 + sizeof(GibInt);
            GibCursor cursor_ptr_3128[7] = {tmpcur_4171, tmpcur_4173,
                                            tmpcur_4175, tmpcur_4177,
                                            tmpcur_4179, tmpcur_4181,
                                            tmpcur_4183};
            GibCursor loc_1310 = arg_206_358_526[0];
            GibCursor jumpf_dloc_1920 = loc_1310 + 1;
            GibCursor loc_IntTy_1311 = arg_206_358_526[1];
            GibCursor loc_IntTy_1312 = arg_206_358_526[2];
            GibCursor loc_IntTy_1313 = arg_206_358_526[3];
            GibCursor loc_IntTy_1314 = arg_206_358_526[4];
            GibCursor loc_IntTy_1315 = arg_206_358_526[5];
            GibCursor loc_IntTy_1316 = arg_206_358_526[6];
            GibCursor jumpf_floc_loc_1921 = soa_field_0_3131 + 8;
            GibCursor jumpf_floc_loc_1922 = soa_field_1_3132 + 8;
            GibCursor jumpf_floc_loc_1923 = soa_field_2_3133 + 8;
            GibCursor jumpf_floc_loc_1924 = soa_field_3_3134 + 8;
            GibCursor jumpf_floc_loc_1925 = soa_field_4_3135 + 8;
            GibCursor jumpf_floc_loc_1926 = soa_field_5_3136 + 8;
            GibCursor loc_1709 = jumpf_dloc_1920 + 0;
            GibCursor loc_1708 = jumpf_floc_loc_1921 + 0;
            GibCursor cursor_ptr_3145[7] = {jumpf_dloc_1920,
                                            jumpf_floc_loc_1921,
                                            jumpf_floc_loc_1922,
                                            jumpf_floc_loc_1923,
                                            jumpf_floc_loc_1924,
                                            jumpf_floc_loc_1925,
                                            jumpf_floc_loc_1926};
            GibCursorPtr7GibCursorPtr7Prod tmp_struct_129 =
                                            _traverse_ListB(cursor_ptr_3126, cursor_ptr_3128);
            GibCursor pvrtmp_4184[7];
            
            memcpy(pvrtmp_4184, tmp_struct_129.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4185[7];
            
            memcpy(pvrtmp_4185, tmp_struct_129.field1, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7Prod return_130;
            
            memcpy(return_130.field0, pvrtmp_4184, sizeof(GibCursor [7]));
            memcpy(return_130.field1, pvrtmp_4185, sizeof(GibCursor [7]));
            return return_130;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_3153 = arg_206_358_526[1];
            GibCursor soa_field_1_3154 = arg_206_358_526[2];
            GibCursor soa_field_2_3155 = arg_206_358_526[3];
            GibCursor soa_field_3_3156 = arg_206_358_526[4];
            GibCursor soa_field_4_3157 = arg_206_358_526[5];
            GibCursor soa_field_5_3158 = arg_206_358_526[6];
            GibCursor loc_1310 = arg_206_358_526[0];
            GibCursor jump_dloc_1935 = loc_1310 + 1;
            GibCursor loc_IntTy_1311 = arg_206_358_526[1];
            GibCursor jump_floc_loc_1936 = loc_IntTy_1311 + 0;
            GibCursor loc_IntTy_1312 = arg_206_358_526[2];
            GibCursor jump_floc_loc_1937 = loc_IntTy_1312 + 0;
            GibCursor loc_IntTy_1313 = arg_206_358_526[3];
            GibCursor jump_floc_loc_1938 = loc_IntTy_1313 + 0;
            GibCursor loc_IntTy_1314 = arg_206_358_526[4];
            GibCursor jump_floc_loc_1939 = loc_IntTy_1314 + 0;
            GibCursor loc_IntTy_1315 = arg_206_358_526[5];
            GibCursor jump_floc_loc_1940 = loc_IntTy_1315 + 0;
            GibCursor loc_IntTy_1316 = arg_206_358_526[6];
            GibCursor jump_floc_loc_1941 = loc_IntTy_1316 + 0;
            GibCursor cursor_ptr_3160[7] = {jump_dloc_1935, jump_floc_loc_1936,
                                            jump_floc_loc_1937,
                                            jump_floc_loc_1938,
                                            jump_floc_loc_1939,
                                            jump_floc_loc_1940,
                                            jump_floc_loc_1941};
            GibCursorPtr7GibCursorPtr7Prod return_131;
            
            memcpy(return_131.field0, cursor_ptr_3126, sizeof(GibCursor [7]));
            memcpy(return_131.field1, cursor_ptr_3160, sizeof(GibCursor [7]));
            return return_131;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_3162 = arg_206_358_526[1];
            GibCursor soa_field_1_3163 = arg_206_358_526[2];
            GibCursor soa_field_2_3164 = arg_206_358_526[3];
            GibCursor soa_field_3_3165 = arg_206_358_526[4];
            GibCursor soa_field_4_3166 = arg_206_358_526[5];
            GibCursor soa_field_5_3167 = arg_206_358_526[6];
            uintptr_t tagged_tmpcur_140 = *(uintptr_t *) tmpcur_4171;
            GibCursor tmpcur_4186 = GIB_UNTAG(tagged_tmpcur_140);
            GibCursor tmpaftercur_4187 = tmpcur_4171 + 8;
            uint16_t tmptag_4188 = GIB_GET_TAG(tagged_tmpcur_140);
            GibCursor end_from_tagged_dcon_redir_3192 = tmpcur_4186 +
                      tmptag_4188;
            GibCursor field_nxt_3185 = soa_field_0_3162 + 1;
            uintptr_t tagged_tmpcur_139 = *(uintptr_t *) field_nxt_3185;
            GibCursor tmpcur_4189 = GIB_UNTAG(tagged_tmpcur_139);
            GibCursor tmpaftercur_4190 = field_nxt_3185 + 8;
            uint16_t tmptag_4191 = GIB_GET_TAG(tagged_tmpcur_139);
            GibCursor end_from_tagged_fld_redir_3193 = tmpcur_4189 +
                      tmptag_4191;
            GibCursor field_nxt_3186 = soa_field_1_3163 + 1;
            uintptr_t tagged_tmpcur_138 = *(uintptr_t *) field_nxt_3186;
            GibCursor tmpcur_4192 = GIB_UNTAG(tagged_tmpcur_138);
            GibCursor tmpaftercur_4193 = field_nxt_3186 + 8;
            uint16_t tmptag_4194 = GIB_GET_TAG(tagged_tmpcur_138);
            GibCursor end_from_tagged_fld_redir_3194 = tmpcur_4192 +
                      tmptag_4194;
            GibCursor field_nxt_3187 = soa_field_2_3164 + 1;
            uintptr_t tagged_tmpcur_137 = *(uintptr_t *) field_nxt_3187;
            GibCursor tmpcur_4195 = GIB_UNTAG(tagged_tmpcur_137);
            GibCursor tmpaftercur_4196 = field_nxt_3187 + 8;
            uint16_t tmptag_4197 = GIB_GET_TAG(tagged_tmpcur_137);
            GibCursor end_from_tagged_fld_redir_3195 = tmpcur_4195 +
                      tmptag_4197;
            GibCursor field_nxt_3188 = soa_field_3_3165 + 1;
            uintptr_t tagged_tmpcur_136 = *(uintptr_t *) field_nxt_3188;
            GibCursor tmpcur_4198 = GIB_UNTAG(tagged_tmpcur_136);
            GibCursor tmpaftercur_4199 = field_nxt_3188 + 8;
            uint16_t tmptag_4200 = GIB_GET_TAG(tagged_tmpcur_136);
            GibCursor end_from_tagged_fld_redir_3196 = tmpcur_4198 +
                      tmptag_4200;
            GibCursor field_nxt_3189 = soa_field_4_3166 + 1;
            uintptr_t tagged_tmpcur_135 = *(uintptr_t *) field_nxt_3189;
            GibCursor tmpcur_4201 = GIB_UNTAG(tagged_tmpcur_135);
            GibCursor tmpaftercur_4202 = field_nxt_3189 + 8;
            uint16_t tmptag_4203 = GIB_GET_TAG(tagged_tmpcur_135);
            GibCursor end_from_tagged_fld_redir_3197 = tmpcur_4201 +
                      tmptag_4203;
            GibCursor field_nxt_3190 = soa_field_5_3167 + 1;
            uintptr_t tagged_tmpcur_134 = *(uintptr_t *) field_nxt_3190;
            GibCursor tmpcur_4204 = GIB_UNTAG(tagged_tmpcur_134);
            GibCursor tmpaftercur_4205 = field_nxt_3190 + 8;
            uint16_t tmptag_4206 = GIB_GET_TAG(tagged_tmpcur_134);
            GibCursor end_from_tagged_fld_redir_3198 = tmpcur_4204 +
                      tmptag_4206;
            GibCursor indr_2135[7] = {tmpcur_4186, tmpcur_4189, tmpcur_4192,
                                      tmpcur_4195, tmpcur_4198, tmpcur_4201,
                                      tmpcur_4204};
            GibCursor loc_1310 = arg_206_358_526[0];
            GibCursor jump_dloc_2143 = loc_1310 + 9;
            GibCursor loc_IntTy_1316 = arg_206_358_526[6];
            GibCursor loc_IntTy_1315 = arg_206_358_526[5];
            GibCursor loc_IntTy_1314 = arg_206_358_526[4];
            GibCursor loc_IntTy_1313 = arg_206_358_526[3];
            GibCursor loc_IntTy_1312 = arg_206_358_526[2];
            GibCursor loc_IntTy_1311 = arg_206_358_526[1];
            GibCursor aft_indir_loc_2159 = loc_IntTy_1311 + 9;
            GibCursor aft_indir_loc_2160 = loc_IntTy_1312 + 9;
            GibCursor aft_indir_loc_2161 = loc_IntTy_1313 + 9;
            GibCursor aft_indir_loc_2162 = loc_IntTy_1314 + 9;
            GibCursor aft_indir_loc_2163 = loc_IntTy_1315 + 9;
            GibCursor aft_indir_loc_2164 = loc_IntTy_1316 + 9;
            GibCursor cursor_ptr_3199[7] = {jump_dloc_2143, aft_indir_loc_2159,
                                            aft_indir_loc_2160,
                                            aft_indir_loc_2161,
                                            aft_indir_loc_2162,
                                            aft_indir_loc_2163,
                                            aft_indir_loc_2164};
            GibCursorPtr7GibCursorPtr7Prod tmp_struct_132 =
                                            _traverse_ListB(indr_2135, indr_2135);
            GibCursor pvrtmp_4207[7];
            
            memcpy(pvrtmp_4207, tmp_struct_132.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4208[7];
            
            memcpy(pvrtmp_4208, tmp_struct_132.field1, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7Prod return_133;
            
            memcpy(return_133.field0, cursor_ptr_3126, sizeof(GibCursor [7]));
            memcpy(return_133.field1, cursor_ptr_3199, sizeof(GibCursor [7]));
            return return_133;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_3207 = arg_206_358_526[1];
            GibCursor soa_field_1_3208 = arg_206_358_526[2];
            GibCursor soa_field_2_3209 = arg_206_358_526[3];
            GibCursor soa_field_3_3210 = arg_206_358_526[4];
            GibCursor soa_field_4_3211 = arg_206_358_526[5];
            GibCursor soa_field_5_3212 = arg_206_358_526[6];
            uintptr_t tagged_tmpcur_149 = *(uintptr_t *) tmpcur_4171;
            GibCursor tmpcur_4209 = GIB_UNTAG(tagged_tmpcur_149);
            GibCursor tmpaftercur_4210 = tmpcur_4171 + 8;
            uint16_t tmptag_4211 = GIB_GET_TAG(tagged_tmpcur_149);
            GibCursor end_from_tagged_dcon_redir_3228 = tmpcur_4209 +
                      tmptag_4211;
            GibCursor field_nxt_3222 = soa_field_0_3207 + 1;
            uintptr_t tagged_tmpcur_148 = *(uintptr_t *) field_nxt_3222;
            GibCursor tmpcur_4212 = GIB_UNTAG(tagged_tmpcur_148);
            GibCursor tmpaftercur_4213 = field_nxt_3222 + 8;
            uint16_t tmptag_4214 = GIB_GET_TAG(tagged_tmpcur_148);
            GibCursor end_from_tagged_fld_redir_3229 = tmpcur_4212 +
                      tmptag_4214;
            GibCursor field_nxt_3223 = soa_field_1_3208 + 1;
            uintptr_t tagged_tmpcur_147 = *(uintptr_t *) field_nxt_3223;
            GibCursor tmpcur_4215 = GIB_UNTAG(tagged_tmpcur_147);
            GibCursor tmpaftercur_4216 = field_nxt_3223 + 8;
            uint16_t tmptag_4217 = GIB_GET_TAG(tagged_tmpcur_147);
            GibCursor end_from_tagged_fld_redir_3230 = tmpcur_4215 +
                      tmptag_4217;
            GibCursor field_nxt_3224 = soa_field_2_3209 + 1;
            uintptr_t tagged_tmpcur_146 = *(uintptr_t *) field_nxt_3224;
            GibCursor tmpcur_4218 = GIB_UNTAG(tagged_tmpcur_146);
            GibCursor tmpaftercur_4219 = field_nxt_3224 + 8;
            uint16_t tmptag_4220 = GIB_GET_TAG(tagged_tmpcur_146);
            GibCursor end_from_tagged_fld_redir_3231 = tmpcur_4218 +
                      tmptag_4220;
            GibCursor field_nxt_3225 = soa_field_3_3210 + 1;
            uintptr_t tagged_tmpcur_145 = *(uintptr_t *) field_nxt_3225;
            GibCursor tmpcur_4221 = GIB_UNTAG(tagged_tmpcur_145);
            GibCursor tmpaftercur_4222 = field_nxt_3225 + 8;
            uint16_t tmptag_4223 = GIB_GET_TAG(tagged_tmpcur_145);
            GibCursor end_from_tagged_fld_redir_3232 = tmpcur_4221 +
                      tmptag_4223;
            GibCursor field_nxt_3226 = soa_field_4_3211 + 1;
            uintptr_t tagged_tmpcur_144 = *(uintptr_t *) field_nxt_3226;
            GibCursor tmpcur_4224 = GIB_UNTAG(tagged_tmpcur_144);
            GibCursor tmpaftercur_4225 = field_nxt_3226 + 8;
            uint16_t tmptag_4226 = GIB_GET_TAG(tagged_tmpcur_144);
            GibCursor end_from_tagged_fld_redir_3233 = tmpcur_4224 +
                      tmptag_4226;
            GibCursor field_nxt_3227 = soa_field_5_3212 + 1;
            uintptr_t tagged_tmpcur_143 = *(uintptr_t *) field_nxt_3227;
            GibCursor tmpcur_4227 = GIB_UNTAG(tagged_tmpcur_143);
            GibCursor tmpaftercur_4228 = field_nxt_3227 + 8;
            uint16_t tmptag_4229 = GIB_GET_TAG(tagged_tmpcur_143);
            GibCursor end_from_tagged_fld_redir_3234 = tmpcur_4227 +
                      tmptag_4229;
            GibCursor indr_2135[7] = {tmpcur_4209, tmpcur_4212, tmpcur_4215,
                                      tmpcur_4218, tmpcur_4221, tmpcur_4224,
                                      tmpcur_4227};
            GibCursorPtr7GibCursorPtr7Prod tmp_struct_141 =
                                            _traverse_ListB(indr_2135, indr_2135);
            GibCursor pvrtmp_4230[7];
            
            memcpy(pvrtmp_4230, tmp_struct_141.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4231[7];
            
            memcpy(pvrtmp_4231, tmp_struct_141.field1, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7Prod return_142;
            
            memcpy(return_142.field0, pvrtmp_4230, sizeof(GibCursor [7]));
            memcpy(return_142.field1, pvrtmp_4231, sizeof(GibCursor [7]));
            return return_142;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4170");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _print_ListA(GibCursor end_r_1326,
                                    GibCursor arg_103_369_535)
{
    GibPackedTag tmpval_4233 = *(GibPackedTag *) arg_103_369_535;
    GibCursor tmpcur_4234 = arg_103_369_535 + 1;
    
    
  switch_4249:
    ;
    switch (tmpval_4233) {
        
      case 0:
        {
            GibInt tmpval_4235 = *(GibInt *) tmpcur_4234;
            GibCursor tmpcur_4236 = tmpcur_4234 + sizeof(GibInt);
            GibCursor jump_1943 = tmpcur_4234 + 8;
            unsigned char wildcard_108_372_538 = gib_print_symbol(3643);
            unsigned char wildcard_111_373_539 = gib_print_symbol(3647);
            unsigned char y_106_374_540 = printf("%ld", tmpval_4235);
            unsigned char wildcard_110_375_541 = gib_print_symbol(3647);
            GibCursorGibCursorProd tmp_struct_150 =
                                    _print_ListA(end_r_1326, tmpcur_4236);
            GibCursor pvrtmp_4237 = tmp_struct_150.field0;
            GibCursor pvrtmp_4238 = tmp_struct_150.field1;
            unsigned char wildcard_109_377_543 = gib_print_symbol(3638);
            GibCursorGibCursorProd return_151;
            
            return_151.field0 = pvrtmp_4237;
            return_151.field1 = pvrtmp_4238;
            return return_151;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1946 = arg_103_369_535 + 1;
            unsigned char wildcard_112_378_544 = gib_print_symbol(3640);
            unsigned char wildcard_113_379_545 = gib_print_symbol(3638);
            GibCursorGibCursorProd return_152;
            
            return_152.field0 = end_r_1326;
            return_152.field1 = jump_loc_1946;
            return return_152;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_155 = *(uintptr_t *) tmpcur_4234;
            GibCursor tmpcur_4239 = GIB_UNTAG(tagged_tmpcur_155);
            GibCursor tmpaftercur_4240 = tmpcur_4234 + 8;
            uint16_t tmptag_4241 = GIB_GET_TAG(tagged_tmpcur_155);
            GibCursor end_from_tagged_indr_2165 = tmpcur_4239 + tmptag_4241;
            GibCursor jump_loc_2167 = tmpcur_4234 + 8;
            unsigned char wildcard_2170 = gib_print_symbol(3646);
            GibCursorGibCursorProd tmp_struct_153 =
                                    _print_ListA(tmpcur_4239, tmpcur_4239);
            GibCursor pvrtmp_4242 = tmp_struct_153.field0;
            GibCursor pvrtmp_4243 = tmp_struct_153.field1;
            GibCursorGibCursorProd return_154;
            
            return_154.field0 = end_r_1326;
            return_154.field1 = jump_loc_2167;
            return return_154;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_158 = *(uintptr_t *) tmpcur_4234;
            GibCursor tmpcur_4244 = GIB_UNTAG(tagged_tmpcur_158);
            GibCursor tmpaftercur_4245 = tmpcur_4234 + 8;
            uint16_t tmptag_4246 = GIB_GET_TAG(tagged_tmpcur_158);
            GibCursor end_from_tagged_indr_2165 = tmpcur_4244 + tmptag_4246;
            unsigned char wildcard_2170 = gib_print_symbol(3645);
            GibCursorGibCursorProd tmp_struct_156 =
                                    _print_ListA(tmpcur_4244, tmpcur_4244);
            GibCursor pvrtmp_4247 = tmp_struct_156.field0;
            GibCursor pvrtmp_4248 = tmp_struct_156.field1;
            GibCursorGibCursorProd return_157;
            
            return_157.field0 = pvrtmp_4247;
            return_157.field1 = pvrtmp_4248;
            return return_157;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4233");
            exit(1);
        }
    }
}
GibCursorPtr7GibCursorPtr7Prod _print_ListB(GibCursor cursor_ptr_3256[7],
                                            GibCursor arg_221_380_546[7])
{
    GibCursor end_r_1334 = cursor_ptr_3256[0];
    GibCursor end_r_1335 = cursor_ptr_3256[1];
    GibCursor end_r_1336 = cursor_ptr_3256[2];
    GibCursor end_r_1337 = cursor_ptr_3256[3];
    GibCursor end_r_1338 = cursor_ptr_3256[4];
    GibCursor end_r_1339 = cursor_ptr_3256[5];
    GibCursor end_r_1340 = cursor_ptr_3256[6];
    GibCursor dcon_3259 = arg_221_380_546[0];
    GibPackedTag tmpval_4250 = *(GibPackedTag *) dcon_3259;
    GibCursor tmpcur_4251 = dcon_3259 + 1;
    
    
  switch_4312:
    ;
    switch (tmpval_4250) {
        
      case 0:
        {
            GibCursor soa_field_0_3261 = arg_221_380_546[1];
            GibCursor soa_field_1_3262 = arg_221_380_546[2];
            GibCursor soa_field_2_3263 = arg_221_380_546[3];
            GibCursor soa_field_3_3264 = arg_221_380_546[4];
            GibCursor soa_field_4_3265 = arg_221_380_546[5];
            GibCursor soa_field_5_3266 = arg_221_380_546[6];
            GibInt tmpval_4252 = *(GibInt *) soa_field_0_3261;
            GibCursor tmpcur_4253 = soa_field_0_3261 + sizeof(GibInt);
            GibInt tmpval_4254 = *(GibInt *) soa_field_1_3262;
            GibCursor tmpcur_4255 = soa_field_1_3262 + sizeof(GibInt);
            GibInt tmpval_4256 = *(GibInt *) soa_field_2_3263;
            GibCursor tmpcur_4257 = soa_field_2_3263 + sizeof(GibInt);
            GibInt tmpval_4258 = *(GibInt *) soa_field_3_3264;
            GibCursor tmpcur_4259 = soa_field_3_3264 + sizeof(GibInt);
            GibInt tmpval_4260 = *(GibInt *) soa_field_4_3265;
            GibCursor tmpcur_4261 = soa_field_4_3265 + sizeof(GibInt);
            GibInt tmpval_4262 = *(GibInt *) soa_field_5_3266;
            GibCursor tmpcur_4263 = soa_field_5_3266 + sizeof(GibInt);
            GibCursor cursor_ptr_3258[7] = {tmpcur_4251, tmpcur_4253,
                                            tmpcur_4255, tmpcur_4257,
                                            tmpcur_4259, tmpcur_4261,
                                            tmpcur_4263};
            GibCursor loc_1327 = arg_221_380_546[0];
            GibCursor jumpf_dloc_1948 = loc_1327 + 1;
            GibCursor loc_IntTy_1328 = arg_221_380_546[1];
            GibCursor loc_IntTy_1329 = arg_221_380_546[2];
            GibCursor loc_IntTy_1330 = arg_221_380_546[3];
            GibCursor loc_IntTy_1331 = arg_221_380_546[4];
            GibCursor loc_IntTy_1332 = arg_221_380_546[5];
            GibCursor loc_IntTy_1333 = arg_221_380_546[6];
            GibCursor jumpf_floc_loc_1949 = soa_field_0_3261 + 8;
            GibCursor jumpf_floc_loc_1950 = soa_field_1_3262 + 8;
            GibCursor jumpf_floc_loc_1951 = soa_field_2_3263 + 8;
            GibCursor jumpf_floc_loc_1952 = soa_field_3_3264 + 8;
            GibCursor jumpf_floc_loc_1953 = soa_field_4_3265 + 8;
            GibCursor jumpf_floc_loc_1954 = soa_field_5_3266 + 8;
            GibCursor loc_1744 = jumpf_dloc_1948 + 0;
            GibCursor loc_1743 = jumpf_floc_loc_1949 + 0;
            GibCursor cursor_ptr_3275[7] = {jumpf_dloc_1948,
                                            jumpf_floc_loc_1949,
                                            jumpf_floc_loc_1950,
                                            jumpf_floc_loc_1951,
                                            jumpf_floc_loc_1952,
                                            jumpf_floc_loc_1953,
                                            jumpf_floc_loc_1954};
            unsigned char wildcard_236_388_554 = gib_print_symbol(3642);
            unsigned char wildcard_244_389_555 = gib_print_symbol(3647);
            unsigned char y_229_390_556 = printf("%ld", tmpval_4252);
            unsigned char wildcard_243_391_557 = gib_print_symbol(3647);
            unsigned char y_230_392_558 = printf("%ld", tmpval_4254);
            unsigned char wildcard_242_393_559 = gib_print_symbol(3647);
            unsigned char y_231_394_560 = printf("%ld", tmpval_4256);
            unsigned char wildcard_241_395_561 = gib_print_symbol(3647);
            unsigned char y_232_396_562 = printf("%ld", tmpval_4258);
            unsigned char wildcard_240_397_563 = gib_print_symbol(3647);
            unsigned char y_233_398_564 = printf("%ld", tmpval_4260);
            unsigned char wildcard_239_399_565 = gib_print_symbol(3647);
            unsigned char y_234_400_566 = printf("%ld", tmpval_4262);
            unsigned char wildcard_238_401_567 = gib_print_symbol(3647);
            GibCursorPtr7GibCursorPtr7Prod tmp_struct_159 =
                                            _print_ListB(cursor_ptr_3256, cursor_ptr_3258);
            GibCursor pvrtmp_4264[7];
            
            memcpy(pvrtmp_4264, tmp_struct_159.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4265[7];
            
            memcpy(pvrtmp_4265, tmp_struct_159.field1, sizeof(GibCursor [7]));
            
            unsigned char wildcard_237_403_569 = gib_print_symbol(3638);
            GibCursorPtr7GibCursorPtr7Prod return_160;
            
            memcpy(return_160.field0, pvrtmp_4264, sizeof(GibCursor [7]));
            memcpy(return_160.field1, pvrtmp_4265, sizeof(GibCursor [7]));
            return return_160;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_3283 = arg_221_380_546[1];
            GibCursor soa_field_1_3284 = arg_221_380_546[2];
            GibCursor soa_field_2_3285 = arg_221_380_546[3];
            GibCursor soa_field_3_3286 = arg_221_380_546[4];
            GibCursor soa_field_4_3287 = arg_221_380_546[5];
            GibCursor soa_field_5_3288 = arg_221_380_546[6];
            GibCursor loc_1327 = arg_221_380_546[0];
            GibCursor jump_dloc_1963 = loc_1327 + 1;
            GibCursor loc_IntTy_1328 = arg_221_380_546[1];
            GibCursor jump_floc_loc_1964 = loc_IntTy_1328 + 0;
            GibCursor loc_IntTy_1329 = arg_221_380_546[2];
            GibCursor jump_floc_loc_1965 = loc_IntTy_1329 + 0;
            GibCursor loc_IntTy_1330 = arg_221_380_546[3];
            GibCursor jump_floc_loc_1966 = loc_IntTy_1330 + 0;
            GibCursor loc_IntTy_1331 = arg_221_380_546[4];
            GibCursor jump_floc_loc_1967 = loc_IntTy_1331 + 0;
            GibCursor loc_IntTy_1332 = arg_221_380_546[5];
            GibCursor jump_floc_loc_1968 = loc_IntTy_1332 + 0;
            GibCursor loc_IntTy_1333 = arg_221_380_546[6];
            GibCursor jump_floc_loc_1969 = loc_IntTy_1333 + 0;
            GibCursor cursor_ptr_3290[7] = {jump_dloc_1963, jump_floc_loc_1964,
                                            jump_floc_loc_1965,
                                            jump_floc_loc_1966,
                                            jump_floc_loc_1967,
                                            jump_floc_loc_1968,
                                            jump_floc_loc_1969};
            unsigned char wildcard_245_404_570 = gib_print_symbol(3639);
            unsigned char wildcard_246_405_571 = gib_print_symbol(3638);
            GibCursorPtr7GibCursorPtr7Prod return_161;
            
            memcpy(return_161.field0, cursor_ptr_3256, sizeof(GibCursor [7]));
            memcpy(return_161.field1, cursor_ptr_3290, sizeof(GibCursor [7]));
            return return_161;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_3292 = arg_221_380_546[1];
            GibCursor soa_field_1_3293 = arg_221_380_546[2];
            GibCursor soa_field_2_3294 = arg_221_380_546[3];
            GibCursor soa_field_3_3295 = arg_221_380_546[4];
            GibCursor soa_field_4_3296 = arg_221_380_546[5];
            GibCursor soa_field_5_3297 = arg_221_380_546[6];
            uintptr_t tagged_tmpcur_170 = *(uintptr_t *) tmpcur_4251;
            GibCursor tmpcur_4266 = GIB_UNTAG(tagged_tmpcur_170);
            GibCursor tmpaftercur_4267 = tmpcur_4251 + 8;
            uint16_t tmptag_4268 = GIB_GET_TAG(tagged_tmpcur_170);
            GibCursor end_from_tagged_dcon_redir_3322 = tmpcur_4266 +
                      tmptag_4268;
            GibCursor field_nxt_3315 = soa_field_0_3292 + 1;
            uintptr_t tagged_tmpcur_169 = *(uintptr_t *) field_nxt_3315;
            GibCursor tmpcur_4269 = GIB_UNTAG(tagged_tmpcur_169);
            GibCursor tmpaftercur_4270 = field_nxt_3315 + 8;
            uint16_t tmptag_4271 = GIB_GET_TAG(tagged_tmpcur_169);
            GibCursor end_from_tagged_fld_redir_3323 = tmpcur_4269 +
                      tmptag_4271;
            GibCursor field_nxt_3316 = soa_field_1_3293 + 1;
            uintptr_t tagged_tmpcur_168 = *(uintptr_t *) field_nxt_3316;
            GibCursor tmpcur_4272 = GIB_UNTAG(tagged_tmpcur_168);
            GibCursor tmpaftercur_4273 = field_nxt_3316 + 8;
            uint16_t tmptag_4274 = GIB_GET_TAG(tagged_tmpcur_168);
            GibCursor end_from_tagged_fld_redir_3324 = tmpcur_4272 +
                      tmptag_4274;
            GibCursor field_nxt_3317 = soa_field_2_3294 + 1;
            uintptr_t tagged_tmpcur_167 = *(uintptr_t *) field_nxt_3317;
            GibCursor tmpcur_4275 = GIB_UNTAG(tagged_tmpcur_167);
            GibCursor tmpaftercur_4276 = field_nxt_3317 + 8;
            uint16_t tmptag_4277 = GIB_GET_TAG(tagged_tmpcur_167);
            GibCursor end_from_tagged_fld_redir_3325 = tmpcur_4275 +
                      tmptag_4277;
            GibCursor field_nxt_3318 = soa_field_3_3295 + 1;
            uintptr_t tagged_tmpcur_166 = *(uintptr_t *) field_nxt_3318;
            GibCursor tmpcur_4278 = GIB_UNTAG(tagged_tmpcur_166);
            GibCursor tmpaftercur_4279 = field_nxt_3318 + 8;
            uint16_t tmptag_4280 = GIB_GET_TAG(tagged_tmpcur_166);
            GibCursor end_from_tagged_fld_redir_3326 = tmpcur_4278 +
                      tmptag_4280;
            GibCursor field_nxt_3319 = soa_field_4_3296 + 1;
            uintptr_t tagged_tmpcur_165 = *(uintptr_t *) field_nxt_3319;
            GibCursor tmpcur_4281 = GIB_UNTAG(tagged_tmpcur_165);
            GibCursor tmpaftercur_4282 = field_nxt_3319 + 8;
            uint16_t tmptag_4283 = GIB_GET_TAG(tagged_tmpcur_165);
            GibCursor end_from_tagged_fld_redir_3327 = tmpcur_4281 +
                      tmptag_4283;
            GibCursor field_nxt_3320 = soa_field_5_3297 + 1;
            uintptr_t tagged_tmpcur_164 = *(uintptr_t *) field_nxt_3320;
            GibCursor tmpcur_4284 = GIB_UNTAG(tagged_tmpcur_164);
            GibCursor tmpaftercur_4285 = field_nxt_3320 + 8;
            uint16_t tmptag_4286 = GIB_GET_TAG(tagged_tmpcur_164);
            GibCursor end_from_tagged_fld_redir_3328 = tmpcur_4284 +
                      tmptag_4286;
            GibCursor indr_2171[7] = {tmpcur_4266, tmpcur_4269, tmpcur_4272,
                                      tmpcur_4275, tmpcur_4278, tmpcur_4281,
                                      tmpcur_4284};
            GibCursor loc_1327 = arg_221_380_546[0];
            GibCursor jump_dloc_2179 = loc_1327 + 9;
            GibCursor loc_IntTy_1333 = arg_221_380_546[6];
            GibCursor loc_IntTy_1332 = arg_221_380_546[5];
            GibCursor loc_IntTy_1331 = arg_221_380_546[4];
            GibCursor loc_IntTy_1330 = arg_221_380_546[3];
            GibCursor loc_IntTy_1329 = arg_221_380_546[2];
            GibCursor loc_IntTy_1328 = arg_221_380_546[1];
            GibCursor aft_indir_loc_2195 = loc_IntTy_1328 + 9;
            GibCursor aft_indir_loc_2196 = loc_IntTy_1329 + 9;
            GibCursor aft_indir_loc_2197 = loc_IntTy_1330 + 9;
            GibCursor aft_indir_loc_2198 = loc_IntTy_1331 + 9;
            GibCursor aft_indir_loc_2199 = loc_IntTy_1332 + 9;
            GibCursor aft_indir_loc_2200 = loc_IntTy_1333 + 9;
            GibCursor cursor_ptr_3329[7] = {jump_dloc_2179, aft_indir_loc_2195,
                                            aft_indir_loc_2196,
                                            aft_indir_loc_2197,
                                            aft_indir_loc_2198,
                                            aft_indir_loc_2199,
                                            aft_indir_loc_2200};
            unsigned char wildcard_2194 = gib_print_symbol(3646);
            GibCursorPtr7GibCursorPtr7Prod tmp_struct_162 =
                                            _print_ListB(indr_2171, indr_2171);
            GibCursor pvrtmp_4287[7];
            
            memcpy(pvrtmp_4287, tmp_struct_162.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4288[7];
            
            memcpy(pvrtmp_4288, tmp_struct_162.field1, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7Prod return_163;
            
            memcpy(return_163.field0, cursor_ptr_3256, sizeof(GibCursor [7]));
            memcpy(return_163.field1, cursor_ptr_3329, sizeof(GibCursor [7]));
            return return_163;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_3337 = arg_221_380_546[1];
            GibCursor soa_field_1_3338 = arg_221_380_546[2];
            GibCursor soa_field_2_3339 = arg_221_380_546[3];
            GibCursor soa_field_3_3340 = arg_221_380_546[4];
            GibCursor soa_field_4_3341 = arg_221_380_546[5];
            GibCursor soa_field_5_3342 = arg_221_380_546[6];
            uintptr_t tagged_tmpcur_179 = *(uintptr_t *) tmpcur_4251;
            GibCursor tmpcur_4289 = GIB_UNTAG(tagged_tmpcur_179);
            GibCursor tmpaftercur_4290 = tmpcur_4251 + 8;
            uint16_t tmptag_4291 = GIB_GET_TAG(tagged_tmpcur_179);
            GibCursor end_from_tagged_dcon_redir_3358 = tmpcur_4289 +
                      tmptag_4291;
            GibCursor field_nxt_3352 = soa_field_0_3337 + 1;
            uintptr_t tagged_tmpcur_178 = *(uintptr_t *) field_nxt_3352;
            GibCursor tmpcur_4292 = GIB_UNTAG(tagged_tmpcur_178);
            GibCursor tmpaftercur_4293 = field_nxt_3352 + 8;
            uint16_t tmptag_4294 = GIB_GET_TAG(tagged_tmpcur_178);
            GibCursor end_from_tagged_fld_redir_3359 = tmpcur_4292 +
                      tmptag_4294;
            GibCursor field_nxt_3353 = soa_field_1_3338 + 1;
            uintptr_t tagged_tmpcur_177 = *(uintptr_t *) field_nxt_3353;
            GibCursor tmpcur_4295 = GIB_UNTAG(tagged_tmpcur_177);
            GibCursor tmpaftercur_4296 = field_nxt_3353 + 8;
            uint16_t tmptag_4297 = GIB_GET_TAG(tagged_tmpcur_177);
            GibCursor end_from_tagged_fld_redir_3360 = tmpcur_4295 +
                      tmptag_4297;
            GibCursor field_nxt_3354 = soa_field_2_3339 + 1;
            uintptr_t tagged_tmpcur_176 = *(uintptr_t *) field_nxt_3354;
            GibCursor tmpcur_4298 = GIB_UNTAG(tagged_tmpcur_176);
            GibCursor tmpaftercur_4299 = field_nxt_3354 + 8;
            uint16_t tmptag_4300 = GIB_GET_TAG(tagged_tmpcur_176);
            GibCursor end_from_tagged_fld_redir_3361 = tmpcur_4298 +
                      tmptag_4300;
            GibCursor field_nxt_3355 = soa_field_3_3340 + 1;
            uintptr_t tagged_tmpcur_175 = *(uintptr_t *) field_nxt_3355;
            GibCursor tmpcur_4301 = GIB_UNTAG(tagged_tmpcur_175);
            GibCursor tmpaftercur_4302 = field_nxt_3355 + 8;
            uint16_t tmptag_4303 = GIB_GET_TAG(tagged_tmpcur_175);
            GibCursor end_from_tagged_fld_redir_3362 = tmpcur_4301 +
                      tmptag_4303;
            GibCursor field_nxt_3356 = soa_field_4_3341 + 1;
            uintptr_t tagged_tmpcur_174 = *(uintptr_t *) field_nxt_3356;
            GibCursor tmpcur_4304 = GIB_UNTAG(tagged_tmpcur_174);
            GibCursor tmpaftercur_4305 = field_nxt_3356 + 8;
            uint16_t tmptag_4306 = GIB_GET_TAG(tagged_tmpcur_174);
            GibCursor end_from_tagged_fld_redir_3363 = tmpcur_4304 +
                      tmptag_4306;
            GibCursor field_nxt_3357 = soa_field_5_3342 + 1;
            uintptr_t tagged_tmpcur_173 = *(uintptr_t *) field_nxt_3357;
            GibCursor tmpcur_4307 = GIB_UNTAG(tagged_tmpcur_173);
            GibCursor tmpaftercur_4308 = field_nxt_3357 + 8;
            uint16_t tmptag_4309 = GIB_GET_TAG(tagged_tmpcur_173);
            GibCursor end_from_tagged_fld_redir_3364 = tmpcur_4307 +
                      tmptag_4309;
            GibCursor indr_2171[7] = {tmpcur_4289, tmpcur_4292, tmpcur_4295,
                                      tmpcur_4298, tmpcur_4301, tmpcur_4304,
                                      tmpcur_4307};
            unsigned char wildcard_2194 = gib_print_symbol(3645);
            GibCursorPtr7GibCursorPtr7Prod tmp_struct_171 =
                                            _print_ListB(indr_2171, indr_2171);
            GibCursor pvrtmp_4310[7];
            
            memcpy(pvrtmp_4310, tmp_struct_171.field0, sizeof(GibCursor [7]));
            
            GibCursor pvrtmp_4311[7];
            
            memcpy(pvrtmp_4311, tmp_struct_171.field1, sizeof(GibCursor [7]));
            
            GibCursorPtr7GibCursorPtr7Prod return_172;
            
            memcpy(return_172.field0, pvrtmp_4310, sizeof(GibCursor [7]));
            memcpy(return_172.field1, pvrtmp_4311, sizeof(GibCursor [7]));
            return return_172;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4250");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_List(GibCursor end_r_1344,
                                                                          GibCursor end_r_1346,
                                                                          GibCursor loc_1342,
                                                                          GibCursor arg_127_406_572)
{
    GibPackedTag tmpval_4313 = *(GibPackedTag *) arg_127_406_572;
    GibCursor tmpcur_4314 = arg_127_406_572 + 1;
    
    
  switch_4377:
    ;
    switch (tmpval_4313) {
        
      case 0:
        {
            GibInt tmpval_4315 = *(GibInt *) tmpcur_4314;
            GibCursor tmpcur_4316 = tmpcur_4314 + sizeof(GibInt);
            GibInt tmpval_4317 = *(GibInt *) tmpcur_4316;
            GibCursor tmpcur_4318 = tmpcur_4316 + sizeof(GibInt);
            GibInt tmpval_4319 = *(GibInt *) tmpcur_4318;
            GibCursor tmpcur_4320 = tmpcur_4318 + sizeof(GibInt);
            GibInt tmpval_4321 = *(GibInt *) tmpcur_4320;
            GibCursor tmpcur_4322 = tmpcur_4320 + sizeof(GibInt);
            GibCursor jump_1974 = tmpcur_4320 + 8;
            GibCursor jump_1973 = tmpcur_4318 + 8;
            GibCursor jump_1972 = tmpcur_4316 + 8;
            GibCursor jump_1971 = tmpcur_4314 + 8;
            GibCursor loc_1773 = loc_1342 + 1;
            GibCursor loc_1774 = loc_1773 + 8;
            GibCursor loc_1775 = loc_1774 + 8;
            GibCursor loc_1776 = loc_1775 + 8;
            GibCursor loc_1777 = loc_1776 + 8;
            
            *(GibPackedTag *) loc_1342 = 0;
            
            GibCursor writetag_3383 = loc_1342 + 1;
            GibCursor after_tag_3384 = loc_1342 + 1;
            
            *(GibInt *) after_tag_3384 = tmpval_4315;
            
            GibCursor writecur_3388 = after_tag_3384 + sizeof(GibInt);
            
            *(GibInt *) writecur_3388 = tmpval_4317;
            
            GibCursor writecur_3389 = writecur_3388 + sizeof(GibInt);
            
            *(GibInt *) writecur_3389 = tmpval_4319;
            
            GibCursor writecur_3390 = writecur_3389 + sizeof(GibInt);
            
            *(GibInt *) writecur_3390 = tmpval_4321;
            
            GibCursor writecur_3391 = writecur_3390 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_180 =
                                                               _copy_without_ptrs_ListA(end_r_1344, end_r_1346, loc_1777, tmpcur_4322);
            GibCursor pvrtmp_4323 = tmp_struct_180.field0;
            GibCursor pvrtmp_4324 = tmp_struct_180.field1;
            GibCursor pvrtmp_4325 = tmp_struct_180.field2;
            GibCursor pvrtmp_4326 = tmp_struct_180.field3;
            GibCursor pvrtmp_4327 = tmp_struct_180.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_181 =
                                                               _copy_without_ptrs_List(pvrtmp_4323, pvrtmp_4324, pvrtmp_4327, pvrtmp_4325);
            GibCursor pvrtmp_4332 = tmp_struct_181.field0;
            GibCursor pvrtmp_4333 = tmp_struct_181.field1;
            GibCursor pvrtmp_4334 = tmp_struct_181.field2;
            GibCursor pvrtmp_4335 = tmp_struct_181.field3;
            GibCursor pvrtmp_4336 = tmp_struct_181.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_182;
            
            return_182.field0 = pvrtmp_4332;
            return_182.field1 = pvrtmp_4333;
            return_182.field2 = pvrtmp_4334;
            return_182.field3 = loc_1342;
            return_182.field4 = pvrtmp_4336;
            return return_182;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_1978 = arg_127_406_572 + 1;
            
            *(GibPackedTag *) loc_1342 = 1;
            
            GibCursor writetag_3398 = loc_1342 + 1;
            GibCursor after_tag_3399 = loc_1342 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_183;
            
            return_183.field0 = end_r_1344;
            return_183.field1 = end_r_1346;
            return_183.field2 = jump_loc_1978;
            return_183.field3 = loc_1342;
            return_183.field4 = after_tag_3399;
            return return_183;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_186 = *(uintptr_t *) tmpcur_4314;
            GibCursor tmpcur_4349 = GIB_UNTAG(tagged_tmpcur_186);
            GibCursor tmpaftercur_4350 = tmpcur_4314 + 8;
            uint16_t tmptag_4351 = GIB_GET_TAG(tagged_tmpcur_186);
            GibCursor end_from_tagged_indr_2201 = tmpcur_4349 + tmptag_4351;
            GibCursor jump_loc_2203 = tmpcur_4314 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_184 =
                                                               _copy_without_ptrs_List(tmpcur_4349, end_r_1346, loc_1342, tmpcur_4349);
            GibCursor pvrtmp_4352 = tmp_struct_184.field0;
            GibCursor pvrtmp_4353 = tmp_struct_184.field1;
            GibCursor pvrtmp_4354 = tmp_struct_184.field2;
            GibCursor pvrtmp_4355 = tmp_struct_184.field3;
            GibCursor pvrtmp_4356 = tmp_struct_184.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_185;
            
            return_185.field0 = end_r_1344;
            return_185.field1 = pvrtmp_4353;
            return_185.field2 = jump_loc_2203;
            return_185.field3 = pvrtmp_4355;
            return_185.field4 = pvrtmp_4356;
            return return_185;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_189 = *(uintptr_t *) tmpcur_4314;
            GibCursor tmpcur_4363 = GIB_UNTAG(tagged_tmpcur_189);
            GibCursor tmpaftercur_4364 = tmpcur_4314 + 8;
            uint16_t tmptag_4365 = GIB_GET_TAG(tagged_tmpcur_189);
            GibCursor end_from_tagged_indr_2201 = tmpcur_4363 + tmptag_4365;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_187 =
                                                               _copy_without_ptrs_List(tmpcur_4363, end_r_1346, loc_1342, tmpcur_4363);
            GibCursor pvrtmp_4366 = tmp_struct_187.field0;
            GibCursor pvrtmp_4367 = tmp_struct_187.field1;
            GibCursor pvrtmp_4368 = tmp_struct_187.field2;
            GibCursor pvrtmp_4369 = tmp_struct_187.field3;
            GibCursor pvrtmp_4370 = tmp_struct_187.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_188;
            
            return_188.field0 = pvrtmp_4366;
            return_188.field1 = pvrtmp_4367;
            return_188.field2 = pvrtmp_4368;
            return_188.field3 = pvrtmp_4369;
            return_188.field4 = pvrtmp_4370;
            return return_188;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_4313");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_197 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_3648 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1376 = region_3648.start;
    GibCursor end_r_1376 = region_3648.end;
    GibChunk region_3649 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1377 = region_3649.start;
    GibCursor end_r_1377 = region_3649.end;
    GibChunk region_3650 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1378 = region_3650.start;
    GibCursor end_r_1378 = region_3650.end;
    GibChunk region_3651 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1379 = region_3651.start;
    GibCursor end_r_1379 = region_3651.end;
    GibChunk region_3652 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1380 = region_3652.start;
    GibCursor end_r_1380 = region_3652.end;
    GibChunk region_3653 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1381 = region_3653.start;
    GibCursor end_r_1381 = region_3653.end;
    GibChunk region_3654 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_1382 = region_3654.start;
    GibCursor end_r_1382 = region_3654.end;
    GibCursor reg_ptr_3415[7] = {r_1376, r_1377, r_1378, r_1379, r_1380, r_1381,
                                 r_1382};
    GibCursor reg_cursor_ptr_3416[7] = {end_r_1376, end_r_1377, end_r_1378,
                                        end_r_1379, end_r_1380, end_r_1381,
                                        end_r_1382};
    GibCursorPtr7GibCursorPtr7GibCursorPtr7Prod tmp_struct_190 =
                                                 mkListB(reg_cursor_ptr_3416, reg_ptr_3415, 2500000);
    GibCursor pvrtmp_3655[7];
    
    memcpy(pvrtmp_3655, tmp_struct_190.field0, sizeof(GibCursor [7]));
    
    GibCursor pvrtmp_3656[7];
    
    memcpy(pvrtmp_3656, tmp_struct_190.field1, sizeof(GibCursor [7]));
    
    GibCursor pvrtmp_3657[7];
    
    memcpy(pvrtmp_3657, tmp_struct_190.field2, sizeof(GibCursor [7]));
    
    GibInt timed_3497;
    GibVector *times_195 = gib_vector_alloc(gib_get_iters_param(),
                                            sizeof(double));
    struct timespec begin_timed_3497;
    struct timespec end_timed_3497;
    
    for (long long iters_timed_3497 = 0; iters_timed_3497 <
         gib_get_iters_param(); iters_timed_3497++) {
        if (iters_timed_3497 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_3497);

        GibInt pvrtmp_3664 = 0;

        reduceB(pvrtmp_3655, pvrtmp_3656, &pvrtmp_3664);
//         GibCursor pvrtmp_3662[7];
//
//         memcpy(pvrtmp_3662, tmp_struct_191.field0, sizeof(GibCursor [7]));
//
//         GibCursor pvrtmp_3663[7];
//
//         memcpy(pvrtmp_3663, tmp_struct_191.field1, sizeof(GibCursor [7]));
//
//         GibInt pvrtmp_3664 = tmp_struct_191.field2;
        
        timed_3497 = pvrtmp_3664;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_3497);
        if (iters_timed_3497 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_192 = gib_difftimespecs(&begin_timed_3497,
                                                &end_timed_3497);
        
        printf("itertime: %lf\n", itertime_192);
        gib_vector_inplace_update(times_195, iters_timed_3497, &itertime_192);

        memcpy(pvrtmp_3655, tmp_struct_190.field0, sizeof(GibCursor [7]));
        memcpy(pvrtmp_3656, tmp_struct_190.field1, sizeof(GibCursor [7]));
        pvrtmp_3664 = 0;

    }
    gib_vector_inplace_sort(times_195, gib_compare_doubles);
    
    double *tmp_196 = (double *) gib_vector_nth(times_195,
                                                gib_get_iters_param() / 2);
    double selftimed_194 = *tmp_196;
    double batchtime_193 = gib_sum_timing_array(times_195);
    
    gib_print_timing_array(times_195);
    gib_vector_free(times_195);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_193);
    printf("SELFTIMED: %e\n", selftimed_194);
    printf("%ld", timed_3497);
    printf("\n");
    
    int exit_198 = gib_exit();
    
    return exit_198;
}

// gcc -std=gnu11  -O3  -flto  -D_GIBBON_GENGC=0  -D_GIBBON_SIMPLE_WRITE_BARRIER=0  -D_GIBBON_EAGER_PROMOTION=1  -o /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/reduceList.soa.exe -I/home/vidushs/Applications/src/gibbon/gibbon-rts/build -L/home/vidushs/Applications/src/gibbon/gibbon-rts/build -Wl,-rpath=/home/vidushs/Applications/src/gibbon/gibbon-rts/build /home/vidushs/Applications/src/gibbon/microbench/manual_soa_examples/reduceList.soa.c /home/vidushs/Applications/src/gibbon/gibbon-rts/build/gibbon_rts.o -lm  -lgibbon_rts_ng

