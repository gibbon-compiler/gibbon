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
typedef struct GibCursorPtr2Prod_struct {
            GibCursor field0[2];
        } GibCursorPtr2Prod;
typedef struct GibCursorPtr2GibCursorPtr2Prod_struct {
            GibCursor field0[2];
            GibCursor field1[2];
        } GibCursorPtr2GibCursorPtr2Prod;
typedef struct GibCursorPtr2GibCursorPtr2GibIntProd_struct {
            GibCursor field0[2];
            GibCursor field1[2];
            GibInt field2;
        } GibCursorPtr2GibCursorPtr2GibIntProd;
typedef struct GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod_struct {
            GibCursor field0[2];
            GibCursor field1[2];
            GibCursor field2[2];
        } GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod;
typedef struct GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod_struct {
            GibCursor field0[2];
            GibCursor field1[2];
            GibCursor field2[2];
            GibCursor field3[2];
            GibCursor field4[2];
        } GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod;
GibCursorPtr2GibCursorPtr2Prod _print_List(GibCursor cursor_ptr_728[2],
                                           GibCursor arg_74_88_130[2]);
GibCursorPtr2GibCursorPtr2Prod _traverse_List(GibCursor cursor_ptr_784[2],
                                              GibCursor arg_69_99_141[2]);
GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod mkList(GibCursor cursor_ptr_839[2],
                                                   GibCursor cursor_ptr_840[2],
                                                   GibInt length_24_103_145);
GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
_copy_List(GibCursor cursor_ptr_867[2], GibCursor cursor_ptr_866[2],
           GibCursor cursor_ptr_868[2], GibCursor arg_59_105_149[2]);
GibCursorPtr2GibCursorPtr2GibIntProd sumList(GibCursor cursor_ptr_954[2],
                                             GibCursor lst_26_110_154[2]);
GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
_copy_without_ptrs_List(GibCursor cursor_ptr_1011[2],
                        GibCursor cursor_ptr_1010[2],
                        GibCursor cursor_ptr_1012[2],
                        GibCursor arg_64_115_158[2]);
GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
add1(GibCursor cursor_ptr_1098[2], GibCursor cursor_ptr_1097[2],
     GibCursor cursor_ptr_1099[2], GibCursor lst_31_120_163[2]);
typedef enum {
            GibInt_T,
            GibFloat_T,
            GibSym_T,
            GibBool_T,
            GibVector_T,
            GibList_T,
            GibCursor_T,
            List_T,
        } GibDatatype;
void info_table_initialize(void)
{
    int error = gib_info_table_initialize(8);
    
    if (error < 0) {
        fprintf(stderr, "Couldn't initialize info table, errorno=%d", error);
        exit(1);
    }
    
    GibDatatype field_tys[2];
    
    field_tys[0] = List_T;
    error = gib_info_table_insert_packed_dcon(List_T, 0, 8, 0, 1, 1, field_tys,
                                              1);
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
    gib_info_table_finalize();
}
void symbol_table_initialize(void)
{
    gib_add_symbol(1333, ")");
    gib_add_symbol(1334, "(Nil");
    gib_add_symbol(1335, "(Cons");
    gib_add_symbol(1336, " ->r ");
    gib_add_symbol(1337, " ->i ");
    gib_add_symbol(1338, " ");
}
GibCursorPtr2GibCursorPtr2Prod _print_List(GibCursor cursor_ptr_728[2],
                                           GibCursor arg_74_88_130[2])
{
    GibCursor end_r_336 = cursor_ptr_728[0];
    GibCursor end_r_337 = cursor_ptr_728[1];
    GibCursor dcon_731 = arg_74_88_130[0];
    GibPackedTag tmpval_1374 = *(GibPackedTag *) dcon_731;
    GibCursor tmpcur_1375 = dcon_731 + 1;
    
    
  switch_1396:
    ;
    switch (tmpval_1374) {
        
      case 0:
        {
            GibCursor soa_field_0_733 = arg_74_88_130[1];
            GibInt tmpval_1376 = *(GibInt *) soa_field_0_733;
            GibCursor tmpcur_1377 = soa_field_0_733 + sizeof(GibInt);
            GibCursor cursor_ptr_730[2] = {tmpcur_1375, tmpcur_1377};
            GibCursor loc_334 = arg_74_88_130[0];
            GibCursor jumpf_dloc_504 = loc_334 + 1;
            GibCursor loc_IntTy_335 = arg_74_88_130[1];
            GibCursor jumpf_floc_loc_505 = soa_field_0_733 + 8;
            GibCursor loc_401 = jumpf_dloc_504 + 0;
            GibCursor loc_400 = jumpf_floc_loc_505 + 0;
            GibCursor cursor_ptr_737[2] = {jumpf_dloc_504, jumpf_floc_loc_505};
            unsigned char wildcard_79_91_133 = gib_print_symbol(1335);
            unsigned char wildcard_82_92_134 = gib_print_symbol(1338);
            unsigned char y_77_93_135 = printf("%ld", tmpval_1376);
            unsigned char wildcard_81_94_136 = gib_print_symbol(1338);
            GibCursorPtr2GibCursorPtr2Prod tmp_struct_0 =
                                            _print_List(cursor_ptr_728, cursor_ptr_730);
            GibCursor pvrtmp_1378[2];
            
            memcpy(pvrtmp_1378, tmp_struct_0.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1379[2];
            
            memcpy(pvrtmp_1379, tmp_struct_0.field1, sizeof(GibCursor [2]));
            
            unsigned char wildcard_80_96_138 = gib_print_symbol(1333);
            GibCursorPtr2GibCursorPtr2Prod return_1;
            
            memcpy(return_1.field0, pvrtmp_1378, sizeof(GibCursor [2]));
            memcpy(return_1.field1, pvrtmp_1379, sizeof(GibCursor [2]));
            return return_1;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_745 = arg_74_88_130[1];
            GibCursor loc_334 = arg_74_88_130[0];
            GibCursor jump_dloc_509 = loc_334 + 1;
            GibCursor loc_IntTy_335 = arg_74_88_130[1];
            GibCursor jump_floc_loc_510 = loc_IntTy_335 + 0;
            GibCursor cursor_ptr_747[2] = {jump_dloc_509, jump_floc_loc_510};
            unsigned char wildcard_83_97_139 = gib_print_symbol(1334);
            unsigned char wildcard_84_98_140 = gib_print_symbol(1333);
            GibCursorPtr2GibCursorPtr2Prod return_2;
            
            memcpy(return_2.field0, cursor_ptr_728, sizeof(GibCursor [2]));
            memcpy(return_2.field1, cursor_ptr_747, sizeof(GibCursor [2]));
            return return_2;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_749 = arg_74_88_130[1];
            uintptr_t tagged_tmpcur_6 = *(uintptr_t *) tmpcur_1375;
            GibCursor tmpcur_1380 = GIB_UNTAG(tagged_tmpcur_6);
            GibCursor tmpaftercur_1381 = tmpcur_1375 + 8;
            uint16_t tmptag_1382 = GIB_GET_TAG(tagged_tmpcur_6);
            GibCursor end_from_tagged_dcon_redir_759 = tmpcur_1380 +
                      tmptag_1382;
            GibCursor field_nxt_757 = soa_field_0_749 + 1;
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) field_nxt_757;
            GibCursor tmpcur_1383 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_1384 = field_nxt_757 + 8;
            uint16_t tmptag_1385 = GIB_GET_TAG(tagged_tmpcur_5);
            GibCursor end_from_tagged_fld_redir_760 = tmpcur_1383 + tmptag_1385;
            GibCursor indr_561[2] = {tmpcur_1380, tmpcur_1383};
            GibCursor loc_334 = arg_74_88_130[0];
            GibCursor jump_dloc_564 = loc_334 + 9;
            GibCursor loc_IntTy_335 = arg_74_88_130[1];
            GibCursor aft_indir_loc_570 = loc_IntTy_335 + 9;
            GibCursor cursor_ptr_761[2] = {jump_dloc_564, aft_indir_loc_570};
            unsigned char wildcard_569 = gib_print_symbol(1337);
            GibCursorPtr2GibCursorPtr2Prod tmp_struct_3 =
                                            _print_List(indr_561, indr_561);
            GibCursor pvrtmp_1386[2];
            
            memcpy(pvrtmp_1386, tmp_struct_3.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1387[2];
            
            memcpy(pvrtmp_1387, tmp_struct_3.field1, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2Prod return_4;
            
            memcpy(return_4.field0, cursor_ptr_728, sizeof(GibCursor [2]));
            memcpy(return_4.field1, cursor_ptr_761, sizeof(GibCursor [2]));
            return return_4;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_769 = arg_74_88_130[1];
            uintptr_t tagged_tmpcur_10 = *(uintptr_t *) tmpcur_1375;
            GibCursor tmpcur_1388 = GIB_UNTAG(tagged_tmpcur_10);
            GibCursor tmpaftercur_1389 = tmpcur_1375 + 8;
            uint16_t tmptag_1390 = GIB_GET_TAG(tagged_tmpcur_10);
            GibCursor end_from_tagged_dcon_redir_775 = tmpcur_1388 +
                      tmptag_1390;
            GibCursor field_nxt_774 = soa_field_0_769 + 1;
            uintptr_t tagged_tmpcur_9 = *(uintptr_t *) field_nxt_774;
            GibCursor tmpcur_1391 = GIB_UNTAG(tagged_tmpcur_9);
            GibCursor tmpaftercur_1392 = field_nxt_774 + 8;
            uint16_t tmptag_1393 = GIB_GET_TAG(tagged_tmpcur_9);
            GibCursor end_from_tagged_fld_redir_776 = tmpcur_1391 + tmptag_1393;
            GibCursor indr_561[2] = {tmpcur_1388, tmpcur_1391};
            unsigned char wildcard_569 = gib_print_symbol(1336);
            GibCursorPtr2GibCursorPtr2Prod tmp_struct_7 =
                                            _print_List(indr_561, indr_561);
            GibCursor pvrtmp_1394[2];
            
            memcpy(pvrtmp_1394, tmp_struct_7.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1395[2];
            
            memcpy(pvrtmp_1395, tmp_struct_7.field1, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2Prod return_8;
            
            memcpy(return_8.field0, pvrtmp_1394, sizeof(GibCursor [2]));
            memcpy(return_8.field1, pvrtmp_1395, sizeof(GibCursor [2]));
            return return_8;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1374");
            exit(1);
        }
    }
}
GibCursorPtr2GibCursorPtr2Prod _traverse_List(GibCursor cursor_ptr_784[2],
                                              GibCursor arg_69_99_141[2])
{
    GibCursor end_r_340 = cursor_ptr_784[0];
    GibCursor end_r_341 = cursor_ptr_784[1];
    GibCursor dcon_787 = arg_69_99_141[0];
    GibPackedTag tmpval_1397 = *(GibPackedTag *) dcon_787;
    GibCursor tmpcur_1398 = dcon_787 + 1;
    
    
  switch_1419:
    ;
    switch (tmpval_1397) {
        
      case 0:
        {
            GibCursor soa_field_0_789 = arg_69_99_141[1];
            GibInt tmpval_1399 = *(GibInt *) soa_field_0_789;
            GibCursor tmpcur_1400 = soa_field_0_789 + sizeof(GibInt);
            GibCursor cursor_ptr_786[2] = {tmpcur_1398, tmpcur_1400};
            GibCursor loc_338 = arg_69_99_141[0];
            GibCursor jumpf_dloc_512 = loc_338 + 1;
            GibCursor loc_IntTy_339 = arg_69_99_141[1];
            GibCursor jumpf_floc_loc_513 = soa_field_0_789 + 8;
            GibCursor loc_410 = jumpf_dloc_512 + 0;
            GibCursor loc_409 = jumpf_floc_loc_513 + 0;
            GibCursor cursor_ptr_793[2] = {jumpf_dloc_512, jumpf_floc_loc_513};
            GibCursorPtr2GibCursorPtr2Prod tmp_struct_11 =
                                            _traverse_List(cursor_ptr_784, cursor_ptr_786);
            GibCursor pvrtmp_1401[2];
            
            memcpy(pvrtmp_1401, tmp_struct_11.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1402[2];
            
            memcpy(pvrtmp_1402, tmp_struct_11.field1, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2Prod return_12;
            
            memcpy(return_12.field0, pvrtmp_1401, sizeof(GibCursor [2]));
            memcpy(return_12.field1, pvrtmp_1402, sizeof(GibCursor [2]));
            return return_12;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_801 = arg_69_99_141[1];
            GibCursor loc_338 = arg_69_99_141[0];
            GibCursor jump_dloc_517 = loc_338 + 1;
            GibCursor loc_IntTy_339 = arg_69_99_141[1];
            GibCursor jump_floc_loc_518 = loc_IntTy_339 + 0;
            GibCursor cursor_ptr_803[2] = {jump_dloc_517, jump_floc_loc_518};
            GibCursorPtr2GibCursorPtr2Prod return_13;
            
            memcpy(return_13.field0, cursor_ptr_784, sizeof(GibCursor [2]));
            memcpy(return_13.field1, cursor_ptr_803, sizeof(GibCursor [2]));
            return return_13;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_805 = arg_69_99_141[1];
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_1398;
            GibCursor tmpcur_1403 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_1404 = tmpcur_1398 + 8;
            uint16_t tmptag_1405 = GIB_GET_TAG(tagged_tmpcur_17);
            GibCursor end_from_tagged_dcon_redir_815 = tmpcur_1403 +
                      tmptag_1405;
            GibCursor field_nxt_813 = soa_field_0_805 + 1;
            uintptr_t tagged_tmpcur_16 = *(uintptr_t *) field_nxt_813;
            GibCursor tmpcur_1406 = GIB_UNTAG(tagged_tmpcur_16);
            GibCursor tmpaftercur_1407 = field_nxt_813 + 8;
            uint16_t tmptag_1408 = GIB_GET_TAG(tagged_tmpcur_16);
            GibCursor end_from_tagged_fld_redir_816 = tmpcur_1406 + tmptag_1408;
            GibCursor indr_571[2] = {tmpcur_1403, tmpcur_1406};
            GibCursor loc_338 = arg_69_99_141[0];
            GibCursor jump_dloc_574 = loc_338 + 9;
            GibCursor loc_IntTy_339 = arg_69_99_141[1];
            GibCursor aft_indir_loc_580 = loc_IntTy_339 + 9;
            GibCursor cursor_ptr_817[2] = {jump_dloc_574, aft_indir_loc_580};
            GibCursorPtr2GibCursorPtr2Prod tmp_struct_14 =
                                            _traverse_List(indr_571, indr_571);
            GibCursor pvrtmp_1409[2];
            
            memcpy(pvrtmp_1409, tmp_struct_14.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1410[2];
            
            memcpy(pvrtmp_1410, tmp_struct_14.field1, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2Prod return_15;
            
            memcpy(return_15.field0, cursor_ptr_784, sizeof(GibCursor [2]));
            memcpy(return_15.field1, cursor_ptr_817, sizeof(GibCursor [2]));
            return return_15;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_825 = arg_69_99_141[1];
            uintptr_t tagged_tmpcur_21 = *(uintptr_t *) tmpcur_1398;
            GibCursor tmpcur_1411 = GIB_UNTAG(tagged_tmpcur_21);
            GibCursor tmpaftercur_1412 = tmpcur_1398 + 8;
            uint16_t tmptag_1413 = GIB_GET_TAG(tagged_tmpcur_21);
            GibCursor end_from_tagged_dcon_redir_831 = tmpcur_1411 +
                      tmptag_1413;
            GibCursor field_nxt_830 = soa_field_0_825 + 1;
            uintptr_t tagged_tmpcur_20 = *(uintptr_t *) field_nxt_830;
            GibCursor tmpcur_1414 = GIB_UNTAG(tagged_tmpcur_20);
            GibCursor tmpaftercur_1415 = field_nxt_830 + 8;
            uint16_t tmptag_1416 = GIB_GET_TAG(tagged_tmpcur_20);
            GibCursor end_from_tagged_fld_redir_832 = tmpcur_1414 + tmptag_1416;
            GibCursor indr_571[2] = {tmpcur_1411, tmpcur_1414};
            GibCursorPtr2GibCursorPtr2Prod tmp_struct_18 =
                                            _traverse_List(indr_571, indr_571);
            GibCursor pvrtmp_1417[2];
            
            memcpy(pvrtmp_1417, tmp_struct_18.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1418[2];
            
            memcpy(pvrtmp_1418, tmp_struct_18.field1, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2Prod return_19;
            
            memcpy(return_19.field0, pvrtmp_1417, sizeof(GibCursor [2]));
            memcpy(return_19.field1, pvrtmp_1418, sizeof(GibCursor [2]));
            return return_19;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1397");
            exit(1);
        }
    }
}
GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod mkList(GibCursor cursor_ptr_839[2],
                                                   GibCursor cursor_ptr_840[2],
                                                   GibInt length_24_103_145)
{
    GibCursor end_r_345 = cursor_ptr_839[1];
    GibCursor end_r_344 = cursor_ptr_839[0];
    GibCursor loc_342 = cursor_ptr_840[0];
    GibCursor loc_IntTy_343 = cursor_ptr_840[1];
    
    if (loc_IntTy_343 + 17 > end_r_345 || loc_342 + 26 > end_r_344) {
        gib_grow_region(&loc_IntTy_343, &end_r_345);
        gib_grow_region(&loc_342, &end_r_344);
    }
    
    GibCursor overwrite_reg_841[2] = {end_r_344, end_r_345};
    GibBool fltIf_124_146 = length_24_103_145 <= 0;
    
    if (fltIf_124_146) {
        GibCursor new_dloc_420 = loc_342 + 1;
        GibCursor new_floc_loc_421 = loc_IntTy_343 + 8;
        
        *(GibPackedTag *) loc_342 = 1;
        
        GibCursor writetag_842 = loc_342 + 1;
        GibCursor after_tag_843 = loc_342 + 1;
        GibCursor aft_soa_loc_847[2] = {after_tag_843, loc_IntTy_343};
        GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod return_22;
        
        memcpy(return_22.field0, overwrite_reg_841, sizeof(GibCursor [2]));
        memcpy(return_22.field1, cursor_ptr_840, sizeof(GibCursor [2]));
        memcpy(return_22.field2, aft_soa_loc_847, sizeof(GibCursor [2]));
        return return_22;
    } else {
        GibInt fltAppE_125_147 = length_24_103_145 - 1;
        GibCursor new_dloc_420 = loc_342 + 1;
        GibCursor new_floc_loc_421 = loc_IntTy_343 + 8;
        GibCursor cursor_ptr_850[2] = {new_dloc_420, new_floc_loc_421};
        
        *(GibPackedTag *) loc_342 = 0;
        
        GibCursor writetag_855 = loc_342 + 1;
        GibCursor after_tag_856 = loc_342 + 1;
        
        *(GibInt *) loc_IntTy_343 = length_24_103_145;
        
        GibCursor writecur_860 = loc_IntTy_343 + sizeof(GibInt);
        GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod tmp_struct_23 =
                                                     mkList(overwrite_reg_841, cursor_ptr_850, fltAppE_125_147);
        GibCursor pvrtmp_1424[2];
        
        memcpy(pvrtmp_1424, tmp_struct_23.field0, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1425[2];
        
        memcpy(pvrtmp_1425, tmp_struct_23.field1, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1426[2];
        
        memcpy(pvrtmp_1426, tmp_struct_23.field2, sizeof(GibCursor [2]));
        
        GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod return_24;
        
        memcpy(return_24.field0, pvrtmp_1424, sizeof(GibCursor [2]));
        memcpy(return_24.field1, cursor_ptr_840, sizeof(GibCursor [2]));
        memcpy(return_24.field2, pvrtmp_1426, sizeof(GibCursor [2]));
        return return_24;
    }
}
GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod _copy_List(GibCursor cursor_ptr_867[2],
                                                                                 GibCursor cursor_ptr_866[2],
                                                                                 GibCursor cursor_ptr_868[2],
                                                                                 GibCursor arg_59_105_149[2])
{
    GibCursor end_r_352 = cursor_ptr_866[0];
    GibCursor end_r_353 = cursor_ptr_866[1];
    GibCursor loc_IntTy_349 = cursor_ptr_868[1];
    GibCursor loc_348 = cursor_ptr_868[0];
    
    if (loc_IntTy_349 + 17 > end_r_353 || loc_348 + 26 > end_r_352) {
        gib_grow_region(&loc_IntTy_349, &end_r_353);
        gib_grow_region(&loc_348, &end_r_352);
    }
    
    GibCursor end_r_350 = cursor_ptr_867[0];
    GibCursor end_r_351 = cursor_ptr_867[1];
    GibCursor overwrite_reg_869[2] = {end_r_352, end_r_353};
    GibCursor dcon_872 = arg_59_105_149[0];
    GibPackedTag tmpval_1435 = *(GibPackedTag *) dcon_872;
    GibCursor tmpcur_1436 = dcon_872 + 1;
    
    
  switch_1490:
    ;
    switch (tmpval_1435) {
        
      case 0:
        {
            GibCursor soa_field_0_874 = arg_59_105_149[1];
            GibInt tmpval_1437 = *(GibInt *) soa_field_0_874;
            GibCursor tmpcur_1438 = soa_field_0_874 + sizeof(GibInt);
            GibCursor cursor_ptr_871[2] = {tmpcur_1436, tmpcur_1438};
            GibCursor loc_346 = arg_59_105_149[0];
            GibCursor jumpf_dloc_522 = loc_346 + 1;
            GibCursor loc_IntTy_347 = arg_59_105_149[1];
            GibCursor jumpf_floc_loc_523 = soa_field_0_874 + 8;
            GibCursor loc_430 = jumpf_dloc_522 + 0;
            GibCursor loc_429 = jumpf_floc_loc_523 + 0;
            GibCursor cursor_ptr_878[2] = {jumpf_dloc_522, jumpf_floc_loc_523};
            GibCursor new_dloc_438 = loc_348 + 1;
            GibCursor new_floc_loc_439 = loc_IntTy_349 + 8;
            GibCursor cursor_ptr_879[2] = {new_dloc_438, new_floc_loc_439};
            
            *(GibPackedTag *) loc_348 = 0;
            
            GibCursor writetag_889 = loc_348 + 1;
            GibCursor after_tag_890 = loc_348 + 1;
            
            *(GibInt *) loc_IntTy_349 = tmpval_1437;
            
            GibCursor writecur_894 = loc_IntTy_349 + sizeof(GibInt);
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_25 =
             _copy_List(cursor_ptr_867, overwrite_reg_869, cursor_ptr_879, cursor_ptr_871);
            GibCursor pvrtmp_1439[2];
            
            memcpy(pvrtmp_1439, tmp_struct_25.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1440[2];
            
            memcpy(pvrtmp_1440, tmp_struct_25.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1441[2];
            
            memcpy(pvrtmp_1441, tmp_struct_25.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1442[2];
            
            memcpy(pvrtmp_1442, tmp_struct_25.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1443[2];
            
            memcpy(pvrtmp_1443, tmp_struct_25.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_26;
            
            memcpy(return_26.field0, pvrtmp_1439, sizeof(GibCursor [2]));
            memcpy(return_26.field1, pvrtmp_1440, sizeof(GibCursor [2]));
            memcpy(return_26.field2, pvrtmp_1441, sizeof(GibCursor [2]));
            memcpy(return_26.field3, cursor_ptr_868, sizeof(GibCursor [2]));
            memcpy(return_26.field4, pvrtmp_1443, sizeof(GibCursor [2]));
            return return_26;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_900 = arg_59_105_149[1];
            GibCursor loc_346 = arg_59_105_149[0];
            GibCursor jump_dloc_527 = loc_346 + 1;
            GibCursor loc_IntTy_347 = arg_59_105_149[1];
            GibCursor jump_floc_loc_528 = loc_IntTy_347 + 0;
            GibCursor cursor_ptr_902[2] = {jump_dloc_527, jump_floc_loc_528};
            GibCursor new_dloc_438 = loc_348 + 1;
            GibCursor new_floc_loc_439 = loc_IntTy_349 + 8;
            
            *(GibPackedTag *) loc_348 = 1;
            
            GibCursor writetag_903 = loc_348 + 1;
            GibCursor after_tag_904 = loc_348 + 1;
            GibCursor aft_soa_loc_908[2] = {after_tag_904, loc_IntTy_349};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_27;
            
            memcpy(return_27.field0, cursor_ptr_867, sizeof(GibCursor [2]));
            memcpy(return_27.field1, overwrite_reg_869, sizeof(GibCursor [2]));
            memcpy(return_27.field2, cursor_ptr_902, sizeof(GibCursor [2]));
            memcpy(return_27.field3, cursor_ptr_868, sizeof(GibCursor [2]));
            memcpy(return_27.field4, aft_soa_loc_908, sizeof(GibCursor [2]));
            return return_27;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_912 = arg_59_105_149[1];
            uintptr_t tagged_tmpcur_31 = *(uintptr_t *) tmpcur_1436;
            GibCursor tmpcur_1456 = GIB_UNTAG(tagged_tmpcur_31);
            GibCursor tmpaftercur_1457 = tmpcur_1436 + 8;
            uint16_t tmptag_1458 = GIB_GET_TAG(tagged_tmpcur_31);
            GibCursor end_from_tagged_dcon_redir_922 = tmpcur_1456 +
                      tmptag_1458;
            GibCursor field_nxt_920 = soa_field_0_912 + 1;
            uintptr_t tagged_tmpcur_30 = *(uintptr_t *) field_nxt_920;
            GibCursor tmpcur_1459 = GIB_UNTAG(tagged_tmpcur_30);
            GibCursor tmpaftercur_1460 = field_nxt_920 + 8;
            uint16_t tmptag_1461 = GIB_GET_TAG(tagged_tmpcur_30);
            GibCursor end_from_tagged_fld_redir_923 = tmpcur_1459 + tmptag_1461;
            GibCursor indr_581[2] = {tmpcur_1456, tmpcur_1459};
            GibCursor loc_346 = arg_59_105_149[0];
            GibCursor jump_dloc_584 = loc_346 + 9;
            GibCursor loc_IntTy_347 = arg_59_105_149[1];
            GibCursor aft_indir_loc_590 = loc_IntTy_347 + 9;
            GibCursor cursor_ptr_924[2] = {jump_dloc_584, aft_indir_loc_590};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_28 =
             _copy_List(indr_581, overwrite_reg_869, cursor_ptr_868, indr_581);
            GibCursor pvrtmp_1462[2];
            
            memcpy(pvrtmp_1462, tmp_struct_28.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1463[2];
            
            memcpy(pvrtmp_1463, tmp_struct_28.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1464[2];
            
            memcpy(pvrtmp_1464, tmp_struct_28.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1465[2];
            
            memcpy(pvrtmp_1465, tmp_struct_28.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1466[2];
            
            memcpy(pvrtmp_1466, tmp_struct_28.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_29;
            
            memcpy(return_29.field0, cursor_ptr_867, sizeof(GibCursor [2]));
            memcpy(return_29.field1, pvrtmp_1463, sizeof(GibCursor [2]));
            memcpy(return_29.field2, cursor_ptr_924, sizeof(GibCursor [2]));
            memcpy(return_29.field3, pvrtmp_1465, sizeof(GibCursor [2]));
            memcpy(return_29.field4, pvrtmp_1466, sizeof(GibCursor [2]));
            return return_29;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_935 = arg_59_105_149[1];
            uintptr_t tagged_tmpcur_35 = *(uintptr_t *) tmpcur_1436;
            GibCursor tmpcur_1473 = GIB_UNTAG(tagged_tmpcur_35);
            GibCursor tmpaftercur_1474 = tmpcur_1436 + 8;
            uint16_t tmptag_1475 = GIB_GET_TAG(tagged_tmpcur_35);
            GibCursor end_from_tagged_dcon_redir_941 = tmpcur_1473 +
                      tmptag_1475;
            GibCursor field_nxt_940 = soa_field_0_935 + 1;
            uintptr_t tagged_tmpcur_34 = *(uintptr_t *) field_nxt_940;
            GibCursor tmpcur_1476 = GIB_UNTAG(tagged_tmpcur_34);
            GibCursor tmpaftercur_1477 = field_nxt_940 + 8;
            uint16_t tmptag_1478 = GIB_GET_TAG(tagged_tmpcur_34);
            GibCursor end_from_tagged_fld_redir_942 = tmpcur_1476 + tmptag_1478;
            GibCursor indr_581[2] = {tmpcur_1473, tmpcur_1476};
            GibCursor copy_dloc_591 = loc_348 + 0;
            GibCursor copy_floc_loc_592 = loc_IntTy_349 + 0;
            GibCursor cursor_ptr_943[2] = {copy_dloc_591, copy_floc_loc_592};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_32 =
             _copy_List(indr_581, overwrite_reg_869, cursor_ptr_943, indr_581);
            GibCursor pvrtmp_1479[2];
            
            memcpy(pvrtmp_1479, tmp_struct_32.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1480[2];
            
            memcpy(pvrtmp_1480, tmp_struct_32.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1481[2];
            
            memcpy(pvrtmp_1481, tmp_struct_32.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1482[2];
            
            memcpy(pvrtmp_1482, tmp_struct_32.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1483[2];
            
            memcpy(pvrtmp_1483, tmp_struct_32.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_33;
            
            memcpy(return_33.field0, pvrtmp_1479, sizeof(GibCursor [2]));
            memcpy(return_33.field1, pvrtmp_1480, sizeof(GibCursor [2]));
            memcpy(return_33.field2, pvrtmp_1481, sizeof(GibCursor [2]));
            memcpy(return_33.field3, pvrtmp_1482, sizeof(GibCursor [2]));
            memcpy(return_33.field4, pvrtmp_1483, sizeof(GibCursor [2]));
            return return_33;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1435");
            exit(1);
        }
    }
}
GibCursorPtr2GibCursorPtr2GibIntProd sumList(GibCursor cursor_ptr_954[2],
                                             GibCursor lst_26_110_154[2])
{
    GibCursor end_r_356 = cursor_ptr_954[0];
    GibCursor end_r_357 = cursor_ptr_954[1];
    GibCursor dcon_957 = lst_26_110_154[0];
    GibPackedTag tmpval_1491 = *(GibPackedTag *) dcon_957;
    GibCursor tmpcur_1492 = dcon_957 + 1;
    
    
  switch_1516:
    ;
    switch (tmpval_1491) {
        
      case 1:
        {
            GibCursor soa_field_0_959 = lst_26_110_154[1];
            GibCursor loc_354 = lst_26_110_154[0];
            GibCursor jump_dloc_531 = loc_354 + 1;
            GibCursor loc_IntTy_355 = lst_26_110_154[1];
            GibCursor jump_floc_loc_532 = loc_IntTy_355 + 0;
            GibCursor cursor_ptr_961[2] = {jump_dloc_531, jump_floc_loc_532};
            GibCursorPtr2GibCursorPtr2GibIntProd return_36;
            
            memcpy(return_36.field0, cursor_ptr_954, sizeof(GibCursor [2]));
            memcpy(return_36.field1, cursor_ptr_961, sizeof(GibCursor [2]));
            return_36.field2 = 0;
            return return_36;
            break;
        }
        
      case 0:
        {
            GibCursor soa_field_0_963 = lst_26_110_154[1];
            GibInt tmpval_1493 = *(GibInt *) soa_field_0_963;
            GibCursor tmpcur_1494 = soa_field_0_963 + sizeof(GibInt);
            GibCursor cursor_ptr_956[2] = {tmpcur_1492, tmpcur_1494};
            GibCursor loc_354 = lst_26_110_154[0];
            GibCursor jumpf_dloc_533 = loc_354 + 1;
            GibCursor loc_IntTy_355 = lst_26_110_154[1];
            GibCursor jumpf_floc_loc_534 = soa_field_0_963 + 8;
            GibCursor loc_450 = jumpf_dloc_533 + 0;
            GibCursor loc_449 = jumpf_floc_loc_534 + 0;
            GibCursor cursor_ptr_967[2] = {jumpf_dloc_533, jumpf_floc_loc_534};
            GibCursorPtr2GibCursorPtr2GibIntProd tmp_struct_37 =
                                                  sumList(cursor_ptr_954, cursor_ptr_956);
            GibCursor pvrtmp_1495[2];
            
            memcpy(pvrtmp_1495, tmp_struct_37.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1496[2];
            
            memcpy(pvrtmp_1496, tmp_struct_37.field1, sizeof(GibCursor [2]));
            
            GibInt pvrtmp_1497 = tmp_struct_37.field2;
            GibInt tailprim_537 = tmpval_1493 + pvrtmp_1497;
            GibCursorPtr2GibCursorPtr2GibIntProd return_38;
            
            memcpy(return_38.field0, pvrtmp_1495, sizeof(GibCursor [2]));
            memcpy(return_38.field1, pvrtmp_1496, sizeof(GibCursor [2]));
            return_38.field2 = tailprim_537;
            return return_38;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_975 = lst_26_110_154[1];
            uintptr_t tagged_tmpcur_42 = *(uintptr_t *) tmpcur_1492;
            GibCursor tmpcur_1498 = GIB_UNTAG(tagged_tmpcur_42);
            GibCursor tmpaftercur_1499 = tmpcur_1492 + 8;
            uint16_t tmptag_1500 = GIB_GET_TAG(tagged_tmpcur_42);
            GibCursor end_from_tagged_dcon_redir_985 = tmpcur_1498 +
                      tmptag_1500;
            GibCursor field_nxt_983 = soa_field_0_975 + 1;
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) field_nxt_983;
            GibCursor tmpcur_1501 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_1502 = field_nxt_983 + 8;
            uint16_t tmptag_1503 = GIB_GET_TAG(tagged_tmpcur_41);
            GibCursor end_from_tagged_fld_redir_986 = tmpcur_1501 + tmptag_1503;
            GibCursor indr_593[2] = {tmpcur_1498, tmpcur_1501};
            GibCursor loc_354 = lst_26_110_154[0];
            GibCursor jump_dloc_596 = loc_354 + 9;
            GibCursor loc_IntTy_355 = lst_26_110_154[1];
            GibCursor aft_indir_loc_602 = loc_IntTy_355 + 9;
            GibCursor cursor_ptr_987[2] = {jump_dloc_596, aft_indir_loc_602};
            GibCursorPtr2GibCursorPtr2GibIntProd tmp_struct_39 =
                                                  sumList(indr_593, indr_593);
            GibCursor pvrtmp_1504[2];
            
            memcpy(pvrtmp_1504, tmp_struct_39.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1505[2];
            
            memcpy(pvrtmp_1505, tmp_struct_39.field1, sizeof(GibCursor [2]));
            
            GibInt pvrtmp_1506 = tmp_struct_39.field2;
            GibCursorPtr2GibCursorPtr2GibIntProd return_40;
            
            memcpy(return_40.field0, cursor_ptr_954, sizeof(GibCursor [2]));
            memcpy(return_40.field1, cursor_ptr_987, sizeof(GibCursor [2]));
            return_40.field2 = pvrtmp_1506;
            return return_40;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_995 = lst_26_110_154[1];
            uintptr_t tagged_tmpcur_46 = *(uintptr_t *) tmpcur_1492;
            GibCursor tmpcur_1507 = GIB_UNTAG(tagged_tmpcur_46);
            GibCursor tmpaftercur_1508 = tmpcur_1492 + 8;
            uint16_t tmptag_1509 = GIB_GET_TAG(tagged_tmpcur_46);
            GibCursor end_from_tagged_dcon_redir_1001 = tmpcur_1507 +
                      tmptag_1509;
            GibCursor field_nxt_1000 = soa_field_0_995 + 1;
            uintptr_t tagged_tmpcur_45 = *(uintptr_t *) field_nxt_1000;
            GibCursor tmpcur_1510 = GIB_UNTAG(tagged_tmpcur_45);
            GibCursor tmpaftercur_1511 = field_nxt_1000 + 8;
            uint16_t tmptag_1512 = GIB_GET_TAG(tagged_tmpcur_45);
            GibCursor end_from_tagged_fld_redir_1002 = tmpcur_1510 +
                      tmptag_1512;
            GibCursor indr_593[2] = {tmpcur_1507, tmpcur_1510};
            GibCursorPtr2GibCursorPtr2GibIntProd tmp_struct_43 =
                                                  sumList(indr_593, indr_593);
            GibCursor pvrtmp_1513[2];
            
            memcpy(pvrtmp_1513, tmp_struct_43.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1514[2];
            
            memcpy(pvrtmp_1514, tmp_struct_43.field1, sizeof(GibCursor [2]));
            
            GibInt pvrtmp_1515 = tmp_struct_43.field2;
            GibCursorPtr2GibCursorPtr2GibIntProd return_44;
            
            memcpy(return_44.field0, pvrtmp_1513, sizeof(GibCursor [2]));
            memcpy(return_44.field1, pvrtmp_1514, sizeof(GibCursor [2]));
            return_44.field2 = pvrtmp_1515;
            return return_44;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1491");
            exit(1);
        }
    }
}
GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod _copy_without_ptrs_List(GibCursor cursor_ptr_1011[2],
                                                                                              GibCursor cursor_ptr_1010[2],
                                                                                              GibCursor cursor_ptr_1012[2],
                                                                                              GibCursor arg_64_115_158[2])
{
    GibCursor end_r_362 = cursor_ptr_1011[0];
    GibCursor end_r_363 = cursor_ptr_1011[1];
    GibCursor end_r_364 = cursor_ptr_1010[0];
    GibCursor end_r_365 = cursor_ptr_1010[1];
    GibCursor dcon_1015 = arg_64_115_158[0];
    GibPackedTag tmpval_1517 = *(GibPackedTag *) dcon_1015;
    GibCursor tmpcur_1518 = dcon_1015 + 1;
    
    
  switch_1572:
    ;
    switch (tmpval_1517) {
        
      case 0:
        {
            GibCursor soa_field_0_1017 = arg_64_115_158[1];
            GibInt tmpval_1519 = *(GibInt *) soa_field_0_1017;
            GibCursor tmpcur_1520 = soa_field_0_1017 + sizeof(GibInt);
            GibCursor cursor_ptr_1014[2] = {tmpcur_1518, tmpcur_1520};
            GibCursor loc_358 = arg_64_115_158[0];
            GibCursor jumpf_dloc_538 = loc_358 + 1;
            GibCursor loc_IntTy_359 = arg_64_115_158[1];
            GibCursor jumpf_floc_loc_539 = soa_field_0_1017 + 8;
            GibCursor loc_459 = jumpf_dloc_538 + 0;
            GibCursor loc_458 = jumpf_floc_loc_539 + 0;
            GibCursor cursor_ptr_1021[2] = {jumpf_dloc_538, jumpf_floc_loc_539};
            GibCursor loc_IntTy_361 = cursor_ptr_1012[1];
            GibCursor new_floc_loc_468 = loc_IntTy_361 + 8;
            GibCursor loc_360 = cursor_ptr_1012[0];
            GibCursor new_dloc_467 = loc_360 + 1;
            GibCursor cursor_ptr_1022[2] = {new_dloc_467, new_floc_loc_468};
            
            *(GibPackedTag *) loc_360 = 0;
            
            GibCursor writetag_1032 = loc_360 + 1;
            GibCursor after_tag_1033 = loc_360 + 1;
            
            *(GibInt *) loc_IntTy_361 = tmpval_1519;
            
            GibCursor writecur_1037 = loc_IntTy_361 + sizeof(GibInt);
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_47 =
             _copy_without_ptrs_List(cursor_ptr_1011, cursor_ptr_1010, cursor_ptr_1022, cursor_ptr_1014);
            GibCursor pvrtmp_1521[2];
            
            memcpy(pvrtmp_1521, tmp_struct_47.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1522[2];
            
            memcpy(pvrtmp_1522, tmp_struct_47.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1523[2];
            
            memcpy(pvrtmp_1523, tmp_struct_47.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1524[2];
            
            memcpy(pvrtmp_1524, tmp_struct_47.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1525[2];
            
            memcpy(pvrtmp_1525, tmp_struct_47.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_48;
            
            memcpy(return_48.field0, pvrtmp_1521, sizeof(GibCursor [2]));
            memcpy(return_48.field1, pvrtmp_1522, sizeof(GibCursor [2]));
            memcpy(return_48.field2, pvrtmp_1523, sizeof(GibCursor [2]));
            memcpy(return_48.field3, cursor_ptr_1012, sizeof(GibCursor [2]));
            memcpy(return_48.field4, pvrtmp_1525, sizeof(GibCursor [2]));
            return return_48;
            break;
        }
        
      case 1:
        {
            GibCursor soa_field_0_1043 = arg_64_115_158[1];
            GibCursor loc_358 = arg_64_115_158[0];
            GibCursor jump_dloc_543 = loc_358 + 1;
            GibCursor loc_IntTy_359 = arg_64_115_158[1];
            GibCursor jump_floc_loc_544 = loc_IntTy_359 + 0;
            GibCursor cursor_ptr_1045[2] = {jump_dloc_543, jump_floc_loc_544};
            GibCursor loc_IntTy_361 = cursor_ptr_1012[1];
            GibCursor new_floc_loc_468 = loc_IntTy_361 + 8;
            GibCursor loc_360 = cursor_ptr_1012[0];
            GibCursor new_dloc_467 = loc_360 + 1;
            
            *(GibPackedTag *) loc_360 = 1;
            
            GibCursor writetag_1046 = loc_360 + 1;
            GibCursor after_tag_1047 = loc_360 + 1;
            GibCursor aft_soa_loc_1051[2] = {after_tag_1047, loc_IntTy_361};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_49;
            
            memcpy(return_49.field0, cursor_ptr_1011, sizeof(GibCursor [2]));
            memcpy(return_49.field1, cursor_ptr_1010, sizeof(GibCursor [2]));
            memcpy(return_49.field2, cursor_ptr_1045, sizeof(GibCursor [2]));
            memcpy(return_49.field3, cursor_ptr_1012, sizeof(GibCursor [2]));
            memcpy(return_49.field4, aft_soa_loc_1051, sizeof(GibCursor [2]));
            return return_49;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1055 = arg_64_115_158[1];
            uintptr_t tagged_tmpcur_53 = *(uintptr_t *) tmpcur_1518;
            GibCursor tmpcur_1538 = GIB_UNTAG(tagged_tmpcur_53);
            GibCursor tmpaftercur_1539 = tmpcur_1518 + 8;
            uint16_t tmptag_1540 = GIB_GET_TAG(tagged_tmpcur_53);
            GibCursor end_from_tagged_dcon_redir_1065 = tmpcur_1538 +
                      tmptag_1540;
            GibCursor field_nxt_1063 = soa_field_0_1055 + 1;
            uintptr_t tagged_tmpcur_52 = *(uintptr_t *) field_nxt_1063;
            GibCursor tmpcur_1541 = GIB_UNTAG(tagged_tmpcur_52);
            GibCursor tmpaftercur_1542 = field_nxt_1063 + 8;
            uint16_t tmptag_1543 = GIB_GET_TAG(tagged_tmpcur_52);
            GibCursor end_from_tagged_fld_redir_1066 = tmpcur_1541 +
                      tmptag_1543;
            GibCursor indr_603[2] = {tmpcur_1538, tmpcur_1541};
            GibCursor loc_358 = arg_64_115_158[0];
            GibCursor jump_dloc_606 = loc_358 + 9;
            GibCursor loc_IntTy_359 = arg_64_115_158[1];
            GibCursor aft_indir_loc_612 = loc_IntTy_359 + 9;
            GibCursor cursor_ptr_1067[2] = {jump_dloc_606, aft_indir_loc_612};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_50 =
             _copy_without_ptrs_List(indr_603, cursor_ptr_1010, cursor_ptr_1012, indr_603);
            GibCursor pvrtmp_1544[2];
            
            memcpy(pvrtmp_1544, tmp_struct_50.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1545[2];
            
            memcpy(pvrtmp_1545, tmp_struct_50.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1546[2];
            
            memcpy(pvrtmp_1546, tmp_struct_50.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1547[2];
            
            memcpy(pvrtmp_1547, tmp_struct_50.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1548[2];
            
            memcpy(pvrtmp_1548, tmp_struct_50.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_51;
            
            memcpy(return_51.field0, cursor_ptr_1011, sizeof(GibCursor [2]));
            memcpy(return_51.field1, pvrtmp_1545, sizeof(GibCursor [2]));
            memcpy(return_51.field2, cursor_ptr_1067, sizeof(GibCursor [2]));
            memcpy(return_51.field3, pvrtmp_1547, sizeof(GibCursor [2]));
            memcpy(return_51.field4, pvrtmp_1548, sizeof(GibCursor [2]));
            return return_51;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1078 = arg_64_115_158[1];
            uintptr_t tagged_tmpcur_57 = *(uintptr_t *) tmpcur_1518;
            GibCursor tmpcur_1555 = GIB_UNTAG(tagged_tmpcur_57);
            GibCursor tmpaftercur_1556 = tmpcur_1518 + 8;
            uint16_t tmptag_1557 = GIB_GET_TAG(tagged_tmpcur_57);
            GibCursor end_from_tagged_dcon_redir_1084 = tmpcur_1555 +
                      tmptag_1557;
            GibCursor field_nxt_1083 = soa_field_0_1078 + 1;
            uintptr_t tagged_tmpcur_56 = *(uintptr_t *) field_nxt_1083;
            GibCursor tmpcur_1558 = GIB_UNTAG(tagged_tmpcur_56);
            GibCursor tmpaftercur_1559 = field_nxt_1083 + 8;
            uint16_t tmptag_1560 = GIB_GET_TAG(tagged_tmpcur_56);
            GibCursor end_from_tagged_fld_redir_1085 = tmpcur_1558 +
                      tmptag_1560;
            GibCursor indr_603[2] = {tmpcur_1555, tmpcur_1558};
            GibCursor loc_360 = cursor_ptr_1012[0];
            GibCursor loc_IntTy_361 = cursor_ptr_1012[1];
            GibCursor copy_dloc_613 = loc_360 + 0;
            GibCursor copy_floc_loc_614 = loc_IntTy_361 + 0;
            GibCursor cursor_ptr_1086[2] = {copy_dloc_613, copy_floc_loc_614};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_54 =
             _copy_without_ptrs_List(indr_603, cursor_ptr_1010, cursor_ptr_1086, indr_603);
            GibCursor pvrtmp_1561[2];
            
            memcpy(pvrtmp_1561, tmp_struct_54.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1562[2];
            
            memcpy(pvrtmp_1562, tmp_struct_54.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1563[2];
            
            memcpy(pvrtmp_1563, tmp_struct_54.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1564[2];
            
            memcpy(pvrtmp_1564, tmp_struct_54.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1565[2];
            
            memcpy(pvrtmp_1565, tmp_struct_54.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_55;
            
            memcpy(return_55.field0, pvrtmp_1561, sizeof(GibCursor [2]));
            memcpy(return_55.field1, pvrtmp_1562, sizeof(GibCursor [2]));
            memcpy(return_55.field2, pvrtmp_1563, sizeof(GibCursor [2]));
            memcpy(return_55.field3, pvrtmp_1564, sizeof(GibCursor [2]));
            memcpy(return_55.field4, pvrtmp_1565, sizeof(GibCursor [2]));
            return return_55;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1517");
            exit(1);
        }
    }
}
GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod add1(GibCursor cursor_ptr_1098[2],
                                                                           GibCursor cursor_ptr_1097[2],
                                                                           GibCursor cursor_ptr_1099[2],
                                                                           GibCursor lst_31_120_163[2])
{
    GibCursor end_r_373 = cursor_ptr_1097[1];
    GibCursor end_r_372 = cursor_ptr_1097[0];
    GibCursor loc_IntTy_369 = cursor_ptr_1099[1];
    GibCursor loc_368 = cursor_ptr_1099[0];
    
    if (loc_IntTy_369 + 17 > end_r_373 || loc_368 + 26 > end_r_372) {
        gib_grow_region(&loc_IntTy_369, &end_r_373);
        gib_grow_region(&loc_368, &end_r_372);
    }
    
    GibCursor end_r_370 = cursor_ptr_1098[0];
    GibCursor end_r_371 = cursor_ptr_1098[1];
    GibCursor overwrite_reg_1100[2] = {end_r_372, end_r_373};
    GibCursor dcon_1103 = lst_31_120_163[0];
    GibPackedTag tmpval_1573 = *(GibPackedTag *) dcon_1103;
    GibCursor tmpcur_1574 = dcon_1103 + 1;
    
    
  switch_1628:
    ;
    switch (tmpval_1573) {
        
      case 1:
        {
            GibCursor soa_field_0_1105 = lst_31_120_163[1];
            GibCursor loc_366 = lst_31_120_163[0];
            GibCursor jump_dloc_546 = loc_366 + 1;
            GibCursor loc_IntTy_367 = lst_31_120_163[1];
            GibCursor jump_floc_loc_547 = loc_IntTy_367 + 0;
            GibCursor cursor_ptr_1107[2] = {jump_dloc_546, jump_floc_loc_547};
            GibCursor new_dloc_489 = loc_368 + 1;
            GibCursor new_floc_loc_490 = loc_IntTy_369 + 8;
            
            *(GibPackedTag *) loc_368 = 1;
            
            GibCursor writetag_1108 = loc_368 + 1;
            GibCursor after_tag_1109 = loc_368 + 1;
            GibCursor aft_soa_loc_1113[2] = {after_tag_1109, loc_IntTy_369};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_58;
            
            memcpy(return_58.field0, cursor_ptr_1098, sizeof(GibCursor [2]));
            memcpy(return_58.field1, overwrite_reg_1100, sizeof(GibCursor [2]));
            memcpy(return_58.field2, cursor_ptr_1107, sizeof(GibCursor [2]));
            memcpy(return_58.field3, cursor_ptr_1099, sizeof(GibCursor [2]));
            memcpy(return_58.field4, aft_soa_loc_1113, sizeof(GibCursor [2]));
            return return_58;
            break;
        }
        
      case 0:
        {
            GibCursor soa_field_0_1117 = lst_31_120_163[1];
            GibInt tmpval_1579 = *(GibInt *) soa_field_0_1117;
            GibCursor tmpcur_1580 = soa_field_0_1117 + sizeof(GibInt);
            GibCursor cursor_ptr_1102[2] = {tmpcur_1574, tmpcur_1580};
            GibCursor loc_366 = lst_31_120_163[0];
            GibCursor jumpf_dloc_549 = loc_366 + 1;
            GibCursor loc_IntTy_367 = lst_31_120_163[1];
            GibCursor jumpf_floc_loc_550 = soa_field_0_1117 + 8;
            GibCursor loc_481 = jumpf_dloc_549 + 0;
            GibCursor loc_480 = jumpf_floc_loc_550 + 0;
            GibCursor cursor_ptr_1121[2] = {jumpf_dloc_549, jumpf_floc_loc_550};
            GibInt i1_34_123_166 = tmpval_1579 + 1;
            GibCursor new_dloc_489 = loc_368 + 1;
            GibCursor new_floc_loc_490 = loc_IntTy_369 + 8;
            GibCursor cursor_ptr_1122[2] = {new_dloc_489, new_floc_loc_490};
            
            *(GibPackedTag *) loc_368 = 0;
            
            GibCursor writetag_1132 = loc_368 + 1;
            GibCursor after_tag_1133 = loc_368 + 1;
            
            *(GibInt *) loc_IntTy_369 = i1_34_123_166;
            
            GibCursor writecur_1137 = loc_IntTy_369 + sizeof(GibInt);
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_59 =
             add1(cursor_ptr_1098, overwrite_reg_1100, cursor_ptr_1122, cursor_ptr_1102);
            GibCursor pvrtmp_1581[2];
            
            memcpy(pvrtmp_1581, tmp_struct_59.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1582[2];
            
            memcpy(pvrtmp_1582, tmp_struct_59.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1583[2];
            
            memcpy(pvrtmp_1583, tmp_struct_59.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1584[2];
            
            memcpy(pvrtmp_1584, tmp_struct_59.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1585[2];
            
            memcpy(pvrtmp_1585, tmp_struct_59.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_60;
            
            memcpy(return_60.field0, pvrtmp_1581, sizeof(GibCursor [2]));
            memcpy(return_60.field1, pvrtmp_1582, sizeof(GibCursor [2]));
            memcpy(return_60.field2, pvrtmp_1583, sizeof(GibCursor [2]));
            memcpy(return_60.field3, cursor_ptr_1099, sizeof(GibCursor [2]));
            memcpy(return_60.field4, pvrtmp_1585, sizeof(GibCursor [2]));
            return return_60;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            GibCursor soa_field_0_1143 = lst_31_120_163[1];
            uintptr_t tagged_tmpcur_64 = *(uintptr_t *) tmpcur_1574;
            GibCursor tmpcur_1594 = GIB_UNTAG(tagged_tmpcur_64);
            GibCursor tmpaftercur_1595 = tmpcur_1574 + 8;
            uint16_t tmptag_1596 = GIB_GET_TAG(tagged_tmpcur_64);
            GibCursor end_from_tagged_dcon_redir_1153 = tmpcur_1594 +
                      tmptag_1596;
            GibCursor field_nxt_1151 = soa_field_0_1143 + 1;
            uintptr_t tagged_tmpcur_63 = *(uintptr_t *) field_nxt_1151;
            GibCursor tmpcur_1597 = GIB_UNTAG(tagged_tmpcur_63);
            GibCursor tmpaftercur_1598 = field_nxt_1151 + 8;
            uint16_t tmptag_1599 = GIB_GET_TAG(tagged_tmpcur_63);
            GibCursor end_from_tagged_fld_redir_1154 = tmpcur_1597 +
                      tmptag_1599;
            GibCursor indr_615[2] = {tmpcur_1594, tmpcur_1597};
            GibCursor loc_366 = lst_31_120_163[0];
            GibCursor jump_dloc_618 = loc_366 + 9;
            GibCursor loc_IntTy_367 = lst_31_120_163[1];
            GibCursor aft_indir_loc_624 = loc_IntTy_367 + 9;
            GibCursor cursor_ptr_1155[2] = {jump_dloc_618, aft_indir_loc_624};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_61 =
             add1(indr_615, overwrite_reg_1100, cursor_ptr_1099, indr_615);
            GibCursor pvrtmp_1600[2];
            
            memcpy(pvrtmp_1600, tmp_struct_61.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1601[2];
            
            memcpy(pvrtmp_1601, tmp_struct_61.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1602[2];
            
            memcpy(pvrtmp_1602, tmp_struct_61.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1603[2];
            
            memcpy(pvrtmp_1603, tmp_struct_61.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1604[2];
            
            memcpy(pvrtmp_1604, tmp_struct_61.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_62;
            
            memcpy(return_62.field0, cursor_ptr_1098, sizeof(GibCursor [2]));
            memcpy(return_62.field1, pvrtmp_1601, sizeof(GibCursor [2]));
            memcpy(return_62.field2, cursor_ptr_1155, sizeof(GibCursor [2]));
            memcpy(return_62.field3, pvrtmp_1603, sizeof(GibCursor [2]));
            memcpy(return_62.field4, pvrtmp_1604, sizeof(GibCursor [2]));
            return return_62;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            GibCursor soa_field_0_1166 = lst_31_120_163[1];
            uintptr_t tagged_tmpcur_68 = *(uintptr_t *) tmpcur_1574;
            GibCursor tmpcur_1611 = GIB_UNTAG(tagged_tmpcur_68);
            GibCursor tmpaftercur_1612 = tmpcur_1574 + 8;
            uint16_t tmptag_1613 = GIB_GET_TAG(tagged_tmpcur_68);
            GibCursor end_from_tagged_dcon_redir_1172 = tmpcur_1611 +
                      tmptag_1613;
            GibCursor field_nxt_1171 = soa_field_0_1166 + 1;
            uintptr_t tagged_tmpcur_67 = *(uintptr_t *) field_nxt_1171;
            GibCursor tmpcur_1614 = GIB_UNTAG(tagged_tmpcur_67);
            GibCursor tmpaftercur_1615 = field_nxt_1171 + 8;
            uint16_t tmptag_1616 = GIB_GET_TAG(tagged_tmpcur_67);
            GibCursor end_from_tagged_fld_redir_1173 = tmpcur_1614 +
                      tmptag_1616;
            GibCursor indr_615[2] = {tmpcur_1611, tmpcur_1614};
            GibCursor copy_dloc_625 = loc_368 + 0;
            GibCursor copy_floc_loc_626 = loc_IntTy_369 + 0;
            GibCursor cursor_ptr_1174[2] = {copy_dloc_625, copy_floc_loc_626};
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            tmp_struct_65 =
             add1(indr_615, overwrite_reg_1100, cursor_ptr_1174, indr_615);
            GibCursor pvrtmp_1617[2];
            
            memcpy(pvrtmp_1617, tmp_struct_65.field0, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1618[2];
            
            memcpy(pvrtmp_1618, tmp_struct_65.field1, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1619[2];
            
            memcpy(pvrtmp_1619, tmp_struct_65.field2, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1620[2];
            
            memcpy(pvrtmp_1620, tmp_struct_65.field3, sizeof(GibCursor [2]));
            
            GibCursor pvrtmp_1621[2];
            
            memcpy(pvrtmp_1621, tmp_struct_65.field4, sizeof(GibCursor [2]));
            
            GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
            return_66;
            
            memcpy(return_66.field0, pvrtmp_1617, sizeof(GibCursor [2]));
            memcpy(return_66.field1, pvrtmp_1618, sizeof(GibCursor [2]));
            memcpy(return_66.field2, pvrtmp_1619, sizeof(GibCursor [2]));
            memcpy(return_66.field3, pvrtmp_1620, sizeof(GibCursor [2]));
            memcpy(return_66.field4, pvrtmp_1621, sizeof(GibCursor [2]));
            return return_66;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1573");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_82 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_1339 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_395 = region_1339.start;
    GibCursor end_r_395 = region_1339.end;
    GibChunk region_1340 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_396 = region_1340.start;
    GibCursor end_r_396 = region_1340.end;
    GibCursor reg_ptr_1184[2] = {r_395, r_396};
    GibCursor reg_cursor_ptr_1185[2] = {end_r_395, end_r_396};
    GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod tmp_struct_69 =
                                                 mkList(reg_cursor_ptr_1185, reg_ptr_1184, 10000000);
    GibCursor pvrtmp_1341[2];
    
    memcpy(pvrtmp_1341, tmp_struct_69.field0, sizeof(GibCursor [2]));
    
    GibCursor pvrtmp_1342[2];
    
    memcpy(pvrtmp_1342, tmp_struct_69.field1, sizeof(GibCursor [2]));
    
    GibCursor pvrtmp_1343[2];
    
    memcpy(pvrtmp_1343, tmp_struct_69.field2, sizeof(GibCursor [2]));
    
    GibChunk region_1348 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_393 = region_1348.start;
    GibCursor end_r_393 = region_1348.end;
    GibChunk region_1349 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_394 = region_1349.start;
    GibCursor end_r_394 = region_1349.end;
    GibCursor reg_ptr_1191[2] = {r_393, r_394};
    GibCursor reg_cursor_ptr_1192[2] = {end_r_393, end_r_394};
    GibCursor pvrtmp_1361[2];
    GibCursor pvrtmp_1362[2];
    GibCursor pvrtmp_1363[2];
    GibVector *times_74 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_1361;
    struct timespec end_pvrtmp_1361;
    
    for (long long iters_pvrtmp_1361 = 0; iters_pvrtmp_1361 <
         gib_get_iters_param(); iters_pvrtmp_1361++) {
        if (iters_pvrtmp_1361 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_1361);
        
        GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2GibCursorPtr2Prod
        tmp_struct_70 =
         add1(pvrtmp_1341, reg_cursor_ptr_1192, reg_ptr_1191, pvrtmp_1342);
        GibCursor pvrtmp_1350[2];
        
        memcpy(pvrtmp_1350, tmp_struct_70.field0, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1351[2];
        
        memcpy(pvrtmp_1351, tmp_struct_70.field1, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1352[2];
        
        memcpy(pvrtmp_1352, tmp_struct_70.field2, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1353[2];
        
        memcpy(pvrtmp_1353, tmp_struct_70.field3, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1354[2];
        
        memcpy(pvrtmp_1354, tmp_struct_70.field4, sizeof(GibCursor [2]));
        memcpy(pvrtmp_1361, pvrtmp_1351, sizeof(GibCursor [2]));
        memcpy(pvrtmp_1362, pvrtmp_1353, sizeof(GibCursor [2]));
        memcpy(pvrtmp_1363, pvrtmp_1354, sizeof(GibCursor [2]));
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_1361);
        if (iters_pvrtmp_1361 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_71 = gib_difftimespecs(&begin_pvrtmp_1361,
                                               &end_pvrtmp_1361);
        
        printf("itertime: %lf\n", itertime_71);
        gib_vector_inplace_update(times_74, iters_pvrtmp_1361, &itertime_71);
    }
    gib_vector_inplace_sort(times_74, gib_compare_doubles);
    
    double *tmp_75 = (double *) gib_vector_nth(times_74, gib_get_iters_param() /
                                               2);
    double selftimed_73 = *tmp_75;
    double batchtime_72 = gib_sum_timing_array(times_74);
    
    gib_print_timing_array(times_74);
    gib_vector_free(times_74);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_72);
    printf("SELFTIMED: %e\n", selftimed_73);
    
    GibInt timed_1250;
    GibVector *times_80 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_1250;
    struct timespec end_timed_1250;
    
    for (long long iters_timed_1250 = 0; iters_timed_1250 <
         gib_get_iters_param(); iters_timed_1250++) {
        if (iters_timed_1250 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_1250);
        
        GibCursorPtr2GibCursorPtr2GibIntProd tmp_struct_76 =
                                              sumList(reg_cursor_ptr_1192, pvrtmp_1362);
        GibCursor pvrtmp_1371[2];
        
        memcpy(pvrtmp_1371, tmp_struct_76.field0, sizeof(GibCursor [2]));
        
        GibCursor pvrtmp_1372[2];
        
        memcpy(pvrtmp_1372, tmp_struct_76.field1, sizeof(GibCursor [2]));
        
        GibInt pvrtmp_1373 = tmp_struct_76.field2;
        
        timed_1250 = pvrtmp_1373;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_1250);
        if (iters_timed_1250 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_77 = gib_difftimespecs(&begin_timed_1250,
                                               &end_timed_1250);
        
        printf("itertime: %lf\n", itertime_77);
        gib_vector_inplace_update(times_80, iters_timed_1250, &itertime_77);
    }
    gib_vector_inplace_sort(times_80, gib_compare_doubles);
    
    double *tmp_81 = (double *) gib_vector_nth(times_80, gib_get_iters_param() /
                                               2);
    double selftimed_79 = *tmp_81;
    double batchtime_78 = gib_sum_timing_array(times_80);
    
    gib_print_timing_array(times_80);
    gib_vector_free(times_80);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_78);
    printf("SELFTIMED: %e\n", selftimed_79);
    printf("%ld", timed_1250);
    printf("\n");
    
    int exit_83 = gib_exit();
    
    return exit_83;
}