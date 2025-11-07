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
GibCursorGibCursorProd _print_List(GibCursor end_r_280,
                                   GibCursor arg_74_88_130);
GibCursorGibCursorProd _traverse_List(GibCursor end_r_283,
                                      GibCursor arg_69_99_141);
GibCursorGibCursorGibCursorProd mkList(GibCursor end_r_286, GibCursor loc_284,
                                       GibInt length_24_103_145);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_List(GibCursor end_r_290, GibCursor end_r_292, GibCursor loc_288,
           GibCursor arg_59_105_149);
GibCursorGibCursorGibIntProd sumList(GibCursor end_r_295,
                                     GibCursor lst_26_110_154);
GibCursorGibCursorGibCursorGibCursorGibCursorProd
_copy_without_ptrs_List(GibCursor end_r_299, GibCursor end_r_301,
                        GibCursor loc_297, GibCursor arg_64_115_158);
GibCursorGibCursorGibCursorGibCursorGibCursorProd add1(GibCursor end_r_305,
                                                       GibCursor end_r_307,
                                                       GibCursor loc_303,
                                                       GibCursor lst_31_120_163);
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
    gib_add_symbol(827, ")");
    gib_add_symbol(828, "(Nil");
    gib_add_symbol(829, "(Cons");
    gib_add_symbol(830, " ->r ");
    gib_add_symbol(831, " ->i ");
    gib_add_symbol(832, " ");
}
GibCursorGibCursorProd _print_List(GibCursor end_r_280, GibCursor arg_74_88_130)
{
    GibPackedTag tmpval_866 = *(GibPackedTag *) arg_74_88_130;
    GibCursor tmpcur_867 = arg_74_88_130 + 1;
    
    
  switch_882:
    ;
    switch (tmpval_866) {
        
      case 0:
        {
            GibInt tmpval_868 = *(GibInt *) tmpcur_867;
            GibCursor tmpcur_869 = tmpcur_867 + sizeof(GibInt);
            GibCursor jump_394 = tmpcur_867 + 8;
            unsigned char wildcard_79_91_133 = gib_print_symbol(829);
            unsigned char wildcard_82_92_134 = gib_print_symbol(832);
            unsigned char y_77_93_135 = printf("%ld", tmpval_868);
            unsigned char wildcard_81_94_136 = gib_print_symbol(832);
            GibCursorGibCursorProd tmp_struct_0 =
                                    _print_List(end_r_280, tmpcur_869);
            GibCursor pvrtmp_870 = tmp_struct_0.field0;
            GibCursor pvrtmp_871 = tmp_struct_0.field1;
            unsigned char wildcard_80_96_138 = gib_print_symbol(827);
            GibCursorGibCursorProd return_1;
            
            return_1.field0 = pvrtmp_870;
            return_1.field1 = pvrtmp_871;
            return return_1;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_397 = arg_74_88_130 + 1;
            unsigned char wildcard_83_97_139 = gib_print_symbol(828);
            unsigned char wildcard_84_98_140 = gib_print_symbol(827);
            GibCursorGibCursorProd return_2;
            
            return_2.field0 = end_r_280;
            return_2.field1 = jump_loc_397;
            return return_2;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_5 = *(uintptr_t *) tmpcur_867;
            GibCursor tmpcur_872 = GIB_UNTAG(tagged_tmpcur_5);
            GibCursor tmpaftercur_873 = tmpcur_867 + 8;
            uint16_t tmptag_874 = GIB_GET_TAG(tagged_tmpcur_5);
            GibCursor end_from_tagged_indr_431 = tmpcur_872 + tmptag_874;
            GibCursor jump_loc_433 = tmpcur_867 + 8;
            unsigned char wildcard_436 = gib_print_symbol(831);
            GibCursorGibCursorProd tmp_struct_3 =
                                    _print_List(tmpcur_872, tmpcur_872);
            GibCursor pvrtmp_875 = tmp_struct_3.field0;
            GibCursor pvrtmp_876 = tmp_struct_3.field1;
            GibCursorGibCursorProd return_4;
            
            return_4.field0 = end_r_280;
            return_4.field1 = jump_loc_433;
            return return_4;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_8 = *(uintptr_t *) tmpcur_867;
            GibCursor tmpcur_877 = GIB_UNTAG(tagged_tmpcur_8);
            GibCursor tmpaftercur_878 = tmpcur_867 + 8;
            uint16_t tmptag_879 = GIB_GET_TAG(tagged_tmpcur_8);
            GibCursor end_from_tagged_indr_431 = tmpcur_877 + tmptag_879;
            unsigned char wildcard_436 = gib_print_symbol(830);
            GibCursorGibCursorProd tmp_struct_6 =
                                    _print_List(tmpcur_877, tmpcur_877);
            GibCursor pvrtmp_880 = tmp_struct_6.field0;
            GibCursor pvrtmp_881 = tmp_struct_6.field1;
            GibCursorGibCursorProd return_7;
            
            return_7.field0 = pvrtmp_880;
            return_7.field1 = pvrtmp_881;
            return return_7;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_866");
            exit(1);
        }
    }
}
GibCursorGibCursorProd _traverse_List(GibCursor end_r_283,
                                      GibCursor arg_69_99_141)
{
    GibPackedTag tmpval_883 = *(GibPackedTag *) arg_69_99_141;
    GibCursor tmpcur_884 = arg_69_99_141 + 1;
    
    
  switch_899:
    ;
    switch (tmpval_883) {
        
      case 0:
        {
            GibInt tmpval_885 = *(GibInt *) tmpcur_884;
            GibCursor tmpcur_886 = tmpcur_884 + sizeof(GibInt);
            GibCursor jump_399 = tmpcur_884 + 8;
            GibCursorGibCursorProd tmp_struct_9 =
                                    _traverse_List(end_r_283, tmpcur_886);
            GibCursor pvrtmp_887 = tmp_struct_9.field0;
            GibCursor pvrtmp_888 = tmp_struct_9.field1;
            GibCursorGibCursorProd return_10;
            
            return_10.field0 = pvrtmp_887;
            return_10.field1 = pvrtmp_888;
            return return_10;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_402 = arg_69_99_141 + 1;
            GibCursorGibCursorProd return_11;
            
            return_11.field0 = end_r_283;
            return_11.field1 = jump_loc_402;
            return return_11;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_14 = *(uintptr_t *) tmpcur_884;
            GibCursor tmpcur_889 = GIB_UNTAG(tagged_tmpcur_14);
            GibCursor tmpaftercur_890 = tmpcur_884 + 8;
            uint16_t tmptag_891 = GIB_GET_TAG(tagged_tmpcur_14);
            GibCursor end_from_tagged_indr_437 = tmpcur_889 + tmptag_891;
            GibCursor jump_loc_439 = tmpcur_884 + 8;
            GibCursorGibCursorProd tmp_struct_12 =
                                    _traverse_List(tmpcur_889, tmpcur_889);
            GibCursor pvrtmp_892 = tmp_struct_12.field0;
            GibCursor pvrtmp_893 = tmp_struct_12.field1;
            GibCursorGibCursorProd return_13;
            
            return_13.field0 = end_r_283;
            return_13.field1 = jump_loc_439;
            return return_13;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_17 = *(uintptr_t *) tmpcur_884;
            GibCursor tmpcur_894 = GIB_UNTAG(tagged_tmpcur_17);
            GibCursor tmpaftercur_895 = tmpcur_884 + 8;
            uint16_t tmptag_896 = GIB_GET_TAG(tagged_tmpcur_17);
            GibCursor end_from_tagged_indr_437 = tmpcur_894 + tmptag_896;
            GibCursorGibCursorProd tmp_struct_15 =
                                    _traverse_List(tmpcur_894, tmpcur_894);
            GibCursor pvrtmp_897 = tmp_struct_15.field0;
            GibCursor pvrtmp_898 = tmp_struct_15.field1;
            GibCursorGibCursorProd return_16;
            
            return_16.field0 = pvrtmp_897;
            return_16.field1 = pvrtmp_898;
            return return_16;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_883");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorProd mkList(GibCursor end_r_286, GibCursor loc_284,
                                       GibInt length_24_103_145)
{
    if (loc_284 + 18 > end_r_286) {
        gib_grow_region(&loc_284, &end_r_286);
    }
    
    GibBool fltIf_124_146 = length_24_103_145 <= 0;
    
    if (fltIf_124_146) {
        *(GibPackedTag *) loc_284 = 1;
        
        GibCursor writetag_563 = loc_284 + 1;
        GibCursor after_tag_564 = loc_284 + 1;
        GibCursorGibCursorGibCursorProd return_18;
        
        return_18.field0 = end_r_286;
        return_18.field1 = loc_284;
        return_18.field2 = after_tag_564;
        return return_18;
    } else {
        GibInt fltAppE_125_147 = length_24_103_145 - 1;
        GibCursor loc_335 = loc_284 + 1;
        GibCursor loc_336 = loc_335 + 8;
        
        *(GibPackedTag *) loc_284 = 0;
        
        GibCursor writetag_572 = loc_284 + 1;
        GibCursor after_tag_573 = loc_284 + 1;
        
        *(GibInt *) after_tag_573 = length_24_103_145;
        
        GibCursor writecur_577 = after_tag_573 + sizeof(GibInt);
        GibCursorGibCursorGibCursorProd tmp_struct_19 =
                                         mkList(end_r_286, loc_336, fltAppE_125_147);
        GibCursor pvrtmp_904 = tmp_struct_19.field0;
        GibCursor pvrtmp_905 = tmp_struct_19.field1;
        GibCursor pvrtmp_906 = tmp_struct_19.field2;
        GibCursorGibCursorGibCursorProd return_20;
        
        return_20.field0 = pvrtmp_904;
        return_20.field1 = loc_284;
        return_20.field2 = pvrtmp_906;
        return return_20;
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_List(GibCursor end_r_290,
                                                             GibCursor end_r_292,
                                                             GibCursor loc_288,
                                                             GibCursor arg_59_105_149)
{
    if (loc_288 + 18 > end_r_292) {
        gib_grow_region(&loc_288, &end_r_292);
    }
    
    GibPackedTag tmpval_915 = *(GibPackedTag *) arg_59_105_149;
    GibCursor tmpcur_916 = arg_59_105_149 + 1;
    
    
  switch_964:
    ;
    switch (tmpval_915) {
        
      case 0:
        {
            GibInt tmpval_917 = *(GibInt *) tmpcur_916;
            GibCursor tmpcur_918 = tmpcur_916 + sizeof(GibInt);
            GibCursor jump_406 = tmpcur_916 + 8;
            GibCursor loc_347 = loc_288 + 1;
            GibCursor loc_348 = loc_347 + 8;
            
            *(GibPackedTag *) loc_288 = 0;
            
            GibCursor writetag_587 = loc_288 + 1;
            GibCursor after_tag_588 = loc_288 + 1;
            
            *(GibInt *) after_tag_588 = tmpval_917;
            
            GibCursor writecur_592 = after_tag_588 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_24 =
                                                               _copy_List(end_r_290, end_r_292, loc_348, tmpcur_918);
            GibCursor pvrtmp_919 = tmp_struct_24.field0;
            GibCursor pvrtmp_920 = tmp_struct_24.field1;
            GibCursor pvrtmp_921 = tmp_struct_24.field2;
            GibCursor pvrtmp_922 = tmp_struct_24.field3;
            GibCursor pvrtmp_923 = tmp_struct_24.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_25;
            
            return_25.field0 = pvrtmp_919;
            return_25.field1 = pvrtmp_920;
            return_25.field2 = pvrtmp_921;
            return_25.field3 = loc_288;
            return_25.field4 = pvrtmp_923;
            return return_25;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_409 = arg_59_105_149 + 1;
            
            *(GibPackedTag *) loc_288 = 1;
            
            GibCursor writetag_597 = loc_288 + 1;
            GibCursor after_tag_598 = loc_288 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_26;
            
            return_26.field0 = end_r_290;
            return_26.field1 = end_r_292;
            return_26.field2 = jump_loc_409;
            return_26.field3 = loc_288;
            return_26.field4 = after_tag_598;
            return return_26;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_29 = *(uintptr_t *) tmpcur_916;
            GibCursor tmpcur_936 = GIB_UNTAG(tagged_tmpcur_29);
            GibCursor tmpaftercur_937 = tmpcur_916 + 8;
            uint16_t tmptag_938 = GIB_GET_TAG(tagged_tmpcur_29);
            GibCursor end_from_tagged_indr_443 = tmpcur_936 + tmptag_938;
            GibCursor jump_loc_445 = tmpcur_916 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_27 =
                                                               _copy_List(tmpcur_936, end_r_292, loc_288, tmpcur_936);
            GibCursor pvrtmp_939 = tmp_struct_27.field0;
            GibCursor pvrtmp_940 = tmp_struct_27.field1;
            GibCursor pvrtmp_941 = tmp_struct_27.field2;
            GibCursor pvrtmp_942 = tmp_struct_27.field3;
            GibCursor pvrtmp_943 = tmp_struct_27.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_28;
            
            return_28.field0 = end_r_290;
            return_28.field1 = pvrtmp_940;
            return_28.field2 = jump_loc_445;
            return_28.field3 = pvrtmp_942;
            return_28.field4 = pvrtmp_943;
            return return_28;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_32 = *(uintptr_t *) tmpcur_916;
            GibCursor tmpcur_950 = GIB_UNTAG(tagged_tmpcur_32);
            GibCursor tmpaftercur_951 = tmpcur_916 + 8;
            uint16_t tmptag_952 = GIB_GET_TAG(tagged_tmpcur_32);
            GibCursor end_from_tagged_indr_443 = tmpcur_950 + tmptag_952;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_30 =
                                                               _copy_List(tmpcur_950, end_r_292, loc_288, tmpcur_950);
            GibCursor pvrtmp_953 = tmp_struct_30.field0;
            GibCursor pvrtmp_954 = tmp_struct_30.field1;
            GibCursor pvrtmp_955 = tmp_struct_30.field2;
            GibCursor pvrtmp_956 = tmp_struct_30.field3;
            GibCursor pvrtmp_957 = tmp_struct_30.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_31;
            
            return_31.field0 = pvrtmp_953;
            return_31.field1 = pvrtmp_954;
            return_31.field2 = pvrtmp_955;
            return_31.field3 = pvrtmp_956;
            return_31.field4 = pvrtmp_957;
            return return_31;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_915");
            exit(1);
        }
    }
}
GibCursorGibCursorGibIntProd sumList(GibCursor end_r_295,
                                     GibCursor lst_26_110_154)
{
    GibPackedTag tmpval_965 = *(GibPackedTag *) lst_26_110_154;
    GibCursor tmpcur_966 = lst_26_110_154 + 1;
    
    
  switch_984:
    ;
    switch (tmpval_965) {
        
      case 1:
        {
            GibCursor jump_loc_412 = lst_26_110_154 + 1;
            GibCursorGibCursorGibIntProd return_36;
            
            return_36.field0 = end_r_295;
            return_36.field1 = jump_loc_412;
            return_36.field2 = 0;
            return return_36;
            break;
        }
        
      case 0:
        {
            GibInt tmpval_967 = *(GibInt *) tmpcur_966;
            GibCursor tmpcur_968 = tmpcur_966 + sizeof(GibInt);
            GibCursor jump_413 = tmpcur_966 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_37 =
                                          sumList(end_r_295, tmpcur_968);
            GibCursor pvrtmp_969 = tmp_struct_37.field0;
            GibCursor pvrtmp_970 = tmp_struct_37.field1;
            GibInt pvrtmp_971 = tmp_struct_37.field2;
            GibInt tailprim_415 = tmpval_967 + pvrtmp_971;
            GibCursorGibCursorGibIntProd return_38;
            
            return_38.field0 = pvrtmp_969;
            return_38.field1 = pvrtmp_970;
            return_38.field2 = tailprim_415;
            return return_38;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_41 = *(uintptr_t *) tmpcur_966;
            GibCursor tmpcur_972 = GIB_UNTAG(tagged_tmpcur_41);
            GibCursor tmpaftercur_973 = tmpcur_966 + 8;
            uint16_t tmptag_974 = GIB_GET_TAG(tagged_tmpcur_41);
            GibCursor end_from_tagged_indr_449 = tmpcur_972 + tmptag_974;
            GibCursor jump_loc_451 = tmpcur_966 + 8;
            GibCursorGibCursorGibIntProd tmp_struct_39 =
                                          sumList(tmpcur_972, tmpcur_972);
            GibCursor pvrtmp_975 = tmp_struct_39.field0;
            GibCursor pvrtmp_976 = tmp_struct_39.field1;
            GibInt pvrtmp_977 = tmp_struct_39.field2;
            GibCursorGibCursorGibIntProd return_40;
            
            return_40.field0 = end_r_295;
            return_40.field1 = jump_loc_451;
            return_40.field2 = pvrtmp_977;
            return return_40;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_44 = *(uintptr_t *) tmpcur_966;
            GibCursor tmpcur_978 = GIB_UNTAG(tagged_tmpcur_44);
            GibCursor tmpaftercur_979 = tmpcur_966 + 8;
            uint16_t tmptag_980 = GIB_GET_TAG(tagged_tmpcur_44);
            GibCursor end_from_tagged_indr_449 = tmpcur_978 + tmptag_980;
            GibCursorGibCursorGibIntProd tmp_struct_42 =
                                          sumList(tmpcur_978, tmpcur_978);
            GibCursor pvrtmp_981 = tmp_struct_42.field0;
            GibCursor pvrtmp_982 = tmp_struct_42.field1;
            GibInt pvrtmp_983 = tmp_struct_42.field2;
            GibCursorGibCursorGibIntProd return_43;
            
            return_43.field0 = pvrtmp_981;
            return_43.field1 = pvrtmp_982;
            return_43.field2 = pvrtmp_983;
            return return_43;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_965");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd _copy_without_ptrs_List(GibCursor end_r_299,
                                                                          GibCursor end_r_301,
                                                                          GibCursor loc_297,
                                                                          GibCursor arg_64_115_158)
{
    GibPackedTag tmpval_985 = *(GibPackedTag *) arg_64_115_158;
    GibCursor tmpcur_986 = arg_64_115_158 + 1;
    
    
  switch_1034:
    ;
    switch (tmpval_985) {
        
      case 0:
        {
            GibInt tmpval_987 = *(GibInt *) tmpcur_986;
            GibCursor tmpcur_988 = tmpcur_986 + sizeof(GibInt);
            GibCursor jump_416 = tmpcur_986 + 8;
            GibCursor loc_366 = loc_297 + 1;
            GibCursor loc_367 = loc_366 + 8;
            
            *(GibPackedTag *) loc_297 = 0;
            
            GibCursor writetag_634 = loc_297 + 1;
            GibCursor after_tag_635 = loc_297 + 1;
            
            *(GibInt *) after_tag_635 = tmpval_987;
            
            GibCursor writecur_639 = after_tag_635 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_45 =
                                                               _copy_without_ptrs_List(end_r_299, end_r_301, loc_367, tmpcur_988);
            GibCursor pvrtmp_989 = tmp_struct_45.field0;
            GibCursor pvrtmp_990 = tmp_struct_45.field1;
            GibCursor pvrtmp_991 = tmp_struct_45.field2;
            GibCursor pvrtmp_992 = tmp_struct_45.field3;
            GibCursor pvrtmp_993 = tmp_struct_45.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_46;
            
            return_46.field0 = pvrtmp_989;
            return_46.field1 = pvrtmp_990;
            return_46.field2 = pvrtmp_991;
            return_46.field3 = loc_297;
            return_46.field4 = pvrtmp_993;
            return return_46;
            break;
        }
        
      case 1:
        {
            GibCursor jump_loc_419 = arg_64_115_158 + 1;
            
            *(GibPackedTag *) loc_297 = 1;
            
            GibCursor writetag_644 = loc_297 + 1;
            GibCursor after_tag_645 = loc_297 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_47;
            
            return_47.field0 = end_r_299;
            return_47.field1 = end_r_301;
            return_47.field2 = jump_loc_419;
            return_47.field3 = loc_297;
            return_47.field4 = after_tag_645;
            return return_47;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_50 = *(uintptr_t *) tmpcur_986;
            GibCursor tmpcur_1006 = GIB_UNTAG(tagged_tmpcur_50);
            GibCursor tmpaftercur_1007 = tmpcur_986 + 8;
            uint16_t tmptag_1008 = GIB_GET_TAG(tagged_tmpcur_50);
            GibCursor end_from_tagged_indr_455 = tmpcur_1006 + tmptag_1008;
            GibCursor jump_loc_457 = tmpcur_986 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_48 =
                                                               _copy_without_ptrs_List(tmpcur_1006, end_r_301, loc_297, tmpcur_1006);
            GibCursor pvrtmp_1009 = tmp_struct_48.field0;
            GibCursor pvrtmp_1010 = tmp_struct_48.field1;
            GibCursor pvrtmp_1011 = tmp_struct_48.field2;
            GibCursor pvrtmp_1012 = tmp_struct_48.field3;
            GibCursor pvrtmp_1013 = tmp_struct_48.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_49;
            
            return_49.field0 = end_r_299;
            return_49.field1 = pvrtmp_1010;
            return_49.field2 = jump_loc_457;
            return_49.field3 = pvrtmp_1012;
            return_49.field4 = pvrtmp_1013;
            return return_49;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_53 = *(uintptr_t *) tmpcur_986;
            GibCursor tmpcur_1020 = GIB_UNTAG(tagged_tmpcur_53);
            GibCursor tmpaftercur_1021 = tmpcur_986 + 8;
            uint16_t tmptag_1022 = GIB_GET_TAG(tagged_tmpcur_53);
            GibCursor end_from_tagged_indr_455 = tmpcur_1020 + tmptag_1022;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_51 =
                                                               _copy_without_ptrs_List(tmpcur_1020, end_r_301, loc_297, tmpcur_1020);
            GibCursor pvrtmp_1023 = tmp_struct_51.field0;
            GibCursor pvrtmp_1024 = tmp_struct_51.field1;
            GibCursor pvrtmp_1025 = tmp_struct_51.field2;
            GibCursor pvrtmp_1026 = tmp_struct_51.field3;
            GibCursor pvrtmp_1027 = tmp_struct_51.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_52;
            
            return_52.field0 = pvrtmp_1023;
            return_52.field1 = pvrtmp_1024;
            return_52.field2 = pvrtmp_1025;
            return_52.field3 = pvrtmp_1026;
            return_52.field4 = pvrtmp_1027;
            return return_52;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_985");
            exit(1);
        }
    }
}
GibCursorGibCursorGibCursorGibCursorGibCursorProd add1(GibCursor end_r_305,
                                                       GibCursor end_r_307,
                                                       GibCursor loc_303,
                                                       GibCursor lst_31_120_163)
{
    if (loc_303 + 18 > end_r_307) {
        gib_grow_region(&loc_303, &end_r_307);
    }
    
    GibPackedTag tmpval_1035 = *(GibPackedTag *) lst_31_120_163;
    GibCursor tmpcur_1036 = lst_31_120_163 + 1;
    
    
  switch_1084:
    ;
    switch (tmpval_1035) {
        
      case 1:
        {
            GibCursor jump_loc_421 = lst_31_120_163 + 1;
            
            *(GibPackedTag *) loc_303 = 1;
            
            GibCursor writetag_663 = loc_303 + 1;
            GibCursor after_tag_664 = loc_303 + 1;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_54;
            
            return_54.field0 = end_r_305;
            return_54.field1 = end_r_307;
            return_54.field2 = jump_loc_421;
            return_54.field3 = loc_303;
            return_54.field4 = after_tag_664;
            return return_54;
            break;
        }
        
      case 0:
        {
            GibInt tmpval_1041 = *(GibInt *) tmpcur_1036;
            GibCursor tmpcur_1042 = tmpcur_1036 + sizeof(GibInt);
            GibCursor jump_423 = tmpcur_1036 + 8;
            GibInt i1_34_123_166 = tmpval_1041 + 1;
            GibCursor loc_380 = loc_303 + 1;
            GibCursor loc_381 = loc_380 + 8;
            
            *(GibPackedTag *) loc_303 = 0;
            
            GibCursor writetag_675 = loc_303 + 1;
            GibCursor after_tag_676 = loc_303 + 1;
            
            *(GibInt *) after_tag_676 = i1_34_123_166;
            
            GibCursor writecur_680 = after_tag_676 + sizeof(GibInt);
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_55 =
                                                               add1(end_r_305, end_r_307, loc_381, tmpcur_1042);
            GibCursor pvrtmp_1043 = tmp_struct_55.field0;
            GibCursor pvrtmp_1044 = tmp_struct_55.field1;
            GibCursor pvrtmp_1045 = tmp_struct_55.field2;
            GibCursor pvrtmp_1046 = tmp_struct_55.field3;
            GibCursor pvrtmp_1047 = tmp_struct_55.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_56;
            
            return_56.field0 = pvrtmp_1043;
            return_56.field1 = pvrtmp_1044;
            return_56.field2 = pvrtmp_1045;
            return_56.field3 = loc_303;
            return_56.field4 = pvrtmp_1047;
            return return_56;
            break;
        }
        
      case GIB_INDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_59 = *(uintptr_t *) tmpcur_1036;
            GibCursor tmpcur_1056 = GIB_UNTAG(tagged_tmpcur_59);
            GibCursor tmpaftercur_1057 = tmpcur_1036 + 8;
            uint16_t tmptag_1058 = GIB_GET_TAG(tagged_tmpcur_59);
            GibCursor end_from_tagged_indr_461 = tmpcur_1056 + tmptag_1058;
            GibCursor jump_loc_463 = tmpcur_1036 + 8;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_57 =
                                                               add1(tmpcur_1056, end_r_307, loc_303, tmpcur_1056);
            GibCursor pvrtmp_1059 = tmp_struct_57.field0;
            GibCursor pvrtmp_1060 = tmp_struct_57.field1;
            GibCursor pvrtmp_1061 = tmp_struct_57.field2;
            GibCursor pvrtmp_1062 = tmp_struct_57.field3;
            GibCursor pvrtmp_1063 = tmp_struct_57.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_58;
            
            return_58.field0 = end_r_305;
            return_58.field1 = pvrtmp_1060;
            return_58.field2 = jump_loc_463;
            return_58.field3 = pvrtmp_1062;
            return_58.field4 = pvrtmp_1063;
            return return_58;
            break;
        }
        
      case GIB_REDIRECTION_TAG:
        {
            uintptr_t tagged_tmpcur_62 = *(uintptr_t *) tmpcur_1036;
            GibCursor tmpcur_1070 = GIB_UNTAG(tagged_tmpcur_62);
            GibCursor tmpaftercur_1071 = tmpcur_1036 + 8;
            uint16_t tmptag_1072 = GIB_GET_TAG(tagged_tmpcur_62);
            GibCursor end_from_tagged_indr_461 = tmpcur_1070 + tmptag_1072;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_60 =
                                                               add1(tmpcur_1070, end_r_307, loc_303, tmpcur_1070);
            GibCursor pvrtmp_1073 = tmp_struct_60.field0;
            GibCursor pvrtmp_1074 = tmp_struct_60.field1;
            GibCursor pvrtmp_1075 = tmp_struct_60.field2;
            GibCursor pvrtmp_1076 = tmp_struct_60.field3;
            GibCursor pvrtmp_1077 = tmp_struct_60.field4;
            GibCursorGibCursorGibCursorGibCursorGibCursorProd return_61;
            
            return_61.field0 = pvrtmp_1073;
            return_61.field1 = pvrtmp_1074;
            return_61.field2 = pvrtmp_1075;
            return_61.field3 = pvrtmp_1076;
            return_61.field4 = pvrtmp_1077;
            return return_61;
            break;
        }
        
      default:
        {
            printf("%s\n", "Unknown tag in: tmpval_1035");
            exit(1);
        }
    }
}
int main(int argc, char **argv)
{
    int init_79 = gib_init(argc, argv);
    
    info_table_initialize();
    symbol_table_initialize();
    
    GibChunk region_833 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_320 = region_833.start;
    GibCursor end_r_320 = region_833.end;
    GibCursorGibCursorGibCursorProd tmp_struct_66 =
                                     mkList(end_r_320, r_320, 10000000);
    GibCursor pvrtmp_834 = tmp_struct_66.field0;
    GibCursor pvrtmp_835 = tmp_struct_66.field1;
    GibCursor pvrtmp_836 = tmp_struct_66.field2;
    GibChunk region_841 =
             gib_alloc_region_on_heap(gib_get_inf_init_chunk_size());
    GibCursor r_319 = region_841.start;
    GibCursor end_r_319 = region_841.end;
    GibCursor pvrtmp_853;
    GibCursor pvrtmp_854;
    GibCursor pvrtmp_855;
    GibVector *times_71 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_pvrtmp_853;
    struct timespec end_pvrtmp_853;
    
    for (long long iters_pvrtmp_853 = 0; iters_pvrtmp_853 <
         gib_get_iters_param(); iters_pvrtmp_853++) {
        if (iters_pvrtmp_853 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_pvrtmp_853);
        
        GibCursorGibCursorGibCursorGibCursorGibCursorProd tmp_struct_67 =
                                                           add1(pvrtmp_834, end_r_319, r_319, pvrtmp_835);
        GibCursor pvrtmp_842 = tmp_struct_67.field0;
        GibCursor pvrtmp_843 = tmp_struct_67.field1;
        GibCursor pvrtmp_844 = tmp_struct_67.field2;
        GibCursor pvrtmp_845 = tmp_struct_67.field3;
        GibCursor pvrtmp_846 = tmp_struct_67.field4;
        
        pvrtmp_853 = pvrtmp_843;
        pvrtmp_854 = pvrtmp_845;
        pvrtmp_855 = pvrtmp_846;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_pvrtmp_853);
        if (iters_pvrtmp_853 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_68 = gib_difftimespecs(&begin_pvrtmp_853,
                                               &end_pvrtmp_853);
        
        printf("itertime: %lf\n", itertime_68);
        gib_vector_inplace_update(times_71, iters_pvrtmp_853, &itertime_68);
    }
    gib_vector_inplace_sort(times_71, gib_compare_doubles);
    
    double *tmp_72 = (double *) gib_vector_nth(times_71, gib_get_iters_param() /
                                               2);
    double selftimed_70 = *tmp_72;
    double batchtime_69 = gib_sum_timing_array(times_71);
    
    gib_print_timing_array(times_71);
    gib_vector_free(times_71);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_69);
    printf("SELFTIMED: %e\n", selftimed_70);
    
    GibInt timed_744;
    GibVector *times_77 = gib_vector_alloc(gib_get_iters_param(),
                                           sizeof(double));
    struct timespec begin_timed_744;
    struct timespec end_timed_744;
    
    for (long long iters_timed_744 = 0; iters_timed_744 < gib_get_iters_param();
         iters_timed_744++) {
        if (iters_timed_744 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_save_state();
            gib_ptr_bumpalloc_save_state();
        }
        clock_gettime(CLOCK_MONOTONIC_RAW, &begin_timed_744);
        
        GibCursorGibCursorGibIntProd tmp_struct_73 =
                                      sumList(end_r_319, pvrtmp_854);
        GibCursor pvrtmp_863 = tmp_struct_73.field0;
        GibCursor pvrtmp_864 = tmp_struct_73.field1;
        GibInt pvrtmp_865 = tmp_struct_73.field2;
        
        timed_744 = pvrtmp_865;
        clock_gettime(CLOCK_MONOTONIC_RAW, &end_timed_744);
        if (iters_timed_744 != gib_get_iters_param() - 1) {
            gib_list_bumpalloc_restore_state();
            gib_ptr_bumpalloc_restore_state();
        }
        
        double itertime_74 = gib_difftimespecs(&begin_timed_744,
                                               &end_timed_744);
        
        printf("itertime: %lf\n", itertime_74);
        gib_vector_inplace_update(times_77, iters_timed_744, &itertime_74);
    }
    gib_vector_inplace_sort(times_77, gib_compare_doubles);
    
    double *tmp_78 = (double *) gib_vector_nth(times_77, gib_get_iters_param() /
                                               2);
    double selftimed_76 = *tmp_78;
    double batchtime_75 = gib_sum_timing_array(times_77);
    
    gib_print_timing_array(times_77);
    gib_vector_free(times_77);
    printf("ITERS: %ld\n", gib_get_iters_param());
    printf("SIZE: %ld\n", gib_get_size_param());
    printf("BATCHTIME: %e\n", batchtime_75);
    printf("SELFTIMED: %e\n", selftimed_76);
    printf("%ld", timed_744);
    printf("\n");
    
    int exit_80 = gib_exit();
    
    return exit_80;
}